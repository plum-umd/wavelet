//! Implementation of the `compile` subcommand.

use std::path::PathBuf;
use std::{collections::HashMap, io::Write};

use anyhow::Context;
use clap::{Parser, ValueEnum};
use thiserror::Error;

use wavelet_core::riptide;
use wavelet_elab as elab;

/// Target IR to output.
#[derive(Debug, Parser, ValueEnum, Clone, PartialEq, Eq)]
enum Target {
    /// Elaborated imperative IR
    Elab,
    /// Elaborated imperative IR in JSON
    ElabJson,
    /// Unoptimized dataflow process
    Unopt,
    /// Optimized dataflow process
    Opt,
    /// CIRCT Handshake dialect
    Handshake,
    /// DOT format
    Dot,
}

#[derive(Debug, Parser)]
pub struct CompileArgs {
    /// Path to the source file (in Wavelet's Rust dialect).
    input: PathBuf,

    /// Output file (stdout if not provided).
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Remove ghost and unit output ports for a smaller dataflow graph.
    #[arg(long)]
    trim_output: bool,

    /// Enable translation validation for ghost token insertion.
    #[arg(long)]
    ghost_check: bool,

    /// Target IR to output.
    #[arg(long, default_value = "opt")]
    target: Target,

    /// Instantiate constants to concrete values ("K1=V1,K2=V2,...").
    /// Primarily used for lowering to CIRCT/Handshake.
    #[arg(short, long, num_args = 0..)]
    consts: Vec<String>,
}

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("compiling empty program")]
    EmptyProgram,
    #[error(transparent)]
    AnyhowError(#[from] anyhow::Error),
    #[error("invalid constant binding(s): {0}")]
    InvalidConstBindings(String),
    #[error("parse error: {0}")]
    ElabParseError(#[from] elab::ParseError),
    #[error("type error: {0}")]
    ElabTypeError(#[from] elab::TypeError),
    #[error("validation error: {0}")]
    ElabValidationError(String),
    #[error("elaboration export error: {0}")]
    ElabExportError(#[from] elab::ghost::json::ExportError),
}

impl CompileArgs {
    /// Writes the given content to the configured output.
    fn output<C>(&self, content: C) -> Result<(), CompileError>
    where
        C: AsRef<[u8]>,
    {
        if let Some(output_path) = &self.output {
            std::fs::write(output_path, content).context("when writing to the output file")?;
        } else {
            std::io::stdout()
                .lock()
                .write_all(content.as_ref())
                .context("when writing to stdout")?;
        }
        Ok(())
    }

    /// Parses user provided constant bindings.
    fn parse_consts(&self) -> Result<HashMap<String, i64>, CompileError> {
        let mut bindings = HashMap::new();
        for consts in &self.consts {
            for pair in consts.split(',') {
                let pair = pair.trim();
                if !pair.is_empty() {
                    if let Some((k, v)) = pair.split_once('=') {
                        let key = k.trim().to_string();
                        let value = v
                            .trim()
                            .parse::<i64>()
                            .map_err(|_| CompileError::InvalidConstBindings(consts.clone()))?;
                        bindings.insert(key, value);
                    } else {
                        return Err(CompileError::InvalidConstBindings(consts.clone()));
                    }
                }
            }
        }
        Ok(bindings)
    }

    pub fn run(&self) -> Result<(), CompileError> {
        // Load source program
        let src = std::fs::read_to_string(&self.input).context("when reading input file")?;
        let mut prog = elab::parse_program(&src)?;

        // Parse constant bindings
        let bindings = self.parse_consts()?;

        if prog.defs.len() == 0 {
            return Err(CompileError::EmptyProgram);
        }

        eprintln!("preprocessing...");
        prog.desugar_tail_calls();

        // Type check
        eprintln!("type checking...");
        let smt = elab::SemanticLogic::new();
        let typed_prog = elab::check::check_program_with_options(&prog, &smt, Default::default())?;

        // Elaboration and validation
        let elab_prog = elab::synthesize_ghost_program(&typed_prog);
        if self.ghost_check {
            eprintln!("validating token placement...");
            elab::ghost::check_ghost_program_with_verbose(&elab_prog, false)
                .map_err(CompileError::ElabValidationError)?;
        }
        let elab_main_fn = elab_prog.defs.last().ok_or(CompileError::EmptyProgram)?;

        if self.target == Target::Elab {
            return self.output(format!("{}", elab_prog));
        }

        // Collect all global array declarations and compute their concrete sizes.
        let mut arrays = Vec::new();
        if self.target == Target::Handshake {
            if let Some(main_fn) = typed_prog.defs.last() {
                // TODO: this is assuming that all functions use the same set
                // of global arrays without renaming.
                arrays.extend(main_fn.get_array_decls(&bindings)?);
            }
        }

        // Transfer to the Lean side through FFI
        let json = elab::ghost::json::export_program_json(arrays, &elab_prog)?;
        if self.target == Target::ElabJson {
            return self.output(json);
        }

        let core_prog = riptide::Prog::from_json(&json)
            .context("when converting elaborated program to lean")?;

        // Validation
        eprintln!("validating core program...");
        core_prog
            .validate()
            .context("when validating core program")?;

        // Lower control-flow to pure dataflow
        eprintln!("lowering control-flow...");
        let core_proc = core_prog
            .lower_control_flow()
            .context("when lowering control-flow")?;
        eprintln!(
            "unoptimized: {} ({}) ops",
            core_proc.num_atoms(),
            core_proc.num_non_trivial_atoms()
        );

        core_proc
            .validate()
            .context("when validating dataflow after control-flow lowering")?;

        if self.target == Target::Unopt {
            return self.output(core_proc.to_json());
        }

        // Remove unnecessary output(s).
        let core_proc = if self.trim_output {
            // The current elaborator should generate exactly two outputs:
            // one for the actual output, and one for the ghost permission token.
            assert!(core_proc.num_outputs() == 2);
            eprintln!("trimming ghost and unit outputs...");

            if elab_main_fn.returns.is_unit() {
                core_proc.sink_last_n_outputs(2)
            } else {
                core_proc.sink_last_n_outputs(1)
            }
        } else {
            core_proc
        };

        // Optimize
        eprintln!("optimizing...");
        let disabled_rules = if self.target == Target::Handshake {
            // Handshake backend does not support `inv` operator yet.
            vec![
                "carry-fork-steer-to-inv-left",
                "carry-fork-steer-to-inv-right",
            ]
        } else {
            vec![]
        };
        let core_proc = core_proc.optimize(disabled_rules);
        eprintln!(
            "final: {} ({}) ops",
            core_proc.num_atoms(),
            core_proc.num_non_trivial_atoms()
        );

        core_proc
            .validate()
            .context("when validating final dataflow")?;

        if self.target == Target::Handshake {
            return self.output(
                core_proc
                    .to_handshake()
                    .context("when compiling to handshake dialect")?,
            );
        }

        if self.target == Target::Dot {
            return self.output(
                core_proc
                    .to_dot()
                    .context("when generating the graph in DOT format")?,
            );
        }

        return self.output(core_proc.to_json());
    }
}
