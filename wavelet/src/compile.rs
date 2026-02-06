use std::collections::HashMap;
use std::path::PathBuf;

use anyhow::Context;
use clap::Parser;
use thiserror::Error;

use wavelet_core::riptide;
use wavelet_elab as elab;

use crate::utils;

/// A compiler from Wavelet's Rust dialect to the core dataflow IR.
#[derive(Debug, Parser)]
pub struct CompileArgs {
    /// Path to the source file written in Wavelet's Rust dialect (default to stdin).
    input: Option<PathBuf>,

    /// Output dataflow graph in JSON (default to stdout).
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Do not remove redundant unit inputs/outputs in the final dataflow.
    #[arg(long)]
    no_trim_io: bool,

    /// Enable translation validation for ghost token insertion.
    #[arg(long)]
    ghost_check: bool,

    /// Emit the elaborated sequential IR to the given file.
    #[arg(long, value_name = "FILE")]
    emit_elab: Option<PathBuf>,

    /// Emit the elaborated sequential IR in JSON to the given file.
    #[arg(long, value_name = "FILE")]
    emit_elab_json: Option<PathBuf>,

    /// Emit the unoptimized process IR in JSON to the given file.
    #[arg(long, value_name = "FILE")]
    emit_unopt: Option<PathBuf>,

    /// Exclude array declarations.
    #[arg(long)]
    exclude_arrays: bool,

    /// Instantiate constants to concrete values ("K1=V1,K2=V2,..."),
    /// so that internal memories (`#[alloc]`) have a concrete size.
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
    #[error("Lean FFI error")]
    RipTideError(#[from] riptide::RipTideError),
}

impl CompileArgs {
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
        let src = utils::read_file_or_stdin(self.input.as_ref())?;
        let mut prog = elab::parse_program(&src)?;

        // Parse constant bindings
        let bindings = self.parse_consts()?;

        if prog.defs.len() == 0 {
            return Err(CompileError::EmptyProgram);
        }

        let typed_prog =
            utils::TaskSpinner::run::<_, CompileError>("type checking + elaboration", |_| {
                prog.desugar_tail_calls();
                let smt = elab::SemanticLogic::new();
                Ok(elab::check::check_program_with_options(
                    &prog,
                    &smt,
                    Default::default(),
                )?)
            })?;

        // Elaboration and validation
        let elab_prog = elab::synthesize_ghost_program(&typed_prog);
        if self.ghost_check {
            utils::TaskSpinner::run("validating token placement", |_| {
                elab::ghost::check_ghost_program_with_verbose(&elab_prog, false)
                    .map_err(CompileError::ElabValidationError)
            })?;
        }

        if let Some(path) = &self.emit_elab {
            std::fs::write(path, format!("{}", elab_prog))
                .context("when writing elaborated program to file")?;
        }

        // Collect all global array declarations and compute their concrete sizes.
        let mut arrays = Vec::new();
        if !self.exclude_arrays {
            if let Some(main_fn) = typed_prog.defs.last() {
                // TODO: this is assuming that all functions use the same set
                // of global arrays without renaming.
                arrays.extend(main_fn.get_array_decls(&bindings)?);
            }
        }

        // Transfer to the Lean side through FFI
        let json = elab::ghost::json::export_program_json(arrays, &elab_prog)?;
        if let Some(path) = &self.emit_elab_json {
            std::fs::write(path, &json)
                .context("when writing elaborated program in JSON to file")?;
        }

        let core_prog = riptide::Prog::from_json(&json)
            .context("when converting elaborated program to lean")?;

        core_prog
            .validate()
            .context("when validating core program")?;
        let core_proc =
            utils::TaskSpinner::run::<_, CompileError>("lowering control-flow", |progress| {
                let core_proc = core_prog
                    .lower_control_flow()
                    .context("when lowering control-flow")?;
                progress.set_message(format!(
                    "{} ({} non-trivial) ops",
                    core_proc.num_atoms(),
                    core_proc.num_non_trivial_atoms()
                ));
                Ok(core_proc)
            })?;
        core_proc
            .validate()
            .context("when validating dataflow after control-flow lowering")?;

        if let Some(path) = &self.emit_unopt {
            std::fs::write(path, core_proc.to_json()?)
                .context("when writing unoptimized process to file")?;
        }

        // Remove unnecessary output(s).
        let core_proc = if self.no_trim_io {
            core_proc
        } else {
            core_proc.trim_unit_io()
        };

        // Some graph rewriting for legalization and optimization
        // TODO: Disabling some rules for now since the handshake
        // backend does not support `inv` operator yet.
        let core_proc = utils::TaskSpinner::run::<_, CompileError>("optimization", |progress| {
            let core_proc = core_proc.optimize(vec![
                "carry-fork-steer-to-inv-left",
                "carry-fork-steer-to-inv-right",
            ]);
            progress.set_message(format!(
                "{} ({} non-trivial) ops",
                core_proc.num_atoms(),
                core_proc.num_non_trivial_atoms()
            ));
            Ok(core_proc)
        })?;

        core_proc
            .validate()
            .context("when validating final dataflow")?;

        utils::write_file_or_stdout(self.output.as_ref(), core_proc.to_json()?)?;

        Ok(())
    }
}
