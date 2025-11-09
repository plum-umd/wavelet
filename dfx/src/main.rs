use std::error::Error;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use dfx::check::{CheckOptions, check_program_with_options};
use dfx::ghost::json::{ExportError, export_program_json};
use dfx::{ParseError, SemanticLogic, TypeError, parse_program, synthesize_ghost_program};
use thiserror::Error;

/// Command line interface for the dfx analyzer.
#[derive(Parser, Debug)]
#[command(
    name = "dfx",
    about = "Type-check capability-annotated Rust and emit ghost JSON",
    author,
    version
)]
struct Cli {
    /// Path to the Rust source file to analyze.
    #[arg(value_name = "INPUT")]
    input: PathBuf,

    /// Write the resulting ghost JSON to this file. Defaults to stdout.
    #[arg(short, long, value_name = "OUTPUT")]
    output: Option<PathBuf>,

    /// Print the evolving typing context while checking.
    #[arg(long)]
    verbose: bool,

    /// Log SMT solver queries issued during checking.
    #[arg(long = "log-solver")]
    log_solver: bool,

    /// Emit a textual rendering of the ghost program.
    #[arg(long)]
    emit_ghost: bool,
}

#[derive(Debug, Error)]
enum CliError {
    #[error("failed to read input '{path}': {source}")]
    ReadFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to parse '{path}': {source}")]
    Parse {
        path: PathBuf,
        #[source]
        source: ParseError,
    },
    #[error("type checking failed for '{path}': {source}")]
    Type {
        path: PathBuf,
        #[source]
        source: TypeError,
    },
    #[error("failed to serialize ghost program: {source}")]
    Export {
        #[source]
        source: ExportError,
    },
    #[error("failed to write output '{path}': {source}")]
    WriteFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match run(cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            report_error(&err);
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<(), CliError> {
    let Cli {
        input,
        output,
        verbose,
        log_solver,
        emit_ghost,
    } = cli;
    let source = fs::read_to_string(&input).map_err(|source| CliError::ReadFile {
        path: input.clone(),
        source,
    })?;

    let program = parse_program(&source).map_err(|source| CliError::Parse {
        path: input.clone(),
        source,
    })?;

    let mut options = CheckOptions::default();
    options.verbose = verbose;
    options.log_solver_queries = log_solver;
    let logic = SemanticLogic::new();

    check_program_with_options(&program, &logic, options).map_err(|source| CliError::Type {
        path: input.clone(),
        source,
    })?;

    let ghost = synthesize_ghost_program(&program);
    if emit_ghost {
        println!("{}", ghost);
    }
    let rendered = export_program_json(&ghost).map_err(|source| CliError::Export { source })?;

    if let Some(out_path) = output {
        fs::write(&out_path, rendered).map_err(|source| CliError::WriteFile {
            path: out_path,
            source,
        })?;
    } else {
        println!("{}", rendered);
    }

    Ok(())
}

fn report_error(err: &CliError) {
    eprintln!("error: {}", err);
    let mut source = err.source();
    while let Some(cause) = source {
        eprintln!("  caused by: {}", cause);
        source = cause.source();
    }

    match err {
        CliError::Parse { .. } => {
            eprintln!(
                "  hint: ensure capability annotations use #[cap(..)] and that the file compiles as Rust."
            );
        }
        CliError::Type { .. } => {
            eprintln!(
                "  hint: re-run with --verbose or --log-solver for more context about the failing obligation."
            );
        }
        CliError::Export { .. } => {
            eprintln!(
                "  hint: the JSON backend may be missing support for this construct."
            );
        }
        _ => {}
    }
}
