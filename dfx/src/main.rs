use std::error::Error;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use dfx::check::{CheckOptions, check_program_with_options};
use dfx::ghost::check_ghost_program_with_verbose;
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
    #[arg(value_name = "INPUT", required_unless_present = "batch")]
    input: Option<PathBuf>,

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

    /// Process multiple programs from a file containing a list of paths (one per line).
    #[arg(long, value_name = "BATCH_FILE", conflicts_with = "input")]
    batch: Option<PathBuf>,

    /// Skip ghost program checking (only check the input program).
    #[arg(long = "skip-ghost-check")]
    skip_ghost_check: bool,
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
    #[error("type checking failed for '{path}'")]
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
        batch,
        skip_ghost_check,
    } = cli;

    // Handle batch mode
    if let Some(batch_file) = batch {
        return run_batch(
            batch_file,
            output,
            verbose,
            log_solver,
            emit_ghost,
            skip_ghost_check,
        );
    }

    // Single file mode
    let input = input.expect("input is required when not in batch mode");
    process_single_file(
        input,
        output,
        verbose,
        log_solver,
        emit_ghost,
        skip_ghost_check,
    )
}

fn run_batch(
    batch_file: PathBuf,
    output: Option<PathBuf>,
    verbose: bool,
    log_solver: bool,
    emit_ghost: bool,
    skip_ghost_check: bool,
) -> Result<(), CliError> {
    let batch_contents = fs::read_to_string(&batch_file).map_err(|source| CliError::ReadFile {
        path: batch_file.clone(),
        source,
    })?;

    let input_files: Vec<PathBuf> = batch_contents
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| PathBuf::from(line.trim()))
        .collect();

    if input_files.is_empty() {
        eprintln!(
            "warning: batch file '{}' contains no input files",
            batch_file.display()
        );
        return Ok(());
    }

    println!(
        "Processing {} file(s) in batch mode...\n",
        input_files.len()
    );

    let mut success_count = 0;
    let mut failure_count = 0;

    for (idx, input_file) in input_files.iter().enumerate() {
        println!(
            "[{}/{}] Processing: {}",
            idx + 1,
            input_files.len(),
            input_file.display()
        );

        // In batch mode, output should go to a derived path if not stdout
        let file_output = output.as_ref().map(|base_path| {
            let file_stem = input_file.file_stem().unwrap_or_default();
            let parent = base_path
                .parent()
                .unwrap_or_else(|| std::path::Path::new("."));
            parent.join(format!("{}.json", file_stem.to_string_lossy()))
        });

        match process_single_file(
            input_file.clone(),
            file_output,
            verbose,
            log_solver,
            emit_ghost,
            skip_ghost_check,
        ) {
            Ok(()) => {
                println!("  ✅ Success\n");
                success_count += 1;
            }
            Err(err) => {
                eprintln!("  ❌ Failed: {}", err);
                report_error(&err);
                eprintln!();
                failure_count += 1;
            }
        }
    }

    println!(
        "Batch processing complete: {} succeeded, {} failed",
        success_count, failure_count
    );

    if failure_count > 0 {
        Err(CliError::Type {
            path: batch_file,
            source: TypeError::InvalidOp {
                op: format!("{} file(s) failed to process", failure_count),
            },
        })
    } else {
        Ok(())
    }
}

fn process_single_file(
    input: PathBuf,
    output: Option<PathBuf>,
    verbose: bool,
    log_solver: bool,
    emit_ghost: bool,
    skip_ghost_check: bool,
) -> Result<(), CliError> {
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
    if verbose {
        println!("\n╔═══════════════════════════════════════════════════════════╗");
        println!("║                  Checking Input Program                   ║");
        println!("╚═══════════════════════════════════════════════════════════╝\n");
    }

    check_program_with_options(&program, &logic, options).map_err(|source| CliError::Type {
        path: input.clone(),
        source,
    })?;
    if verbose {
        println!("\n✅ Type checking succeeded!\n");
    }
    let ghost = synthesize_ghost_program(&program);

    // Check the ghost program unless skip_ghost_check is set
    if !skip_ghost_check {
        if verbose {
            println!("\n╔═══════════════════════════════════════════════════════════╗");
            println!("║         Checking Synthesized Ghost Program                ║");
            println!("╚═══════════════════════════════════════════════════════════╝\n");
        }

        check_ghost_program_with_verbose(&ghost, verbose).map_err(|err| CliError::Type {
            path: input.clone(),
            source: TypeError::InvalidOp {
                op: format!("Ghost program check failed: {}", err),
            },
        })?;
        if verbose {
            println!("\n✅ Ghost program validation succeeded!\n");
        }
    } else if verbose {
        println!("\n⏭️  Skipping ghost program check (--skip-ghost-check enabled)\n");
    }

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
            eprintln!("  hint: the JSON backend may be missing support for this construct.");
        }
        _ => {}
    }
}
