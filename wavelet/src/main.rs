//! Main CLI of Wavelet.

mod compile;

use std::process::ExitCode;

use clap::{Parser, Subcommand};
use thiserror::Error;

use compile::{CompileArgs, CompileError};

#[derive(Debug, Parser)]
#[command(long_about = None)]
struct Args {
    #[clap(subcommand)]
    action: Action,
}

#[derive(Debug, Subcommand)]
enum Action {
    Compile(CompileArgs),
}

#[derive(Debug, Error)]
enum Error {
    #[error("compile error: {0}")]
    CompileError(#[from] CompileError),
}

impl Args {
    fn run(&self) -> Result<(), Error> {
        match &self.action {
            Action::Compile(args) => Ok(args.run()?),
        }
    }
}

fn main() -> ExitCode {
    match Args::parse().run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("{}", err);
            ExitCode::FAILURE
        }
    }
}
