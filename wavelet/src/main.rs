//! Main CLI of Wavelet.

mod compile;
mod exec;
mod handshake;
mod plot;
mod utils;

use std::process::ExitCode;

use clap::{Parser, Subcommand};
use thiserror::Error;

#[derive(Debug, Parser)]
#[command(long_about = None)]
struct Args {
    #[clap(subcommand)]
    action: Action,
}

#[derive(Debug, Subcommand)]
enum Action {
    Compile(compile::CompileArgs),
    Handshake(handshake::HandshakeArgs),
    Plot(plot::PlotArgs),
    Exec(exec::ExecArgs),
}

#[derive(Debug, Error)]
enum Error {
    #[error("compile error: {0}")]
    CompileError(#[from] compile::CompileError),
    #[error("handshake compilation error: {0}")]
    HandshakeError(#[from] handshake::HandshakeError),
    #[error("plot error: {0}")]
    PlotError(#[from] plot::PlotError),
    #[error("execution error: {0}")]
    ExecError(#[from] exec::ExecError),
}

impl Args {
    fn run(&self) -> Result<(), Error> {
        match &self.action {
            Action::Compile(args) => Ok(args.run()?),
            Action::Handshake(args) => Ok(args.run()?),
            Action::Plot(args) => Ok(args.run()?),
            Action::Exec(args) => Ok(args.run()?),
        }
    }
}

fn main() -> ExitCode {
    match Args::parse().run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            let err: anyhow::Error = err.into();
            eprintln!("{}", err);
            err.chain()
                .skip(2)
                .for_each(|cause| eprintln!("  caused by: {}", cause));
            ExitCode::FAILURE
        }
    }
}
