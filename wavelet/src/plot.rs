use clap::Parser;
use std::path::PathBuf;
use thiserror::Error;

use wavelet_core::riptide;

use crate::utils;

/// Plots the dataflow IR in Graphviz DOT format.
#[derive(Debug, Parser)]
pub struct PlotArgs {
    /// Path to the source dataflow IR in JSON (default to stdin).
    input: Option<PathBuf>,

    /// Output file in DOT format (default to stdout).
    #[arg(short, long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Error)]
pub enum PlotError {
    #[error(transparent)]
    AnyhowError(#[from] anyhow::Error),
    #[error("Lean FFI error")]
    RipTideError(#[from] riptide::RipTideError),
}

impl PlotArgs {
    pub fn run(&self) -> Result<(), PlotError> {
        let json = utils::read_file_or_stdin(self.input.as_ref())?;
        let proc = riptide::Proc::from_json(&json)?;
        utils::write_file_or_stdout(self.output.as_ref(), proc.to_dot()?)?;
        Ok(())
    }
}
