use clap::Parser;
use std::path::PathBuf;
use thiserror::Error;

use wavelet_core::riptide;

use crate::utils;

/// Compiles from the dataflow IR to the CIRCT Handshake dialect.
#[derive(Debug, Parser)]
pub struct HandshakeArgs {
    /// Path to the source dataflow IR in JSON (default to stdin).
    input: Option<PathBuf>,

    /// Output file in MLIR/Handshake (default to stdout).
    #[arg(short, long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Error)]
pub enum HandshakeError {
    #[error(transparent)]
    AnyhowError(#[from] anyhow::Error),
    #[error("Lean FFI error")]
    RipTideError(#[from] riptide::RipTideError),
}

impl HandshakeArgs {
    pub fn run(&self) -> Result<(), HandshakeError> {
        let json = utils::read_file_or_stdin(self.input.as_ref())?;
        let proc = riptide::Proc::from_json(&json)?;
        utils::write_file_or_stdout(self.output.as_ref(), proc.to_handshake()?)?;
        Ok(())
    }
}
