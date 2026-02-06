use clap::Parser;
use std::path::PathBuf;
use thiserror::Error;

use wavelet_core::riptide;

use crate::utils;

/// Compiles from the dataflow IR to the CIRCT Handshake dialect.
#[derive(Debug, Parser)]
pub struct ExecArgs {
    /// Path to the source dataflow IR in JSON (default to stdin).
    input: Option<PathBuf>,

    /// Comma-separated list of arguments.
    #[arg(short, long, num_args = 0..)]
    args: Vec<String>,

    /// Initializes a memory with the given array of values ("MEM=V1,V2,...")
    #[arg(long, num_args = 0..)]
    mem: Vec<String>,
}

#[derive(Debug, Error)]
pub enum ExecError {
    #[error(transparent)]
    AnyhowError(#[from] anyhow::Error),
    #[error("Lean FFI error")]
    RipTideError(#[from] riptide::RipTideError),
    #[error("invalid value: {0}")]
    InvalidValue(String),
    #[error("missing outputs at termination")]
    MissingOutputs(#[source] riptide::RipTideError),
}

impl ExecArgs {
    /// A simple parser for values.
    fn parse_value(arg: &str) -> Result<riptide::Value, ExecError> {
        let arg = arg.trim();
        if arg == "true" {
            Ok(true.into())
        } else if arg == "false" {
            Ok(false.into())
        } else if arg == "()" {
            Ok(riptide::Value::unit())
        } else if let Ok(i) = arg.parse::<i32>() {
            Ok(i.into())
        } else {
            Err(ExecError::InvalidValue(arg.to_string()))
        }
    }

    pub fn run(&self) -> Result<(), ExecError> {
        let json = utils::read_file_or_stdin(self.input.as_ref())?;
        let proc = riptide::Proc::from_json(&json)?;

        let mut config = riptide::Config::new(&proc);
        let mut inputs = Vec::new();

        // Initialize inputs
        for args in &self.args {
            for arg in args.split(',') {
                let arg = arg.trim();
                if arg.is_empty() {
                    continue;
                }
                inputs.push(Self::parse_value(arg)?);
            }
        }
        config.push_inputs(inputs)?;

        // Initialize memories
        for mem in &self.mem {
            if let Some((name, values)) = mem.split_once('=') {
                let mut addr = 0i32;
                for value in values.split(',') {
                    let value = value.trim();
                    if value.is_empty() {
                        addr += 1;
                        continue;
                    }
                    let value = Self::parse_value(value)?;
                    config.store_mem(name, &addr.into(), &value);
                    addr += 1;
                }
            }
        }

        let mut progress = utils::TaskSpinner::new("executing")?;
        let mut total_steps = 0;
        loop {
            let trace = config.steps(Some(10))?;
            if trace.is_empty() {
                break;
            }
            total_steps += trace.len();
            progress.set_message(format!("{} steps", total_steps));
        }
        progress.finish();

        let outputs = config.pop_outputs().map_err(ExecError::MissingOutputs)?;
        println!(
            "outputs: {}",
            outputs
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );

        println!("memory state:");
        for mem in config.mem_names()? {
            println!("  {}:", mem);
            for addr in config.mem_addrs(&mem)? {
                if let Some(value) = config.load_mem(&mem, &addr)? {
                    println!("    {}: {}", addr, value);
                }
            }
        }

        Ok(())
    }
}
