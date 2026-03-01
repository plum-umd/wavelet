use clap::Parser;
use std::path::PathBuf;
use thiserror::Error;

use wavelet_core::riptide;

use crate::utils;

/// Dataflow IR interpreter.
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

    /// Do not report intemediate steps, and keep executing until termination.
    #[arg(long)]
    no_bound: bool,
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
                    config.store_mem(name, addr.into(), value);
                    addr += 1;
                }
            }
        }

        let mut progress = utils::TaskSpinner::new("executing")?;
        let mut cycles = 0;
        let mut fired = 0;
        loop {
            let trace = config.eager_steps(if self.no_bound { None } else { Some(10) })?;
            if trace.is_empty() {
                break;
            }
            cycles += trace.len();
            fired += trace.iter().map(|labels| labels.len()).sum::<usize>();
            progress.set_message(format!("{} ops fired in {} cycles", fired, cycles));
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

        for mem in config.mem_names()? {
            // Tries to print the first chunk of contiguous memory values as an array for better readability.
            let mut cont_mem = Vec::new();
            let mut cont_addr = 0;
            while let Some(value) = config.load_mem(&mem, cont_addr.into())? {
                cont_mem.push(format!("{}", value));
                cont_addr += 1;
            }

            if !cont_mem.is_empty() {
                println!("{}: [{}]", mem, cont_mem.join(", "));
            } else {
                println!("{}:", mem);
            }

            // Look up other addresses
            let mut addrs = config.mem_addrs(&mem)?;
            addrs.sort_by_key(|v| i32::try_from(v.clone()).unwrap_or(i32::MIN));

            for addr in addrs {
                if let Ok(addr) = i32::try_from(addr.clone()) {
                    if addr < cont_addr {
                        continue;
                    }
                }
                if let Some(value) = config.load_mem(&mem, addr.clone())? {
                    println!("  {}: {}", addr, value);
                }
            }
        }

        Ok(())
    }
}
