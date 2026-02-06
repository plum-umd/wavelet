//! Some common utilities.

use std::io::{IsTerminal, Read, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::Context;
use indicatif::style::ProgressTracker;
use indicatif::{HumanDuration, ProgressBar, ProgressState, ProgressStyle};

/// Reads the optional file or stdin into a string.
pub fn read_file_or_stdin(path: Option<&PathBuf>) -> anyhow::Result<String> {
    if let Some(path) = path {
        std::fs::read_to_string(&path)
            .with_context(|| format!("when reading input file {}", path.display()))
    } else {
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .context("when reading from stdin")?;
        Ok(buf)
    }
}

/// Writes to the optional file or stdout.
pub fn write_file_or_stdout(
    path: Option<&PathBuf>,
    content: impl AsRef<[u8]>,
) -> anyhow::Result<()> {
    if let Some(path) = path {
        std::fs::write(&path, content)
            .with_context(|| format!("when writing to output file {}", path.display()))
    } else {
        std::io::stdout()
            .lock()
            .write_all(content.as_ref())
            .context("when writing to stdout")
    }
}

pub struct TaskSpinner {
    name: String,
    bar: ProgressBar,
}

impl Drop for TaskSpinner {
    fn drop(&mut self) {
        self.bar.disable_steady_tick();
    }
}

/// Similar to the built-in `elapsed` template key, but
/// shows milliseconds if the elapsed time is less than 1s.
struct ElapsedMillisecondTracker;

impl ProgressTracker for ElapsedMillisecondTracker {
    fn clone_box(&self) -> Box<dyn ProgressTracker> {
        Box::new(ElapsedMillisecondTracker)
    }

    fn tick(&mut self, _state: &ProgressState, _now: Instant) {}

    fn reset(&mut self, _state: &ProgressState, _now: Instant) {}

    fn write(&self, state: &ProgressState, w: &mut dyn std::fmt::Write) {
        let elapsed = state.elapsed();
        if elapsed < Duration::from_secs(1) {
            write!(w, "{}ms", elapsed.as_millis()).unwrap();
        } else {
            write!(w, "{:#}", HumanDuration(elapsed)).unwrap();
        }
    }
}

impl TaskSpinner {
    /// Creates a new spinner with the given task name.
    pub fn new(task_name: impl Into<String>) -> anyhow::Result<Self> {
        let task_name = task_name.into();
        let bar = ProgressBar::new_spinner();
        let style = ProgressStyle::with_template("{spinner} {msg:.bold} ({elapsed_ms})")
            .context("failed to parse template")?
            .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏✔")
            .with_key("elapsed_ms", ElapsedMillisecondTracker);
        bar.set_style(style);
        bar.set_message(task_name.clone());
        bar.enable_steady_tick(Duration::from_millis(50));

        if !std::io::stderr().is_terminal() {
            eprintln!("[{}] started", task_name);
        }

        Ok(Self {
            name: task_name,
            bar,
        })
    }

    /// Marks the task as finished
    pub fn finish(self) {
        self.bar.finish();
    }

    /// Sets the message of the spinner besides the task name.
    pub fn set_message(&mut self, msg: impl Into<String>) {
        if !std::io::stderr().is_terminal() {
            eprintln!("[{}] {}", self.name, msg.into());
        } else {
            self.bar
                .set_message(format!("{}: {}", self.name, msg.into()));
        }
    }

    /// Creates a spinner for the task name, runs the given function,
    /// and then marks the task as finished.
    pub fn run<V, E>(
        task_name: impl Into<String>,
        f: impl FnOnce(&mut TaskSpinner) -> Result<V, E>,
    ) -> Result<V, E>
    where
        E: From<anyhow::Error>,
    {
        let begin = Instant::now();
        let mut spinner = Self::new(task_name)?;
        let res = f(&mut spinner);
        let elapsed = begin.elapsed();
        if !std::io::stderr().is_terminal() {
            eprintln!("[{}] finished in {} ms", spinner.name, elapsed.as_millis());
        }
        spinner.finish();
        res
    }
}
