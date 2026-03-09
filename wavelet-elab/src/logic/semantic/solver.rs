//! SMT-based reasoning for proposition contexts.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::{self, Display},
    io::{BufRead, BufReader, Read, Write},
    process::{Child, ChildStderr, ChildStdin, ChildStdout, Command, Stdio},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
};

use crate::logic::cap::RegionModel;

/// An index expression used throughout the type system. Indices are
/// symbolic arithmetic expressions built from variables, constants and
/// addition/subtraction.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Idx {
    /// A constant index.
    Const(i64),
    /// A variable index (function parameters or local variables).
    Var(String),
    /// Sum of two indices.
    Add(Box<Idx>, Box<Idx>),
    /// Difference of two indices.
    Sub(Box<Idx>, Box<Idx>),
    /// Product of two indices.
    Mul(Box<Idx>, Box<Idx>),
}

impl Idx {
    /// Create a constant index from a `usize`.
    pub fn from_usize(n: usize) -> Self {
        Idx::Const(n as i64)
    }
}

/// A real-valued expression for fractional permissions and other
/// real arithmetic. Similar to `Idx` but represents values in the
/// SMT `Real` sort rather than `Int`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RealExpr {
    /// A rational constant, encoded as numerator/denominator pair.
    Const(i64, i64),
    /// A named real variable.
    Var(String),
    /// Sum of two real expressions.
    Add(Box<RealExpr>, Box<RealExpr>),
    /// Difference of two real expressions.
    Sub(Box<RealExpr>, Box<RealExpr>),
}

impl Display for RealExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RealExpr::Const(n, d) => {
                if *d == 1 {
                    write!(f, "{}", n)
                } else {
                    write!(f, "({}/{})", n, d)
                }
            }
            RealExpr::Var(name) => write!(f, "{}", name),
            RealExpr::Add(lhs, rhs) => write!(f, "({} + {})", lhs, rhs),
            RealExpr::Sub(lhs, rhs) => write!(f, "({} - {})", lhs, rhs),
        }
    }
}

impl RealExpr {
    /// Create a rational constant from a numerator and denominator.
    pub fn from_ratio(num: i64, den: i64) -> Self {
        assert!(den != 0, "denominator must not be zero");
        let (n, d) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd_i64(n.abs(), d);
        RealExpr::Const(n / g, d / g)
    }

    /// Create an integer constant (denominator = 1).
    pub fn from_int(n: i64) -> Self {
        RealExpr::Const(n, 1)
    }

    /// Construct the sum of two real expressions.
    pub fn sum(a: RealExpr, b: RealExpr) -> Self {
        RealExpr::Add(Box::new(a), Box::new(b))
    }

    /// Construct the difference of two real expressions.
    pub fn diff(a: RealExpr, b: RealExpr) -> Self {
        RealExpr::Sub(Box::new(a), Box::new(b))
    }
}

/// Compute GCD for normalizing rational constants.
fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.abs()
}

/// Logical atoms over index expressions. Only simple relational
/// predicates are supported.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// `a <= b` (integer comparison)
    Le(Idx, Idx),
    /// `a < b` (integer comparison)
    Lt(Idx, Idx),
    /// `a == b` (integer comparison)
    Eq(Idx, Idx),
    /// `a <= b` (real comparison)
    RealLe(RealExpr, RealExpr),
    /// `a < b` (real comparison)
    RealLt(RealExpr, RealExpr),
    /// `a == b` (real comparison)
    RealEq(RealExpr, RealExpr),
    /// Named boolean variable.
    BoolVar(String),
    /// Conjunction of two atoms.
    And(Box<Atom>, Box<Atom>),
    /// Disjunction of two atoms.
    Or(Box<Atom>, Box<Atom>),
    /// Implication between atoms (`lhs => rhs`).
    Implies(Box<Atom>, Box<Atom>),
    /// Negation of an atom.
    Not(Box<Atom>),
}

/// A collection of logical atoms. Semantically this is a big
/// conjunction.
#[derive(Clone, Debug, Default)]
pub struct Phi {
    pub atoms: Vec<Atom>,
}

impl Phi {
    /// Create a new, empty `Phi`.
    pub fn new() -> Self {
        Self { atoms: Vec::new() }
    }

    /// Append a new atom to the context.
    pub fn push(&mut self, atom: Atom) {
        self.atoms.push(atom);
    }

    /// Iterate over all atoms contained in this context.
    pub fn iter(&self) -> std::slice::Iter<'_, Atom> {
        self.atoms.iter()
    }
}

/// A solver for entailment queries over [`Phi`].
pub trait PhiSolver {
    type Region: RegionModel;

    /// Determine whether the given atom is entailed by the current
    /// context.
    fn entails(&self, ctx: &Phi, atom: &Atom) -> bool;
}

/// Supported SMT backends.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SmtBackend {
    #[default]
    Z3,
    Cvc5,
}

impl SmtBackend {
    fn default_command(self) -> &'static str {
        match self {
            SmtBackend::Z3 => "z3",
            SmtBackend::Cvc5 => "cvc5",
        }
    }

    fn configure_command(self, command: &mut Command, config: &SmtSolverConfig) {
        match self {
            SmtBackend::Z3 => {
                command.args(["-in", "-smt2"]);
                if let Some(timeout_ms) = config.timeout_ms {
                    command.arg(format!("-t:{timeout_ms}"));
                }
                if let Some(rlimit) = config.rlimit {
                    command.arg(format!("rlimit={rlimit}"));
                }
            }
            SmtBackend::Cvc5 => {
                command.args(["--lang=smt2", "--incremental"]);
            }
        }
    }
}

impl Display for SmtBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtBackend::Z3 => write!(f, "z3"),
            SmtBackend::Cvc5 => write!(f, "cvc5"),
        }
    }
}

/// Configuration for launching the SMT solver process.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmtSolverConfig {
    backend: SmtBackend,
    timeout_ms: Option<u64>,
    rlimit: Option<u64>,
}

impl Default for SmtSolverConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSolverConfig {
    /// Create a default Z3 configuration.
    pub fn new() -> Self {
        Self::with_backend(SmtBackend::Cvc5)
    }

    /// Create a configuration for the given backend.
    pub fn with_backend(backend: SmtBackend) -> Self {
        Self {
            backend,
            timeout_ms: None,
            rlimit: None,
        }
    }

    /// Configure a timeout (in milliseconds) applied to solver invocations.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }

    /// Configure a resource limit for backends that support it.
    pub fn with_rlimit(mut self, rlimit: u64) -> Self {
        self.rlimit = Some(rlimit);
        self
    }

    /// Return the selected backend.
    pub fn backend(&self) -> SmtBackend {
        self.backend
    }

    /// Return the configured timeout, if any.
    pub fn timeout_ms(&self) -> Option<u64> {
        self.timeout_ms
    }

    /// Return the configured resource limit, if any.
    pub fn rlimit(&self) -> Option<u64> {
        self.rlimit
    }
}

/// SMT-backed solver that emits SMT-LIB directly and invokes an external solver.
pub struct SmtSolver {
    config: SmtSolverConfig,
    log_queries: Arc<AtomicBool>,
    cache: Arc<Mutex<HashMap<String, CheckSatResult>>>,
    process: Arc<Mutex<Option<SolverProcess>>>,
}

impl SmtSolver {
    /// Create a solver that looks for `z3` on the current `$PATH`.
    pub fn new() -> Self {
        Self::from_config(SmtSolverConfig::new())
    }

    /// Create a solver from an explicit backend configuration.
    pub fn from_config(config: SmtSolverConfig) -> Self {
        Self {
            config,
            log_queries: Arc::new(AtomicBool::new(false)),
            cache: Arc::new(Mutex::new(HashMap::new())),
            process: Arc::new(Mutex::new(None)),
        }
    }

    /// Create a solver for the given backend using its default command name.
    pub fn with_backend(backend: SmtBackend) -> Self {
        Self::from_config(SmtSolverConfig::with_backend(backend))
    }

    /// Configure a timeout (in milliseconds) applied to solver invocations.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.config = self.config.clone().with_timeout(timeout_ms);
        self
    }

    /// Configure a resource limit for backends that support it.
    pub fn with_rlimit(mut self, rlimit: u64) -> Self {
        self.config = self.config.clone().with_rlimit(rlimit);
        self
    }

    /// Enable or disable dumping of SMT queries to stdout.
    pub fn set_query_logging(&self, enabled: bool) {
        self.log_queries.store(enabled, Ordering::SeqCst);
    }

    pub(crate) fn is_query_logging_enabled(&self) -> bool {
        self.log_queries.load(Ordering::Relaxed)
    }

    pub(crate) fn backend(&self) -> SmtBackend {
        self.config.backend()
    }

    pub(crate) fn command(&self) -> &str {
        self.config.backend().default_command()
    }

    pub(crate) fn timeout_ms(&self) -> Option<u64> {
        self.config.timeout_ms()
    }

    pub(crate) fn rlimit(&self) -> Option<u64> {
        self.config.rlimit()
    }

    pub fn config(&self) -> &SmtSolverConfig {
        &self.config
    }

    fn build_entailment_script(&self, ctx: &Phi, goal: &Atom) -> String {
        let mut int_vars = BTreeSet::new();
        let mut bool_vars = BTreeSet::new();
        let mut real_vars = BTreeSet::new();

        for assumption in ctx.iter() {
            collect_atom_vars(assumption, &mut int_vars, &mut bool_vars, &mut real_vars);
        }
        collect_atom_vars(goal, &mut int_vars, &mut bool_vars, &mut real_vars);

        let symbols = SymbolTable::new(&int_vars, &bool_vars, &real_vars);
        let encoder = Encoder::new(&symbols);

        let mut lines = vec!["(reset)".to_string(), "(set-logic ALL)".to_string()];
        for decl in symbols.declarations() {
            lines.push(decl);
        }
        for assumption in ctx.iter() {
            lines.push(format!("(assert {})", encoder.encode_atom(assumption)));
        }
        let negated_goal = Atom::Not(Box::new(goal.clone()));
        lines.push(format!("(assert {})", encoder.encode_atom(&negated_goal)));
        lines.push("(check-sat)".to_string());
        lines.join("\n")
    }

    fn run_script(&self, script: &str) -> Result<CheckSatResult, String> {
        let mut process_guard = match self.process.lock() {
            Ok(guard) => guard,
            Err(poisoned) => poisoned.into_inner(),
        };

        if process_guard.is_none() {
            *process_guard = Some(SolverProcess::new(&self.config)?);
        }

        let output = match process_guard
            .as_mut()
            .expect("solver process should be initialised")
            .execute(script)
        {
            Ok(output) => output,
            Err(err) => {
                *process_guard = None;
                return Err(err);
            }
        };

        if let Some(result) = parse_check_sat_result(&output) {
            Ok(result)
        } else {
            Err(format!(
                "{} backend '{}' produced no satisfiability result\noutput:\n{}",
                self.backend(),
                self.command(),
                output
            ))
        }
    }

    fn log_query(&self, script: &str, result: Result<CheckSatResult, &str>) {
        if !self.is_query_logging_enabled() {
            return;
        }

        println!(
            "; {} entailment query via {} ({})",
            self.backend(),
            self.command(),
            match (self.timeout_ms(), self.rlimit()) {
                (Some(timeout), Some(rlimit)) =>
                    format!("timeout={}ms, rlimit={}", timeout, rlimit),
                (Some(timeout), None) => format!("timeout={}ms", timeout),
                (None, Some(rlimit)) => format!("rlimit={}", rlimit),
                (None, None) => "default options".to_string(),
            }
        );
        for line in script.lines() {
            println!("{line}");
        }
        match result {
            Ok(status) => println!("; result: {status}"),
            Err(err) => println!("; solver failure: {err}"),
        }
    }
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for SmtSolver {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            log_queries: Arc::clone(&self.log_queries),
            cache: Arc::clone(&self.cache),
            process: Arc::clone(&self.process),
        }
    }
}

impl fmt::Debug for SmtSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let has_process = self
            .process
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false);
        let cache_entries = self.cache.lock().map(|guard| guard.len()).unwrap_or(0);
        f.debug_struct("SmtSolver")
            .field("backend", &self.backend())
            .field("command", &self.command())
            .field("timeout_ms", &self.timeout_ms())
            .field("rlimit", &self.rlimit())
            .field("process_cached", &has_process)
            .field("cache_entries", &cache_entries)
            .field("log_queries", &self.log_queries.load(Ordering::Relaxed))
            .finish()
    }
}

impl PhiSolver for SmtSolver {
    type Region = super::region_set::RegionSetExpr;

    fn entails(&self, ctx: &Phi, atom: &Atom) -> bool {
        let script = self.build_entailment_script(ctx, atom);
        if let Some(status) = self
            .cache
            .lock()
            .map(|cache| cache.get(&script).copied())
            .unwrap_or(None)
        {
            self.log_query(&script, Ok(status));
            return matches!(status, CheckSatResult::Unsat);
        }

        match self.run_script(&script) {
            Ok(status) => {
                if let Ok(mut cache) = self.cache.lock() {
                    cache.insert(script.clone(), status);
                }
                self.log_query(&script, Ok(status));
                matches!(status, CheckSatResult::Unsat)
            }
            Err(err) => {
                eprintln!("solver failure while checking entailment: {err}");
                self.log_query(&script, Err(&err));
                false
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CheckSatResult {
    Sat,
    Unsat,
    Unknown,
}

impl Display for CheckSatResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckSatResult::Sat => write!(f, "sat"),
            CheckSatResult::Unsat => write!(f, "unsat"),
            CheckSatResult::Unknown => write!(f, "unknown"),
        }
    }
}

fn parse_check_sat_result(output: &str) -> Option<CheckSatResult> {
    output.lines().find_map(|line| match line.trim() {
        "sat" => Some(CheckSatResult::Sat),
        "unsat" => Some(CheckSatResult::Unsat),
        "unknown" => Some(CheckSatResult::Unknown),
        _ => None,
    })
}

const QUERY_SENTINEL: &str = "__wavelet_query_end__";

struct SolverProcess {
    backend: SmtBackend,
    command: String,
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    stderr: ChildStderr,
}

impl SolverProcess {
    fn new(config: &SmtSolverConfig) -> Result<Self, String> {
        let command_name = config.backend().default_command().to_string();
        let mut command = Command::new(&command_name);
        config.backend().configure_command(&mut command, config);
        command.stdin(Stdio::piped());
        command.stdout(Stdio::piped());
        command.stderr(Stdio::piped());

        let mut child = command.spawn().map_err(|err| {
            format!(
                "failed to launch {} backend '{}': {err}",
                config.backend(),
                command_name
            )
        })?;

        let stdin = child.stdin.take().ok_or_else(|| {
            format!(
                "failed to open stdin for {} backend '{}'",
                config.backend(),
                command_name
            )
        })?;
        let stdout = child.stdout.take().ok_or_else(|| {
            format!(
                "failed to open stdout for {} backend '{}'",
                config.backend(),
                command_name
            )
        })?;
        let stderr = child.stderr.take().ok_or_else(|| {
            format!(
                "failed to open stderr for {} backend '{}'",
                config.backend(),
                command_name
            )
        })?;

        Ok(Self {
            backend: config.backend(),
            command: command_name,
            child,
            stdin,
            stdout: BufReader::new(stdout),
            stderr,
        })
    }

    fn execute(&mut self, script: &str) -> Result<String, String> {
        self.stdin.write_all(script.as_bytes()).map_err(|err| {
            format!(
                "failed to send SMT-LIB script to {} backend '{}': {err}",
                self.backend, self.command
            )
        })?;
        self.stdin.write_all(b"\n").map_err(|err| {
            format!(
                "failed to terminate SMT-LIB script for {} backend '{}': {err}",
                self.backend, self.command
            )
        })?;
        self.stdin
            .write_all(format!("(echo \"{QUERY_SENTINEL}\")\n").as_bytes())
            .map_err(|err| {
                format!(
                    "failed to write SMT sentinel to {} backend '{}': {err}",
                    self.backend, self.command
                )
            })?;
        self.stdin.flush().map_err(|err| {
            format!(
                "failed to flush SMT-LIB script to {} backend '{}': {err}",
                self.backend, self.command
            )
        })?;

        let mut output = String::new();
        loop {
            let mut line = String::new();
            let bytes = self.stdout.read_line(&mut line).map_err(|err| {
                format!(
                    "failed to read output from {} backend '{}': {err}",
                    self.backend, self.command
                )
            })?;
            if bytes == 0 {
                let mut stderr = String::new();
                let _ = self.stderr.read_to_string(&mut stderr);
                let status = self
                    .child
                    .try_wait()
                    .ok()
                    .flatten()
                    .map(|status| status.to_string())
                    .unwrap_or_else(|| "still running".to_string());
                return Err(format!(
                    "{} backend '{}' closed stdout unexpectedly (status: {})\nstderr:\n{}",
                    self.backend, self.command, status, stderr
                ));
            }
            let trimmed = line.trim();
            if trimmed == QUERY_SENTINEL || trimmed.trim_matches('"') == QUERY_SENTINEL {
                break;
            }
            output.push_str(&line);
        }

        Ok(output)
    }
}

impl Drop for SolverProcess {
    fn drop(&mut self) {
        let _ = self.stdin.write_all(b"(exit)\n");
        let _ = self.stdin.flush();
        let _ = self.child.wait();
    }
}

struct SymbolTable {
    ints: BTreeMap<String, String>,
    bools: BTreeMap<String, String>,
    reals: BTreeMap<String, String>,
}

impl SymbolTable {
    fn new(
        int_vars: &BTreeSet<String>,
        bool_vars: &BTreeSet<String>,
        real_vars: &BTreeSet<String>,
    ) -> Self {
        Self {
            ints: assign_symbols("idx", int_vars),
            bools: assign_symbols("bool", bool_vars),
            reals: assign_symbols("real", real_vars),
        }
    }

    fn declarations(&self) -> Vec<String> {
        let mut lines = Vec::new();
        for symbol in self.ints.values() {
            lines.push(format!("(declare-const {symbol} Int)"));
        }
        for symbol in self.bools.values() {
            lines.push(format!("(declare-const {symbol} Bool)"));
        }
        for symbol in self.reals.values() {
            lines.push(format!("(declare-const {symbol} Real)"));
        }
        lines
    }

    fn int_symbol(&self, name: &str) -> &str {
        self.ints
            .get(name)
            .map(String::as_str)
            .unwrap_or_else(|| panic!("missing Int symbol for variable `{name}`"))
    }

    fn bool_symbol(&self, name: &str) -> &str {
        self.bools
            .get(name)
            .map(String::as_str)
            .unwrap_or_else(|| panic!("missing Bool symbol for variable `{name}`"))
    }

    fn real_symbol(&self, name: &str) -> &str {
        self.reals
            .get(name)
            .map(String::as_str)
            .unwrap_or_else(|| panic!("missing Real symbol for variable `{name}`"))
    }
}

fn assign_symbols(prefix: &str, vars: &BTreeSet<String>) -> BTreeMap<String, String> {
    vars.iter()
        .enumerate()
        .map(|(idx, name)| (name.clone(), format!("__{}_{}", prefix, idx)))
        .collect()
}

struct Encoder<'a> {
    symbols: &'a SymbolTable,
}

impl<'a> Encoder<'a> {
    fn new(symbols: &'a SymbolTable) -> Self {
        Self { symbols }
    }

    fn encode_idx(&self, idx: &Idx) -> String {
        match idx {
            Idx::Const(value) => encode_int_const(*value),
            Idx::Var(name) => self.symbols.int_symbol(name).to_string(),
            Idx::Add(lhs, rhs) => format!("(+ {} {})", self.encode_idx(lhs), self.encode_idx(rhs)),
            Idx::Sub(lhs, rhs) => format!("(- {} {})", self.encode_idx(lhs), self.encode_idx(rhs)),
            Idx::Mul(lhs, rhs) => format!("(* {} {})", self.encode_idx(lhs), self.encode_idx(rhs)),
        }
    }

    fn encode_real(&self, expr: &RealExpr) -> String {
        match expr {
            RealExpr::Const(num, den) => encode_real_const(*num, *den),
            RealExpr::Var(name) => self.symbols.real_symbol(name).to_string(),
            RealExpr::Add(lhs, rhs) => {
                format!("(+ {} {})", self.encode_real(lhs), self.encode_real(rhs))
            }
            RealExpr::Sub(lhs, rhs) => {
                format!("(- {} {})", self.encode_real(lhs), self.encode_real(rhs))
            }
        }
    }

    fn encode_atom(&self, atom: &Atom) -> String {
        match atom {
            Atom::Le(lhs, rhs) => format!("(<= {} {})", self.encode_idx(lhs), self.encode_idx(rhs)),
            Atom::Lt(lhs, rhs) => format!("(< {} {})", self.encode_idx(lhs), self.encode_idx(rhs)),
            Atom::Eq(lhs, rhs) => format!("(= {} {})", self.encode_idx(lhs), self.encode_idx(rhs)),
            Atom::RealLe(lhs, rhs) => {
                format!("(<= {} {})", self.encode_real(lhs), self.encode_real(rhs))
            }
            Atom::RealLt(lhs, rhs) => {
                format!("(< {} {})", self.encode_real(lhs), self.encode_real(rhs))
            }
            Atom::RealEq(lhs, rhs) => {
                format!("(= {} {})", self.encode_real(lhs), self.encode_real(rhs))
            }
            Atom::BoolVar(name) => self.symbols.bool_symbol(name).to_string(),
            Atom::And(lhs, rhs) => {
                format!("(and {} {})", self.encode_atom(lhs), self.encode_atom(rhs))
            }
            Atom::Or(lhs, rhs) => {
                format!("(or {} {})", self.encode_atom(lhs), self.encode_atom(rhs))
            }
            Atom::Implies(lhs, rhs) => {
                format!("(=> {} {})", self.encode_atom(lhs), self.encode_atom(rhs))
            }
            Atom::Not(inner) => format!("(not {})", self.encode_atom(inner)),
        }
    }
}

fn encode_int_const(value: i64) -> String {
    if value < 0 {
        format!("(- {})", value.unsigned_abs())
    } else {
        value.to_string()
    }
}

fn encode_real_const(num: i64, den: i64) -> String {
    assert!(den != 0, "real constant denominator must not be zero");
    let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
    let den = u64::try_from(den).expect("real denominator should be positive");
    let positive = format!("(/ {} {})", num.unsigned_abs(), den);
    if num < 0 {
        format!("(- {positive})")
    } else {
        positive
    }
}

fn collect_atom_vars(
    atom: &Atom,
    ints: &mut BTreeSet<String>,
    bools: &mut BTreeSet<String>,
    reals: &mut BTreeSet<String>,
) {
    match atom {
        Atom::Le(lhs, rhs) | Atom::Lt(lhs, rhs) | Atom::Eq(lhs, rhs) => {
            collect_idx_vars(lhs, ints);
            collect_idx_vars(rhs, ints);
        }
        Atom::RealLe(lhs, rhs) | Atom::RealLt(lhs, rhs) | Atom::RealEq(lhs, rhs) => {
            collect_real_vars(lhs, reals);
            collect_real_vars(rhs, reals);
        }
        Atom::BoolVar(name) => {
            bools.insert(name.clone());
        }
        Atom::And(lhs, rhs) | Atom::Or(lhs, rhs) | Atom::Implies(lhs, rhs) => {
            collect_atom_vars(lhs, ints, bools, reals);
            collect_atom_vars(rhs, ints, bools, reals);
        }
        Atom::Not(inner) => collect_atom_vars(inner, ints, bools, reals),
    }
}

fn collect_idx_vars(idx: &Idx, ints: &mut BTreeSet<String>) {
    match idx {
        Idx::Const(_) => {}
        Idx::Var(name) => {
            ints.insert(name.clone());
        }
        Idx::Add(lhs, rhs) | Idx::Sub(lhs, rhs) | Idx::Mul(lhs, rhs) => {
            collect_idx_vars(lhs, ints);
            collect_idx_vars(rhs, ints);
        }
    }
}

fn collect_real_vars(expr: &RealExpr, reals: &mut BTreeSet<String>) {
    match expr {
        RealExpr::Const(_, _) => {}
        RealExpr::Var(name) => {
            reals.insert(name.clone());
        }
        RealExpr::Add(lhs, rhs) | RealExpr::Sub(lhs, rhs) => {
            collect_real_vars(lhs, reals);
            collect_real_vars(rhs, reals);
        }
    }
}
