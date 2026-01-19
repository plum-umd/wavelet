//! SMT-based reasoning for proposition contexts.

use std::{
    collections::HashMap,
    fmt::{self, Display},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
    },
};

use smtlib::prelude::Sorted;
use smtlib::terms::IntoWithStorage;
use smtlib::{Bool, Int, Real, SatResult, Solver, Storage, backend::z3_binary::Z3Binary};

use smtlib::terms::StaticSorted;
use smtlib_lowlevel::ast;

use crate::logic::cap::RegionModel;

/// An index expression used throughout the type system. Indices are
/// symbolic arithmetic expressions built from variables, constants and
/// addition/subtraction.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

/// SMT-backed solver that delegates to Z3 through the `smtlib` crate.
pub struct SmtSolver {
    z3_path: String,
    timeout_ms: Option<u64>,
    rlimit: Option<u64>,
    log_queries: Arc<AtomicBool>,
    solver: Arc<Mutex<Option<SolverInstance>>>,
}

impl SmtSolver {
    /// Create a solver that looks for `z3` on the current `$PATH` with
    /// no timeout.
    pub fn new() -> Self {
        Self {
            z3_path: "z3".into(),
            timeout_ms: None,
            rlimit: None,
            log_queries: Arc::new(AtomicBool::new(false)),
            solver: Arc::new(Mutex::new(None)),
        }
    }

    /// Customize the path used to invoke the Z3 binary.
    pub fn with_z3_path(path: impl Into<String>) -> Self {
        Self {
            z3_path: path.into(),
            timeout_ms: None,
            rlimit: None,
            log_queries: Arc::new(AtomicBool::new(false)),
            solver: Arc::new(Mutex::new(None)),
        }
    }

    /// Configure a timeout (in milliseconds) applied to solver
    /// invocations.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }

    /// Configure Z3's `:rlimit` counter.
    pub fn with_rlimit(mut self, rlimit: u64) -> Self {
        self.rlimit = Some(rlimit);
        self
    }

    /// Enable or disable dumping of SMT queries to stdout.
    pub fn set_query_logging(&self, enabled: bool) {
        self.log_queries.store(enabled, Ordering::SeqCst);
    }

    #[allow(dead_code)]
    pub(crate) fn z3_path(&self) -> &str {
        &self.z3_path
    }

    #[allow(dead_code)]
    pub(crate) fn timeout_ms(&self) -> Option<u64> {
        self.timeout_ms
    }

    pub(crate) fn is_query_logging_enabled(&self) -> bool {
        self.log_queries.load(Ordering::Relaxed)
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
            z3_path: self.z3_path.clone(),
            timeout_ms: self.timeout_ms,
            rlimit: self.rlimit,
            log_queries: Arc::clone(&self.log_queries),
            solver: Arc::clone(&self.solver),
        }
    }
}

impl fmt::Debug for SmtSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let has_solver = self
            .solver
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false);
        f.debug_struct("SmtSolver")
            .field("z3_path", &self.z3_path)
            .field("timeout_ms", &self.timeout_ms)
            .field("rlimit", &self.rlimit)
            .field("solver_cached", &has_solver)
            .field("log_queries", &self.log_queries.load(Ordering::Relaxed))
            .finish()
    }
}

impl PhiSolver for SmtSolver {
    type Region = super::region_set::RegionSetExpr;

    fn entails(&self, ctx: &Phi, atom: &Atom) -> bool {
        let mut solver_guard = match self.solver.lock() {
            Ok(guard) => guard,
            Err(poisoned) => poisoned.into_inner(),
        };

        if solver_guard.is_none() {
            match SolverInstance::new(&self.z3_path) {
                Ok(instance) => {
                    *solver_guard = Some(instance);
                }
                Err(err) => {
                    eprintln!("failed to initialise z3 backend: {err}");
                    return false;
                }
            }
        }

        let instance = solver_guard.as_mut().expect("solver instance initialised");
        let storage_ptr = instance.storage_ptr();
        let solver = instance.solver_mut();
        let storage = unsafe { &*storage_ptr };

        if let Some(timeout) = self.timeout_ms {
            let timeout = timeout.min(usize::MAX as u64) as usize;
            if let Err(err) = solver.set_timeout(timeout) {
                eprintln!("failed to set solver timeout: {err}");
            }
        }

        if let Some(limit) = self.rlimit {
            let limit = limit.min(usize::MAX as u64) as usize;
            if let Err(err) = solver.set_rlimit(limit) {
                eprintln!("failed to set solver rlimit: {err}");
            }
        }

        let mut encoder = Encoder::new(storage);
        let logging = self.log_queries.load(Ordering::Relaxed);
        let mut smt_trace = Vec::new();
        if logging {
            smt_trace.push("; z3 entailment query".to_string());
            smt_trace.push("; assumptions".to_string());
        }

        let mut had_assert_failure = false;
        for assumption in ctx.iter() {
            let term = encoder.encode_atom(assumption);
            if logging {
                smt_trace.push(format!("(assert {})", term));
            }
            if let Err(err) = solver.assert(term) {
                eprintln!("failed to assert assumption: {err}");
                if logging {
                    smt_trace.push(format!("; solver error while asserting assumption: {err}"));
                }
                had_assert_failure = true;
                break;
            }
        }

        let mut result = false;
        if !had_assert_failure {
            let negated_atom = Atom::Not(Box::new(atom.clone()));
            let negated = encoder.encode_atom(&negated_atom);
            if logging {
                smt_trace.push(format!("(assert {}) ; negated goal", negated));
                smt_trace.push("(check-sat)".to_string());
            }

            let mut sat_outcome: Option<String> = None;
            match solver.scope(|solver| {
                solver.assert(negated)?;
                let outcome = solver.check_sat()?;
                sat_outcome = Some(format!("{:?}", outcome));
                match outcome {
                    SatResult::Unsat => Ok(true),
                    _ => Ok(false),
                }
            }) {
                Ok(scope_result) => {
                    result = scope_result;
                    if logging {
                        if let Some(outcome) = sat_outcome {
                            smt_trace.push(format!("; result: {outcome}"));
                        }
                        for line in &smt_trace {
                            println!("{line}");
                        }
                    }
                }
                Err(err) => {
                    eprintln!("solver failure while checking entailment: {err}");
                    if logging {
                        smt_trace.push(format!("; solver failure: {err}"));
                        for line in &smt_trace {
                            println!("{line}");
                        }
                    }
                }
            }
        } else if logging {
            for line in &smt_trace {
                println!("{line}");
            }
        }

        if let Err(err) = solver.reset() {
            eprintln!("failed to reset solver state: {err}");
        }

        drop(solver_guard);

        result
    }
}

struct SolverInstance {
    storage: *mut Storage,
    solver: Solver<'static, Z3Binary>,
}

impl SolverInstance {
    fn new(z3_path: &str) -> Result<Self, String> {
        let storage = Box::into_raw(Box::new(Storage::new()));
        let storage_ref = unsafe { &*storage };

        let backend = match Z3Binary::new(z3_path) {
            Ok(backend) => backend,
            Err(err) => {
                unsafe {
                    drop(Box::from_raw(storage));
                }
                return Err(err.to_string());
            }
        };

        let solver = match Solver::new(storage_ref, backend) {
            Ok(solver) => solver,
            Err(err) => {
                unsafe {
                    drop(Box::from_raw(storage));
                }
                return Err(err.to_string());
            }
        };

        Ok(Self { storage, solver })
    }

    fn storage_ptr(&self) -> *const Storage {
        self.storage as *const Storage
    }

    fn solver_mut(&mut self) -> &mut Solver<'static, Z3Binary> {
        &mut self.solver
    }
}

impl Drop for SolverInstance {
    fn drop(&mut self) {
        if let Err(err) = self.solver.run_command(ast::Command::Exit) {
            eprintln!("failed to shut down z3 backend: {err}");
        }
        // Safety: storage was created with Box::into_raw in new()
        unsafe {
            drop(Box::from_raw(self.storage));
        }
    }
}

pub struct Encoder<'st> {
    storage: &'st Storage,
    int_vars: HashMap<String, Int<'st>>,
    bool_vars: HashMap<String, Bool<'st>>,
    real_vars: HashMap<String, Real<'st>>,
}

impl<'st> Encoder<'st> {
    fn new(storage: &'st Storage) -> Self {
        Self {
            storage,
            int_vars: HashMap::new(),
            bool_vars: HashMap::new(),
            real_vars: HashMap::new(),
        }
    }

    fn encode_idx(&mut self, idx: &Idx) -> Int<'st> {
        match idx {
            Idx::Const(n) => Int::new(self.storage, *n),
            Idx::Var(name) => *self
                .int_vars
                .entry(name.clone())
                .or_insert_with(|| Int::new_const(self.storage, name).into()),
            Idx::Add(lhs, rhs) => {
                let l = self.encode_idx(lhs);
                let r = self.encode_idx(rhs);
                l + r
            }
            Idx::Sub(lhs, rhs) => {
                let l = self.encode_idx(lhs);
                let r = self.encode_idx(rhs);
                l - r
            }
            Idx::Mul(lhs, rhs) => {
                let l = self.encode_idx(lhs);
                let r = self.encode_idx(rhs);
                l * r
            }
        }
    }

    fn encode_real(&mut self, expr: &RealExpr) -> Real<'st> {
        match expr {
            RealExpr::Const(n, d) => {
                // Convert the rational to a Real value
                // We compute the exact decimal value
                let value = (*n as f64) / (*d as f64);
                value.into_with_storage(self.storage)
            }
            RealExpr::Var(name) => *self
                .real_vars
                .entry(name.clone())
                .or_insert_with(|| Real::new_const(self.storage, name).into()),
            RealExpr::Add(lhs, rhs) => {
                let l = self.encode_real(lhs);
                let r = self.encode_real(rhs);
                l + r
            }
            RealExpr::Sub(lhs, rhs) => {
                let l = self.encode_real(lhs);
                let r = self.encode_real(rhs);
                l - r
            }
        }
    }

    fn encode_bool_var(&mut self, name: &str) -> Bool<'st> {
        *self
            .bool_vars
            .entry(name.to_string())
            .or_insert_with(|| Bool::new_const(self.storage, name).into())
    }

    fn encode_atom(&mut self, atom: &Atom) -> Bool<'st> {
        match atom {
            Atom::Le(lhs, rhs) => {
                let l = self.encode_idx(lhs);
                let r = self.encode_idx(rhs);
                l.le(r)
            }
            Atom::Lt(lhs, rhs) => {
                let l = self.encode_idx(lhs);
                let r = self.encode_idx(rhs);
                l.lt(r)
            }
            Atom::Eq(lhs, rhs) => {
                let l = self.encode_idx(lhs);
                let r = self.encode_idx(rhs);
                l._eq(r)
            }
            Atom::RealLe(lhs, rhs) => {
                let l = self.encode_real(lhs);
                let r = self.encode_real(rhs);
                l.le(r)
            }
            Atom::RealLt(lhs, rhs) => {
                let l = self.encode_real(lhs);
                let r = self.encode_real(rhs);
                l.lt(r)
            }
            Atom::RealEq(lhs, rhs) => {
                let l = self.encode_real(lhs);
                let r = self.encode_real(rhs);
                l._eq(r)
            }
            Atom::BoolVar(name) => self.encode_bool_var(name),
            Atom::And(lhs, rhs) => self.encode_atom(lhs) & self.encode_atom(rhs),
            Atom::Or(lhs, rhs) => self.encode_atom(lhs) | self.encode_atom(rhs),
            Atom::Implies(lhs, rhs) => self.encode_atom(lhs).implies(self.encode_atom(rhs)),
            Atom::Not(inner) => !self.encode_atom(inner),
        }
    }
}
