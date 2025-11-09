//! SMT-based reasoning for proposition contexts.

use std::collections::HashMap;

use smtlib::prelude::Sorted;
use smtlib::{Bool, Int, SatResult, Solver, Storage, backend::z3_binary::Z3Binary};

use smtlib::terms::StaticSorted;

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
}

impl Idx {
    /// Create a constant index from a `usize`.
    pub fn from_usize(n: usize) -> Self {
        Idx::Const(n as i64)
    }
}

/// Logical atoms over index expressions. Only simple relational
/// predicates are supported.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// `a <= b`
    Le(Idx, Idx),
    /// `a < b`
    Lt(Idx, Idx),
    /// `a == b`
    Eq(Idx, Idx),
    /// Conjunction of two atoms.
    And(Box<Atom>, Box<Atom>),
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
    /// Determine whether the given atom is entailed by the current
    /// context.
    fn entails(&self, ctx: &Phi, atom: &Atom) -> bool;
}

/// SMT-backed solver that delegates to Z3 through the `smtlib` crate.
#[derive(Clone, Debug)]
pub struct SmtSolver {
    z3_path: String,
    timeout_ms: Option<u64>,
}

impl SmtSolver {
    /// Create a solver that looks for `z3` on the current `$PATH` with
    /// no timeout.
    pub fn new() -> Self {
        Self {
            z3_path: "z3".into(),
            timeout_ms: None,
        }
    }

    /// Customize the path used to invoke the Z3 binary.
    pub fn with_z3_path(path: impl Into<String>) -> Self {
        Self {
            z3_path: path.into(),
            timeout_ms: None,
        }
    }

    /// Configure a timeout (in milliseconds) applied to solver
    /// invocations.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl PhiSolver for SmtSolver {
    fn entails(&self, ctx: &Phi, atom: &Atom) -> bool {
        let storage = Storage::new();
        let backend = match Z3Binary::new(&self.z3_path) {
            Ok(backend) => backend,
            Err(err) => {
                eprintln!("failed to initialise z3 backend: {err}");
                return false;
            }
        };
        let mut solver = match Solver::new(&storage, backend) {
            Ok(solver) => solver,
            Err(err) => {
                eprintln!("failed to construct solver: {err}");
                return false;
            }
        };

        if let Some(timeout) = self.timeout_ms {
            if let Err(err) = solver.set_timeout(timeout as usize) {
                eprintln!("failed to set solver timeout: {err}");
            }
        }

        let mut encoder = Encoder::new(&storage);
        for assumption in ctx.iter() {
            let term = encoder.encode_atom(assumption);
            if let Err(err) = solver.assert(term) {
                eprintln!("failed to assert assumption: {err}");
                return false;
            }
        }

        let negated = encoder.encode_atom(&Atom::Not(Box::new(atom.clone())));
        match solver.scope(|solver| {
            solver.assert(negated)?;
            match solver.check_sat()? {
                SatResult::Unsat => Ok(true),
                _ => Ok(false),
            }
        }) {
            Ok(result) => result,
            Err(err) => {
                eprintln!("solver failure while checking entailment: {err}");
                false
            }
        }
    }
}

struct Encoder<'st> {
    storage: &'st Storage,
    vars: HashMap<String, Int<'st>>,
}

impl<'st> Encoder<'st> {
    fn new(storage: &'st Storage) -> Self {
        Self {
            storage,
            vars: HashMap::new(),
        }
    }

    fn encode_idx(&mut self, idx: &Idx) -> Int<'st> {
        match idx {
            Idx::Const(n) => Int::new(self.storage, *n),
            Idx::Var(name) => *self
                .vars
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
        }
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
            Atom::And(lhs, rhs) => self.encode_atom(lhs) & self.encode_atom(rhs),
            Atom::Not(inner) => !self.encode_atom(inner),
        }
    }
}
