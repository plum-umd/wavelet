//! Environment structures used during type checking.

use std::collections::BTreeMap;

use crate::error::TypeError;
use crate::ir::{FnDef, FnName, Ty, Var};
use crate::logic::CapabilityLogic;
use crate::logic::cap::Delta;
use crate::logic::semantic::solver::Phi;

/// Variable environment mapping variable names to their types.
#[derive(Clone, Debug, Default)]
pub struct Gamma(pub BTreeMap<String, Ty>);

impl Gamma {
    /// Look up the type of a variable.  Returns an error if the variable
    /// is not in scope.
    pub fn get(&self, var: &Var) -> Result<Ty, TypeError> {
        self.0
            .get(&var.0)
            .cloned()
            .ok_or_else(|| TypeError::UndeclaredVar(var.0.clone()))
    }

    /// Introduce a new variable.
    pub fn insert(&mut self, var: Var, ty: Ty) {
        self.0.insert(var.0, ty);
    }
}

/// The type checker context.  Contains the variable environment
/// (`Gamma`), the capability environment (`Delta`), the proposition
/// context (`Phi`), and a reference to a solver implementation.
pub struct Ctx<'logic, L: CapabilityLogic> {
    pub gamma: Gamma,
    pub delta: Delta<L::Region>,
    pub initial_delta: Delta<L::Region>,
    pub phi: Phi,
    pub logic: &'logic L,
    pub verbose: bool,
}

impl<'logic, L: CapabilityLogic> Ctx<'logic, L> {
    /// Create a new empty context with a given capability logic backend.
    pub fn new(logic: &'logic L, verbose: bool) -> Self {
        Self {
            gamma: Gamma::default(),
            delta: Delta::default(),
            initial_delta: Delta::default(),
            phi: Phi::default(),
            logic,
            verbose,
        }
    }
}

/// A registry of function definitions.  During type checking we need
/// to look up function signatures to ensure calls respect their
/// capability contracts.
#[derive(Clone, Debug, Default)]
pub struct FnRegistry(pub BTreeMap<String, FnDef>);

impl FnRegistry {
    /// Insert a new function into the registry.
    pub fn insert(&mut self, def: FnDef) {
        self.0.insert(def.name.0.clone(), def);
    }

    /// Look up a function definition.
    pub fn get(&self, name: &FnName) -> Option<&FnDef> {
        self.0.get(&name.0)
    }
}
