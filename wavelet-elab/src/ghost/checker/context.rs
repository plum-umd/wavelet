//! Shared validation context for ghost permission checking.

use std::collections::HashMap;

use crate::ghost::ir::GhostVar;
use crate::logic::semantic::solver::{Atom, Phi, SmtSolver};

use super::contract::FunctionSignature;
use super::perm_env::PermissionEnv;
use super::permission::PermExpr;

#[derive(Clone, Debug)]
pub struct CheckContext {
    pub phi: Phi,
    pub penv: PermissionEnv,
    pub solver: SmtSolver,
    pub signatures: HashMap<String, FunctionSignature>,
    pub current_fn_name: Option<String>,
    current_fn_entry_perms: Option<(PermExpr, PermExpr)>,
    pub verbose: bool,
}

impl CheckContext {
    pub fn new(solver: SmtSolver) -> Self {
        Self::new_with_verbose(solver, false)
    }

    pub fn new_with_verbose(solver: SmtSolver, verbose: bool) -> Self {
        Self {
            phi: Phi::new(),
            penv: PermissionEnv::new(),
            solver,
            signatures: HashMap::new(),
            current_fn_name: None,
            current_fn_entry_perms: None,
            verbose,
        }
    }

    pub fn add_constraint(&mut self, atom: Atom) {
        self.phi.push(atom);
    }

    pub fn bind_perm(&mut self, var: &GhostVar, perm: PermExpr) {
        self.penv.bind(var, perm);
    }

    pub fn lookup_perm(&self, var: &GhostVar) -> Option<&PermExpr> {
        self.penv.lookup(var)
    }

    pub fn register_signature(&mut self, name: String, sig: FunctionSignature) {
        self.signatures.insert(name, sig);
    }

    pub fn get_signature(&self, name: &str) -> Option<&FunctionSignature> {
        self.signatures.get(name)
    }

    pub fn set_current_fn_entry_perms(&mut self, perms: Option<(PermExpr, PermExpr)>) {
        self.current_fn_entry_perms = perms;
    }

    pub fn current_fn_entry_perms(&self) -> Option<&(PermExpr, PermExpr)> {
        self.current_fn_entry_perms.as_ref()
    }
}
