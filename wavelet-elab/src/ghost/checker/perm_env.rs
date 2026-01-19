//! Permission environment mapping ghost variables to permissions.

use std::collections::HashMap;

use crate::ghost::ir::GhostVar;

use super::permission::PermExpr;

/// A permission environment mapping ghost variables to permissions.
#[derive(Clone, Debug, Default)]
pub struct PermissionEnv {
    /// Map from ghost variable names to their associated permissions.
    perms: HashMap<String, PermExpr>,
}

impl PermissionEnv {
    pub fn new() -> Self {
        Self {
            perms: HashMap::new(),
        }
    }

    /// Bind a ghost variable to a permission expression.
    pub fn bind(&mut self, var: &GhostVar, perm: PermExpr) {
        self.perms.insert(var.0.clone(), perm);
    }

    /// Lookup a permission expression by ghost variable.
    pub fn lookup(&self, var: &GhostVar) -> Option<&PermExpr> {
        self.perms.get(&var.0)
    }

    /// Check if a ghost variable is bound.
    pub fn contains(&self, var: &GhostVar) -> bool {
        self.perms.contains_key(&var.0)
    }

    /// Remove a binding.
    pub fn remove(&mut self, var: &GhostVar) -> Option<PermExpr> {
        self.perms.remove(&var.0)
    }

    /// Iterate over all permission bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &PermExpr)> {
        self.perms.iter()
    }
}
