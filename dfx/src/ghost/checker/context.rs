//! Check context for ghost program verification.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::GhostVar;
use crate::ir::{Ty, Var};
use crate::logic::cap::CapPattern;
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, Phi, RealExpr, SmtSolver};

use super::permission::{Permission, PermExpr};
use super::perm_env::PermissionEnv;

static FRACTION_FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A function signature for permission checking.
#[derive(Clone, Debug)]
pub struct FunctionSignature {
    /// Function parameters (variables and their types).
    pub params: Vec<(Var, Ty)>,
    /// Initial permission assignments from CapPattern: (p_sync, p_garb).
    pub initial_perms: (PermExpr, PermExpr),
}

/// The checking context accumulated during ghost program traversal.
#[derive(Clone, Debug)]
pub struct CheckContext {
    /// Logical constraints on integer and boolean variables.
    pub phi: Phi,
    /// Permission environment.
    pub penv: PermissionEnv,
    /// SMT solver instance.
    pub solver: SmtSolver,
    /// Function signatures for call checking.
    pub signatures: HashMap<String, FunctionSignature>,
    /// Cached entry permissions (p_sync, p_garb) for the function being checked.
    current_fn_entry_perms: Option<(PermExpr, PermExpr)>,
    /// Emit detailed traces of the checking context as it evolves.
    pub verbose: bool,
}

impl CheckContext {
    pub fn new(solver: SmtSolver) -> Self {
        Self {
            phi: Phi::new(),
            penv: PermissionEnv::new(),
            solver,
            signatures: HashMap::new(),
            current_fn_entry_perms: None,
            verbose: false,
        }
    }

    pub fn new_with_verbose(solver: SmtSolver, verbose: bool) -> Self {
        Self {
            phi: Phi::new(),
            penv: PermissionEnv::new(),
            solver,
            signatures: HashMap::new(),
            current_fn_entry_perms: None,
            verbose,
        }
    }

    /// Add a logical constraint to the context.
    pub fn add_constraint(&mut self, atom: Atom) {
        self.phi.push(atom);
    }

    /// Bind a ghost variable to a permission expression.
    pub fn bind_perm(&mut self, var: &GhostVar, perm: PermExpr) {
        let normalized = perm.normalize(&self.phi, &self.solver);
        self.penv.bind(var, normalized.unwrap_or(perm));
    }

    /// Lookup a permission expression.
    pub fn lookup_perm(&self, var: &GhostVar) -> Option<&PermExpr> {
        self.penv.lookup(var)
    }

    /// Register a function signature for call checking.
    pub fn register_signature(&mut self, name: String, sig: FunctionSignature) {
        self.signatures.insert(name, sig);
    }

    /// Lookup a function signature.
    pub fn get_signature(&self, name: &str) -> Option<&FunctionSignature> {
        self.signatures.get(name)
    }

    /// Record the entry permissions (p_sync, p_garb) for the current function.
    pub fn set_current_fn_entry_perms(&mut self, perms: Option<(PermExpr, PermExpr)>) {
        self.current_fn_entry_perms = perms;
    }

    /// Retrieve the entry permissions for the current function.
    pub fn current_fn_entry_perms(&self) -> Option<&(PermExpr, PermExpr)> {
        self.current_fn_entry_perms.as_ref()
    }

    /// Create a fresh symbolic fraction variable using the shared counter.
    pub fn fresh_fraction_var(&self, prefix: &str) -> FractionExpr {
        let id = FRACTION_FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
        FractionExpr::Var(format!("{}{}", prefix, id))
    }

    /// Add validity constraints for a fractional expression: 0 < f <= 1
    pub fn add_fraction_validity_constraint(&mut self, frac: &FractionExpr) {
        let zero = RealExpr::from_int(0);
        let one = RealExpr::from_int(1);
        let frac_real = frac.to_real_expr();

        // Add: 0 < frac
        self.add_constraint(Atom::RealLt(zero, frac_real.clone()));
        // Add: frac <= 1
        self.add_constraint(Atom::RealLe(frac_real, one));
    }

    /// Parse capability patterns into initial permission assignments
    /// (modifies self.phi and self.penv).
    ///
    /// For a capability pattern like `A: uniq @ i..N`, we create:
    /// - p_sync_a = 1.0@A{i..N}  (the unique/writable region)
    /// - p_garb_a = 1.0@A{0..i} (or more generally the complement region {0..N} \ {i..N})
    ///
    /// For `A: shrd @ i..N`, we create:
    /// - p_sync_a = f@A{i..N} where f is a symbolic fraction, where f ∈ (0, 1] (to be
    ///   added to Phi)
    /// - p_garb_a = f@A{0..N \ i..N} (the complement region)
    ///
    /// The final `p_sync` and `p_garb` permissions are the unions over all arrays.
    pub fn caps_to_permissions(
        &mut self,
        caps: &[CapPattern],
        p_sync: &GhostVar,
        p_garb: &GhostVar,
    ) {
        let mut sync_perms = Vec::new();
        let mut garb_perms = Vec::new();

        for cap_pattern in caps {
            let array = Var(cap_pattern.array.clone());

            // Get the total region for this array (0..len)
            let total_region = match &cap_pattern.len {
                crate::ir::ArrayLen::Const(n) => {
                    RegionSetExpr::interval(Idx::Const(0), Idx::Const(*n as i64))
                }
                crate::ir::ArrayLen::Symbol(name) => {
                    RegionSetExpr::interval(Idx::Const(0), Idx::Var(name.clone()))
                }
                crate::ir::ArrayLen::Expr(expr) => {
                    RegionSetExpr::interval(Idx::Const(0), expr.clone())
                }
            };

            // Process uniq region if present
            if let Some(uniq_region) = &cap_pattern.uniq {
                let region_expr = RegionSetExpr::from_region(uniq_region);

                // Create p_sync_a = 1.0@A{uniq_region}
                let sync_perm = Permission::new(
                    FractionExpr::from_int(1),
                    array.clone(),
                    region_expr.clone(),
                );
                sync_perms.push(PermExpr::singleton(sync_perm));

                // Create p_garb_a = 1.0@A{total \ uniq_region}
                let garb_region = RegionSetExpr::difference(total_region.clone(), region_expr);
                let garb_perm =
                    Permission::new(FractionExpr::from_int(1), array.clone(), garb_region);
                garb_perms.push(PermExpr::singleton(garb_perm));
            }

            // Process shrd region if present
            if let Some(shrd_region) = &cap_pattern.shrd {
                let region_expr = RegionSetExpr::from_region(shrd_region);

                // Create symbolic fraction variable for this shared region
                let frac_var_name = format!("f_shrd_{}", cap_pattern.array);
                let frac = FractionExpr::Var(frac_var_name);

                // Add validity constraints: 0 < f <= 1
                self.add_fraction_validity_constraint(&frac);

                // Create p_sync_a = f@A{shrd_region}
                let sync_perm = Permission::new(frac.clone(), array.clone(), region_expr.clone());
                sync_perms.push(PermExpr::singleton(sync_perm));

                // Create p_garb_a = f@A{total \ shrd_region}
                let garb_region = RegionSetExpr::difference(total_region, region_expr);
                let garb_perm = Permission::new(frac, array, garb_region);
                garb_perms.push(PermExpr::singleton(garb_perm));
            }
        }

        // Bind p_sync to the union of all sync permissions
        let sync_expr = if sync_perms.is_empty() {
            PermExpr::empty()
        } else {
            PermExpr::union(sync_perms)
        };
        self.bind_perm(p_sync, sync_expr);

        // Bind p_garb to the union of all garb permissions
        let garb_expr = if garb_perms.is_empty() {
            PermExpr::empty()
        } else {
            PermExpr::union(garb_perms)
        };
        self.bind_perm(p_garb, garb_expr);
    }

    /// Try to join multiple permissions and check validity.
    pub fn join_perms(&mut self, inputs: &[GhostVar]) -> Result<PermExpr, String> {
        let joined = inputs
            .iter()
            .filter_map(|var| self.penv.remove(var))
            .collect::<Vec<_>>();
        let result = PermExpr::union(joined);
        if result.is_valid(&self.phi, &self.solver) {
            Ok(result)
        } else {
            Err("Joined permission is not valid".to_string())
        }
    }
}
