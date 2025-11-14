//! Check context for ghost program verification.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::GhostVar;
use crate::ir::{Ty, Var};
use crate::logic::cap::CapPattern;
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, Phi, RealExpr, SmtSolver};

use super::perm_env::PermissionEnv;
use super::permission::{PermExpr, Permission};
use super::pretty_print::render_perm_expr;

static FRACTION_FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A function signature for permission checking.
#[derive(Clone, Debug)]
pub struct FunctionSignature {
    /// Function parameters (variables and their types).
    pub params: Vec<(Var, Ty)>,
    /// Initial permission assignments from CapPattern: (p_sync, p_garb).
    pub initial_perms: (PermExpr, PermExpr),
    /// Arithmetic preconditions implied by the capability regions.
    pub preconditions: Vec<Atom>,
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
    /// Ghost variables that temporarily hold permissions returned from calls or
    /// have had permissions injected back into them for bookkeeping. These
    /// contributions should be ignored when validating the final return.
    return_contributions: HashMap<String, Vec<PermExpr>>,
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
            return_contributions: HashMap::new(),
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
            return_contributions: HashMap::new(),
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

    /// Remember that `var` contains bookkeeping-only permissions which should be
    /// discounted at function return.
    pub fn register_return_contribution(&mut self, var: &GhostVar, perm: PermExpr) {
        self.return_contributions
            .entry(var.0.clone())
            .or_insert_with(Vec::new)
            .push(perm);
    }

    /// Retrieve and remove the recorded return contribution for `var`, if any.
    pub fn take_return_contribution(&mut self, var: &GhostVar) -> Option<PermExpr> {
        self.return_contributions.remove(&var.0).map(|mut perms| {
            if perms.len() == 1 {
                perms.remove(0)
            } else {
                PermExpr::union(perms)
            }
        })
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
        preconditions: Option<&mut Vec<Atom>>,
    ) {
        let mut preconds = preconditions;
        let mut sync_perms = Vec::new();
        let mut garb_perms = Vec::new();

        for cap_pattern in caps {
            let array = Var(cap_pattern.array.clone());

            // Get the total region for this array (0..len)
            let len_idx = match &cap_pattern.len {
                crate::ir::ArrayLen::Const(n) => Idx::Const(*n as i64),
                crate::ir::ArrayLen::Symbol(name) => Idx::Var(name.clone()),
                crate::ir::ArrayLen::Expr(expr) => expr.clone(),
            };
            let total_region = RegionSetExpr::interval(Idx::Const(0), len_idx.clone());

            let mut record_interval_bounds = |region: &crate::logic::region::Region| {
                if let Some(preconds_vec) = preconds.as_mut() {
                    for interval in region.iter() {
                        preconds_vec.push(Atom::Le(Idx::Const(0), interval.lo.clone()));
                        preconds_vec.push(Atom::Le(interval.lo.clone(), interval.hi.clone()));
                        preconds_vec.push(Atom::Le(interval.hi.clone(), len_idx.clone()));
                    }
                }
            };

            // Process uniq region if present
            if let Some(uniq_region) = &cap_pattern.uniq {
                record_interval_bounds(uniq_region);
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
                record_interval_bounds(shrd_region);
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
        let mut real_inputs: Vec<PermExpr> = Vec::new();
        let mut alias_inputs: Vec<PermExpr> = Vec::new();

        for var in inputs {
            if let Some(expr) = self.penv.remove(var) {
                if self.return_contributions.contains_key(&var.0) {
                    if self.verbose {
                        println!(
                            "  ▹ Ignoring bookkeeping contribution from {} during join",
                            var.0
                        );
                    }
                    alias_inputs.push(expr);
                } else {
                    real_inputs.push(expr);
                }
            }
        }

        if real_inputs.is_empty() && !alias_inputs.is_empty() {
            real_inputs.extend(alias_inputs.drain(..));
        }

        let result = PermExpr::union(real_inputs);
        let normalized = result
            .normalize(&self.phi, &self.solver)
            .ok_or_else(|| "Joined permission could not be normalised".to_string())?;

        if normalized.is_valid(&self.phi, &self.solver) {
            Ok(normalized)
        } else {
            if self.verbose {
                println!(
                    "  ✗ Joined permission invalid: {}",
                    render_perm_expr(&normalized)
                );
            }
            Err("Joined permission is not valid".to_string())
        }
    }
}
