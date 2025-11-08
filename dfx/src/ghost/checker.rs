//! Permission-based checker for GhostProgram using fractional permissions PCM.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::Val;
use crate::ghost::fracperms::{FractionExpr, check_fraction_valid};
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostProgram, GhostStmt, GhostTail, GhostVar};
use crate::ir::{Signedness, Ty, Var};
use crate::logic::cap::{CapPattern, RegionModel};
use crate::logic::semantic::PhiSolver;
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, Phi, SmtSolver};

static FRACTION_FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A fractional permission on a specific array region.
/// Represents `f@A{region}` where f is a fractional value in [0, 1].
#[derive(Clone, Debug, PartialEq)]
pub struct Permission {
    /// The fractional value (symbolic expression).
    pub fraction: FractionExpr,
    /// The array variable this permission refers to.
    pub array: Var,
    /// The region of indices covered by this permission.
    pub region: RegionSetExpr,
}

/// Permission expression.
///
/// e.g., `eps`, `1.0@A{i..N}`, `f@A{i..N} + g@A{0...i}`, `f@A{i..N} -
/// f@A{i..i+1}`, `1.0@A{i..N} + f@B{0..M}` etc.
#[derive(Clone, Debug, PartialEq)]
pub enum PermExpr {
    /// The empty permission (epsilon).
    Empty,
    /// A single permission.
    Singleton(Permission),
    /// A (PCM) sum of multiple permissions.
    Add(Vec<PermExpr>),
    /// A difference of two permissions.
    Sub(Box<PermExpr>, Box<PermExpr>),
}

impl PermExpr {
    /// Create an empty (zero) permission expression.
    pub fn empty() -> Self {
        PermExpr::Empty
    }

    /// Create a permission expression from a single permission.
    pub fn singleton(perm: Permission) -> Self {
        PermExpr::Singleton(perm)
    }

    /// Create a union (sum) of multiple permission expressions.
    pub fn union(perms: impl IntoIterator<Item = PermExpr>) -> Self {
        let items: Vec<_> = perms.into_iter().collect();
        if items.is_empty() {
            PermExpr::Empty
        } else {
            PermExpr::Add(items)
        }
    }
}

impl PermExpr {
    /// Check if this permission expression is valid under the given context.
    pub fn is_valid(&self, phi: &Phi, solver: &SmtSolver) -> bool {
        match self {
            PermExpr::Empty => true,
            PermExpr::Singleton(perm) => perm.is_valid(phi, solver),
            PermExpr::Add(items) => {
                // we need to
                // 1. separate the permissions by array
                // 2. for each array, check that
                //   a. if there are multiple permissions on the same array,
                //      i. if their regions are disjoint: just check each
                //      permission is valid
                //      ii. if their regions overlap: we need to check that
                //      the sum of their fractions is <= 1.0 on the overlapping
                //      region, and each individual permission is valid
                //   b. if there's only one permission on the array, just check
                //   it's valid

                use crate::ghost::fracperms::check_fraction_leq;
                use crate::logic::semantic::region_set::overlaps;
                use std::collections::HashMap;

                // Group permissions by array
                let mut perms_by_array: HashMap<Var, Vec<&Permission>> = HashMap::new();
                for item in items {
                    if let PermExpr::Singleton(perm) = item {
                        perms_by_array
                            .entry(perm.array.clone())
                            .or_insert_with(Vec::new)
                            .push(perm);
                    } else {
                        // Nested Add expressions should have been flattened
                        // For now, recursively check them
                        if !item.is_valid(phi, solver) {
                            return false;
                        }
                    }
                }

                // Check each array's permissions
                for (_, perms_for_array) in perms_by_array {
                    if perms_for_array.len() == 1 {
                        // Single permission on array: just check it's valid
                        if !perms_for_array[0].is_valid(phi, solver) {
                            return false;
                        }
                    } else {
                        // Multiple permissions on same array: check for overlaps
                        for i in 0..perms_for_array.len() {
                            // Each permission must be individually valid
                            if !perms_for_array[i].is_valid(phi, solver) {
                                return false;
                            }

                            // Check for overlaps with other permissions
                            for j in (i + 1)..perms_for_array.len() {
                                if overlaps(
                                    phi,
                                    &perms_for_array[i].region,
                                    &perms_for_array[j].region,
                                    solver,
                                ) {
                                    // On overlapping region, fractions must sum to <= 1.0
                                    let sum_fraction = FractionExpr::sum(
                                        perms_for_array[i].fraction.clone(),
                                        perms_for_array[j].fraction.clone(),
                                    );
                                    let one = FractionExpr::from_int(1);

                                    if !check_fraction_leq(phi, &sum_fraction, &one, solver) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }

                true
            }
            PermExpr::Sub(lhs, rhs) => {
                // For subtraction, we need to ensure that lhs >= rhs
                if !lhs.is_valid(phi, solver) || !rhs.is_valid(phi, solver) {
                    return false;
                }

                // Attempt to normalise the subtraction; failure means we
                // cannot cover rhs with lhs.
                self.collect_permissions(phi, solver).is_some()
            }
        }
    }

    /// Flatten the permission expression into the multiset of positive
    /// permissions it represents. Returns `None` if the expression encodes an
    /// invalid subtraction (i.e., tries to consume more than available).
    fn collect_permissions(&self, phi: &Phi, solver: &SmtSolver) -> Option<Vec<Permission>> {
        match self {
            PermExpr::Empty => Some(Vec::new()),
            PermExpr::Singleton(perm) => Some(vec![perm.clone()]),
            PermExpr::Add(items) => {
                let mut acc = Vec::new();
                for item in items {
                    let mut child = item.collect_permissions(phi, solver)?;
                    acc.append(&mut child);
                }
                Some(acc)
            }
            PermExpr::Sub(lhs, rhs) => {
                let mut available = lhs.collect_permissions(phi, solver)?;
                let needed = rhs.collect_permissions(phi, solver)?;
                for perm_rhs in needed {
                    if !consume_permission(&mut available, &perm_rhs, phi, solver) {
                        return None;
                    }
                }
                Some(available)
            }
        }
    }
}

fn consume_permission(
    available: &mut Vec<Permission>,
    needed: &Permission,
    phi: &Phi,
    solver: &SmtSolver,
) -> bool {
    use crate::ghost::fracperms::{check_fraction_leq, try_sub_fractions};
    use crate::logic::semantic::region_set::{check_subset, overlaps};

    let mut idx = 0;
    while idx < available.len() {
        let candidate = &available[idx];
        if candidate.array != needed.array {
            idx += 1;
            continue;
        }

        if !overlaps(phi, &candidate.region, &needed.region, solver) {
            idx += 1;
            continue;
        }

        if !check_subset(phi, &needed.region, &candidate.region, solver) {
            idx += 1;
            continue;
        }

        if !check_fraction_leq(phi, &needed.fraction, &candidate.fraction, solver) {
            idx += 1;
            continue;
        }

        let candidate = available.remove(idx);
        let diff_fraction =
            match try_sub_fractions(&candidate.fraction, &needed.fraction, phi, solver) {
                Some(diff) => diff,
                None => return false,
            };

        if !is_fraction_zero(phi, &diff_fraction, solver) {
            available.push(Permission::new(
                diff_fraction,
                candidate.array.clone(),
                needed.region.clone(),
            ));
        }

        let leftover_region =
            RegionSetExpr::difference(candidate.region.clone(), needed.region.clone());
        if !leftover_region.is_empty(phi, solver) {
            available.push(Permission::new(
                candidate.fraction,
                candidate.array,
                leftover_region,
            ));
        }

        return true;
    }

    false
}

fn is_fraction_zero(phi: &Phi, frac: &FractionExpr, solver: &SmtSolver) -> bool {
    use crate::ghost::fracperms::check_fraction_leq;

    let zero = FractionExpr::from_int(0);
    check_fraction_leq(phi, frac, &zero, solver) && check_fraction_leq(phi, &zero, frac, solver)
}

impl Permission {
    /// Create a new permission.
    pub fn new(fraction: FractionExpr, array: Var, region: RegionSetExpr) -> Self {
        Self {
            fraction,
            array,
            region,
        }
    }

    /// Check if this permission is valid under the given context.
    pub fn is_valid(&self, phi: &Phi, solver: &SmtSolver) -> bool {
        check_fraction_valid(phi, &self.fraction, solver)
    }

    /// Substitute index variables in the region.
    /// For example, if region is `{i..N}` and we substitute `i -> j`,
    /// the result is `{j..N}`.
    pub fn substitute_region(&self, from: &str, to: &Idx) -> Self {
        Self {
            fraction: self.fraction.clone(),
            array: self.array.clone(),
            region: substitute_idx_in_region(&self.region, from, to),
        }
    }
}

/// Substitute an index variable in a region expression.
fn substitute_idx_in_region(region: &RegionSetExpr, from: &str, to: &Idx) -> RegionSetExpr {
    match region {
        RegionSetExpr::Empty => RegionSetExpr::Empty,
        RegionSetExpr::Interval { lo, hi } => RegionSetExpr::Interval {
            lo: substitute_idx(lo, from, to),
            hi: substitute_idx(hi, from, to),
        },
        RegionSetExpr::Union(items) => {
            let new_items: Vec<_> = items
                .iter()
                .map(|r| substitute_idx_in_region(r, from, to))
                .collect();
            RegionSetExpr::Union(new_items)
        }
        RegionSetExpr::Difference(lhs, rhs) => RegionSetExpr::Difference(
            Box::new(substitute_idx_in_region(lhs, from, to)),
            Box::new(substitute_idx_in_region(rhs, from, to)),
        ),
        RegionSetExpr::Intersection(lhs, rhs) => RegionSetExpr::Intersection(
            Box::new(substitute_idx_in_region(lhs, from, to)),
            Box::new(substitute_idx_in_region(rhs, from, to)),
        ),
    }
}

/// Substitute an index variable in an index expression.
fn substitute_idx(idx: &Idx, from: &str, to: &Idx) -> Idx {
    match idx {
        Idx::Const(n) => Idx::Const(*n),
        Idx::Var(name) => {
            if name == from {
                to.clone()
            } else {
                Idx::Var(name.clone())
            }
        }
        Idx::Add(lhs, rhs) => Idx::Add(
            Box::new(substitute_idx(lhs, from, to)),
            Box::new(substitute_idx(rhs, from, to)),
        ),
        Idx::Sub(lhs, rhs) => Idx::Sub(
            Box::new(substitute_idx(lhs, from, to)),
            Box::new(substitute_idx(rhs, from, to)),
        ),
        Idx::Mul(lhs, rhs) => Idx::Mul(
            Box::new(substitute_idx(lhs, from, to)),
            Box::new(substitute_idx(rhs, from, to)),
        ),
    }
}

fn apply_idx_substitutions(
    region: &RegionSetExpr,
    substitutions: &[(String, Idx)],
) -> RegionSetExpr {
    let mut current = region.clone();
    for (name, idx) in substitutions {
        current = substitute_idx_in_region(&current, name.as_str(), idx);
    }
    current
}

fn substitute_permission_with_maps(
    perm: &Permission,
    idx_substitutions: &[(String, Idx)],
) -> Permission {
    let substituted_region = apply_idx_substitutions(&perm.region, idx_substitutions);

    Permission::new(
        perm.fraction.clone(),
        perm.array.clone(),
        substituted_region,
    )
}

fn substitute_perm_expr_with_maps(
    expr: &PermExpr,
    idx_substitutions: &[(String, Idx)],
) -> PermExpr {
    match expr {
        PermExpr::Empty => PermExpr::Empty,
        PermExpr::Singleton(perm) => {
            PermExpr::singleton(substitute_permission_with_maps(perm, idx_substitutions))
        }
        PermExpr::Add(items) => PermExpr::Add(
            items
                .iter()
                .map(|item| substitute_perm_expr_with_maps(item, idx_substitutions))
                .collect(),
        ),
        PermExpr::Sub(lhs, rhs) => PermExpr::Sub(
            Box::new(substitute_perm_expr_with_maps(lhs, idx_substitutions)),
            Box::new(substitute_perm_expr_with_maps(rhs, idx_substitutions)),
        ),
    }
}

fn permissions_to_expr(perms: Vec<Permission>) -> PermExpr {
    if perms.is_empty() {
        PermExpr::empty()
    } else {
        PermExpr::union(perms.into_iter().map(PermExpr::singleton))
    }
}

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
}

impl CheckContext {
    pub fn new(solver: SmtSolver) -> Self {
        Self {
            phi: Phi::new(),
            penv: PermissionEnv::new(),
            solver,
            signatures: HashMap::new(),
            current_fn_entry_perms: None,
        }
    }

    /// Add a logical constraint to the context.
    pub fn add_constraint(&mut self, atom: Atom) {
        self.phi.push(atom);
    }

    /// Bind a ghost variable to a permission expression.
    pub fn bind_perm(&mut self, var: &GhostVar, perm: PermExpr) {
        self.penv.bind(var, perm);
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
    fn fresh_fraction_var(&self, prefix: &str) -> FractionExpr {
        let id = FRACTION_FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
        FractionExpr::Var(format!("{}{}", prefix, id))
    }

    /// Add validity constraints for a fractional expression: 0 < f <= 1
    fn add_fraction_validity_constraint(&mut self, frac: &FractionExpr) {
        use crate::logic::semantic::solver::RealExpr;

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

/// Check a ghost program for permission correctness.
pub fn check_ghost_program(program: &GhostProgram) -> Result<(), String> {
    let solver = SmtSolver::new();
    let mut ctx = CheckContext::new(solver.clone());

    // First pass: collect function signatures
    for def in &program.defs {
        let sig = build_function_signature(def);
        ctx.register_signature(def.name.0.clone(), sig);
    }

    // Second pass: check each function
    for def in &program.defs {
        check_ghost_fn(def, &mut ctx)?;
    }

    Ok(())
}

/// Build a function signature from a ghost function definition.
/// This extracts the initial permission setup from CapPattern.
fn build_function_signature(def: &GhostFnDef) -> FunctionSignature {
    let params = def.params.clone();

    let solver = SmtSolver::new();
    let mut temp_ctx = CheckContext::new(solver);

    let p_sync = GhostVar("__sig_p_sync".to_string());
    let p_garb = GhostVar("__sig_p_garb".to_string());

    // Parse caps into permissions
    temp_ctx.caps_to_permissions(&def.caps, &p_sync, &p_garb);

    // Extract the permissions
    let sync_perm = match temp_ctx.lookup_perm(&p_sync) {
        Some(perm) => perm.clone(),
        None => unreachable!(),
    };
    let garb_perm = match temp_ctx.lookup_perm(&p_garb) {
        Some(perm) => perm.clone(),
        None => unreachable!(),
    };
    FunctionSignature {
        params,
        initial_perms: (sync_perm, garb_perm),
    }
}

/// Check a single ghost function definition.
fn check_ghost_fn(def: &GhostFnDef, ctx: &mut CheckContext) -> Result<(), String> {
    ctx.set_current_fn_entry_perms(None);

    for (var, ty) in &def.params {
        if let Ty::Int(Signedness::Unsigned) = ty {
            ctx.add_constraint(Atom::Le(Idx::Const(0), Idx::Var(var.0.clone())));
        }
    }

    if def.ghost_params.len() >= 2 {
        let p_sync = &def.ghost_params[0];
        let p_garb = &def.ghost_params[1];

        ctx.caps_to_permissions(&def.caps, p_sync, p_garb);

        if let (Some(sync), Some(garb)) = (ctx.lookup_perm(p_sync), ctx.lookup_perm(p_garb)) {
            ctx.set_current_fn_entry_perms(Some((sync.clone(), garb.clone())));
        }
    }

    check_ghost_expr(&def.body, ctx)?;

    ctx.set_current_fn_entry_perms(None);

    Ok(())
}

fn check_ghost_expr(expr: &GhostExpr, ctx: &mut CheckContext) -> Result<(), String> {
    let stmts = &expr.stmts;
    let mut i = 0;

    while i < stmts.len() {
        match &stmts[i] {
            GhostStmt::Pure { .. } => {
                // Pure statements stand alone
                check_ghost_stmt_pure(&stmts[i], ctx)?;
                i += 1;
            }
            GhostStmt::JoinSplit { .. } => {
                // JoinSplit must be followed by another statement or tail
                if i + 1 >= stmts.len() {
                    // This is the last statement, so it must precede a tail (Return)
                    check_ghost_tail_with_joinsplit(&stmts[i], &expr.tail, ctx)?;
                    return Ok(());
                }

                match &stmts[i + 1] {
                    GhostStmt::Const { .. } => {
                        // JoinSplit followed by Const
                        check_ghost_stmt_joinsplit_const(&stmts[i], &stmts[i + 1], ctx)?;
                        i += 2;
                    }
                    GhostStmt::Load { .. } => {
                        // JoinSplit followed by Load
                        check_ghost_stmt_joinsplit_load(&stmts[i], &stmts[i + 1], ctx)?;
                        i += 2;
                    }
                    GhostStmt::Store { .. } => {
                        // JoinSplit followed by Store
                        check_ghost_stmt_joinsplit_store(&stmts[i], &stmts[i + 1], ctx)?;
                        i += 2;
                    }
                    GhostStmt::JoinSplit { .. } => {
                        // Two JoinSplits must be followed by Call or tail
                        if i + 2 >= stmts.len() {
                            // The two JoinSplits are the last statements, so
                            // they must precede a tail (Call)
                            check_ghost_tail_with_two_joinsplits(
                                &stmts[i],
                                &stmts[i + 1],
                                &expr.tail,
                                ctx,
                            )?;
                            return Ok(());
                        }
                        match &stmts[i + 2] {
                            GhostStmt::Call { .. } => {
                                // Two JoinSplits followed by Call
                                check_ghost_stmt_jnsplt_jnsplt_call(
                                    &stmts[i],
                                    &stmts[i + 1],
                                    &stmts[i + 2],
                                    ctx,
                                )?;
                                i += 3;
                            }
                            _ => {
                                return Err(format!(
                                    "Two JoinSplits must be followed by Call or TailCall, found {:?}",
                                    stmts[i + 2]
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(format!(
                            "Invalid statement sequence: JoinSplit followed by {:?}",
                            stmts[i + 1]
                        ));
                    }
                }
            }
            _ => {
                return Err(format!(
                    "Statement {:?} must be preceded by JoinSplit",
                    stmts[i]
                ));
            }
        }
    }

    // If no more statements, check the tail if-else
    check_ghost_tail_if(&expr.tail, ctx)?;
    Ok(())
}

/// Check a standalone Pure statement.
fn check_ghost_stmt_pure(stmt: &GhostStmt, ctx: &mut CheckContext) -> Result<(), String> {
    let (inputs, output, op) = match stmt {
        GhostStmt::Pure {
            inputs,
            output,
            op,
            ghost_out: _,
        } => (inputs, output, op),
        _ => unreachable!(),
    };

    // Pure operations don't consume permissions
    // Add semantic constraints to phi based on the operation
    use crate::ir::Op;
    match op {
        Op::LessThan | Op::LessEqual | Op::Equal if inputs.len() == 2 => {
            let comparison = match op {
                Op::LessThan => {
                    Atom::Lt(Idx::Var(inputs[0].0.clone()), Idx::Var(inputs[1].0.clone()))
                }
                Op::LessEqual => {
                    Atom::Le(Idx::Var(inputs[0].0.clone()), Idx::Var(inputs[1].0.clone()))
                }
                Op::Equal => Atom::Eq(Idx::Var(inputs[0].0.clone()), Idx::Var(inputs[1].0.clone())),
                _ => unreachable!(),
            };
            let result_atom = Atom::BoolVar(output.0.clone());
            ctx.add_constraint(Atom::Implies(
                Box::new(result_atom.clone()),
                Box::new(comparison.clone()),
            ));
            ctx.add_constraint(Atom::Implies(
                Box::new(Atom::Not(Box::new(result_atom))),
                Box::new(Atom::Not(Box::new(comparison))),
            ));
        }
        Op::Add | Op::Sub | Op::Mul if inputs.len() == 2 => {
            // output == inputs[0] op inputs[1]
            let lhs = Box::new(Idx::Var(inputs[0].0.clone()));
            let rhs = Box::new(Idx::Var(inputs[1].0.clone()));
            let result = match op {
                Op::Add => Idx::Add(lhs, rhs),
                Op::Sub => Idx::Sub(lhs, rhs),
                Op::Mul => Idx::Mul(lhs, rhs),
                _ => unreachable!(),
            };
            ctx.add_constraint(Atom::Eq(Idx::Var(output.0.clone()), result));
        }
        _ => {
            // Other operations don't add semantic constraints yet
        }
    }
    Ok(())
}

/// Check JoinSplit followed by Const.
fn check_ghost_stmt_joinsplit_const(
    join_stmt: &GhostStmt,
    const_stmt: &GhostStmt,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    // Process JoinSplit
    // For const, left would always be epsilon
    let (left, right, inputs) = match join_stmt {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => (left, right, inputs),
        _ => unreachable!(),
    };

    let joined_perm = ctx.join_perms(inputs)?;
    ctx.bind_perm(right, joined_perm);

    // Process Const
    let (value, output, ghost_in, _ghost_out) = match const_stmt {
        GhostStmt::Const {
            value,
            output,
            ghost_in,
            ghost_out,
        } => (value, output, ghost_in, ghost_out),
        _ => unreachable!(),
    };

    if ghost_in.0 != left.0 {
        return Err(format!(
            "Const ghost_in {} does not match JoinSplit left {}",
            ghost_in.0, left.0
        ));
    }

    // Add semantic constraints to phi
    let ty = match value {
        Val::Int(n) => {
            if *n >= 0 {
                Ty::Int(Signedness::Unsigned)
            } else {
                Ty::Int(Signedness::Signed)
            }
        }
        Val::Bool(_) => Ty::Bool,
        Val::Unit => Ty::Unit,
    };
    if let Ty::Int(Signedness::Unsigned) = ty {
        ctx.add_constraint(Atom::Le(Idx::Const(0), Idx::Var(output.0.clone())));
    }
    match value {
        Val::Int(n) => ctx.add_constraint(Atom::Eq(Idx::Var(output.0.clone()), Idx::Const(*n))),
        Val::Bool(true) => ctx.add_constraint(Atom::BoolVar(output.0.clone())),
        Val::Bool(false) => {
            ctx.add_constraint(Atom::Not(Box::new(Atom::BoolVar(output.0.clone()))))
        }
        Val::Unit => {}
    }

    // For const, both ghost_in and ghost_out would be epsilon so we are done
    Ok(())
}

/// Check JoinSplit followed by Load.
fn check_ghost_stmt_joinsplit_load(
    join_stmt: &GhostStmt,
    load_stmt: &GhostStmt,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    use crate::logic::semantic::region_set::check_subset;
    use crate::logic::semantic::solver::RealExpr;

    // Process JoinSplit
    let (left, right, inputs) = match join_stmt {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => (left, right, inputs),
        _ => unreachable!(),
    };

    let joined_perm = ctx.join_perms(inputs)?;

    // Process Load
    let (array, index, ghost_in, ghost_out) = match load_stmt {
        GhostStmt::Load {
            array,
            index,
            ghost_in,
            ghost_out,
            ..
        } => (array, index, ghost_in, ghost_out),
        _ => unreachable!(),
    };

    if ghost_in.0 != left.0 {
        return Err(format!(
            "Load ghost_in {} does not match JoinSplit left {}",
            ghost_in.0, left.0
        ));
    }

    let access_region = RegionSetExpr::interval(
        Idx::Var(index.0.clone()),
        Idx::Add(Box::new(Idx::Var(index.0.clone())), Box::new(Idx::Const(1))),
    );

    let collected = joined_perm
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| "Joined permission could not be normalised".to_string())?;

    let zero = RealExpr::from_int(0);
    let mut candidate: Option<Permission> = None;
    for perm in &collected {
        if perm.array != *array {
            continue;
        }
        if !check_subset(&ctx.phi, &access_region, &perm.region, &ctx.solver) {
            continue;
        }
        let g_real = perm.fraction.to_real_expr();
        if !ctx
            .solver
            .entails(&ctx.phi, &Atom::RealLt(zero.clone(), g_real.clone()))
        {
            continue;
        }
        candidate = Some(perm.clone());
        break;
    }

    let source_perm = candidate.ok_or_else(|| {
        format!(
            "Load at {}[{}] requires a positive permission covering the index",
            array.0, index.0
        )
    })?;

    let g_fraction = source_perm.fraction.clone();
    let f_fraction = ctx.fresh_fraction_var("__load_frac_");
    ctx.add_fraction_validity_constraint(&f_fraction);
    let f_real = f_fraction.to_real_expr();
    let g_real = g_fraction.to_real_expr();
    // Add constraint: 0 < f < g
    // to make sure subsequent load/call won't stuck
    ctx.add_fraction_validity_constraint(&g_fraction);
    ctx.add_constraint(Atom::RealLt(f_real.clone(), g_real.clone()));

    let load_perm = Permission::new(f_fraction.clone(), array.clone(), access_region.clone());
    let load_perm_expr = PermExpr::singleton(load_perm.clone());

    let rem_perm = PermExpr::Sub(Box::new(joined_perm), Box::new(load_perm_expr.clone()));
    if !rem_perm.is_valid(&ctx.phi, &ctx.solver) {
        return Err(format!(
            "Load at {}[{}] cannot split available permissions",
            array.0, index.0
        ));
    }

    ctx.bind_perm(right, rem_perm);
    ctx.bind_perm(ghost_out, load_perm_expr);

    Ok(())
}

/// Check JoinSplit followed by Store.
fn check_ghost_stmt_joinsplit_store(
    join_stmt: &GhostStmt,
    store_stmt: &GhostStmt,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    // Process JoinSplit
    let (left, right, inputs) = match join_stmt {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => (left, right, inputs),
        _ => unreachable!(),
    };

    let joined_perm = ctx.join_perms(inputs)?;

    // Process Store
    let (array, index, ghost_in, ghost_out) = match store_stmt {
        GhostStmt::Store {
            array,
            index,
            value: _,
            ghost_in,
            ghost_out,
        } => (array, index, ghost_in, ghost_out),
        _ => unreachable!(),
    };

    if ghost_in.0 != left.0 {
        return Err(format!(
            "Store ghost_in {} does not match JoinSplit left {}",
            ghost_in.0, left.0
        ));
    }

    let (lo, hi) = (
        Idx::Var(index.0.clone()),
        Idx::Add(Box::new(Idx::Var(index.0.clone())), Box::new(Idx::Const(1))),
    );
    // full permission on array at `index`
    let store_perm = PermExpr::Singleton(Permission {
        fraction: FractionExpr::from_int(1),
        array: array.clone(),
        region: RegionSetExpr::interval(lo, hi),
    });

    let rem_perm: PermExpr = PermExpr::Sub(Box::new(joined_perm), Box::new(store_perm.clone()));

    if !rem_perm.is_valid(&ctx.phi, &ctx.solver) {
        return Err(format!(
            "Store at {} requires full permission on region containing {}",
            array.0, index.0
        ));
    }

    ctx.bind_perm(right, rem_perm);
    ctx.bind_perm(&ghost_out.1, store_perm);
    Ok(())
}

/// Check two JoinSplits followed by Call.
fn check_ghost_stmt_jnsplt_jnsplt_call(
    join_stmt1: &GhostStmt,
    join_stmt2: &GhostStmt,
    call_stmt: &GhostStmt,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    let (left1, right1, inputs1) = match join_stmt1 {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => (left, right, inputs),
        _ => unreachable!(),
    };
    let joined_perm1 = ctx.join_perms(inputs1)?;

    let (left2, right2, inputs2) = match join_stmt2 {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => (left, right, inputs),
        _ => unreachable!(),
    };
    let joined_perm2 = ctx.join_perms(inputs2)?;

    let (_outputs, func, args, ghost_need, ghost_left, ghost_ret) = match call_stmt {
        GhostStmt::Call {
            outputs,
            func,
            args,
            ghost_need,
            ghost_left,
            ghost_ret,
        } => (outputs, func, args, ghost_need, ghost_left, ghost_ret),
        _ => unreachable!(),
    };

    if ghost_need.0 != left1.0 {
        return Err(format!(
            "Call ghost_need {} does not match first JoinSplit left {}",
            ghost_need.0, left1.0
        ));
    }
    if ghost_left.0 != left2.0 {
        return Err(format!(
            "Call ghost_left {} does not match second JoinSplit left {}",
            ghost_left.0, left2.0
        ));
    }

    let sig = ctx
        .get_signature(&func.0)
        .ok_or_else(|| format!("Call to unknown function {}", func.0))?;

    if sig.params.len() != args.len() {
        return Err(format!(
            "Call to {} expects {} arguments but received {}",
            func.0,
            sig.params.len(),
            args.len()
        ));
    }

    let mut idx_substitutions: Vec<(String, Idx)> = Vec::new();

    for ((param_var, ty), arg) in sig.params.iter().zip(args.iter()) {
        if ty.is_int() {
            idx_substitutions.push((param_var.0.clone(), Idx::Var(arg.0.clone())));
        }
    }

    idx_substitutions.sort_by(|a, b| a.0.cmp(&b.0));

    let required_sync = substitute_perm_expr_with_maps(&sig.initial_perms.0, &idx_substitutions);
    let required_garb = substitute_perm_expr_with_maps(&sig.initial_perms.1, &idx_substitutions);

    if !required_sync.is_valid(&ctx.phi, &ctx.solver) {
        return Err(format!(
            "Required permission for {} (p_sync) is invalid after substitution",
            func.0
        ));
    }
    if !required_garb.is_valid(&ctx.phi, &ctx.solver) {
        return Err(format!(
            "Required permission for {} (p_garb) is invalid after substitution",
            func.0
        ));
    }

    let mut available_sync = joined_perm1
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| {
            "Joined permissions for first JoinSplit could not be normalised".to_string()
        })?;
    let needed_sync = required_sync
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| "Required p_sync permissions could not be normalised".to_string())?;
    for need in &needed_sync {
        if !consume_permission(&mut available_sync, need, &ctx.phi, &ctx.solver) {
            return Err(format!(
                "Call to {} cannot provide required permission for p_sync",
                func.0
            ));
        }
    }
    let remainder_sync_expr = permissions_to_expr(available_sync);
    if !remainder_sync_expr.is_valid(&ctx.phi, &ctx.solver) {
        return Err(format!(
            "Remaining permissions after consuming p_sync for {} are invalid",
            func.0
        ));
    }
    ctx.bind_perm(right1, remainder_sync_expr);

    let mut available_garb = joined_perm2
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| {
            "Joined permissions for second JoinSplit could not be normalised".to_string()
        })?;
    let needed_garb = required_garb
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| "Required p_garb permissions could not be normalised".to_string())?;
    for need in &needed_garb {
        if !consume_permission(&mut available_garb, need, &ctx.phi, &ctx.solver) {
            return Err(format!(
                "Call to {} cannot provide required permission for p_garb",
                func.0
            ));
        }
    }
    let remainder_garb_expr = permissions_to_expr(available_garb);
    if !remainder_garb_expr.is_valid(&ctx.phi, &ctx.solver) {
        return Err(format!(
            "Remaining permissions after consuming p_garb for {} are invalid",
            func.0
        ));
    }
    ctx.bind_perm(right2, remainder_garb_expr);

    // bind ghost_ret with the sum of the callee's needed sync and garb permissions
    let ret_perm_expr = PermExpr::union(vec![required_sync, required_garb]);
    ctx.bind_perm(ghost_ret, ret_perm_expr);

    Ok(())
}

/// Check a JoinSplit followed by Return tail.
fn check_ghost_tail_with_joinsplit(
    join_stmt: &GhostStmt,
    tail: &GhostTail,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    match tail {
        GhostTail::Return { value: _, perm } => {
            // Process JoinSplit
            // For Return, right would always be epsilon
            let (left, _right, inputs) = match join_stmt {
                GhostStmt::JoinSplit {
                    left,
                    right,
                    inputs,
                } => (left, right, inputs),
                _ => unreachable!(),
            };

            let joined_perm = ctx.join_perms(inputs)?;

            if left.0 != perm.0 {
                return Err(format!(
                    "Return permission {} does not match JoinSplit left {}",
                    perm.0, left.0
                ));
            }

            let entry_perms = ctx.current_fn_entry_perms().ok_or_else(|| {
                "Return encountered without recorded entry permissions".to_string()
            })?;

            let expected_total =
                PermExpr::union(vec![entry_perms.0.clone(), entry_perms.1.clone()]);

            let joined_flat = joined_perm
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Returned permission could not be normalised".to_string())?;
            let mut expected_flat = expected_total
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Entry permissions could not be normalised".to_string())?;

            for perm_piece in &joined_flat {
                if !consume_permission(&mut expected_flat, perm_piece, &ctx.phi, &ctx.solver) {
                    return Err(format!(
                        "Return permission contains {:?} which was not present at function entry",
                        perm_piece
                    ));
                }
            }

            if !expected_flat.is_empty() {
                return Err(
                    "Return permission is missing resources that were provided at function entry"
                        .to_string(),
                );
            }

            Ok(())
        }
        _ => Err(format!(
            "Single JoinSplit at end of expression must be followed by Return tail, found {:?}",
            tail
        )),
    }
}

/// Check two JoinSplits followed by TailCall tail.
fn check_ghost_tail_with_two_joinsplits(
    join_stmt1: &GhostStmt,
    join_stmt2: &GhostStmt,
    tail: &GhostTail,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    match tail {
        GhostTail::TailCall {
            func,
            args,
            ghost_need,
            ghost_left,
        } => {
            // Process first JoinSplit
            let (left1, right1, inputs1) = match join_stmt1 {
                GhostStmt::JoinSplit {
                    left,
                    right,
                    inputs,
                } => (left, right, inputs),
                _ => unreachable!(),
            };
            let joined_perm1 = ctx.join_perms(inputs1)?;

            // Process second JoinSplit
            let (left2, right2, inputs2) = match join_stmt2 {
                GhostStmt::JoinSplit {
                    left,
                    right,
                    inputs,
                } => (left, right, inputs),
                _ => unreachable!(),
            };
            let joined_perm2 = ctx.join_perms(inputs2)?;

            // Verify ghost_need and ghost_left match the JoinSplits
            if ghost_need.0 != left1.0 {
                return Err(format!(
                    "TailCall ghost_need {} does not match first JoinSplit left {}",
                    ghost_need.0, left1.0
                ));
            }
            if ghost_left.0 != left2.0 {
                return Err(format!(
                    "TailCall ghost_left {} does not match second JoinSplit left {}",
                    ghost_left.0, left2.0
                ));
            }

            // Look up the callee's signature
            let sig = ctx
                .get_signature(&func.0)
                .ok_or_else(|| format!("Tail call to unknown function {}", func.0))?;

            if sig.params.len() != args.len() {
                return Err(format!(
                    "Tail call to {} expects {} arguments but received {}",
                    func.0,
                    sig.params.len(),
                    args.len()
                ));
            }

            // Build index substitutions
            let mut idx_substitutions: Vec<(String, Idx)> = Vec::new();
            for ((param_var, ty), arg) in sig.params.iter().zip(args.iter()) {
                if ty.is_int() {
                    idx_substitutions.push((param_var.0.clone(), Idx::Var(arg.0.clone())));
                }
            }
            idx_substitutions.sort_by(|a, b| a.0.cmp(&b.0));

            // Substitute parameters in the callee's required permissions
            let required_sync =
                substitute_perm_expr_with_maps(&sig.initial_perms.0, &idx_substitutions);
            let required_garb =
                substitute_perm_expr_with_maps(&sig.initial_perms.1, &idx_substitutions);

            if !required_sync.is_valid(&ctx.phi, &ctx.solver) {
                return Err(format!(
                    "Required permission for {} (p_sync) is invalid after substitution",
                    func.0
                ));
            }
            if !required_garb.is_valid(&ctx.phi, &ctx.solver) {
                return Err(format!(
                    "Required permission for {} (p_garb) is invalid after substitution",
                    func.0
                ));
            }

            // Check that ghost_need (joined_perm1) provides required_sync
            let mut available_sync = joined_perm1
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| {
                    "Joined permissions for first JoinSplit could not be normalised".to_string()
                })?;
            let needed_sync = required_sync
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Required p_sync permissions could not be normalised".to_string())?;
            for need in &needed_sync {
                if !consume_permission(&mut available_sync, need, &ctx.phi, &ctx.solver) {
                    return Err(format!(
                        "Tail call to {} cannot provide required permission for p_sync",
                        func.0
                    ));
                }
            }
            let remainder_sync_expr = permissions_to_expr(available_sync);
            if !remainder_sync_expr.is_valid(&ctx.phi, &ctx.solver) {
                return Err(format!(
                    "Remaining permissions after consuming p_sync for {} are invalid",
                    func.0
                ));
            }
            ctx.bind_perm(right1, remainder_sync_expr);

            // Check that ghost_left (joined_perm2) provides required_garb
            let mut available_garb = joined_perm2
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| {
                    "Joined permissions for second JoinSplit could not be normalised".to_string()
                })?;
            let needed_garb = required_garb
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Required p_garb permissions could not be normalised".to_string())?;
            for need in &needed_garb {
                if !consume_permission(&mut available_garb, need, &ctx.phi, &ctx.solver) {
                    return Err(format!(
                        "Tail call to {} cannot provide required permission for p_garb",
                        func.0
                    ));
                }
            }
            let remainder_garb_expr = permissions_to_expr(available_garb);
            if !remainder_garb_expr.is_valid(&ctx.phi, &ctx.solver) {
                return Err(format!(
                    "Remaining permissions after consuming p_garb for {} are invalid",
                    func.0
                ));
            }
            ctx.bind_perm(right2, remainder_garb_expr);

            Ok(())
        }
        _ => Err(format!(
            "Two JoinSplits at end of expression must be followed by TailCall tail, found {:?}",
            tail
        )),
    }
}

/// Check a tail if-else expression.
pub fn check_ghost_tail_if(tail: &GhostTail, ctx: &mut CheckContext) -> Result<(), String> {
    match tail {
        GhostTail::IfElse {
            cond,
            then_expr,
            else_expr,
        } => {
            // Branch: create two sub-contexts
            let mut then_ctx = ctx.clone();
            let mut else_ctx = ctx.clone();

            // Add branching constraints
            let cond_var = Atom::BoolVar(cond.0.clone());
            then_ctx.add_constraint(cond_var.clone());
            else_ctx.add_constraint(Atom::Not(Box::new(cond_var)));

            // Check both branches
            check_ghost_expr(then_expr, &mut then_ctx)?;
            check_ghost_expr(else_expr, &mut else_ctx)?;

            // Both branches must succeed independently
            Ok(())
        }
        _ => Err(format!("Tail expression must be IfElse, found {:?}", tail)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::semantic::solver::Phi;

    fn make_perm(fraction: FractionExpr, array: &str, lo: i64, hi: i64) -> PermExpr {
        PermExpr::singleton(Permission::new(
            fraction,
            Var(array.to_string()),
            RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi)),
        ))
    }

    #[test]
    fn test_permission_env() {
        let mut env = PermissionEnv::new();
        let var = GhostVar("p1".to_string());
        let perm = Permission::new(
            FractionExpr::from_ratio(1, 2),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
        );

        env.bind(&var, PermExpr::singleton(perm.clone()));
        assert!(env.contains(&var));

        // Extract the permission from the stored expression
        if let PermExpr::Singleton(stored_perm) = env.lookup(&var).unwrap() {
            assert_eq!(stored_perm.fraction, perm.fraction);
        } else {
            panic!("Expected singleton permission");
        }
    }

    #[test]
    fn test_region_substitution() {
        use super::substitute_idx_in_region;

        // Test substituting i -> j in region {i..N}
        let region = RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string()));

        let substituted = substitute_idx_in_region(&region, "i", &Idx::Var("j".to_string()));

        match substituted {
            RegionSetExpr::Interval { lo, hi } => {
                assert_eq!(lo, Idx::Var("j".to_string()));
                assert_eq!(hi, Idx::Var("N".to_string()));
            }
            _ => panic!("Expected interval"),
        }
    }

    #[test]
    fn test_permission_substitution() {
        // Test Permission::substitute_region
        let perm = Permission::new(
            FractionExpr::from_ratio(1, 2),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
        );

        let substituted = perm.substitute_region("i", &Idx::Var("j".to_string()));

        match substituted.region {
            RegionSetExpr::Interval { lo, hi } => {
                assert_eq!(lo, Idx::Var("j".to_string()));
                assert_eq!(hi, Idx::Var("N".to_string()));
            }
            _ => panic!("Expected interval"),
        }
        assert_eq!(substituted.fraction, perm.fraction);
        assert_eq!(substituted.array, perm.array);
    }

    #[test]
    fn test_perm_sub_valid() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let rhs = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 5);

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_invalid_fraction() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        let lhs = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 10);
        let rhs = make_perm(FractionExpr::from_ratio(3, 4), "A", 0, 10);

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(!expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_invalid_region() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 5);
        let rhs = make_perm(FractionExpr::from_ratio(1, 2), "A", 4, 8);

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(!expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_nested() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        let inner_lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let inner_rhs = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);
        let lhs = PermExpr::Sub(Box::new(inner_lhs), Box::new(inner_rhs));

        let rhs_valid = make_perm(FractionExpr::from_ratio(3, 5), "A", 0, 10);
        let rhs_invalid = make_perm(FractionExpr::from_ratio(4, 5), "A", 0, 10);

        let expr_valid = PermExpr::Sub(Box::new(lhs.clone()), Box::new(rhs_valid));
        assert!(expr_valid.is_valid(&phi, &solver));

        let expr_invalid = PermExpr::Sub(Box::new(lhs), Box::new(rhs_invalid));
        assert!(!expr_invalid.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_symbolic_fraction_valid() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Create a symbolic fraction f where f ∈ (0, 1]
        let f = FractionExpr::Var("f".to_string());

        // Add constraint: 0 < f <= 1
        use crate::logic::semantic::solver::RealExpr;
        let zero = RealExpr::from_int(0);
        let one = RealExpr::from_int(1);
        let f_real = f.to_real_expr();
        phi.push(Atom::RealLt(zero, f_real.clone()));
        phi.push(Atom::RealLe(f_real.clone(), one));

        // Create permissions: lhs = 1.0 @ A{0..10}, rhs = f @ A{0..10}
        let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let rhs = PermExpr::singleton(Permission::new(
            f,
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_symbolic_fraction_invalid() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Create a symbolic fraction f where f > 1
        let f = FractionExpr::Var("f".to_string());

        use crate::logic::semantic::solver::RealExpr;
        let one = RealExpr::from_int(1);
        let f_real = f.to_real_expr();
        // Add constraint: f > 1 (invalid for a fraction)
        phi.push(Atom::RealLt(one, f_real));

        // Create permissions: lhs = 1.0 @ A{0..10}, rhs = f @ A{0..10}
        let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let rhs = PermExpr::singleton(Permission::new(
            f,
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(!expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_symbolic_region_variable_indices() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Add constraints: i < j < N (concrete values)
        phi.push(Atom::Lt(
            Idx::Var("i".to_string()),
            Idx::Var("j".to_string()),
        ));
        phi.push(Atom::Lt(
            Idx::Var("j".to_string()),
            Idx::Var("N".to_string()),
        ));

        // Create permissions: lhs = 1.0 @ A{i..N}, rhs = 1.0 @ A{j..N}
        let lhs = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
        ));
        let rhs = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("j".to_string()), Idx::Var("N".to_string())),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_symbolic_region_non_subset() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Add constraints: i < j < k < N
        phi.push(Atom::Lt(
            Idx::Var("i".to_string()),
            Idx::Var("j".to_string()),
        ));
        phi.push(Atom::Lt(
            Idx::Var("j".to_string()),
            Idx::Var("k".to_string()),
        ));
        phi.push(Atom::Lt(
            Idx::Var("k".to_string()),
            Idx::Var("N".to_string()),
        ));

        // Create permissions: lhs = 1.0 @ A{i..j}, rhs = 1.0 @ A{k..N}
        // Since i..j does not contain k..N, this should fail
        let lhs = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("j".to_string())),
        ));
        let rhs = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("k".to_string()), Idx::Var("N".to_string())),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(!expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_symbolic_fraction_and_region() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Add constraints: 0 < f <= 1, 0 < g <= 1/2, and g <= f, i < j < N
        let f = FractionExpr::Var("f".to_string());
        let g = FractionExpr::Var("g".to_string());

        use crate::logic::semantic::solver::RealExpr;
        let zero = RealExpr::from_int(0);
        let half = RealExpr::from_ratio(1, 2);
        let one = RealExpr::from_int(1);
        let f_real = f.to_real_expr();
        let g_real = g.to_real_expr();

        phi.push(Atom::RealLt(zero.clone(), f_real.clone()));
        phi.push(Atom::RealLe(f_real.clone(), one));
        phi.push(Atom::RealLt(zero, g_real.clone()));
        phi.push(Atom::RealLe(g_real.clone(), half));
        phi.push(Atom::RealLe(g_real, f_real)); // Ensure g <= f
        phi.push(Atom::Lt(
            Idx::Var("i".to_string()),
            Idx::Var("j".to_string()),
        ));
        phi.push(Atom::Lt(
            Idx::Var("j".to_string()),
            Idx::Var("N".to_string()),
        ));

        // Create permissions: lhs = f @ A{i..N}, rhs = g @ A{i..j}
        let lhs = PermExpr::singleton(Permission::new(
            f.clone(),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
        ));
        let rhs = PermExpr::singleton(Permission::new(
            g.clone(),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("j".to_string())),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_leftover_region() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Add constraints: i < j < N
        phi.push(Atom::Lt(
            Idx::Var("i".to_string()),
            Idx::Var("j".to_string()),
        ));
        phi.push(Atom::Lt(
            Idx::Var("j".to_string()),
            Idx::Var("N".to_string()),
        ));

        // Create permissions: lhs = 1.0 @ A{i..N}, rhs = 1.0 @ A{i..j}
        // After subtraction, we should have leftover region j..N
        let lhs = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
        ));
        let rhs = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("j".to_string())),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_fractional_leftover() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        // Create permissions: lhs = 1.0 @ A{0..10}, rhs = 1/3 @ A{0..10}
        // After subtraction, we should have leftover 2/3 on same region
        let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let rhs = make_perm(FractionExpr::from_ratio(1, 3), "A", 0, 10);

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_multiple_arrays() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        // Create permissions for different arrays
        // lhs = 1.0 @ A{0..10} + 1.0 @ B{0..5}
        // rhs = 1.0 @ A{0..5}
        let perm_a = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
        ));
        let perm_b = PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            Var("B".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(5)),
        ));
        let lhs = PermExpr::Add(vec![perm_a, perm_b]);

        let rhs = make_perm(FractionExpr::from_int(1), "A", 0, 5);

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_multiple_arrays_insufficient() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        // Create permissions for different arrays
        // lhs = 1.0 @ A{0..10}
        // rhs = 1.0 @ A{0..5} + 1.0 @ B{0..5} (needs B, but not available)
        let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);

        let perm_a = make_perm(FractionExpr::from_int(1), "A", 0, 5);
        let perm_b = make_perm(FractionExpr::from_int(1), "B", 0, 5);
        let rhs = PermExpr::Add(vec![perm_a, perm_b]);

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(!expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_symbolic_both_decrease() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();

        // Create symbolic fractions f and g where 0 < g < f <= 1
        let f = FractionExpr::Var("f".to_string());
        let g = FractionExpr::Var("g".to_string());

        use crate::logic::semantic::solver::RealExpr;
        let zero = RealExpr::from_int(0);
        let one = RealExpr::from_int(1);
        let f_real = f.to_real_expr();
        let g_real = g.to_real_expr();

        phi.push(Atom::RealLt(zero.clone(), g_real.clone()));
        phi.push(Atom::RealLt(g_real, f_real.clone()));
        phi.push(Atom::RealLe(f_real, one));

        // Create permissions: lhs = f @ A{0..10}, rhs = g @ A{0..10}
        let lhs = PermExpr::singleton(Permission::new(
            f,
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
        ));
        let rhs = PermExpr::singleton(Permission::new(
            g,
            Var("A".to_string()),
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
        ));

        let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
        assert!(expr.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_deeply_nested() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        // Create nested subtractions: ((1.0 - 1/4) - 1/4) should still be valid
        let p1 = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let p2 = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);
        let p3 = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);

        let first_sub = PermExpr::Sub(Box::new(p1), Box::new(p2));
        let second_sub = PermExpr::Sub(Box::new(first_sub), Box::new(p3));

        assert!(second_sub.is_valid(&phi, &solver));
    }

    #[test]
    fn test_perm_sub_deeply_nested_invalid() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        // Create nested subtractions: ((1.0 - 1/2) - 1/2) - 1/4 should be invalid
        // (trying to subtract 5/4 total from 1.0)
        let p1 = make_perm(FractionExpr::from_int(1), "A", 0, 10);
        let p2 = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 10);
        let p3 = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 10);
        let p4 = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);

        let first_sub = PermExpr::Sub(Box::new(p1), Box::new(p2));
        let second_sub = PermExpr::Sub(Box::new(first_sub), Box::new(p3));
        let third_sub = PermExpr::Sub(Box::new(second_sub), Box::new(p4));

        assert!(!third_sub.is_valid(&phi, &solver));
    }
}
