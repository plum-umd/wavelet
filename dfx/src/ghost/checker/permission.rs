//! Permission types and operations.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use crate::ghost::fracperms::{
    FractionExpr, check_fraction_leq, check_fraction_valid, try_add_fractions, try_sub_fractions,
};
use crate::ir::Var;
use crate::logic::cap::RegionModel;
use crate::logic::semantic::region_set::{RegionSetExpr, check_subset, overlaps};
use crate::logic::semantic::solver::{Atom, Idx, Phi, SmtSolver};

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
        } else if items.len() == 1 {
            items.into_iter().next().unwrap()
        } else {
            PermExpr::Add(items)
        }
    }

    /// Check if this permission expression is valid under the given context.
    pub fn is_valid(&self, phi: &Phi, solver: &SmtSolver) -> bool {
        match self {
            PermExpr::Empty => true,
            PermExpr::Singleton(perm) => perm.is_valid(phi, solver),
            PermExpr::Add(items) => {
                let mut perms_by_array: HashMap<Var, Vec<&Permission>> = HashMap::new();
                for item in items {
                    if let PermExpr::Singleton(perm) = item {
                        perms_by_array
                            .entry(perm.array.clone())
                            .or_insert_with(Vec::new)
                            .push(perm);
                    } else {
                        if !item.is_valid(phi, solver) {
                            return false;
                        }
                    }
                }

                for (_, perms_for_array) in perms_by_array {
                    if perms_for_array.len() == 1 {
                        if !perms_for_array[0].is_valid(phi, solver) {
                            return false;
                        }
                    } else {
                        for i in 0..perms_for_array.len() {
                            if !perms_for_array[i].is_valid(phi, solver) {
                                return false;
                            }

                            for j in (i + 1)..perms_for_array.len() {
                                if overlaps(
                                    phi,
                                    &perms_for_array[i].region,
                                    &perms_for_array[j].region,
                                    solver,
                                ) {
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
                if !lhs.is_valid(phi, solver) || !rhs.is_valid(phi, solver) {
                    return false;
                }

                self.collect_permissions(phi, solver).is_some()
            }
        }
    }

    /// Flatten the permission expression into the multiset of positive
    /// permissions it represents. Returns `None` if the expression encodes an
    /// invalid subtraction (i.e., tries to consume more than available).
    pub fn collect_permissions(&self, phi: &Phi, solver: &SmtSolver) -> Option<Vec<Permission>> {
        match self {
            PermExpr::Empty => Some(Vec::new()),
            PermExpr::Singleton(perm) => {
                let perms = normalize_permission_list(vec![perm.clone()], phi, solver);
                Some(perms)
            }
            PermExpr::Add(items) => {
                let mut acc = Vec::new();
                for item in items {
                    let mut child = item.collect_permissions(phi, solver)?;
                    acc.append(&mut child);
                }
                let perms = normalize_permission_list(acc, phi, solver);
                Some(perms)
            }
            PermExpr::Sub(lhs, rhs) => {
                let mut available = lhs.collect_permissions(phi, solver)?;
                let needed = rhs.collect_permissions(phi, solver)?;
                for perm_rhs in needed {
                    if !consume_permission(&mut available, &perm_rhs, phi, solver) {
                        return None;
                    }
                }
                let perms = normalize_permission_list(available, phi, solver);
                Some(perms)
            }
        }
    }

    /// Produce a canonical representation of this permission expression by
    /// flattening sums/subtractions and simplifying regions and fractions.
    pub fn normalize(&self, phi: &Phi, solver: &SmtSolver) -> Option<PermExpr> {
        let perms = self.collect_permissions(phi, solver)?;
        let normalized = normalize_permission_list(perms, phi, solver);
        Some(permissions_to_expr(normalized))
    }
}

pub fn normalize_fraction_expr(expr: FractionExpr) -> FractionExpr {
    fn is_structural_zero(expr: &FractionExpr) -> bool {
        matches!(expr, FractionExpr::Const(n, _) if *n == 0)
    }

    fn hash_fraction(expr: &FractionExpr) -> u64 {
        let mut hasher = DefaultHasher::new();
        expr.hash(&mut hasher);
        hasher.finish()
    }

    fn normalize_once(expr: FractionExpr) -> FractionExpr {
        match expr {
            FractionExpr::Const(_, _) | FractionExpr::Var(_) => expr,
            FractionExpr::Add(lhs, rhs) => {
                let lhs = normalize_fraction_expr(*lhs);
                let rhs = normalize_fraction_expr(*rhs);

                if is_structural_zero(&lhs) {
                    return rhs;
                }
                if is_structural_zero(&rhs) {
                    return lhs;
                }

                if let (FractionExpr::Const(n1, d1), FractionExpr::Const(n2, d2)) = (&lhs, &rhs) {
                    let num = (*n1 as i128) * (*d2 as i128) + (*n2 as i128) * (*d1 as i128);
                    let den = (*d1 as i128) * (*d2 as i128);
                    return FractionExpr::from_ratio(num as i64, den as i64);
                }

                if let FractionExpr::Sub(a, b) = &lhs {
                    if **b == rhs {
                        return (**a).clone();
                    }
                }
                if let FractionExpr::Sub(a, b) = &rhs {
                    if **b == lhs {
                        return (**a).clone();
                    }
                }

                FractionExpr::Add(Box::new(lhs), Box::new(rhs))
            }
            FractionExpr::Sub(lhs, rhs) => {
                let lhs = normalize_fraction_expr(*lhs);
                let rhs = normalize_fraction_expr(*rhs);

                if lhs == rhs {
                    return FractionExpr::from_int(0);
                }

                if is_structural_zero(&rhs) {
                    return lhs;
                }

                if let (FractionExpr::Const(n1, d1), FractionExpr::Const(n2, d2)) = (&lhs, &rhs) {
                    let num = (*n1 as i128) * (*d2 as i128) - (*n2 as i128) * (*d1 as i128);
                    let den = (*d1 as i128) * (*d2 as i128);
                    return FractionExpr::from_ratio(num as i64, den as i64);
                }

                if let FractionExpr::Add(a, b) = &lhs {
                    if **a == rhs {
                        return (**b).clone();
                    }
                    if **b == rhs {
                        return (**a).clone();
                    }
                }

                if let FractionExpr::Sub(a, b) = &lhs {
                    if **b == rhs {
                        return (**a).clone();
                    }
                }

                if let FractionExpr::Sub(a, b) = &rhs {
                    if **a == lhs {
                        return (**b).clone();
                    }
                }

                FractionExpr::Sub(Box::new(lhs), Box::new(rhs))
            }
        }
    }

    let mut current = expr;
    let mut seen: HashSet<u64> = HashSet::new();
    loop {
        let fingerprint = hash_fraction(&current);
        if !seen.insert(fingerprint) {
            return current;
        }
        let next = normalize_once(current.clone());
        if next == current {
            return next;
        }
        let next_fingerprint = hash_fraction(&next);
        if seen.contains(&next_fingerprint) {
            return next;
        }
        current = next;
    }
}

pub fn normalize_permission_list(
    perms: Vec<Permission>,
    phi: &Phi,
    solver: &SmtSolver,
) -> Vec<Permission> {
    let mut normalized: Vec<Permission> = Vec::new();

    for perm in perms {
        let region = perm.region.simplify(phi, solver);
        if region.is_empty(phi, solver) {
            continue;
        }
        let fraction = normalize_fraction_expr(perm.fraction);
        if is_fraction_zero(phi, &fraction, solver) {
            continue;
        }

        let mut merged = false;
        for existing in &mut normalized {
            if existing.array == perm.array && existing.region == region {
                if let Some(sum) = try_add_fractions(&existing.fraction, &fraction, phi, solver) {
                    existing.fraction = normalize_fraction_expr(sum);
                    merged = true;
                    break;
                }
            }

            if !merged && existing.array == perm.array && existing.fraction == fraction {
                let combined = RegionSetExpr::union([existing.region.clone(), region.clone()])
                    .simplify(phi, solver);

                existing.region = combined;
                merged = true;
                break;
            }
        }

        if !merged {
            normalized.push(Permission::new(fraction, perm.array, region));
        }
    }

    normalized.sort_by(|a, b| {
        a.array
            .0
            .cmp(&b.array.0)
            .then_with(|| a.region.to_string().cmp(&b.region.to_string()))
    });

    normalized
}

// Iteratively carve out overlapping slices of `available` until `needed` is
// satisfied, splitting regions/fractions as required and queuing leftovers.
pub fn consume_permission(
    available: &mut Vec<Permission>,
    needed: &Permission,
    phi: &Phi,
    solver: &SmtSolver,
) -> bool {
    let mut pending: Vec<Permission> = vec![needed.clone()];

    while let Some(piece) = pending.pop() {
        let region = piece.region.simplify(phi, solver);
        if region.is_empty(phi, solver) {
            continue;
        }

        let mut idx = 0;
        let mut satisfied = false;
        while idx < available.len() {
            if available[idx].array != piece.array {
                idx += 1;
                continue;
            }

            let candidate_region = available[idx].region.clone();
            let overlap = RegionSetExpr::intersection(candidate_region.clone(), region.clone())
                .simplify(phi, solver);
            if overlap.is_empty(phi, solver) {
                idx += 1;
                continue;
            }

            let candidate_ge_piece =
                check_fraction_leq(phi, &piece.fraction, &available[idx].fraction, solver);
            let piece_ge_candidate = if candidate_ge_piece {
                false
            } else {
                check_fraction_leq(phi, &available[idx].fraction, &piece.fraction, solver)
            };

            if !candidate_ge_piece && !piece_ge_candidate {
                idx += 1;
                continue;
            }

            let candidate = available.swap_remove(idx);

            let piece_subset_candidate = check_subset(phi, &region, &candidate.region, solver);
            let candidate_subset_piece = check_subset(phi, &candidate.region, &region, solver);

            let candidate_outside_raw =
                RegionSetExpr::difference(candidate.region.clone(), overlap.clone())
                    .simplify(phi, solver);
            let candidate_outside = if candidate_subset_piece {
                RegionSetExpr::Empty
            } else {
                candidate_outside_raw
            };
            if !candidate_outside.is_empty(phi, solver) {
                available.push(Permission::new(
                    normalize_fraction_expr(candidate.fraction.clone()),
                    candidate.array.clone(),
                    candidate_outside,
                ));
            }

            let piece_outside_raw =
                RegionSetExpr::difference(region.clone(), overlap.clone()).simplify(phi, solver);
            let piece_outside = if piece_subset_candidate {
                RegionSetExpr::Empty
            } else {
                piece_outside_raw
            };
            if !piece_outside.is_empty(phi, solver) {
                pending.push(Permission::new(
                    normalize_fraction_expr(piece.fraction.clone()),
                    piece.array.clone(),
                    piece_outside,
                ));
            }

            if candidate_ge_piece {
                if let Some(diff_fraction) =
                    try_sub_fractions(&candidate.fraction, &piece.fraction, phi, solver)
                {
                    let diff_fraction = normalize_fraction_expr(diff_fraction);
                    if !is_fraction_zero(phi, &diff_fraction, solver) {
                        available.push(Permission::new(
                            diff_fraction,
                            candidate.array.clone(),
                            overlap.clone(),
                        ));
                    }
                    satisfied = true;
                } else {
                    // Should not happen because candidate_ge_piece ensured candidate >= piece,
                    // but fall back to trying other candidates for robustness.
                    available.push(candidate);
                    continue;
                }
            } else if let Some(diff_fraction) =
                try_sub_fractions(&piece.fraction, &candidate.fraction, phi, solver)
            {
                let diff_fraction = normalize_fraction_expr(diff_fraction);
                if !is_fraction_zero(phi, &diff_fraction, solver) {
                    pending.push(Permission::new(
                        diff_fraction,
                        piece.array.clone(),
                        overlap.clone(),
                    ));
                }
                satisfied = true;
            } else {
                // Could not use this candidate after removal; restore it and try another.
                available.push(candidate);
                continue;
            }

            break;
        }

        if !satisfied {
            return false;
        }
    }

    true
}

pub fn is_fraction_zero(phi: &Phi, frac: &FractionExpr, solver: &SmtSolver) -> bool {
    let zero = FractionExpr::from_int(0);
    check_fraction_leq(phi, frac, &zero, solver) && check_fraction_leq(phi, &zero, frac, solver)
}

/// Substitute an index variable in a region expression.
pub fn substitute_idx_in_region(region: &RegionSetExpr, from: &str, to: &Idx) -> RegionSetExpr {
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

pub fn apply_idx_substitutions_to_idx(idx: &Idx, substitutions: &[(String, Idx)]) -> Idx {
    let mut current = idx.clone();
    for (name, replacement) in substitutions {
        current = substitute_idx(&current, name, replacement);
    }
    current
}

/// Substitute an index variable in an index expression.
pub fn substitute_idx(idx: &Idx, from: &str, to: &Idx) -> Idx {
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

pub fn apply_idx_substitutions(
    region: &RegionSetExpr,
    substitutions: &[(String, Idx)],
) -> RegionSetExpr {
    let mut current = region.clone();
    for (name, idx) in substitutions {
        current = substitute_idx_in_region(&current, name.as_str(), idx);
    }
    current
}

pub fn substitute_permission_with_maps(
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

pub fn substitute_perm_expr_with_maps(
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

pub fn permissions_to_expr(perms: Vec<Permission>) -> PermExpr {
    if perms.is_empty() {
        PermExpr::empty()
    } else {
        PermExpr::union(perms.into_iter().map(PermExpr::singleton))
    }
}

pub fn substitute_atom_with_maps(atom: &Atom, substitutions: &[(String, Idx)]) -> Atom {
    match atom {
        Atom::Le(lhs, rhs) => Atom::Le(
            apply_idx_substitutions_to_idx(lhs, substitutions),
            apply_idx_substitutions_to_idx(rhs, substitutions),
        ),
        Atom::Lt(lhs, rhs) => Atom::Lt(
            apply_idx_substitutions_to_idx(lhs, substitutions),
            apply_idx_substitutions_to_idx(rhs, substitutions),
        ),
        Atom::Eq(lhs, rhs) => Atom::Eq(
            apply_idx_substitutions_to_idx(lhs, substitutions),
            apply_idx_substitutions_to_idx(rhs, substitutions),
        ),
        Atom::And(lhs, rhs) => Atom::And(
            Box::new(substitute_atom_with_maps(lhs, substitutions)),
            Box::new(substitute_atom_with_maps(rhs, substitutions)),
        ),
        Atom::Or(lhs, rhs) => Atom::Or(
            Box::new(substitute_atom_with_maps(lhs, substitutions)),
            Box::new(substitute_atom_with_maps(rhs, substitutions)),
        ),
        Atom::Implies(lhs, rhs) => Atom::Implies(
            Box::new(substitute_atom_with_maps(lhs, substitutions)),
            Box::new(substitute_atom_with_maps(rhs, substitutions)),
        ),
        Atom::Not(inner) => Atom::Not(Box::new(substitute_atom_with_maps(inner, substitutions))),
        _ => atom.clone(),
    }
}

pub fn substitute_fraction_expr(
    expr: &FractionExpr,
    substitutions: &HashMap<String, FractionExpr>,
) -> FractionExpr {
    match expr {
        FractionExpr::Const(_, _) => expr.clone(),
        FractionExpr::Var(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| FractionExpr::Var(name.clone())),
        FractionExpr::Add(lhs, rhs) => FractionExpr::Add(
            Box::new(substitute_fraction_expr(lhs, substitutions)),
            Box::new(substitute_fraction_expr(rhs, substitutions)),
        ),
        FractionExpr::Sub(lhs, rhs) => FractionExpr::Sub(
            Box::new(substitute_fraction_expr(lhs, substitutions)),
            Box::new(substitute_fraction_expr(rhs, substitutions)),
        ),
    }
}

pub fn substitute_fraction_in_permission(
    perm: &Permission,
    substitutions: &HashMap<String, FractionExpr>,
) -> Permission {
    Permission::new(
        substitute_fraction_expr(&perm.fraction, substitutions),
        perm.array.clone(),
        perm.region.clone(),
    )
}

pub fn substitute_fraction_in_perm_expr(
    expr: &PermExpr,
    substitutions: &HashMap<String, FractionExpr>,
) -> PermExpr {
    match expr {
        PermExpr::Empty => PermExpr::Empty,
        PermExpr::Singleton(perm) => {
            PermExpr::singleton(substitute_fraction_in_permission(perm, substitutions))
        }
        PermExpr::Add(items) => PermExpr::Add(
            items
                .iter()
                .map(|item| substitute_fraction_in_perm_expr(item, substitutions))
                .collect(),
        ),
        PermExpr::Sub(lhs, rhs) => PermExpr::Sub(
            Box::new(substitute_fraction_in_perm_expr(lhs, substitutions)),
            Box::new(substitute_fraction_in_perm_expr(rhs, substitutions)),
        ),
    }
}
