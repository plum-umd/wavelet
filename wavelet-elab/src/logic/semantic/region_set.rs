use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

use super::{Atom, Idx, Phi, PhiSolver, SmtSolver};
use crate::logic::cap::RegionModel;
use crate::logic::region::Region;

/// Boolean region expressions interpreted as sets of integer indices.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RegionSetExpr {
    /// The empty set.
    Empty,
    /// Half-open interval `[lo, hi)`.
    Interval { lo: Idx, hi: Idx },
    /// Finite union of region expressions.
    Union(Vec<RegionSetExpr>),
    /// Set difference `lhs \\ rhs`.
    Difference(Box<RegionSetExpr>, Box<RegionSetExpr>),
    /// Intersection `lhs ∩ rhs`.
    Intersection(Box<RegionSetExpr>, Box<RegionSetExpr>),
}

impl Default for RegionSetExpr {
    fn default() -> Self {
        RegionSetExpr::Empty
    }
}

impl RegionSetExpr {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn interval(lo: Idx, hi: Idx) -> Self {
        Self::Interval { lo, hi }
    }

    pub fn union<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RegionSetExpr>,
    {
        let mut items: Vec<_> = iter.into_iter().collect();
        if items.len() == 1 {
            items.pop().unwrap()
        } else {
            Self::Union(items)
        }
    }

    pub fn difference(lhs: RegionSetExpr, rhs: RegionSetExpr) -> Self {
        Self::Difference(Box::new(lhs), Box::new(rhs))
    }

    pub fn intersection(lhs: RegionSetExpr, rhs: RegionSetExpr) -> Self {
        Self::Intersection(Box::new(lhs), Box::new(rhs))
    }

    pub fn from_region(region: &Region) -> Self {
        let items: Vec<_> = region
            .iter()
            .map(|interval| RegionSetExpr::interval(interval.lo.clone(), interval.hi.clone()))
            .collect();
        if items.is_empty() {
            RegionSetExpr::Empty
        } else {
            RegionSetExpr::Union(items)
        }
    }

    fn collect_idx_vars(&self, set: &mut BTreeSet<String>) {
        match self {
            RegionSetExpr::Empty => {}
            RegionSetExpr::Interval { lo, hi } => {
                collect_idx_vars(lo, set);
                collect_idx_vars(hi, set);
            }
            RegionSetExpr::Union(items) => {
                for item in items {
                    item.collect_idx_vars(set);
                }
            }
            RegionSetExpr::Difference(lhs, rhs) => {
                lhs.collect_idx_vars(set);
                rhs.collect_idx_vars(set);
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                lhs.collect_idx_vars(set);
                rhs.collect_idx_vars(set);
            }
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            RegionSetExpr::Empty | RegionSetExpr::Interval { .. } => 3,
            RegionSetExpr::Intersection(_, _) => 2,
            RegionSetExpr::Difference(_, _) => 1,
            RegionSetExpr::Union(_) => 0,
        }
    }

    fn fmt_with_prec(&self, f: &mut fmt::Formatter<'_>, parent_prec: u8) -> fmt::Result {
        let prec = self.precedence();
        let needs_paren = prec < parent_prec;
        if needs_paren {
            write!(f, "(")?;
        }

        match self {
            RegionSetExpr::Empty => write!(f, "∅")?,
            RegionSetExpr::Interval { lo, hi } => write!(f, "[{}..{})", lo, hi)?,
            RegionSetExpr::Union(items) => {
                if items.is_empty() {
                    write!(f, "∅")?
                } else {
                    let mut first = true;
                    for item in items {
                        if first {
                            first = false;
                        } else {
                            write!(f, " ∪ ")?;
                        }
                        item.fmt_with_prec(f, prec)?;
                    }
                }
            }
            RegionSetExpr::Difference(lhs, rhs) => {
                lhs.fmt_with_prec(f, prec)?;
                write!(f, " \\ ")?;
                rhs.fmt_with_prec(f, prec + 1)?;
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                lhs.fmt_with_prec(f, prec)?;
                write!(f, " ∩ ")?;
                rhs.fmt_with_prec(f, prec)?;
            }
        }

        if needs_paren {
            write!(f, ")")?;
        }

        Ok(())
    }

    pub fn simplify(&self, phi: &Phi, solver: &SmtSolver) -> RegionSetExpr {
        let mut current = self.clone();
        let mut seen: HashSet<u64> = HashSet::new();
        loop {
            let fingerprint = hash_region_expr(&current);
            if !seen.insert(fingerprint) {
                return current;
            }
            let next = current.simplify_once(phi, solver);
            if next == current {
                return current;
            }
            let next_fingerprint = hash_region_expr(&next);
            if seen.contains(&next_fingerprint) {
                return next;
            }
            current = next;
        }
    }

    /// Apply a single round of region simplification by eliminating structural
    /// noise (such as nested unions, empty pieces, redundant subsets, and
    /// degenerate differences/intersections) while respecting the logical
    /// context carried in `phi`.
    fn simplify_once(&self, phi: &Phi, solver: &SmtSolver) -> RegionSetExpr {
        match self {
            RegionSetExpr::Empty => RegionSetExpr::Empty,
            RegionSetExpr::Interval { .. } => self.clone(),
            RegionSetExpr::Union(items) => {
                // Flatten nested unions and simplify each child first.
                let mut flat: Vec<RegionSetExpr> = Vec::new();
                for item in items {
                    let simplified = item.simplify(phi, solver);
                    match simplified {
                        RegionSetExpr::Union(inner) => flat.extend(inner),
                        other => flat.push(other),
                    }
                }

                flat.retain(|expr| !is_empty_expr(expr, phi, solver));

                // Remove redundant subsets while preserving larger covering regions.
                let mut normalized: Vec<RegionSetExpr> = Vec::new();
                'outer: for expr in flat {
                    let mut to_remove = Vec::new();
                    for (idx, existing) in normalized.iter().enumerate() {
                        if is_subset_expr(&expr, existing, phi, solver) {
                            continue 'outer;
                        }
                        if is_subset_expr(existing, &expr, phi, solver) {
                            to_remove.push(idx);
                        }
                    }
                    for idx in to_remove.into_iter().rev() {
                        normalized.remove(idx);
                    }
                    normalized.push(expr);
                }

                loop {
                    let mut reduced = false;
                    'outer_reduce: for idx in 0..normalized.len() {
                        if let RegionSetExpr::Difference(base, rhs) = normalized[idx].clone() {
                            for j in 0..normalized.len() {
                                if idx == j {
                                    continue;
                                }
                                if regions_equivalent(phi, &normalized[j], &rhs, solver) {
                                    let base_expr = base.simplify(phi, solver);
                                    normalized[idx] = base_expr;
                                    normalized.remove(j);
                                    reduced = true;
                                    break 'outer_reduce;
                                }
                            }
                            if normalized.len() > 1 {
                                let mut others: Vec<RegionSetExpr> = Vec::new();
                                for (j, item) in normalized.iter().enumerate() {
                                    if j == idx {
                                        continue;
                                    }
                                    others.push(item.clone());
                                }
                                if !others.is_empty() {
                                    let others_union =
                                        RegionSetExpr::union(others).simplify(phi, solver);
                                    if regions_equivalent(phi, &others_union, &rhs, solver) {
                                        let base_expr = base.simplify(phi, solver);
                                        normalized.clear();
                                        normalized.push(base_expr);
                                        reduced = true;
                                        break 'outer_reduce;
                                    }
                                }
                            }
                        }
                    }
                    if !reduced {
                        break;
                    }
                }

                if normalized.is_empty() {
                    RegionSetExpr::Empty
                } else if normalized.len() == 1 {
                    normalized.pop().unwrap()
                } else {
                    normalized.sort_by(|a, b| format!("{}", a).cmp(&format!("{}", b)));
                    RegionSetExpr::Union(normalized)
                }
            }
            RegionSetExpr::Difference(lhs, rhs) => {
                let left = lhs.simplify(phi, solver);
                let right = rhs.simplify(phi, solver);

                // Short-circuit obvious empty or redundant differences.
                if is_empty_expr(&left, phi, solver) {
                    return RegionSetExpr::Empty;
                }
                if is_empty_expr(&right, phi, solver) {
                    return left;
                }

                if let RegionSetExpr::Difference(inner_base, inner_removed) = &right {
                    if regions_equivalent(phi, &left, inner_base, solver) {
                        let intersect = RegionSetExpr::intersection(
                            left.clone(),
                            inner_removed.as_ref().clone(),
                        )
                        .simplify(phi, solver);
                        return intersect;
                    }
                }

                if let RegionSetExpr::Union(items) = &left {
                    let mut pieces: Vec<RegionSetExpr> = Vec::new();
                    for item in items {
                        let diff = RegionSetExpr::difference(item.clone(), right.clone())
                            .simplify(phi, solver);
                        if !is_empty_expr(&diff, phi, solver) {
                            pieces.push(diff);
                        }
                    }
                    if pieces.is_empty() {
                        return RegionSetExpr::Empty;
                    }
                    return RegionSetExpr::Union(pieces).simplify(phi, solver);
                }

                if is_subset_expr(&left, &right, phi, solver) {
                    return RegionSetExpr::Empty;
                }

                // Pull nested differences apart so we can combine all subtractions.
                let mut base = left;
                let mut subtracts = vec![right];
                loop {
                    match base {
                        RegionSetExpr::Difference(inner_lhs, inner_rhs) => {
                            subtracts.push(*inner_rhs);
                            base = *inner_lhs;
                        }
                        _ => break,
                    }
                }

                let subtraction = RegionSetExpr::union(subtracts).simplify(phi, solver);

                if is_empty_expr(&subtraction, phi, solver) {
                    return base;
                }
                if is_subset_expr(&base, &subtraction, phi, solver) {
                    return RegionSetExpr::Empty;
                }

                RegionSetExpr::Difference(Box::new(base), Box::new(subtraction))
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                let left = lhs.simplify(phi, solver);
                let right = rhs.simplify(phi, solver);

                // Intersection collapses to empty or a subset if either side dominates.
                if is_empty_expr(&left, phi, solver) || is_empty_expr(&right, phi, solver) {
                    return RegionSetExpr::Empty;
                }
                if is_subset_expr(&left, &right, phi, solver) {
                    return left;
                }
                if is_subset_expr(&right, &left, phi, solver) {
                    return right;
                }

                RegionSetExpr::Intersection(Box::new(left), Box::new(right))
            }
        }
    }
}

fn hash_region_expr(expr: &RegionSetExpr) -> u64 {
    let mut hasher = DefaultHasher::new();
    expr.hash(&mut hasher);
    hasher.finish()
}

impl fmt::Display for RegionSetExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_prec(f, 0)
    }
}

fn is_empty_expr(expr: &RegionSetExpr, phi: &Phi, solver: &SmtSolver) -> bool {
    check_subset(phi, expr, &RegionSetExpr::Empty, solver)
}

fn is_subset_expr(lhs: &RegionSetExpr, rhs: &RegionSetExpr, phi: &Phi, solver: &SmtSolver) -> bool {
    check_subset(phi, lhs, rhs, solver)
}

fn regions_equivalent(
    phi: &Phi,
    lhs: &RegionSetExpr,
    rhs: &RegionSetExpr,
    solver: &SmtSolver,
) -> bool {
    check_subset(phi, lhs, rhs, solver) && check_subset(phi, rhs, lhs, solver)
}

impl RegionModel for RegionSetExpr {
    type Solver = SmtSolver;

    fn from_region(region: &Region) -> Self {
        RegionSetExpr::from_region(region)
    }

    fn union(&self, other: &Self, _phi: &Phi, _solver: &Self::Solver) -> Self {
        RegionSetExpr::union([self.clone(), other.clone()])
    }

    fn diff(&self, other: &Self, _phi: &Phi, _solver: &Self::Solver) -> Self {
        RegionSetExpr::difference(self.clone(), other.clone())
    }

    fn is_subregion_of(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> bool {
        check_subset(phi, self, other, solver)
    }

    fn is_empty(&self, phi: &Phi, solver: &Self::Solver) -> bool {
        check_subset(phi, self, &RegionSetExpr::Empty, solver)
    }

    fn display(&self) -> String {
        format!("{}", self)
    }

    fn display_with(&self, phi: &Phi, solver: &Self::Solver) -> String {
        self.simplify(phi, solver).to_string()
    }
}

/// Decide whether `lhs ⊆ rhs` holds by asking the SMT solver for a counterexample.
pub fn check_subset(
    phi: &Phi,
    lhs: &RegionSetExpr,
    rhs: &RegionSetExpr,
    solver: &SmtSolver,
) -> bool {
    let const_map = build_const_map(phi);

    if let (
        RegionSetExpr::Interval {
            lo: lo_lhs,
            hi: hi_lhs,
        },
        RegionSetExpr::Interval {
            lo: lo_rhs,
            hi: hi_rhs,
        },
    ) = (lhs, rhs)
    {
        let lo_lhs_sub = substitute_idx_consts(lo_lhs, &const_map);
        let hi_lhs_sub = substitute_idx_consts(hi_lhs, &const_map);
        let lo_rhs_sub = substitute_idx_consts(lo_rhs, &const_map);
        let hi_rhs_sub = substitute_idx_consts(hi_rhs, &const_map);

        let lower_ok = solver.entails(phi, &Atom::Le(lo_rhs_sub.clone(), lo_lhs_sub.clone()));
        let upper_ok = solver.entails(phi, &Atom::Le(hi_lhs_sub.clone(), hi_rhs_sub.clone()));
        if lower_ok && upper_ok {
            return true;
        }
    }

    match lhs {
        RegionSetExpr::Empty => return true,
        RegionSetExpr::Union(items) => {
            return items
                .iter()
                .all(|item| check_subset(phi, item, rhs, solver));
        }
        _ => {}
    }

    let mut int_vars = BTreeSet::new();
    let mut bool_vars = BTreeSet::new();

    for atom in phi.iter() {
        collect_atom_vars(atom, &mut int_vars, &mut bool_vars);
    }
    lhs.collect_idx_vars(&mut int_vars);
    rhs.collect_idx_vars(&mut int_vars);

    if let Some(conflict) = int_vars
        .iter()
        .find(|var| bool_vars.contains(*var))
        .cloned()
    {
        if solver.is_query_logging_enabled() {
            println!(
                "; variable `{}` used as both int and bool; aborting set entailment",
                conflict
            );
        }
        return false;
    }

    let witness_name = choose_witness_name(&int_vars, &bool_vars);
    let lhs_membership = region_membership_atom(lhs, &witness_name);
    let rhs_membership = region_membership_atom(rhs, &witness_name);

    let mut extended_ctx = phi.clone();
    extended_ctx.push(lhs_membership);

    solver.entails(&extended_ctx, &rhs_membership)
}

fn build_const_map(phi: &Phi) -> HashMap<String, i64> {
    let mut consts = HashMap::new();
    for atom in phi.iter() {
        if let Atom::Eq(lhs, rhs) = atom {
            match (lhs, rhs) {
                (Idx::Var(name), Idx::Const(val)) => {
                    consts.insert(name.clone(), *val);
                }
                (Idx::Const(val), Idx::Var(name)) => {
                    consts.insert(name.clone(), *val);
                }
                _ => {}
            }
        }
    }
    consts
}

fn substitute_idx_consts(idx: &Idx, consts: &HashMap<String, i64>) -> Idx {
    match idx {
        Idx::Const(n) => Idx::Const(*n),
        Idx::Var(name) => consts
            .get(name)
            .map(|val| Idx::Const(*val))
            .unwrap_or_else(|| Idx::Var(name.clone())),
        Idx::Add(lhs, rhs) => Idx::Add(
            Box::new(substitute_idx_consts(lhs, consts)),
            Box::new(substitute_idx_consts(rhs, consts)),
        ),
        Idx::Sub(lhs, rhs) => Idx::Sub(
            Box::new(substitute_idx_consts(lhs, consts)),
            Box::new(substitute_idx_consts(rhs, consts)),
        ),
        Idx::Mul(lhs, rhs) => Idx::Mul(
            Box::new(substitute_idx_consts(lhs, consts)),
            Box::new(substitute_idx_consts(rhs, consts)),
        ),
    }
}

fn region_membership_atom(expr: &RegionSetExpr, witness: &str) -> Atom {
    match expr {
        RegionSetExpr::Empty => atom_false(),
        RegionSetExpr::Interval { lo, hi } => {
            let witness_idx = idx_var(witness);
            let upper = witness_idx.clone();
            mk_and(
                Atom::Le(lo.clone(), witness_idx),
                Atom::Lt(upper, hi.clone()),
            )
        }
        RegionSetExpr::Union(items) => {
            let disjuncts: Vec<_> = items
                .iter()
                .map(|item| region_membership_atom(item, witness))
                .collect();
            disjunction(disjuncts)
        }
        RegionSetExpr::Difference(lhs, rhs) => mk_and(
            region_membership_atom(lhs, witness),
            mk_not(region_membership_atom(rhs, witness)),
        ),
        RegionSetExpr::Intersection(lhs, rhs) => mk_and(
            region_membership_atom(lhs, witness),
            region_membership_atom(rhs, witness),
        ),
    }
}

fn disjunction(mut atoms: Vec<Atom>) -> Atom {
    match atoms.len() {
        0 => atom_false(),
        1 => atoms.pop().unwrap(),
        _ => atoms
            .into_iter()
            .reduce(|acc, next| mk_or(acc, next))
            .unwrap(),
    }
}

fn mk_and(lhs: Atom, rhs: Atom) -> Atom {
    Atom::And(Box::new(lhs), Box::new(rhs))
}

fn mk_or(lhs: Atom, rhs: Atom) -> Atom {
    Atom::Or(Box::new(lhs), Box::new(rhs))
}

fn mk_not(atom: Atom) -> Atom {
    Atom::Not(Box::new(atom))
}

fn atom_false() -> Atom {
    Atom::Lt(Idx::Const(0), Idx::Const(0))
}

fn idx_var(name: &str) -> Idx {
    Idx::Var(name.to_string())
}

/// Determine whether two region expressions are equivalent under `phi`.
pub fn check_equivalent(
    phi: &Phi,
    lhs: &RegionSetExpr,
    rhs: &RegionSetExpr,
    solver: &SmtSolver,
) -> bool {
    check_subset(phi, lhs, rhs, solver) && check_subset(phi, rhs, lhs, solver)
}

/// Determine whether two region expressions overlap under `phi`.
pub fn overlaps(phi: &Phi, lhs: &RegionSetExpr, rhs: &RegionSetExpr, solver: &SmtSolver) -> bool {
    let intersection = RegionSetExpr::intersection(lhs.clone(), rhs.clone());
    !check_subset(phi, &intersection, &RegionSetExpr::Empty, solver)
}

fn choose_witness_name(int_vars: &BTreeSet<String>, bool_vars: &BTreeSet<String>) -> String {
    let mut candidate = "__region_elem".to_string();
    let mut serial = 0usize;
    while int_vars.contains(&candidate) || bool_vars.contains(&candidate) {
        serial += 1;
        candidate = format!("__region_elem{serial}");
    }
    candidate
}

pub fn collect_atom_vars(atom: &Atom, ints: &mut BTreeSet<String>, bools: &mut BTreeSet<String>) {
    match atom {
        Atom::Le(lhs, rhs) | Atom::Lt(lhs, rhs) | Atom::Eq(lhs, rhs) => {
            collect_idx_vars(lhs, ints);
            collect_idx_vars(rhs, ints);
        }
        Atom::RealLe(_, _) | Atom::RealLt(_, _) | Atom::RealEq(_, _) => {
            // Real variables are collected separately in fracperms.rs
            // They are not mixed with integer variables here
        }
        Atom::BoolVar(name) => {
            bools.insert(name.clone());
        }
        Atom::And(lhs, rhs) | Atom::Or(lhs, rhs) | Atom::Implies(lhs, rhs) => {
            collect_atom_vars(lhs, ints, bools);
            collect_atom_vars(rhs, ints, bools);
        }
        Atom::Not(inner) => collect_atom_vars(inner, ints, bools),
    }
}

/// Collect variables from atoms, including real variables from RealExpr atoms.
pub fn collect_all_vars(
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
            collect_all_vars(lhs, ints, bools, reals);
            collect_all_vars(rhs, ints, bools, reals);
        }
        Atom::Not(inner) => collect_all_vars(inner, ints, bools, reals),
    }
}

fn collect_real_vars(expr: &super::solver::RealExpr, set: &mut BTreeSet<String>) {
    match expr {
        super::solver::RealExpr::Const(_, _) => {}
        super::solver::RealExpr::Var(name) => {
            set.insert(name.clone());
        }
        super::solver::RealExpr::Add(lhs, rhs) | super::solver::RealExpr::Sub(lhs, rhs) => {
            collect_real_vars(lhs, set);
            collect_real_vars(rhs, set);
        }
    }
}

fn collect_idx_vars(idx: &Idx, set: &mut BTreeSet<String>) {
    match idx {
        Idx::Const(_) => {}
        Idx::Var(name) => {
            set.insert(name.clone());
        }
        Idx::Add(lhs, rhs) | Idx::Sub(lhs, rhs) | Idx::Mul(lhs, rhs) => {
            collect_idx_vars(lhs, set);
            collect_idx_vars(rhs, set);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::cap::RegionModel;
    use crate::logic::region::{Interval, Region};

    fn const_interval(lo: i64, hi: i64) -> RegionSetExpr {
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi))
    }

    #[test]
    fn subset_simple_interval() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let left = const_interval(0, 8);
        let right = const_interval(0, 16);
        assert!(check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn subset_detects_counterexample() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let left = const_interval(0, 8);
        let right = const_interval(2, 6);
        assert!(!check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn subset_respects_phi() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();
        phi.push(Atom::Le(Idx::Var("a".into()), Idx::Var("b".into())));
        let left = RegionSetExpr::interval(Idx::Var("a".into()), Idx::Var("b".into()));
        let right = RegionSetExpr::interval(Idx::Var("a".into()), Idx::Var("b".into()));
        assert!(check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn difference_support() {
        let solver = SmtSolver::new();
        // solver.set_query_logging(true);
        let phi = Phi::new();
        let left = RegionSetExpr::difference(
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
            RegionSetExpr::interval(Idx::Const(2), Idx::Const(5)),
        );
        let right = RegionSetExpr::union([
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(2)),
            RegionSetExpr::interval(Idx::Const(5), Idx::Const(10)),
        ]);
        assert!(check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn equivalence_helper_round_trip() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let region = Region::from_intervals(vec![
            Interval::bounded(Idx::Const(0), Idx::Const(4)),
            Interval::bounded(Idx::Const(6), Idx::Const(9)),
        ]);
        let expr = RegionSetExpr::from_region(&region);
        let manual = RegionSetExpr::union([
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(4)),
            RegionSetExpr::interval(Idx::Const(6), Idx::Const(9)),
        ]);
        assert!(check_equivalent(&phi, &expr, &manual, &solver));
    }

    #[test]
    fn overlap_detection() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let left = const_interval(0, 8);
        let right = const_interval(5, 12);
        assert!(overlaps(&phi, &left, &right, &solver));

        let disjoint_left = const_interval(0, 3);
        let disjoint_right = const_interval(5, 7);
        assert!(!overlaps(&phi, &disjoint_left, &disjoint_right, &solver));
    }

    #[test]
    fn display_handles_primitives() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        assert_eq!(RegionSetExpr::Empty.display_with(&phi, &solver), "∅");

        let interval = RegionSetExpr::interval(Idx::Const(0), Idx::Const(4));
        assert_eq!(interval.display_with(&phi, &solver), "[0..4)");
    }

    #[test]
    fn display_formats_composite() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        let first = RegionSetExpr::interval(Idx::Const(0), Idx::Const(2));
        let second = RegionSetExpr::interval(Idx::Const(4), Idx::Const(6));
        let union = RegionSetExpr::union([first.clone(), second.clone()]);
        assert_eq!(union.display_with(&phi, &solver), "[0..2) ∪ [4..6)");

        let diff = RegionSetExpr::difference(
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(8)),
            RegionSetExpr::interval(Idx::Const(2), Idx::Const(3)),
        );
        let expr = RegionSetExpr::intersection(diff, second);
        assert_eq!(expr.display_with(&phi, &solver), "[4..6)");
    }

    #[test]
    fn display_drops_empty_unions() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let expr = RegionSetExpr::union([
            RegionSetExpr::Empty,
            RegionSetExpr::Empty,
            RegionSetExpr::interval(Idx::Const(10), Idx::Const(11)),
        ]);

        assert_eq!(expr.display_with(&phi, &solver), "[10..11)");
    }
}
