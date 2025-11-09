use std::collections::BTreeMap;

use crate::ghost::pcm::{Permission, RegionCtx};

/// Permission environment indexed by array identifiers.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PermissionEnv {
    pub map: BTreeMap<String, Permission>,
}

impl PermissionEnv {
    /// Create an empty permission environment.
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    /// Insert or replace a permission associated with an array.
    pub fn insert(&mut self, array: String, perm: Permission, ctx: RegionCtx<'_>) {
        let perm = perm.normalised(ctx);
        if perm.is_empty() {
            self.map.remove(&array);
        } else {
            self.map.insert(array, perm);
        }
    }

    /// Fetch permission associated with an array.
    pub fn get(&self, array: &str) -> Option<&Permission> {
        self.map.get(array)
    }

    /// Returns the permission associated with `array`, or an empty permission if absent.
    pub fn get_or_empty(&self, array: &str) -> Permission {
        self.map.get(array).cloned().unwrap_or_else(Permission::empty)
    }

    /// Add (join) a permission into the environment entry for `array`.
    pub fn add_permission(&mut self, array: &str, perm: Permission, ctx: RegionCtx<'_>) {
        if perm.is_empty() {
            return;
        }
        let perm = perm.normalised(ctx);
        let entry = self.map.entry(array.to_owned()).or_insert_with(Permission::empty);
        *entry = entry.join(&perm, ctx);
        if entry.is_empty() {
            self.map.remove(array);
        }
    }

    /// Point-wise join of two permission environments.
    pub fn join(&self, other: &PermissionEnv, ctx: RegionCtx<'_>) -> PermissionEnv {
        let mut result = self.clone();
        for (array, perm) in &other.map {
            result.add_permission(array, perm.clone(), ctx);
        }
        result
    }

    /// Check whether `self <= other` in the point-wise PCM ordering.
    pub fn leq(&self, other: &PermissionEnv, ctx: RegionCtx<'_>) -> bool {
        for (array, perm) in &self.map {
            let rhs = other.map.get(array).cloned().unwrap_or_else(Permission::empty);
            if !perm.leq(&rhs, ctx) {
                return false;
            }
        }
        true
    }

    /// Compute the point-wise difference `self - other`, if defined.
    pub fn diff(&self, other: &PermissionEnv, ctx: RegionCtx<'_>) -> Option<PermissionEnv> {
        if !other.leq(self, ctx) {
            return None;
        }
        let mut result = PermissionEnv::new();
        for (array, perm) in &self.map {
            let sub = other.map.get(array).cloned().unwrap_or_else(Permission::empty);
            if let Some(diff) = perm.diff(&sub, ctx) {
                result.insert(array.clone(), diff, ctx);
            } else {
                return None;
            }
        }
        for (array, perm) in &other.map {
            if !self.map.contains_key(array) && !perm.is_empty() {
                return None;
            }
        }
        Some(result)
    }

    /// Determine whether environment contains no meaningful permissions.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ghost::pcm::{rational, PermChunk, RegionCtx};
    use crate::logic::semantic::region_set::RegionSetExpr;
    use crate::logic::semantic::solver::{Atom, Idx, Phi, SmtSolver};

    fn interval(lo: i64, hi: i64) -> RegionSetExpr {
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi))
    }

    fn perm(coeff_num: i64, coeff_den: i64, lo: i64, hi: i64) -> Permission {
        Permission::singleton(PermChunk::new(rational(coeff_num, coeff_den), interval(lo, hi)))
    }

    fn ctx<'a>(phi: &'a Phi, solver: &'a SmtSolver) -> RegionCtx<'a> {
        RegionCtx { phi, solver }
    }

    #[test]
    fn join_combines_entries() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut left = PermissionEnv::new();
        left.insert("A".into(), perm(1, 2, 0, 4), ctx);
        let mut right = PermissionEnv::new();
        right.insert("A".into(), perm(1, 2, 0, 4), ctx);
        right.insert("B".into(), perm(1, 4, 1, 3), ctx);

        let joined = left.join(&right, ctx);
        assert_eq!(joined.get("A").unwrap().chunks()[0].coeff, rational(1, 1));
        assert!(joined.get("B").is_some());
    }

    #[test]
    fn diff_requires_subset() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut base = PermissionEnv::new();
        base.insert("A".into(), perm(3, 4, 0, 4), ctx);
        let mut sub = PermissionEnv::new();
        sub.insert("A".into(), perm(1, 2, 0, 4), ctx);
        let diff = base.diff(&sub, ctx).expect("diff should succeed");
        assert_eq!(diff.get("A").unwrap().chunks()[0].coeff, rational(1, 4));
    }

    #[test]
    fn diff_fails_without_capability() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut base = PermissionEnv::new();
        base.insert("A".into(), perm(1, 4, 0, 2), ctx);
        let mut sub = PermissionEnv::new();
        sub.insert("A".into(), perm(1, 2, 0, 2), ctx);
        assert!(base.diff(&sub, ctx).is_none());
    }

    #[test]
    fn leq_checks_pointwise() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut strong = PermissionEnv::new();
        strong.insert("A".into(), perm(3, 4, 0, 4), ctx);
        let mut weak = PermissionEnv::new();
        weak.insert("A".into(), perm(1, 4, 0, 4), ctx);
        assert!(weak.leq(&strong, ctx));
        assert!(!strong.leq(&weak, ctx));
    }

    #[test]
    fn add_permission_accumulates() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut env = PermissionEnv::new();
        env.add_permission("A", perm(1, 4, 0, 4), ctx);
        env.add_permission("A", perm(1, 4, 0, 4), ctx);
        assert_eq!(env.get("A").unwrap().chunks()[0].coeff, rational(1, 2));
    }

    #[test]
    fn solver_normalises_equivalent_regions() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);

        let composite_region = RegionSetExpr::union(vec![interval(0, 2), interval(2, 4)]);
        let mut env = PermissionEnv::new();
        env.insert(
            "A".into(),
            Permission::singleton(PermChunk::new(rational(1, 4), composite_region.clone())),
            ctx,
        );
        env.add_permission(
            "A",
            Permission::singleton(PermChunk::new(rational(1, 4), interval(0, 4))),
            ctx,
        );

        let perm = env.get("A").unwrap();
        assert_eq!(perm.chunks().len(), 1);
        assert_eq!(perm.chunks()[0].coeff, rational(1, 2));
        assert_eq!(perm.chunks()[0].region, interval(0, 4));
    }

    #[test]
    fn symbolic_regions_compare_under_phi() {
        let mut phi = Phi::default();
        let solver = SmtSolver::new();
        let i = Idx::Var("i".to_string());
        let j = Idx::Var("j".to_string());
        phi.push(Atom::Eq(
            Idx::Add(Box::new(i.clone()), Box::new(Idx::Const(1))),
            j.clone(),
        ));
        let ctx = ctx(&phi, &solver);

        let region_i = RegionSetExpr::interval(i.clone(), j.clone());
        let region_i_plus = RegionSetExpr::interval(
            i.clone(),
            Idx::Add(Box::new(i.clone()), Box::new(Idx::Const(1))),
        );

        let mut env = PermissionEnv::new();
        env.insert(
            "A".into(),
            Permission::singleton(PermChunk::new(rational(1, 3), region_i)),
            ctx,
        );
        env.add_permission(
            "A",
            Permission::singleton(PermChunk::new(rational(1, 3), region_i_plus)),
            ctx,
        );

        let perm = env.get("A").unwrap();
        assert_eq!(perm.chunks().len(), 1);
        assert_eq!(perm.chunks()[0].coeff, rational(2, 3));
    }
}
