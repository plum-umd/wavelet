use std::collections::BTreeMap;

use crate::ghost::{
    ir::GhostVar,
    pcm::{FracPerm, RegionCtx, normalise_permissions},
};

/// Denotes `1.0@A{i..N}`, `shrd@B{0..M}` etc.
pub type ArrFracPerm = (String, FracPerm);

/// Permission environment indexed by permission vars.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PermissionEnv {
    pub map: BTreeMap<GhostVar, Vec<ArrFracPerm>>,
}

impl PermissionEnv {
    /// Create an empty permission environment.
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    /// Insert or replace a permission associated with an array.
    pub fn insert(
        &mut self,
        var: GhostVar,
        array_name: String,
        perm: FracPerm,
        ctx: RegionCtx<'_>,
    ) {
        let perms = normalise_permissions(vec![perm], ctx);
        let entry = self.map.entry(var).or_insert_with(Vec::new);

        // Remove existing permission for this array name
        entry.retain(|(name, _)| name != &array_name);

        // Add new permissions if not empty
        for p in perms {
            if !p.is_zero() {
                entry.push((array_name.clone(), p));
            }
        }

        // Clean up empty vectors
        self.map.retain(|_, v| !v.is_empty());
    }

    /// Fetch permission associated with a specific array name under a ghost variable.
    pub fn get(&self, var: &GhostVar, array_name: &str) -> Option<&FracPerm> {
        self.map
            .get(var)?
            .iter()
            .find(|(name, _)| name == array_name)
            .map(|(_, perm)| perm)
    }

    /// Returns the permission associated with `array_name` under `var`, or an empty permission if absent.
    pub fn get_or_empty(&self, var: &GhostVar, array_name: &str) -> FracPerm {
        self.get(var, array_name).cloned().unwrap_or_else(|| {
            FracPerm::zero(crate::logic::semantic::region_set::RegionSetExpr::empty())
        })
    }

    /// Add (join) a permission into the environment entry for `array_name` under `var`.
    pub fn add_permission(
        &mut self,
        var: &GhostVar,
        array_name: &str,
        perm: FracPerm,
        ctx: RegionCtx<'_>,
    ) {
        if perm.is_zero() {
            return;
        }

        let entry = self.map.entry(var.clone()).or_insert_with(Vec::new);

        // Find existing permission for this array name
        if let Some((_, existing_perm)) = entry.iter_mut().find(|(name, _)| name == array_name) {
            // Combine the two permissions and normalize
            let combined = normalise_permissions(vec![existing_perm.clone(), perm], ctx);
            if combined.is_empty() {
                // Remove this array from the vector
                entry.retain(|(name, _)| name != array_name);
            } else if combined.len() == 1 {
                *existing_perm = combined.into_iter().next().unwrap();
            } else {
                // Multiple permissions after normalization - just keep the first one
                *existing_perm = combined.into_iter().next().unwrap();
            }
        } else {
            // No existing permission for this array name, add it
            entry.push((array_name.to_string(), perm));
        }

        // Clean up empty vectors
        self.map.retain(|_, v| !v.is_empty());
    }

    /// Point-wise join of two permission environments.
    pub fn join(&self, other: &PermissionEnv, ctx: RegionCtx<'_>) -> PermissionEnv {
        let mut result = self.clone();
        for (var, arr_perms) in &other.map {
            for (array_name, perm) in arr_perms {
                result.add_permission(var, array_name, perm.clone(), ctx);
            }
        }
        result
    }

    /// Check whether `self <= other` in the point-wise PCM ordering.
    pub fn leq(&self, other: &PermissionEnv, ctx: RegionCtx<'_>) -> bool {
        for (var, arr_perms) in &self.map {
            for (array_name, perm) in arr_perms {
                let rhs = other.get(var, array_name).cloned().unwrap_or_else(|| {
                    FracPerm::zero(crate::logic::semantic::region_set::RegionSetExpr::empty())
                });
                // Check if perm <= rhs by trying to compute rhs - perm
                if crate::ghost::pcm::subtract_permissions(&[rhs.clone()], &[perm.clone()], ctx)
                    .is_none()
                {
                    return false;
                }
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
        for (var, arr_perms) in &self.map {
            for (array_name, perm) in arr_perms {
                let sub = other.get(var, array_name).cloned().unwrap_or_else(|| {
                    FracPerm::zero(crate::logic::semantic::region_set::RegionSetExpr::empty())
                });
                let diff = crate::ghost::pcm::subtract_permissions(&[perm.clone()], &[sub], ctx)?;
                if !diff.is_empty() {
                    if diff.len() == 1 {
                        result.insert(
                            var.clone(),
                            array_name.clone(),
                            diff.into_iter().next().unwrap(),
                            ctx,
                        );
                    } else {
                        // Multiple permissions after subtraction - shouldn't happen for simple subtractions
                        return None;
                    }
                }
            }
        }
        for (var, arr_perms) in &other.map {
            for (array_name, perm) in arr_perms {
                if self.get(var, array_name).is_none() && !perm.is_zero() {
                    return None;
                }
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
    use crate::ghost::ir::GhostVar;
    use crate::ghost::pcm::{Coeff, Frac, NNRat, Numerator, RegionCtx};
    use crate::logic::semantic::region_set::RegionSetExpr;
    use crate::logic::semantic::solver::{Atom, Idx, Phi, SmtSolver};

    fn interval(lo: i64, hi: i64) -> RegionSetExpr {
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi))
    }

    fn rational(num: usize, den: usize) -> Coeff {
        NNRat::Atomic(Frac {
            numer: Numerator::Const(num),
            denom: den,
        })
    }

    fn perm(coeff_num: usize, coeff_den: usize, lo: i64, hi: i64) -> FracPerm {
        FracPerm::new(rational(coeff_num, coeff_den), interval(lo, hi))
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
        left.insert(GhostVar("v1".into()), "A".into(), perm(1, 2, 0, 4), ctx);
        let mut right = PermissionEnv::new();
        right.insert(GhostVar("v1".into()), "A".into(), perm(1, 2, 0, 4), ctx);
        right.insert(GhostVar("v1".into()), "B".into(), perm(1, 4, 1, 3), ctx);

        let joined = left.join(&right, ctx);
        assert_eq!(
            joined.get(&GhostVar("v1".into()), "A").unwrap().coeff,
            rational(1, 1)
        );
        assert!(joined.get(&GhostVar("v1".into()), "B").is_some());
    }

    #[test]
    fn diff_requires_subset() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut base = PermissionEnv::new();
        base.insert(GhostVar("v1".into()), "A".into(), perm(3, 4, 0, 4), ctx);
        let mut sub = PermissionEnv::new();
        sub.insert(GhostVar("v1".into()), "A".into(), perm(1, 2, 0, 4), ctx);
        let diff = base.diff(&sub, ctx).expect("diff should succeed");
        assert_eq!(
            diff.get(&GhostVar("v1".into()), "A").unwrap().coeff,
            rational(1, 4)
        );
    }

    #[test]
    fn diff_fails_without_capability() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut base = PermissionEnv::new();
        base.insert(GhostVar("v1".into()), "A".into(), perm(1, 4, 0, 2), ctx);
        let mut sub = PermissionEnv::new();
        sub.insert(GhostVar("v1".into()), "A".into(), perm(1, 2, 0, 2), ctx);
        assert!(base.diff(&sub, ctx).is_none());
    }

    #[test]
    fn leq_checks_pointwise() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut strong = PermissionEnv::new();
        strong.insert(GhostVar("v1".into()), "A".into(), perm(3, 4, 0, 4), ctx);
        let mut weak = PermissionEnv::new();
        weak.insert(GhostVar("v1".into()), "A".into(), perm(1, 4, 0, 4), ctx);
        assert!(weak.leq(&strong, ctx));
        assert!(!strong.leq(&weak, ctx));
    }

    #[test]
    fn add_permission_accumulates() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let mut env = PermissionEnv::new();
        env.add_permission(&GhostVar("v1".into()), "A", perm(1, 4, 0, 4), ctx);
        env.add_permission(&GhostVar("v1".into()), "A", perm(1, 4, 0, 4), ctx);
        assert_eq!(
            env.get(&GhostVar("v1".into()), "A").unwrap().coeff,
            rational(1, 2)
        );
    }

    #[test]
    fn solver_normalises_equivalent_regions() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);

        let composite_region = RegionSetExpr::union(vec![interval(0, 2), interval(2, 4)]);
        let mut env = PermissionEnv::new();
        env.insert(
            GhostVar("v1".into()),
            "A".into(),
            FracPerm::new(rational(1, 4), composite_region.clone()),
            ctx,
        );
        env.add_permission(
            &GhostVar("v1".into()),
            "A",
            FracPerm::new(rational(1, 4), interval(0, 4)),
            ctx,
        );

        let perm = env.get(&GhostVar("v1".into()), "A").unwrap();
        assert_eq!(perm.coeff, rational(1, 2));
        assert_eq!(perm.region, interval(0, 4));
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
            GhostVar("v1".into()),
            "A".into(),
            FracPerm::new(rational(1, 3), region_i),
            ctx,
        );
        env.add_permission(
            &GhostVar("v1".into()),
            "A",
            FracPerm::new(rational(1, 3), region_i_plus),
            ctx,
        );

        let perm = env.get(&GhostVar("v1".into()), "A").unwrap();
        assert_eq!(perm.coeff, rational(2, 3));
    }
}
