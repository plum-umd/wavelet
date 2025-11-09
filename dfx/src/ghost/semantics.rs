//! Semantic specifications and validation helpers for ghost-level operators.

use crate::ghost::pcm::{Coeff, Permission, PermChunk, RegionCtx};
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::region_set::check_equivalent;

/// Errors that arise when validating ghost-permission semantics of IR operators.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticsError {
    /// Requested split requires more permission than available.
    InsufficientPermission,
    /// Pure operation expected empty permission.
    PureOperationRequiresEmpty,
    /// Constant expected empty permission.
    ConstOperationRequiresEmpty,
    /// Load permission must be a single chunk with `0 < coeff ≤ 1`.
    InvalidLoadPermission,
    /// Store permission must be a single chunk with coefficient exactly `1`.
    InvalidStorePermission,
    /// Function call expected combined permission to equal full spatial permission.
    CallPermissionMismatch,
}

/// Sum a slice of permissions using the PCM operation.
pub fn sum_permissions(perms: &[Permission], ctx: RegionCtx<'_>) -> Permission {
    perms
        .iter()
        .fold(Permission::empty(), |acc, perm| acc.join(perm, ctx))
}

/// Perform a join-and-split operation given an explicit left fragment to extract.
pub fn spec_join_split(
    inputs: &[Permission],
    left: &Permission,
    ctx: RegionCtx<'_>,
) -> Result<(Permission, Permission), SemanticsError> {
    let total = sum_permissions(inputs, ctx);
    if !left.leq(&total, ctx) {
        return Err(SemanticsError::InsufficientPermission);
    }
    let right = total
        .diff(left, ctx)
        .ok_or(SemanticsError::InsufficientPermission)?;
    Ok((left.clone(), right))
}

/// Validate the semantics of pure operations that should only operate on empty permission.
pub fn spec_pure_op(input: &Permission) -> Result<Permission, SemanticsError> {
    if input.is_empty() {
        Ok(input.clone())
    } else {
        Err(SemanticsError::PureOperationRequiresEmpty)
    }
}

/// Validate the semantics of constant operations that should only operate on empty permission.
pub fn spec_const(input: &Permission) -> Result<Permission, SemanticsError> {
    if input.is_empty() {
        Ok(input.clone())
    } else {
        Err(SemanticsError::ConstOperationRequiresEmpty)
    }
}

fn ensure_single_chunk(permission: &Permission) -> Option<&PermChunk> {
    let chunks = permission.chunks();
    if chunks.len() == 1 {
        Some(&chunks[0])
    } else {
        None
    }
}

/// Validate load semantics: permission must carry some fraction <= 1 for the expected region.
pub fn spec_load(
    input: &Permission,
    expected: &RegionSetExpr,
    ctx: RegionCtx<'_>,
) -> Result<Permission, SemanticsError> {
    let chunk = ensure_single_chunk(input).ok_or(SemanticsError::InvalidLoadPermission)?;
    if !chunk.coeff.gt_zero(ctx) {
        return Err(SemanticsError::InvalidLoadPermission);
    }
    if !chunk.coeff.leq(&Coeff::one(), ctx) {
        return Err(SemanticsError::InvalidLoadPermission);
    }
    if !check_equivalent(ctx.phi, &chunk.region, expected, ctx.solver) {
        return Err(SemanticsError::InvalidLoadPermission);
    }
    Ok(input.clone())
}

/// Validate store semantics: permission must be unique (coefficient exactly 1).
pub fn spec_store(
    input: &Permission,
    expected: &RegionSetExpr,
    ctx: RegionCtx<'_>,
) -> Result<Permission, SemanticsError> {
    let chunk = ensure_single_chunk(input).ok_or(SemanticsError::InvalidStorePermission)?;
    if chunk.coeff.eq(&Coeff::one(), ctx) {
        if check_equivalent(ctx.phi, &chunk.region, expected, ctx.solver) {
            Ok(input.clone())
        } else {
            Err(SemanticsError::InvalidStorePermission)
        }
    } else {
        Err(SemanticsError::InvalidStorePermission)
    }
}

/// Validate function call semantics, ensuring needed plus leftover equals full permission.
pub fn spec_call(
    needed: &Permission,
    leftover: &Permission,
    full: &Permission,
    ctx: RegionCtx<'_>,
) -> Result<Permission, SemanticsError> {
    let combined = needed.join(leftover, ctx);
    if !combined.leq(full, ctx) || !full.leq(&combined, ctx) {
        return Err(SemanticsError::CallPermissionMismatch);
    }
    Ok(combined)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ghost::pcm::{rational, Permission, PermChunk, RegionCtx};
    use crate::logic::semantic::region_set::RegionSetExpr;
    use crate::logic::semantic::solver::{Idx, Phi, SmtSolver};

    fn region(lo: i64, hi: i64) -> RegionSetExpr {
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi))
    }

    fn perm(num: i64, den: i64, lo: i64, hi: i64) -> Permission {
        Permission::singleton(PermChunk::new(rational(num, den), region(lo, hi)))
    }

    fn ctx<'a>(phi: &'a Phi, solver: &'a SmtSolver) -> RegionCtx<'a> {
        RegionCtx { phi, solver }
    }

    #[test]
    fn join_split_respects_diff() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let total = vec![perm(1, 2, 0, 8), perm(1, 2, 0, 8)];
        let desired = perm(1, 2, 0, 8);
        let (left, right) = spec_join_split(&total, &desired, ctx).expect("split should succeed");
        assert_eq!(left.chunks()[0].coeff, rational(1, 2));
        assert_eq!(right.chunks()[0].coeff, rational(1, 2));
    }

    #[test]
    fn join_split_rejects_overdraw() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let total = vec![perm(1, 2, 0, 8)];
        let desired = perm(3, 4, 0, 8);
        assert_eq!(
            spec_join_split(&total, &desired, ctx),
            Err(SemanticsError::InsufficientPermission)
        );
    }

    #[test]
    fn pure_requires_empty() {
        let empty = Permission::empty();
        assert!(spec_pure_op(&empty).is_ok());
        let non_empty = perm(1, 2, 0, 4);
        assert_eq!(spec_pure_op(&non_empty), Err(SemanticsError::PureOperationRequiresEmpty));
    }

    #[test]
    fn const_requires_empty() {
        let empty = Permission::empty();
        assert!(spec_const(&empty).is_ok());
        let non_empty = perm(1, 2, 0, 4);
        assert_eq!(spec_const(&non_empty), Err(SemanticsError::ConstOperationRequiresEmpty));
    }

    #[test]
    fn load_checks_fraction_bounds() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let target = region(0, 4);
        let ok = perm(1, 2, 0, 4);
        assert!(spec_load(&ok, &target, ctx).is_ok());
        let zero = perm(0, 1, 0, 4);
        assert_eq!(spec_load(&zero, &target, ctx), Err(SemanticsError::InvalidLoadPermission));
        let over = perm(3, 2, 0, 4);
        assert_eq!(spec_load(&over, &target, ctx), Err(SemanticsError::InvalidLoadPermission));
        let wrong_region = perm(1, 2, 2, 6);
        assert_eq!(spec_load(&wrong_region, &target, ctx), Err(SemanticsError::InvalidLoadPermission));
    }

    #[test]
    fn store_requires_unique() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let target = region(0, 4);
        let uniq = perm(1, 1, 0, 4);
        assert!(spec_store(&uniq, &target, ctx).is_ok());
        let partial = perm(1, 2, 0, 4);
        assert_eq!(spec_store(&partial, &target, ctx), Err(SemanticsError::InvalidStorePermission));
        let wrong_region = perm(1, 1, 1, 5);
        assert_eq!(spec_store(&wrong_region, &target, ctx), Err(SemanticsError::InvalidStorePermission));
    }

    #[test]
    fn call_requires_full_permission() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = ctx(&phi, &solver);
        let needed = perm(1, 2, 0, 4);
        let leftover = perm(1, 2, 0, 4);
        let full = perm(1, 1, 0, 4);
        assert!(spec_call(&needed, &leftover, &full, ctx).is_ok());
        let mismatch_full = perm(3, 4, 0, 4);
        assert_eq!(
            spec_call(&needed, &leftover, &mismatch_full, ctx),
            Err(SemanticsError::CallPermissionMismatch)
        );
    }
}
