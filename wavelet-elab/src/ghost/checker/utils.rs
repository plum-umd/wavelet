//! Some shared helpers

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::{GhostStmt, GhostVar};
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::Idx;

use super::permission::{PermExpr, Permission};

pub fn join_parts<V>(stmt: &GhostStmt<V>) -> Result<(&GhostVar, &GhostVar, &[GhostVar]), String> {
    match stmt {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => Ok((left, right, inputs)),
        _ => Err("expected join/split statement".to_string()),
    }
}

pub fn access_region(index: &str) -> RegionSetExpr {
    RegionSetExpr::interval(
        Idx::Var(index.to_string()),
        Idx::Add(
            Box::new(Idx::Var(index.to_string())),
            Box::new(Idx::Const(1)),
        ),
    )
}

pub fn access_permission(frac: FractionExpr, array: &str, index: &str) -> Permission {
    Permission::new(frac, array.into(), access_region(index))
}

pub fn access_perm_expr(frac: FractionExpr, array: &str, index: &str) -> PermExpr {
    PermExpr::singleton(access_permission(frac, array, index))
}
