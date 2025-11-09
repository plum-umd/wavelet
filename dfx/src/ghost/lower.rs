use std::collections::BTreeMap;

use crate::ghost::ir::GhostProgram;
use crate::ghost::pcm::{Coeff, Permission, PermChunk, RegionCtx, rational};
use crate::ghost::permission::PermissionEnv;
use crate::ir::{ArrayLen, FnDef, Program, Signedness, Ty};
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, Phi, SmtSolver};
use crate::logic::CapabilityLogic;

/// Initial permission state for a lowered function.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Debug)]
struct InitialPermissions {
    phi: Phi,
    sync: PermissionEnv,
    leftover: PermissionEnv,
}

/// Synthesize a ghost-level program from the typed IR. Currently a stub while
/// the lowering pipeline is being implemented.
pub fn synthesize_ghost_program<L: CapabilityLogic>(prog: &Program, logic: &L) -> GhostProgram
where
    L::Region: crate::logic::cap::RegionModel<Solver = SmtSolver>,
{
    for def in &prog.defs {
        let _ = compute_initial_permissions(def, logic);
    }
    GhostProgram::new()
}

fn compute_initial_permissions<L: CapabilityLogic>(def: &FnDef, logic: &L) -> InitialPermissions
where
    L::Region: crate::logic::cap::RegionModel<Solver = SmtSolver>,
{
    let mut phi = Phi::default();
    let mut gamma: BTreeMap<String, Ty> = BTreeMap::new();
    for (var, ty) in &def.params {
        gamma.insert(var.0.clone(), ty.clone());
        if let Ty::Int(Signedness::Unsigned) = ty {
            phi.push(Atom::Le(Idx::Const(0), Idx::Var(var.0.clone())));
        }
    }

    let solver = logic.solver();
    let ctx = RegionCtx { phi: &phi, solver };
    let mut sync = PermissionEnv::new();
    let mut leftover = PermissionEnv::new();

    for cap in &def.caps {
        if let Some(entry_ty) = gamma.get(&cap.array) {
            if let Some((full_region, array_name)) = full_region_for_array(&cap.array, entry_ty) {
                if let Some(region) = &cap.uniq {
                    let region_expr = RegionSetExpr::from_region(region);
                    let uniq_perm = permission_from_region(rational(1, 1), region_expr.clone(), ctx);
                    sync.add_permission(&array_name, uniq_perm, ctx);

                    let complement = complement_region(&full_region, &region_expr, ctx);
                    let uniq_left = permission_from_region(rational(1, 1), complement, ctx);
                    leftover.add_permission(&array_name, uniq_left, ctx);
                }
                if let Some(region) = &cap.shrd {
                    let region_expr = RegionSetExpr::from_region(region);
                    let shrd_perm = permission_from_region(rational(1, 1), region_expr.clone(), ctx);
                    sync.add_permission(&array_name, shrd_perm, ctx);

                    let complement = complement_region(&full_region, &region_expr, ctx);
                    let shrd_left = permission_from_region(rational(1, 1), complement, ctx);
                    leftover.add_permission(&array_name, shrd_left, ctx);
                }
            }
        }
    }

    InitialPermissions { phi, sync, leftover }
}

fn permission_from_region(coeff: Coeff, region: RegionSetExpr, ctx: RegionCtx<'_>) -> Permission {
    let chunk = PermChunk::new(coeff, region);
    Permission::singleton(chunk).normalised(ctx)
}

fn complement_region(full: &RegionSetExpr, target: &RegionSetExpr, ctx: RegionCtx<'_>) -> RegionSetExpr {
    RegionSetExpr::difference(full.clone(), target.clone()).simplify(ctx.phi, ctx.solver)
}

fn full_region_for_array(array: &str, ty: &Ty) -> Option<(RegionSetExpr, String)> {
    match ty {
        Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => {
            let hi = idx_from_array_len(len);
            let full = RegionSetExpr::interval(Idx::Const(0), hi);
            Some((full, array.to_string()))
        }
        _ => None,
    }
}

fn idx_from_array_len(len: &ArrayLen) -> Idx {
    match len {
        ArrayLen::Const(n) => Idx::Const(*n as i64),
        ArrayLen::Symbol(name) => Idx::Var(name.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ghost::pcm::RegionCtx;
    use crate::ir::{FnName, Var};
    use crate::logic::cap::CapPattern;
    use crate::logic::region::Region;
    use crate::logic::semantic::region_set::check_equivalent;
    use crate::logic::semantic::{RegionSetExpr, SemanticLogic};

    fn solver_ctx<'a>(phi: &'a Phi, logic: &'a SemanticLogic) -> RegionCtx<'a> {
        RegionCtx {
            phi,
            solver: logic.solver(),
        }
    }

    fn bin_ty() -> Ty {
        Ty::Int(Signedness::Unsigned)
    }

    fn array_ty(len: ArrayLen) -> Ty {
        Ty::RefShrd {
            elem: Box::new(Ty::Int(Signedness::Unsigned)),
            len,
        }
    }

    #[test]
    fn compute_initial_permissions_shared() {
        let logic = SemanticLogic::new();
        let region = Region::from_bounded(Idx::Var("i".into()), Idx::Var("N".into()));
        let def = FnDef {
            name: FnName("sum_aux".into()),
            params: vec![
                (Var("i".into()), bin_ty()),
                (Var("N".into()), bin_ty()),
                (Var("A".into()), array_ty(ArrayLen::Symbol("N".into()))),
            ],
            caps: vec![CapPattern {
                array: "A".into(),
                uniq: None,
                shrd: Some(region.clone()),
            }],
            returns: Ty::Int(Signedness::Unsigned),
            body: crate::ir::Expr::new(vec![], crate::ir::Tail::RetVar(Var("i".into()))),
        };

        let init = compute_initial_permissions(&def, &logic);
        let ctx = solver_ctx(&init.phi, &logic);

        let sync = init.sync.get("A").expect("sync permission for A");
        assert_eq!(sync.chunks().len(), 1);
        assert_eq!(sync.chunks()[0].coeff, rational(1, 1));
        let expected_region = RegionSetExpr::from_region(&region);
        assert!(check_equivalent(ctx.phi, &sync.chunks()[0].region, &expected_region, ctx.solver));

        let leftover = init.leftover.get("A").expect("leftover permission for A");
        let full_region = RegionSetExpr::interval(Idx::Const(0), Idx::Var("N".into()));
        let expected_left = RegionSetExpr::difference(full_region, expected_region).simplify(ctx.phi, ctx.solver);
        assert!(check_equivalent(ctx.phi, &leftover.chunks()[0].region, &expected_left, ctx.solver));
    }

    #[test]
    fn compute_initial_permissions_unique() {
        let logic = SemanticLogic::new();
        let region = Region::from_bounded(Idx::Var("start".into()), Idx::Var("N".into()));
        let def = FnDef {
            name: FnName("mk_all_zero_aux".into()),
            params: vec![
                (Var("start".into()), bin_ty()),
                (Var("N".into()), bin_ty()),
                (Var("A".into()), Ty::RefUniq {
                    elem: Box::new(Ty::Int(Signedness::Unsigned)),
                    len: ArrayLen::Symbol("N".into()),
                }),
            ],
            caps: vec![CapPattern {
                array: "A".into(),
                uniq: Some(region.clone()),
                shrd: None,
            }],
            returns: Ty::Unit,
            body: crate::ir::Expr::new(vec![], crate::ir::Tail::RetVar(Var("start".into()))),
        };

        let init = compute_initial_permissions(&def, &logic);
        let ctx = solver_ctx(&init.phi, &logic);

        let sync = init.sync.get("A").expect("sync permission for A");
        assert_eq!(sync.chunks().len(), 1);
        assert_eq!(sync.chunks()[0].coeff, rational(1, 1));
        let expected_region = RegionSetExpr::from_region(&region);
        assert!(check_equivalent(ctx.phi, &sync.chunks()[0].region, &expected_region, ctx.solver));

        let leftover = init.leftover.get("A").expect("leftover permission for A");
        let full_region = RegionSetExpr::interval(Idx::Const(0), Idx::Var("N".into()));
        let expected_left = RegionSetExpr::difference(full_region, expected_region).simplify(ctx.phi, ctx.solver);
        assert!(check_equivalent(ctx.phi, &leftover.chunks()[0].region, &expected_left, ctx.solver));
    }
}
