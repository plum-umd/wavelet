//! Statement checking functions for ghost programs.

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::GhostStmt;
use crate::ir::Op;
use crate::logic::semantic::region_set::{check_subset, RegionSetExpr};
use crate::logic::semantic::solver::{Atom, Idx, PhiSolver, RealExpr};
use crate::Val;

use super::context::CheckContext;
use super::permission::{consume_permission, permissions_to_expr, Permission, PermExpr};
use super::pretty_print::{render_permission, render_perm_expr, render_region};

/// Check a standalone Pure statement.
pub fn check_ghost_stmt_pure(stmt: &GhostStmt, ctx: &mut CheckContext) -> Result<(), String> {
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
        Op::And if inputs.len() == 2 => {
            let lhs = Atom::BoolVar(inputs[0].0.clone());
            let rhs = Atom::BoolVar(inputs[1].0.clone());
            let out = Atom::BoolVar(output.0.clone());

            // out => lhs and out => rhs
            ctx.add_constraint(Atom::Implies(
                Box::new(out.clone()),
                Box::new(lhs.clone()),
            ));
            ctx.add_constraint(Atom::Implies(
                Box::new(out.clone()),
                Box::new(rhs.clone()),
            ));

            // lhs ∧ rhs => out
            let lhs_and_rhs = Atom::And(Box::new(lhs.clone()), Box::new(rhs.clone()));
            ctx.add_constraint(Atom::Implies(
                Box::new(lhs_and_rhs),
                Box::new(out.clone()),
            ));

            // ¬out => ¬lhs ∨ ¬rhs
            let not_out = Atom::Not(Box::new(out.clone()));
            let not_lhs = Atom::Not(Box::new(lhs));
            let not_rhs = Atom::Not(Box::new(rhs));
            let not_lhs_or_not_rhs = Atom::Or(Box::new(not_lhs), Box::new(not_rhs));
            ctx.add_constraint(Atom::Implies(Box::new(not_out), Box::new(not_lhs_or_not_rhs)));
        }
        Op::Or if inputs.len() == 2 => {
            let lhs = Atom::BoolVar(inputs[0].0.clone());
            let rhs = Atom::BoolVar(inputs[1].0.clone());
            let out = Atom::BoolVar(output.0.clone());

            // lhs => out and rhs => out
            ctx.add_constraint(Atom::Implies(
                Box::new(lhs.clone()),
                Box::new(out.clone()),
            ));
            ctx.add_constraint(Atom::Implies(
                Box::new(rhs.clone()),
                Box::new(out.clone()),
            ));

            // out => lhs ∨ rhs
            let lhs_or_rhs = Atom::Or(Box::new(lhs.clone()), Box::new(rhs.clone()));
            ctx.add_constraint(Atom::Implies(
                Box::new(out.clone()),
                Box::new(lhs_or_rhs),
            ));

            // ¬lhs ∧ ¬rhs => ¬out
            let not_lhs = Atom::Not(Box::new(lhs));
            let not_rhs = Atom::Not(Box::new(rhs));
            let not_lhs_and_not_rhs = Atom::And(Box::new(not_lhs), Box::new(not_rhs));
            ctx.add_constraint(Atom::Implies(
                Box::new(not_lhs_and_not_rhs),
                Box::new(Atom::Not(Box::new(out))),
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

            match op {
                Op::Add => {
                    // Also relate operands back to the result to aid solver reasoning.
                    let out_var = Idx::Var(output.0.clone());
                    let lhs_var = Idx::Var(inputs[0].0.clone());
                    let rhs_var = Idx::Var(inputs[1].0.clone());
                    ctx.add_constraint(Atom::Eq(
                        lhs_var.clone(),
                        Idx::Sub(Box::new(out_var.clone()), Box::new(rhs_var.clone())),
                    ));
                    ctx.add_constraint(Atom::Eq(
                        rhs_var,
                        Idx::Sub(Box::new(out_var), Box::new(lhs_var)),
                    ));
                }
                Op::Sub => {
                    // output = lhs - rhs  =>  lhs = output + rhs, rhs = lhs - output
                    let out_var = Idx::Var(output.0.clone());
                    let lhs_var = Idx::Var(inputs[0].0.clone());
                    let rhs_var = Idx::Var(inputs[1].0.clone());
                    ctx.add_constraint(Atom::Eq(
                        lhs_var.clone(),
                        Idx::Add(Box::new(out_var.clone()), Box::new(rhs_var.clone())),
                    ));
                    ctx.add_constraint(Atom::Eq(
                        rhs_var,
                        Idx::Sub(Box::new(lhs_var), Box::new(out_var)),
                    ));
                }
                _ => {}
            }
        }
        _ => {
            // Other operations don't add semantic constraints yet
        }
    }
    Ok(())
}

/// Check JoinSplit followed by Const.
pub fn check_ghost_stmt_joinsplit_const(
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

    if ctx.verbose {
        println!("  Joining permissions: [{}]", inputs.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
    }

    let joined_perm = ctx.join_perms(inputs)?;

    if ctx.verbose {
        println!("  Joined: {}", render_perm_expr(&joined_perm));
    }

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
    use crate::ir::{Signedness, Ty};
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
pub fn check_ghost_stmt_joinsplit_load(
    join_stmt: &GhostStmt,
    load_stmt: &GhostStmt,
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

    if ctx.verbose {
        println!("  Joining permissions: [{}]", inputs.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
    }

    let joined_perm = ctx.join_perms(inputs)?;

    if ctx.verbose {
        println!("  Joined: {}", render_perm_expr(&joined_perm));
    }

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

    if ctx.verbose {
        println!("  Load from {}[{}], accessing region {}", array.0, index.0, render_region(&access_region));
    }

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

    if ctx.verbose {
        println!("  Found covering permission: {}", render_permission(&source_perm));
    }

    let g_fraction = source_perm.fraction.clone();
    let f_fraction = ctx.fresh_fraction_var("__frac_");
    ctx.add_fraction_validity_constraint(&f_fraction);
    let f_real = f_fraction.to_real_expr();
    let g_real = g_fraction.to_real_expr();
    // Add constraint: 0 < f < g
    // to make sure subsequent load/call won't stuck
    ctx.add_constraint(Atom::RealLt(f_real.clone(), g_real.clone()));

    if ctx.verbose {
        use super::pretty_print::render_fraction;
        println!("  Splitting permission: {} < {}", render_fraction(&f_fraction), render_fraction(&g_fraction));
    }

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
pub fn check_ghost_stmt_joinsplit_store(
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

    if ctx.verbose {
        println!("  Joining permissions: [{}]", inputs.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
    }

    let joined_perm = ctx.join_perms(inputs)?;

    if ctx.verbose {
        println!("  Joined: {}", render_perm_expr(&joined_perm));
    }

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
    let store_region = RegionSetExpr::interval(lo, hi);
    
    if ctx.verbose {
        println!("  Store to {}[{}], region {}", array.0, index.0, render_region(&store_region));
        println!("  Requires full permission (1.0) on this region");
    }

    // full permission on array at `index`
    let store_perm = PermExpr::Singleton(Permission {
        fraction: FractionExpr::from_int(1),
        array: array.clone(),
        region: store_region,
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
pub fn check_ghost_stmt_jnsplt_jnsplt_call(
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
    
    if ctx.verbose {
        println!("  First JoinSplit: joining [{}]", inputs1.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
    }
    
    let joined_perm1 = ctx.join_perms(inputs1)?;

    if ctx.verbose {
        println!("    Joined (p_sync): {}", render_perm_expr(&joined_perm1));
    }

    let (left2, right2, inputs2) = match join_stmt2 {
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => (left, right, inputs),
        _ => unreachable!(),
    };
    
    if ctx.verbose {
        println!("  Second JoinSplit: joining [{}]", inputs2.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
    }
    
    let joined_perm2 = ctx.join_perms(inputs2)?;

    if ctx.verbose {
        println!("    Joined (p_garb): {}", render_perm_expr(&joined_perm2));
    }

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

    if ctx.verbose {
        println!("  Calling function: {}({})", func.0, args.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
    }

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

    use super::permission::substitute_perm_expr_with_maps;
    let required_sync = substitute_perm_expr_with_maps(&sig.initial_perms.0, &idx_substitutions);
    let required_garb = substitute_perm_expr_with_maps(&sig.initial_perms.1, &idx_substitutions);

    if ctx.verbose {
        println!("  Required p_sync: {}", render_perm_expr(&required_sync));
        println!("  Required p_garb: {}", render_perm_expr(&required_garb));
    }

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

    if ctx.verbose {
        println!("  Consuming p_sync permissions...");
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

    if ctx.verbose {
        println!("    Remainder p_sync: {}", render_perm_expr(&remainder_sync_expr));
        println!("  Consuming p_garb permissions...");
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

    if ctx.verbose {
        println!("    Remainder p_garb: {}", render_perm_expr(&remainder_garb_expr));
    }

    ctx.bind_perm(right2, remainder_garb_expr);

    // bind ghost_ret with the sum of the callee's needed sync and garb permissions
    let ret_perm_expr = PermExpr::union(vec![required_sync, required_garb]);
    ctx.bind_perm(ghost_ret, ret_perm_expr);

    Ok(())
}
