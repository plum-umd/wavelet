//! Tail expression checking functions for ghost programs.

use crate::ghost::ir::{GhostStmt, GhostTail};
use crate::logic::semantic::solver::{Atom, Idx};

use super::context::CheckContext;
use super::permission::{consume_permission, permissions_to_expr, PermExpr, substitute_perm_expr_with_maps};
use super::pretty_print::{render_permission, render_perm_expr};

/// Check a JoinSplit followed by Return tail.
pub fn check_ghost_tail_with_joinsplit(
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

            if ctx.verbose {
                println!("  Joining permissions for return: [{}]", inputs.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
            }

            let joined_perm = ctx.join_perms(inputs)?;

            if ctx.verbose {
                println!("  Joined: {}", render_perm_expr(&joined_perm));
            }

            if left.0 != perm.0 {
                return Err(format!(
                    "Return permission {} does not match JoinSplit left {}",
                    perm.0, left.0
                ));
            }

            let entry_perms = ctx.current_fn_entry_perms().ok_or_else(|| {
                "Return encountered without recorded entry permissions".to_string()
            })?;

            if ctx.verbose {
                println!("  Checking return permissions match entry permissions...");
                println!("    Entry p_sync: {}", render_perm_expr(&entry_perms.0));
                println!("    Entry p_garb: {}", render_perm_expr(&entry_perms.1));
            }

            let expected_total =
                PermExpr::union(vec![entry_perms.0.clone(), entry_perms.1.clone()]);

            let joined_flat = joined_perm
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Returned permission could not be normalised".to_string())?;
            let mut expected_flat = expected_total
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Entry permissions could not be normalised".to_string())?;

            if ctx.verbose {
                println!("  Verifying returned permissions consume exactly the entry permissions...");
            }

            for perm_piece in &joined_flat {
                if !consume_permission(&mut expected_flat, perm_piece, &ctx.phi, &ctx.solver) {
                    return Err(format!(
                        "Return permission contains {} which was not present at function entry",
                        render_permission(perm_piece)
                    ));
                }
            }

            if !expected_flat.is_empty() {
                if ctx.verbose {
                    println!("  ✗ Missing permissions in return:");
                    for missing in &expected_flat {
                        println!("    - {}", render_permission(missing));
                    }
                }
                return Err(
                    "Return permission is missing resources that were provided at function entry"
                        .to_string(),
                );
            }

            if ctx.verbose {
                println!("  ✓ Return permissions match entry permissions exactly");
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
pub fn check_ghost_tail_with_two_joinsplits(
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
            if ctx.verbose {
                println!("  Tail calling: {}({})", func.0, args.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
            }

            let sig = ctx
                .get_signature(&func.0)
                .ok_or_else(|| format!("TailCall to unknown function {}", func.0))?;
            let sig = sig.clone();

            if sig.params.len() != args.len() {
                return Err(format!(
                    "TailCall to {} expects {} arguments but received {}",
                    func.0,
                    sig.params.len(),
                    args.len()
                ));
            }

            // right1 would be added to the garb ctx at lowering
            let (left1, right1, inputs1) = match join_stmt1 {
                GhostStmt::JoinSplit {
                    left,
                    right,
                    inputs,
                } => (left, right, inputs),
                _ => unreachable!(),
            };

            // right2 would always be epsilon
            let (left2, right2, inputs2) = match join_stmt2 {
                GhostStmt::JoinSplit {
                    left,
                    right,
                    inputs,
                } => (left, right, inputs),
                _ => unreachable!(),
            };
            
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
            // check right1 is part of inputs2
            if !inputs2.iter().any(|v| v.0 == right1.0) {
                return Err(format!(
                    "TailCall ghost_left {} does not join first JoinSplit right {}",
                    ghost_left.0, right1.0
                ));
            }

            if ctx.verbose {
                println!("  First JoinSplit (p_sync): joining [{}]", inputs1.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
            }

            let joined_perm1 = ctx.join_perms(inputs1)?;

            if ctx.verbose {
                println!("    Joined: {}", render_perm_expr(&joined_perm1));
            }

            let mut idx_substitutions: Vec<(String, Idx)> = Vec::new();
            for ((param_var, ty), arg) in sig.params.iter().zip(args.iter()) {
                if ty.is_int() {
                    idx_substitutions.push((param_var.0.clone(), Idx::Var(arg.0.clone())));
                }
            }
            idx_substitutions.sort_by(|a, b| a.0.cmp(&b.0));

            let required_sync =
                substitute_perm_expr_with_maps(&sig.initial_perms.0, &idx_substitutions);
            let required_garb =
                substitute_perm_expr_with_maps(&sig.initial_perms.1, &idx_substitutions);

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
                .ok_or_else(|| {
                    "Required p_sync permissions could not be normalised".to_string()
                })?;
            for need in &needed_sync {
                if !consume_permission(&mut available_sync, need, &ctx.phi, &ctx.solver) {
                    if ctx.verbose {
                        println!("    ✗ Cannot consume required permission: {}", render_permission(need));
                    }
                    return Err(format!(
                        "TailCall to {} cannot provide required permission for p_sync",
                        func.0
                    ));
                }
            }

            // bind remainder to right1
            let remainder_sync_expr = permissions_to_expr(available_sync);
            if !remainder_sync_expr.is_valid(&ctx.phi, &ctx.solver) {
                return Err(format!(
                    "Remaining permissions after consuming p_sync for {} are invalid",
                    func.0
                ));
            }
            ctx.bind_perm(right1, remainder_sync_expr);

            if ctx.verbose {
                println!("    ✓ p_sync consumed successfully");
                println!("  Consuming p_garb permissions...");
            }

            if ctx.verbose {
                println!("  Second JoinSplit (p_garb): joining [{}]", inputs2.iter().map(|v| v.0.as_str()).collect::<Vec<_>>().join(", "));
            }

            let joined_perm2 = ctx.join_perms(inputs2)?;

            if ctx.verbose {
                println!("    Joined: {}", render_perm_expr(&joined_perm2));
            }

            let mut available_garb = joined_perm2
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| {
                    "Joined permissions for second JoinSplit could not be normalised"
                        .to_string()
                })?;
            let needed_garb = required_garb
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| {
                    "Required p_garb permissions could not be normalised".to_string()
                })?;
            for need in &needed_garb {
                if !consume_permission(&mut available_garb, need, &ctx.phi, &ctx.solver) {
                    if ctx.verbose {
                        println!("    ✗ Cannot consume required permission: {}", render_permission(need));
                    }
                    return Err(format!(
                        "TailCall to {} cannot provide required permission for p_garb",
                        func.0
                    ));
                }
            }
            let leftover_expr = permissions_to_expr(available_garb);
            let leftover_norm = leftover_expr
                .normalize(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "TailCall leftover permissions could not be normalised".to_string())?;
            let leftover_perms = leftover_norm
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "TailCall leftover permissions could not be collected".to_string())?;

            if !leftover_perms.is_empty() {
                if ctx.verbose {
                    println!("    ✗ Extra permissions remaining after p_garb consumption:");
                    for extra in &leftover_perms {
                        println!("      - {}", render_permission(extra));
                    }
                }
                return Err(format!(
                    "TailCall to {} leaves extra permission for p_garb after consumption",
                    func.0
                ));
            }

            if ctx.verbose {
                println!("    ✓ p_garb consumed exactly");
                println!("  Verifying total permissions match entry permissions...");
            }

            // Bind the remainder (which should be empty) back to the second JoinSplit right.
            ctx.bind_perm(right2, leftover_norm);

            let entry_perms = ctx.current_fn_entry_perms().ok_or_else(|| {
                "TailCall encountered without recorded entry permissions".to_string()
            })?;

            if ctx.verbose {
                println!("    Entry p_sync: {}", render_perm_expr(&entry_perms.0));
                println!("    Entry p_garb: {}", render_perm_expr(&entry_perms.1));
            }

            let tail_total =
                PermExpr::union(vec![required_sync.clone(), required_garb.clone()]);
            let expected_total =
                PermExpr::union(vec![entry_perms.0.clone(), entry_perms.1.clone()]);

            let tail_flat = tail_total
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "TailCall permissions could not be normalised".to_string())?;
            let mut expected_flat = expected_total
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Entry permissions could not be normalised".to_string())?;

            for perm_piece in &tail_flat {
                if !consume_permission(&mut expected_flat, perm_piece, &ctx.phi, &ctx.solver) {
                    return Err(format!(
                        "TailCall permissions contain {} which was not present at function entry",
                        render_permission(perm_piece)
                    ));
                }
            }

            if !expected_flat.is_empty() {
                if ctx.verbose {
                    println!("    ✗ Missing permissions in tail call:");
                    for missing in &expected_flat {
                        println!("      - {}", render_permission(missing));
                    }
                }
                return Err(
                    "TailCall permissions are missing resources that were provided at function entry"
                        .to_string(),
                );
            }

            if ctx.verbose {
                println!("    ✓ Total permissions match entry permissions exactly");
            }

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
            if ctx.verbose {
                println!("\n === Checking if-else with condition: {} ===", cond.0);
            }

            // Branch: create two sub-contexts
            let mut then_ctx = ctx.clone();
            let mut else_ctx = ctx.clone();

            // Add branching constraints
            let cond_var = Atom::BoolVar(cond.0.clone());
            then_ctx.add_constraint(cond_var.clone());
            else_ctx.add_constraint(Atom::Not(Box::new(cond_var)));

            if ctx.verbose {
                println!("  ├─ Then branch (assuming {}):", cond.0);
            }
            // Check both branches
            super::expr_checker::check_ghost_expr(then_expr, &mut then_ctx)?;
            
            if ctx.verbose {
                println!("  ├─ Else branch (assuming !{}):", cond.0);
            }
            super::expr_checker::check_ghost_expr(else_expr, &mut else_ctx)?;

            if ctx.verbose {
                println!("  === Both branches checked successfully ===\n");
            }

            // Both branches must succeed independently
            Ok(())
        }
        _ => Err(format!("Tail expression must be IfElse, found {:?}", tail)),
    }
}
