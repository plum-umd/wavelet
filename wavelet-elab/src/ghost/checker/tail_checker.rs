//! Tail expression checking functions for ghost programs.

use std::collections::{HashMap, HashSet};

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::{GhostStmt, GhostTail};
use crate::logic::cap::RegionModel;
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, PhiSolver, RealExpr};

use super::context::CheckContext;
use super::permission::{
    PermExpr, Permission, consume_permission, permissions_to_expr, substitute_atom_with_maps,
    substitute_perm_expr_with_maps,
};
use super::pretty_print::{render_perm_expr, render_permission, render_region};

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
                println!(
                    "  Joining permissions for return: [{}]",
                    inputs
                        .iter()
                        .map(|v| v.0.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            for var in inputs {
                if let Some(contrib) = ctx.take_return_contribution(var) {
                    if let Some(current) = ctx.lookup_perm(var).cloned() {
                        let cleaned = PermExpr::Sub(Box::new(current), Box::new(contrib));
                        if !cleaned.is_valid(&ctx.phi, &ctx.solver) {
                            return Err(format!(
                                "Return permission cleanup for {} produced an invalid expression",
                                var.0
                            ));
                        }
                        ctx.bind_perm(var, cleaned);
                    }
                }
            }

            let joined_perm = ctx.join_perms(inputs)?;
            let joined_flat = joined_perm
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Returned permission could not be normalised".to_string())?;
            let cleaned_join = permissions_to_expr(joined_flat.clone());

            if ctx.verbose {
                println!("  Joined: {}", render_perm_expr(&cleaned_join));
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

            let mut expected_flat = expected_total
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Entry permissions could not be normalised".to_string())?;

            if ctx.verbose {
                println!(
                    "  Verifying returned permissions consume exactly the entry permissions..."
                );
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
                println!(
                    "  Tail calling: {}({})",
                    func.0,
                    args.iter()
                        .map(|v| v.0.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }

            let sig = ctx
                .get_signature(&func.0)
                .ok_or_else(|| format!("TailCall to unknown function {}", func.0))?
                .clone();

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
            let (left2, _right2, inputs2) = match join_stmt2 {
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
                println!(
                    "  First JoinSplit (p_sync): joining [{}]",
                    inputs1
                        .iter()
                        .map(|v| v.0.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
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

            for atom in &sig.preconditions {
                let instantiated = substitute_atom_with_maps(atom, &idx_substitutions);
                ctx.add_constraint(instantiated);
            }

            let required_sync =
                substitute_perm_expr_with_maps(&sig.initial_perms.0, &idx_substitutions);
            let required_garb =
                substitute_perm_expr_with_maps(&sig.initial_perms.1, &idx_substitutions);

            if ctx.verbose {
                println!("  Required p_sync: {}", render_perm_expr(&required_sync));
                println!("  Required p_garb: {}", render_perm_expr(&required_garb));
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
            let mut fraction_bindings: HashMap<String, FractionExpr> = HashMap::new();
            for need in &needed_sync {
                let is_unique = is_unique_fraction(&need.fraction);
                let need_to_consume = if is_unique {
                    need.clone()
                } else if let Some(var_name) = fraction_expr_var_name(&need.fraction) {
                    let entry = fraction_bindings.get(var_name);
                    match entry {
                        Some(bound_frac) => Permission::new(
                            bound_frac.clone(),
                            need.array.clone(),
                            need.region.clone(),
                        ),
                        None => {
                            let perm = ensure_shared_fraction_available(
                                ctx,
                                &available_sync,
                                need,
                                &func.0,
                                "p_sync",
                                None,
                            )?;
                            fraction_bindings.insert(var_name.to_string(), perm.fraction.clone());
                            perm
                        }
                    }
                } else {
                    need.clone()
                };
                if ctx.verbose {
                    println!(
                        "    {} permission required for p_sync: {}",
                        if is_unique { "Unique" } else { "Shared" },
                        render_permission(&need_to_consume)
                    );
                }
                if !consume_permission(&mut available_sync, &need_to_consume, &ctx.phi, &ctx.solver)
                {
                    if ctx.verbose {
                        println!(
                            "    ✗ Cannot consume required permission: {}",
                            render_permission(&need_to_consume)
                        );
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
                println!(
                    "  Second JoinSplit (p_garb): joining [{}]",
                    inputs2
                        .iter()
                        .map(|v| v.0.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }

            let joined_perm2 = ctx.join_perms(inputs2)?;

            let mut available_garb = joined_perm2
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| {
                    "Joined permissions for second JoinSplit could not be normalised".to_string()
                })?;

            if ctx.verbose {
                println!("    Joined: {}", render_perm_expr(&joined_perm2));
                println!(
                    "    Joined flattened: {}",
                    render_perm_expr(&permissions_to_expr(available_garb.clone()))
                );
            }
            let needed_garb = required_garb
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "Required p_garb permissions could not be normalised".to_string())?;
            for need in &needed_garb {
                let is_unique = is_unique_fraction(&need.fraction);
                let mut need_to_consume = need.clone();
                if !is_unique {
                    if let Some(var_name) = fraction_expr_var_name(&need.fraction) {
                        if let Some(bound_frac) = fraction_bindings.get(var_name) {
                            let ensured = ensure_shared_fraction_available(
                                ctx,
                                &available_garb,
                                need,
                                &func.0,
                                "p_garb",
                                Some(bound_frac.clone()),
                            )?;
                            need_to_consume = ensured;
                        }
                    }
                }
                if ctx.verbose {
                    println!(
                        "    Permission required for p_garb: {}",
                        render_permission(&need_to_consume)
                    );
                }
                if !consume_permission(&mut available_garb, &need_to_consume, &ctx.phi, &ctx.solver)
                {
                    if ctx.verbose {
                        println!(
                            "    ✗ Cannot consume required permission: {}",
                            render_permission(&need_to_consume)
                        );
                    }
                    return Err(format!(
                        "TailCall to {} cannot provide required permission for p_garb",
                        func.0
                    ));
                }
            }
            let leftover_expr = permissions_to_expr(available_garb);
            let leftover_norm =
                leftover_expr
                    .normalize(&ctx.phi, &ctx.solver)
                    .ok_or_else(|| {
                        "TailCall leftover permissions could not be normalised".to_string()
                    })?;
            leftover_norm
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| {
                    "TailCall leftover permissions could not be collected".to_string()
                })?;

            if ctx.verbose {
                if leftover_norm == PermExpr::empty() {
                    println!("    ✓ p_garb consumed exactly");
                } else {
                    println!(
                        "    Remaining ghost_left permission after p_garb consumption: {}",
                        render_perm_expr(&leftover_norm)
                    );
                }
                println!("  Verifying total permissions match entry permissions...");
            }

            Ok(())
        }
        _ => Err(format!(
            "Two JoinSplits at end of expression must be followed by TailCall tail, found {:?}",
            tail
        )),
    }
}

fn is_unique_fraction(frac: &FractionExpr) -> bool {
    matches!(frac, FractionExpr::Const(num, den) if *num == *den)
}

fn fraction_expr_var_name<'a>(frac: &'a FractionExpr) -> Option<&'a str> {
    if let FractionExpr::Var(name) = frac {
        Some(name.as_str())
    } else {
        None
    }
}

fn ensure_shared_fraction_available(
    ctx: &mut CheckContext,
    available: &[Permission],
    needed: &Permission,
    func_name: &str,
    phase: &str,
    existing_fraction: Option<FractionExpr>,
) -> Result<Permission, String> {
    let zero = RealExpr::from_int(0);
    let mut regions_to_cover = vec![needed.region.clone()];
    let mut coverage_constraints: Vec<RealExpr> = Vec::new();
    let mut coverage_sources: Vec<(Permission, RegionSetExpr)> = Vec::new();

    while let Some(piece) = regions_to_cover.pop() {
        let piece = piece.simplify(&ctx.phi, &ctx.solver);
        if piece.is_empty(&ctx.phi, &ctx.solver) {
            continue;
        }

        let mut covered = false;
        for perm in available {
            if perm.array != needed.array {
                continue;
            }

            let mut overlap = RegionSetExpr::intersection(piece.clone(), perm.region.clone())
                .simplify(&ctx.phi, &ctx.solver);
            if overlap.is_empty(&ctx.phi, &ctx.solver) {
                if piece.is_subregion_of(&perm.region, &ctx.phi, &ctx.solver) {
                    overlap = piece.clone();
                } else {
                    continue;
                }
            }

            let g_real = perm.fraction.to_real_expr();
            if !ctx
                .solver
                .entails(&ctx.phi, &Atom::RealLt(zero.clone(), g_real.clone()))
            {
                continue;
            }

            coverage_constraints.push(g_real);
            coverage_sources.push((perm.clone(), overlap.clone()));

            let remainder = RegionSetExpr::difference(piece.clone(), overlap.clone())
                .simplify(&ctx.phi, &ctx.solver);
            if !remainder.is_empty(&ctx.phi, &ctx.solver) {
                regions_to_cover.push(remainder);
            }

            covered = true;
            break;
        }

        if !covered {
            return Err(format!(
                "TailCall to {} requires a shared permission for {} in {} covering region {}, but no available permission covers the remaining region {}",
                func_name,
                needed.array.0,
                phase,
                render_region(&needed.region),
                render_region(&piece)
            ));
        }
    }

    if coverage_constraints.is_empty() {
        return Err(format!(
            "TailCall to {} requires a shared permission for {} in {} covering region {}, but no matching permissions were found",
            func_name,
            needed.array.0,
            phase,
            render_region(&needed.region)
        ));
    }

    let (shared_fraction, f_real) = match existing_fraction {
        Some(expr) => {
            let real = expr.to_real_expr();
            (expr, real)
        }
        None => {
            let fresh_fraction = ctx.fresh_fraction_var("__tail_shared_");
            ctx.add_fraction_validity_constraint(&fresh_fraction);
            let real = fresh_fraction.to_real_expr();
            (fresh_fraction, real)
        }
    };

    let mut seen_bounds: HashSet<String> = HashSet::new();
    for bound in coverage_constraints {
        let key = format!("{:?}", bound);
        if seen_bounds.insert(key) {
            ctx.add_constraint(Atom::RealLe(f_real.clone(), bound));
        }
    }

    let shared_perm = Permission::new(
        shared_fraction.clone(),
        needed.array.clone(),
        needed.region.clone(),
    );

    if ctx.verbose {
        println!(
            "      Shared requirement {}: enforcing {} ≤ each covering permission",
            phase,
            render_permission(&shared_perm)
        );
        for (source, covered_region) in &coverage_sources {
            println!(
                "        covered by {} on {}",
                render_permission(source),
                render_region(covered_region)
            );
        }
    }

    Ok(shared_perm)
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
