//! Top-level program and function checking.

use crate::ghost::ir::{GhostFnDef, GhostProgram};
use crate::ir::{Signedness, Ty};
use crate::logic::semantic::solver::{Atom, Idx, SmtSolver};

use super::context::{CheckContext, FunctionSignature};
use super::expr_checker::check_ghost_expr;
use super::pretty_print::trace_context;

/// Check a ghost program for permission correctness.
pub fn check_ghost_program(program: &GhostProgram) -> Result<(), String> {
    check_ghost_program_with_verbose(program, false)
}

/// Check a ghost program for permission correctness with optional verbose mode.
pub fn check_ghost_program_with_verbose(
    program: &GhostProgram,
    verbose: bool,
) -> Result<(), String> {
    let solver = SmtSolver::new();
    let mut ctx = CheckContext::new_with_verbose(solver.clone(), verbose);

    // First pass: collect function signatures
    if verbose {
        println!("=== Collecting function signatures ===\n");
    }
    for def in &program.defs {
        let sig = build_function_signature(def);
        if verbose {
            println!("Function: {}", def.name.0);
            println!(
                "  Parameters: {}",
                def.params
                    .iter()
                    .map(|(v, _)| v.0.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            println!(
                "  Ghost parameters: {}",
                def.ghost_params
                    .iter()
                    .map(|v| v.0.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            println!();
        }
        ctx.register_signature(def.name.0.clone(), sig);
    }

    // Second pass: check each function
    if verbose {
        println!("=== Checking function bodies ===\n");
    }
    for def in &program.defs {
        if verbose {
            println!("\n╭───────────────────────────────────────────────────────────────╮");
            println!("│ Checking function: {:42} │", def.name.0);
            println!("╰───────────────────────────────────────────────────────────────╯");
        }
        check_ghost_fn(def, &mut ctx)?;
        if verbose {
            println!("✓ Function {} checked successfully\n", def.name.0);
        }
    }

    if verbose {
        println!("\n╔═══════════════════════════════════════════════════════════╗");
        println!("║           ✓ All checks passed successfully                ║");
        println!("╚═══════════════════════════════════════════════════════════╝\n");
    }

    Ok(())
}

/// Build a function signature from a ghost function definition.
/// This extracts the initial permission setup from CapPattern.
fn build_function_signature(def: &GhostFnDef) -> FunctionSignature {
    use crate::ghost::ir::GhostVar;

    let params = def.params.clone();

    let solver = SmtSolver::new();
    let mut temp_ctx = CheckContext::new(solver);

    let p_sync = GhostVar("__sig_p_sync".to_string());
    let p_garb = GhostVar("__sig_p_garb".to_string());

    // Parse caps into permissions
    let mut preconditions = Vec::new();
    temp_ctx.caps_to_permissions(&def.caps, &p_sync, &p_garb, Some(&mut preconditions));

    // Extract the permissions
    let sync_perm = match temp_ctx.lookup_perm(&p_sync) {
        Some(perm) => perm.clone(),
        None => unreachable!(),
    };
    let garb_perm = match temp_ctx.lookup_perm(&p_garb) {
        Some(perm) => perm.clone(),
        None => unreachable!(),
    };
    FunctionSignature {
        params,
        initial_perms: (sync_perm, garb_perm),
        preconditions,
    }
}

/// Check a single ghost function definition.
fn check_ghost_fn(def: &GhostFnDef, ctx: &mut CheckContext) -> Result<(), String> {
    use super::pretty_print::render_perm_expr;

    // clear propositional context and permission env
    ctx.phi.atoms.clear();
    ctx.penv = super::perm_env::PermissionEnv::new();
    ctx.set_current_fn_entry_perms(None);

    trace_context(ctx, &format!("Initial context for function {}", def.name.0));

    for (var, ty) in &def.params {
        if let Ty::Int(Signedness::Unsigned) = ty {
            ctx.add_constraint(Atom::Le(Idx::Const(0), Idx::Var(var.0.clone())));
        }
    }

    if def.ghost_params.len() >= 2 {
        let p_sync = &def.ghost_params[0];
        let p_garb = &def.ghost_params[1];

        let mut preconditions = Vec::new();
        ctx.caps_to_permissions(&def.caps, p_sync, p_garb, Some(&mut preconditions));

        // Clone the permissions before setting them
        let sync = ctx.lookup_perm(p_sync).cloned();
        let garb = ctx.lookup_perm(p_garb).cloned();

        if let (Some(sync), Some(garb)) = (sync, garb) {
            if ctx.verbose {
                println!("  p_sync = {}", render_perm_expr(&sync));
                println!("  p_garb = {}", render_perm_expr(&garb));
            }
            ctx.set_current_fn_entry_perms(Some((sync, garb)));
        }

        for atom in preconditions {
            ctx.add_constraint(atom);
        }
    }

    trace_context(ctx, "After capability initialization");

    check_ghost_expr(&def.body, ctx)?;

    ctx.set_current_fn_entry_perms(None);

    Ok(())
}
