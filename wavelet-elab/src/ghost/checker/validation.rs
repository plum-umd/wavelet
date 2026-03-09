//! SMT-backed validation for synthesized ghost permissions.

use std::collections::HashSet;

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostProgram, GhostStmt, GhostTail, GhostVar};
use crate::ir::{Op, Signedness, Ty, Val, Variable};
use crate::logic::cap::RegionModel;
use crate::logic::semantic::solver::{Atom, Idx, PhiSolver, RealExpr, SmtSolver};

use super::context::CheckContext;
use super::contract::{fraction_validity_atoms, instantiate_call_contract};
use super::permission::{consume_permission, PermExpr, Permission};
use super::pretty_print::{
    render_consistency_check, render_fraction_of, render_ghost_stmt, render_ghost_tail,
    render_join_split_check, render_named_perm_expr, render_perm_expr, render_perm_target_check,
    render_permission, render_region, render_relation,
};
use super::synthesis::{FunctionPermissionModel, ProgramPermissionModel};
use super::trace::{trace_context, trace_obligation, trace_validation_step, TraceDetails};
use super::utils::{access_region, join_parts};

pub fn validate_synthesized_program<V: Variable>(
    program: &GhostProgram<V>,
    model: &ProgramPermissionModel,
    solver: SmtSolver,
    verbose: bool,
) -> Result<(), String> {
    let mut ctx = CheckContext::new_with_verbose(solver, verbose);
    for (name, signature) in &model.signatures {
        ctx.register_signature(name.clone(), signature.clone());
    }

    for def in &program.defs {
        let function_model = model
            .functions
            .get(&def.name.0)
            .ok_or_else(|| format!("missing synthesized permissions for {}", def.name.0))?;
        validate_function(def, function_model, &mut ctx)?;
    }

    Ok(())
}

fn validate_function<V: Variable>(
    def: &GhostFnDef<V>,
    model: &FunctionPermissionModel,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    ctx.current_fn_name = Some(def.name.0.clone());
    ctx.phi.atoms.clear();
    ctx.penv = model.bindings.clone();
    ctx.set_current_fn_entry_perms(None);

    for param in &def.params {
        if let Ty::Int(Signedness::Unsigned) = param.ty {
            ctx.add_constraint(Atom::Le(Idx::Const(0), Idx::Var(param.name.clone())));
        }
    }

    if def.ghost_params.len() >= 2 {
        let p_sync = ctx
            .lookup_perm(&def.ghost_params[0])
            .cloned()
            .ok_or_else(|| format!("missing synthesized binding for {}", def.ghost_params[0].0))?;
        let p_garb = ctx
            .lookup_perm(&def.ghost_params[1])
            .cloned()
            .ok_or_else(|| format!("missing synthesized binding for {}", def.ghost_params[1].0))?;
        ctx.set_current_fn_entry_perms(Some((p_sync, p_garb)));
    }

    trace_context(ctx, "Initial context");

    let signature = ctx
        .get_signature(&def.name.0)
        .ok_or_else(|| format!("missing signature for {}", def.name.0))?
        .clone();
    for assumption in &signature.contract.assumptions {
        ctx.add_constraint(assumption.clone());
    }
    ensure_constraints_preserve_consistency(
        ctx,
        true,
        &format!("entry assumptions for {}", def.name.0),
    )?;

    trace_context(ctx, "After entry assumptions");
    validate_expr(&def.body, ctx)?;
    ctx.set_current_fn_entry_perms(None);
    ctx.current_fn_name = None;
    Ok(())
}

fn validate_expr<V: Variable>(expr: &GhostExpr<V>, ctx: &mut CheckContext) -> Result<(), String> {
    trace_context(ctx, "Entering ghost expression");

    let stmts = &expr.stmts;
    let mut i = 0;
    while i < stmts.len() {
        match &stmts[i] {
            GhostStmt::Pure { .. } => {
                trace_validation_step(
                    ctx,
                    format!("stmt {i}: {}", render_ghost_stmt(&stmts[i])),
                    |ctx| validate_pure_stmt(&stmts[i], ctx),
                )?;
                i += 1;
            }
            GhostStmt::JoinSplit { .. } => {
                if i + 1 >= stmts.len() {
                    trace_validation_step(
                        ctx,
                        format!(
                            "tail: {}; {}",
                            render_ghost_stmt(&stmts[i]),
                            render_ghost_tail(&expr.tail)
                        ),
                        |ctx| validate_tail_after_join(&stmts[i], &expr.tail, ctx),
                    )?;
                    return Ok(());
                }

                match &stmts[i + 1] {
                    GhostStmt::Const { .. } => {
                        trace_validation_step(
                            ctx,
                            format!(
                                "stmts {i}-{}: {}; {}",
                                i + 1,
                                render_ghost_stmt(&stmts[i]),
                                render_ghost_stmt(&stmts[i + 1])
                            ),
                            |ctx| validate_join_const(&stmts[i], &stmts[i + 1], ctx),
                        )?;
                        i += 2;
                    }
                    GhostStmt::Load { .. } => {
                        trace_validation_step(
                            ctx,
                            format!(
                                "stmts {i}-{}: {}; {}",
                                i + 1,
                                render_ghost_stmt(&stmts[i]),
                                render_ghost_stmt(&stmts[i + 1])
                            ),
                            |ctx| validate_join_load(&stmts[i], &stmts[i + 1], ctx),
                        )?;
                        i += 2;
                    }
                    GhostStmt::Store { .. } => {
                        trace_validation_step(
                            ctx,
                            format!(
                                "stmts {i}-{}: {}; {}",
                                i + 1,
                                render_ghost_stmt(&stmts[i]),
                                render_ghost_stmt(&stmts[i + 1])
                            ),
                            |ctx| validate_join_store(&stmts[i], &stmts[i + 1], ctx),
                        )?;
                        i += 2;
                    }
                    GhostStmt::JoinSplit { .. } => {
                        if i + 2 >= stmts.len() {
                            trace_validation_step(
                                ctx,
                                format!(
                                    "tail: {}; {}; {}",
                                    render_ghost_stmt(&stmts[i]),
                                    render_ghost_stmt(&stmts[i + 1]),
                                    render_ghost_tail(&expr.tail)
                                ),
                                |ctx| {
                                    validate_tail_after_two_joins(
                                        &stmts[i],
                                        &stmts[i + 1],
                                        &expr.tail,
                                        ctx,
                                    )
                                },
                            )?;
                            return Ok(());
                        }
                        match &stmts[i + 2] {
                            GhostStmt::Call { .. } => {
                                trace_validation_step(
                                    ctx,
                                    format!(
                                        "stmts {i}-{}: {}; {}; {}",
                                        i + 2,
                                        render_ghost_stmt(&stmts[i]),
                                        render_ghost_stmt(&stmts[i + 1]),
                                        render_ghost_stmt(&stmts[i + 2])
                                    ),
                                    |ctx| {
                                        validate_join_join_call(
                                            &stmts[i],
                                            &stmts[i + 1],
                                            &stmts[i + 2],
                                            ctx,
                                        )
                                    },
                                )?;
                                i += 3;
                            }
                            other => {
                                return Err(format!(
                                    "two join/splits must be followed by a call or tail call, found {}",
                                    render_ghost_stmt(other)
                                ));
                            }
                        }
                    }
                    other => {
                        return Err(format!(
                            "join/split must be followed by a const/load/store/call site, found {}",
                            render_ghost_stmt(other)
                        ));
                    }
                }
            }
            other => {
                return Err(format!(
                    "malformed lowered program: {} is missing its leading join/split",
                    render_ghost_stmt(other)
                ));
            }
        }
    }

    match &expr.tail {
        GhostTail::IfElse {
            cond,
            then_expr,
            else_expr,
        } => {
            let mut then_ctx = ctx.clone();
            let mut else_ctx = ctx.clone();
            then_ctx.add_constraint(Atom::BoolVar(cond.name().to_string()));
            else_ctx.add_constraint(Atom::Not(Box::new(Atom::BoolVar(cond.name().to_string()))));
            validate_expr(then_expr, &mut then_ctx)?;
            validate_expr(else_expr, &mut else_ctx)?;
            Ok(())
        }
        other => Err(format!(
            "tail {} must be preceded by lowering-introduced join/split statements",
            render_ghost_tail(other)
        )),
    }
}

fn validate_pure_stmt<V: Variable>(
    stmt: &GhostStmt<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    let (inputs, output, op) = match stmt {
        GhostStmt::Pure { inputs, output, op } => (inputs, output, op),
        _ => unreachable!(),
    };

    match op {
        Op::SignedLessThan
        | Op::SignedLessEqual
        | Op::UnsignedLessThan
        | Op::UnsignedLessEqual
        | Op::Equal
            if inputs.len() == 2 =>
        {
            let comparison = match op {
                Op::SignedLessThan | Op::UnsignedLessThan => Atom::Lt(
                    Idx::Var(inputs[0].name().to_string()),
                    Idx::Var(inputs[1].name().to_string()),
                ),
                Op::SignedLessEqual | Op::UnsignedLessEqual => Atom::Le(
                    Idx::Var(inputs[0].name().to_string()),
                    Idx::Var(inputs[1].name().to_string()),
                ),
                Op::Equal => Atom::Eq(
                    Idx::Var(inputs[0].name().to_string()),
                    Idx::Var(inputs[1].name().to_string()),
                ),
                _ => unreachable!(),
            };
            let result_atom = Atom::BoolVar(output.name().to_string());
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
            let lhs = Atom::BoolVar(inputs[0].name().to_string());
            let rhs = Atom::BoolVar(inputs[1].name().to_string());
            let out = Atom::BoolVar(output.name().to_string());
            ctx.add_constraint(Atom::Implies(Box::new(out.clone()), Box::new(lhs.clone())));
            ctx.add_constraint(Atom::Implies(Box::new(out.clone()), Box::new(rhs.clone())));
            ctx.add_constraint(Atom::Implies(
                Box::new(Atom::And(Box::new(lhs.clone()), Box::new(rhs.clone()))),
                Box::new(out.clone()),
            ));
            ctx.add_constraint(Atom::Implies(
                Box::new(Atom::Not(Box::new(out))),
                Box::new(Atom::Or(
                    Box::new(Atom::Not(Box::new(lhs))),
                    Box::new(Atom::Not(Box::new(rhs))),
                )),
            ));
        }
        Op::Or if inputs.len() == 2 => {
            let lhs = Atom::BoolVar(inputs[0].name().to_string());
            let rhs = Atom::BoolVar(inputs[1].name().to_string());
            let out = Atom::BoolVar(output.name().to_string());
            ctx.add_constraint(Atom::Implies(Box::new(lhs.clone()), Box::new(out.clone())));
            ctx.add_constraint(Atom::Implies(Box::new(rhs.clone()), Box::new(out.clone())));
            ctx.add_constraint(Atom::Implies(
                Box::new(out.clone()),
                Box::new(Atom::Or(Box::new(lhs.clone()), Box::new(rhs.clone()))),
            ));
            ctx.add_constraint(Atom::Implies(
                Box::new(Atom::And(
                    Box::new(Atom::Not(Box::new(lhs))),
                    Box::new(Atom::Not(Box::new(rhs))),
                )),
                Box::new(Atom::Not(Box::new(out))),
            ));
        }
        Op::Add | Op::Sub | Op::Mul if inputs.len() == 2 => {
            let lhs = Box::new(Idx::Var(inputs[0].name().to_string()));
            let rhs = Box::new(Idx::Var(inputs[1].name().to_string()));
            let result = match op {
                Op::Add => Idx::Add(lhs, rhs),
                Op::Sub => Idx::Sub(lhs, rhs),
                Op::Mul => Idx::Mul(lhs, rhs),
                _ => unreachable!(),
            };
            ctx.add_constraint(Atom::Eq(Idx::Var(output.name().to_string()), result));
        }
        _ => {}
    }

    Ok(())
}

fn validate_join_const<V: Variable>(
    join_stmt: &GhostStmt<V>,
    const_stmt: &GhostStmt<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    let (left, right, inputs) = join_parts(join_stmt)?;
    validate_join_split_law(ctx, inputs, left, right, "const")?;

    let ghost_in = match const_stmt {
        GhostStmt::Const { ghost_in, .. } => ghost_in,
        _ => unreachable!(),
    };
    if ghost_in.0 != left.0 {
        return Err(format!("const expects {}, found {}", ghost_in.0, left.0));
    }
    assert_perm_equal(ctx, &lookup(ctx, left)?, &PermExpr::empty(), "const input")?;

    let (value, output) = match const_stmt {
        GhostStmt::Const { value, output, .. } => (value, output),
        _ => unreachable!(),
    };
    validate_const_value(value, output, ctx);
    Ok(())
}

fn validate_join_load<V: Variable>(
    join_stmt: &GhostStmt<V>,
    load_stmt: &GhostStmt<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    let (left, right, inputs) = join_parts(join_stmt)?;
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
        return Err(format!("load expects {}, found {}", ghost_in.0, left.0));
    }

    let expected_region = access_region(index.name());
    let joined_inputs = join_inputs_expr(ctx, inputs)?;
    let left_expr = lookup(ctx, left)?;
    let right_expr = lookup(ctx, right)?;
    let out_expr = lookup(ctx, ghost_out)?;
    let details = TraceDetails::new()
        .permission("sum(inputs)", &joined_inputs)
        .permission(format!("{} (ghost in)", left.0), &left_expr)
        .permission(format!("{} (remainder)", right.0), &right_expr)
        .permission(format!("{} (ghost out)", ghost_out.0), &out_expr)
        .line(format!(
            "expected region: {}{}",
            array.name(),
            render_region(&expected_region)
        ))
        .check(render_join_split_check(inputs, left, right))
        .check(render_perm_target_check(
            left,
            array.name(),
            &expected_region,
        ))
        .check(render_relation(render_fraction_of(&left.0), ">", "0"))
        .check(render_named_perm_expr(&ghost_out.0, &left_expr))
        .finish();

    trace_obligation(
        ctx,
        format!("ghost load: {}[{}]", array.name(), index.name()),
        details,
        |ctx| {
            let load_perm = raw_single_permission(&left_expr, "load input")?;
            for atom in fraction_validity_atoms(&load_perm.fraction) {
                ctx.add_constraint(atom);
            }
            let available = joined_inputs
                .collect_permissions(&ctx.phi, &ctx.solver)
                .ok_or_else(|| "load inputs could not be normalized".to_string())?;
            constrain_fraction_from_available(ctx, &available, &load_perm, "load input", false)?;
            validate_join_split_law(ctx, inputs, left, right, "load")?;
            assert_perm_equal(ctx, &left_expr, &out_expr, "load output permission")?;
            if load_perm.array.name() != array.name() {
                return Err(format!(
                    "load permission targets {}, but the load accesses {}",
                    load_perm.array.0,
                    array.name()
                ));
            }
            if load_perm.region != expected_region {
                return Err(format!(
                    "load permission {} does not match access region {}",
                    render_permission(&load_perm),
                    render_region(&expected_region)
                ));
            }
            validate_fraction_positive(ctx, &load_perm.fraction, "load permission")?;
            Ok(())
        },
    )
}

fn validate_join_store<V: Variable>(
    join_stmt: &GhostStmt<V>,
    store_stmt: &GhostStmt<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    let (left, right, inputs) = join_parts(join_stmt)?;
    validate_join_split_law(ctx, inputs, left, right, "store")?;

    let (array, index, ghost_in, ghost_out) = match store_stmt {
        GhostStmt::Store {
            array,
            index,
            ghost_in,
            ghost_out,
            ..
        } => (array, index, ghost_in, ghost_out),
        _ => unreachable!(),
    };
    if ghost_in.0 != left.0 {
        return Err(format!("store expects {}, found {}", ghost_in.0, left.0));
    }

    let expected_region = access_region(index.name());
    let joined_inputs = join_inputs_expr(ctx, inputs)?;
    let left_expr = lookup(ctx, left)?;
    let right_expr = lookup(ctx, right)?;
    let dummy_out = lookup(ctx, &ghost_out.0)?;
    let returned_out = lookup(ctx, &ghost_out.1)?;
    let details = TraceDetails::new()
        .permission("sum(inputs)", &joined_inputs)
        .permission(format!("{} (ghost in)", left.0), &left_expr)
        .permission(format!("{} (remainder)", right.0), &right_expr)
        .permission(format!("{} (ghost out)", ghost_out.1 .0), &returned_out)
        .line(format!(
            "expected region: {}{}",
            array.name(),
            render_region(&expected_region)
        ))
        .check(render_join_split_check(inputs, left, right))
        .check(render_perm_target_check(
            left,
            array.name(),
            &expected_region,
        ))
        .check(render_relation(render_fraction_of(&left.0), "=", "1"))
        .check(render_named_perm_expr(&ghost_out.1 .0, &left_expr))
        .finish();

    trace_obligation(
        ctx,
        format!("ghost store: {}[{}]", array.name(), index.name()),
        details,
        |ctx| {
            validate_join_split_law(ctx, inputs, left, right, "store")?;

            let store_perm = expect_single_permission(ctx, &left_expr, "store input")?;
            if store_perm.array.name() != array.name() {
                return Err(format!(
                    "store permission targets {}, but the store updates {}",
                    store_perm.array.0,
                    array.name()
                ));
            }
            if store_perm.region != expected_region {
                return Err(format!(
                    "store permission {} does not match access region {}",
                    render_permission(&store_perm),
                    render_region(&expected_region)
                ));
            }
            if store_perm.fraction != FractionExpr::from_int(1) {
                return Err(format!(
                    "store requires full permission, synthesized {} instead",
                    render_permission(&store_perm)
                ));
            }

            assert_perm_equal(ctx, &dummy_out, &PermExpr::empty(), "store dummy output")?;
            assert_perm_equal(ctx, &left_expr, &returned_out, "store returned permission")?;
            Ok(())
        },
    )
}

fn validate_join_join_call<V: Variable>(
    join_stmt_1: &GhostStmt<V>,
    join_stmt_2: &GhostStmt<V>,
    call_stmt: &GhostStmt<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    let (left_1, right_1, inputs_1) = join_parts(join_stmt_1)?;
    let (left_2, right_2, inputs_2) = join_parts(join_stmt_2)?;

    let (func, args, ghost_need, ghost_left, ghost_ret) = match call_stmt {
        GhostStmt::Call {
            func,
            args,
            ghost_need,
            ghost_left,
            ghost_ret,
            ..
        } => (func, args, ghost_need, ghost_left, ghost_ret),
        _ => unreachable!(),
    };
    if ghost_need.0 != left_1.0 || ghost_left.0 != left_2.0 {
        return Err(format!(
            "call {} does not line up with its join/splits",
            func.0
        ));
    }

    let signature = ctx
        .get_signature(&func.0)
        .ok_or_else(|| format!("call to unknown function {}", func.0))?
        .clone();
    let contract = instantiate_call_contract(&signature, args, &ghost_need.0)?;
    let need_expr = lookup(ctx, ghost_need)?;
    let left_expr = lookup(ctx, ghost_left)?;
    let ret_expr = lookup(ctx, ghost_ret)?;
    let sync_inputs = join_inputs_expr(ctx, inputs_1)?;
    let garb_inputs = join_inputs_expr(ctx, inputs_2)?;
    let returned_perm = PermExpr::union([contract.sync.clone(), contract.garb.clone()]);
    let details = TraceDetails::new()
        .permission("sum(sync inputs)", &sync_inputs)
        .permission("sum(garb inputs)", &garb_inputs)
        .permission(format!("{} (ghost need)", ghost_need.0), &need_expr)
        .permission(format!("{} (ghost left)", ghost_left.0), &left_expr)
        .permission(format!("{} (ghost ret)", ghost_ret.0), &ret_expr)
        .permission("required p_sync", &contract.sync)
        .permission("required p_garb", &contract.garb)
        .check(render_consistency_check(&func.0))
        .check(render_join_split_check(inputs_1, left_1, right_1))
        .check(render_join_split_check(inputs_2, left_2, right_2))
        .check(render_named_perm_expr(&ghost_need.0, &contract.sync))
        .check(render_named_perm_expr(&ghost_left.0, &contract.garb))
        .check(render_named_perm_expr(&ghost_ret.0, &returned_perm))
        .finish();

    trace_obligation(ctx, format!("ghost call: {}", func.0), details, |ctx| {
        justify_contract_sync_from_inputs(
            ctx,
            &func.0,
            &contract.assumptions,
            &sync_inputs,
            &contract.sync,
            "call",
        )?;
        validate_join_split_law(ctx, inputs_1, left_1, right_1, "call p_sync")?;
        validate_join_split_law(ctx, inputs_2, left_2, right_2, "call p_garb")?;
        assert_perm_equal(ctx, &need_expr, &contract.sync, "call p_sync")?;
        assert_perm_equal(ctx, &left_expr, &contract.garb, "call p_garb")?;
        assert_perm_equal(
            ctx,
            &ret_expr,
            &PermExpr::union([contract.sync.clone(), contract.garb.clone()]),
            "call return permission",
        )?;

        let garb_norm = contract
            .garb
            .normalize(&ctx.phi, &ctx.solver)
            .unwrap_or(contract.garb.clone());
        if garb_norm != PermExpr::empty() {
            return Err(format!(
                "non-tail call {} synthesized non-empty p_garb {}",
                func.0,
                render_perm_expr(&garb_norm)
            ));
        }

        Ok(())
    })
}

fn validate_tail_after_join<V: Variable>(
    join_stmt: &GhostStmt<V>,
    tail: &GhostTail<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    match tail {
        GhostTail::Return { perm, .. } => {
            let (left, right, inputs) = join_parts(join_stmt)?;
            let returned = lookup(ctx, perm)?;
            let expected = current_entry_total(ctx)?;
            let joined_inputs = join_inputs_expr(ctx, inputs)?;
            let right_expr = lookup(ctx, right)?;
            let details = TraceDetails::new()
                .permission("sum(inputs)", &joined_inputs)
                .permission(format!("{} (return perm)", perm.0), &returned)
                .permission(format!("{} (remainder)", right.0), &right_expr)
                .permission("entry total", &expected)
                .check(render_join_split_check(inputs, left, right))
                .check(render_named_perm_expr(&perm.0, &expected))
                .finish();
            trace_obligation(ctx, "ghost return", details, |ctx| {
                validate_join_split_law(ctx, inputs, left, right, "return")?;
                assert_perm_equal(ctx, &returned, &expected, "returned permission")?;
                Ok(())
            })
        }
        other => Err(format!(
            "single trailing join/split must feed a return, found {}",
            render_ghost_tail(other)
        )),
    }
}

fn validate_tail_after_two_joins<V: Variable>(
    join_stmt_1: &GhostStmt<V>,
    join_stmt_2: &GhostStmt<V>,
    tail: &GhostTail<V>,
    ctx: &mut CheckContext,
) -> Result<(), String> {
    match tail {
        GhostTail::TailCall {
            func,
            args,
            ghost_need,
            ghost_left,
        } => {
            let (left_1, right_1, inputs_1) = join_parts(join_stmt_1)?;
            let (left_2, right_2, inputs_2) = join_parts(join_stmt_2)?;

            if ghost_need.0 != left_1.0 || ghost_left.0 != left_2.0 {
                return Err(format!(
                    "tail call {} does not line up with its join/splits",
                    func.0
                ));
            }

            let signature = ctx
                .get_signature(&func.0)
                .ok_or_else(|| format!("tail call to unknown function {}", func.0))?
                .clone();
            let contract = instantiate_call_contract(&signature, args, &ghost_need.0)?;
            let need_expr = lookup(ctx, ghost_need)?;
            let left_expr = lookup(ctx, ghost_left)?;
            let sync_inputs = join_inputs_expr(ctx, inputs_1)?;
            let garb_inputs = join_inputs_expr(ctx, inputs_2)?;
            let entry_total = current_entry_total(ctx)?;
            let passed_total = PermExpr::union([need_expr.clone(), left_expr.clone()]);
            let right_2_expr = lookup(ctx, right_2)?;
            let details = TraceDetails::new()
                .permission("sum(sync inputs)", &sync_inputs)
                .permission("sum(garb inputs)", &garb_inputs)
                .permission(format!("{} (ghost need)", ghost_need.0), &need_expr)
                .permission(format!("{} (ghost left)", ghost_left.0), &left_expr)
                .permission("required p_sync", &contract.sync)
                .permission("passed total", &passed_total)
                .permission("entry total", &entry_total)
                .permission(format!("{} (tail remainder)", right_2.0), &right_2_expr)
                .check(render_consistency_check(&func.0))
                .check(render_join_split_check(inputs_1, left_1, right_1))
                .check(render_join_split_check(inputs_2, left_2, right_2))
                .check(render_named_perm_expr(&ghost_need.0, &contract.sync))
                .check(render_named_perm_expr(
                    format!("({} + {})", ghost_need.0, ghost_left.0),
                    &entry_total,
                ))
                .check(render_named_perm_expr(&right_2.0, &PermExpr::empty()))
                .finish();

            trace_obligation(
                ctx,
                format!("ghost tail call: {}", func.0),
                details,
                |ctx| {
                    justify_contract_sync_from_inputs(
                        ctx,
                        &func.0,
                        &contract.assumptions,
                        &sync_inputs,
                        &contract.sync,
                        "tail-call",
                    )?;
                    validate_join_split_law(ctx, inputs_1, left_1, right_1, "tail-call p_sync")?;
                    validate_join_split_law(ctx, inputs_2, left_2, right_2, "tail-call p_garb")?;
                    assert_perm_equal(ctx, &need_expr, &contract.sync, "tail-call p_sync")?;
                    assert_perm_equal(
                        ctx,
                        &passed_total,
                        &entry_total,
                        "tail-call total permission",
                    )?;
                    assert_perm_equal(
                        ctx,
                        &right_2_expr,
                        &PermExpr::empty(),
                        "tail-call remainder",
                    )?;
                    Ok(())
                },
            )
        }
        other => Err(format!(
            "two trailing join/splits must feed a tail call, found {}",
            render_ghost_tail(other)
        )),
    }
}

fn validate_join_split_law(
    ctx: &CheckContext,
    inputs: &[GhostVar],
    left: &GhostVar,
    right: &GhostVar,
    label: &str,
) -> Result<(), String> {
    let mut input_exprs = Vec::with_capacity(inputs.len());
    for input in inputs {
        let expr = lookup(ctx, input)?;
        validate_perm_expr(ctx, &expr, &format!("{label} input {}", input.0))?;
        input_exprs.push(expr);
    }
    let joined_inputs = PermExpr::union(input_exprs);
    let left_expr = lookup(ctx, left)?;
    let right_expr = lookup(ctx, right)?;
    validate_perm_expr(ctx, &left_expr, &format!("{label} left"))?;
    validate_perm_expr(ctx, &right_expr, &format!("{label} right"))?;
    let split_total = PermExpr::union([left_expr, right_expr]);
    assert_perm_equal(
        ctx,
        &joined_inputs,
        &split_total,
        &format!("{label} join/split law"),
    )
}

fn join_inputs_expr(ctx: &CheckContext, inputs: &[GhostVar]) -> Result<PermExpr, String> {
    let mut exprs = Vec::with_capacity(inputs.len());
    for input in inputs {
        exprs.push(lookup(ctx, input)?);
    }
    Ok(PermExpr::union(exprs))
}

fn validate_perm_expr(ctx: &CheckContext, expr: &PermExpr, what: &str) -> Result<(), String> {
    if expr.is_valid(&ctx.phi, &ctx.solver) {
        Ok(())
    } else {
        Err(format!(
            "{} is not a valid permission expression: {}",
            what,
            render_perm_expr(expr)
        ))
    }
}

fn validate_call_assumptions(
    ctx: &mut CheckContext,
    assumptions: &[Atom],
    func_name: &str,
) -> Result<(), String> {
    let was_consistent = phi_is_consistent(ctx);
    for atom in assumptions {
        ctx.add_constraint(atom.clone());
    }
    ensure_constraints_preserve_consistency(
        ctx,
        was_consistent,
        &format!("call assumptions for {}", func_name),
    )?;
    Ok(())
}

fn justify_contract_sync_from_inputs(
    ctx: &mut CheckContext,
    func_name: &str,
    assumptions: &[Atom],
    sync_inputs: &PermExpr,
    contract_sync: &PermExpr,
    call_kind: &str,
) -> Result<(), String> {
    validate_call_assumptions(ctx, assumptions, func_name)?;
    let available_sync = sync_inputs
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| format!("{call_kind} inputs for {func_name} could not be normalized"))?;
    for perm in contract_sync
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| format!("{call_kind} contract for {func_name} could not be normalized"))?
    {
        if !is_unique_fraction(&perm.fraction) {
            constrain_fraction_from_available(
                ctx,
                &available_sync,
                &perm,
                &format!("{call_kind} p_sync"),
                false,
            )?;
        }
    }
    Ok(())
}

fn lookup(ctx: &CheckContext, var: &GhostVar) -> Result<PermExpr, String> {
    ctx.lookup_perm(var)
        .cloned()
        .ok_or_else(|| format!("missing synthesized binding for {}", var.0))
}

fn assert_perm_equal(
    ctx: &CheckContext,
    actual: &PermExpr,
    expected: &PermExpr,
    what: &str,
) -> Result<(), String> {
    let actual_flat = actual
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| format!("{} could not be normalized", what))?;
    let expected_flat = expected
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| format!("{} expected value could not be normalized", what))?;

    let mut missing_from_expected = expected_flat.clone();
    for perm in &actual_flat {
        if !consume_permission(&mut missing_from_expected, perm, &ctx.phi, &ctx.solver) {
            return Err(format!(
                "{} contains extra permission {}",
                what,
                render_permission(perm)
            ));
        }
    }

    let mut missing_from_actual = actual_flat.clone();
    for perm in &expected_flat {
        if !consume_permission(&mut missing_from_actual, perm, &ctx.phi, &ctx.solver) {
            return Err(format!(
                "{} is missing permission {}",
                what,
                render_permission(perm)
            ));
        }
    }

    Ok(())
}

fn expect_single_permission(
    ctx: &CheckContext,
    expr: &PermExpr,
    what: &str,
) -> Result<Permission, String> {
    let perms = expr
        .collect_permissions(&ctx.phi, &ctx.solver)
        .ok_or_else(|| format!("{} could not be normalized", what))?;
    if perms.len() == 1 {
        Ok(perms.into_iter().next().unwrap())
    } else {
        Err(format!(
            "{} must be a singleton permission, found {}",
            what,
            render_perm_expr(expr)
        ))
    }
}

fn raw_single_permission(expr: &PermExpr, what: &str) -> Result<Permission, String> {
    match expr {
        PermExpr::Singleton(perm) => Ok(perm.clone()),
        _ => Err(format!(
            "{} must be synthesized as a singleton permission, found {}",
            what,
            render_perm_expr(expr)
        )),
    }
}

fn validate_fraction_positive(
    ctx: &CheckContext,
    fraction: &FractionExpr,
    what: &str,
) -> Result<(), String> {
    for atom in fraction_validity_atoms(fraction) {
        if !ctx.solver.entails(&ctx.phi, &atom) {
            return Err(format!(
                "{} does not satisfy {}",
                what,
                super::pretty_print::render_atom(&atom)
            ));
        }
    }
    if !ctx.solver.entails(
        &ctx.phi,
        &Atom::RealLt(RealExpr::from_int(0), fraction.to_real_expr()),
    ) {
        return Err(format!("{} is not provably positive", what));
    }
    Ok(())
}

fn constrain_fraction_from_available(
    ctx: &mut CheckContext,
    available: &[Permission],
    needed: &Permission,
    label: &str,
    strict_upper_bound: bool,
) -> Result<(), String> {
    let was_consistent = phi_is_consistent(ctx);
    let mut regions_to_cover = vec![needed.region.clone()];
    let mut coverage_bounds = Vec::new();

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

            let mut overlap = crate::logic::semantic::region_set::RegionSetExpr::intersection(
                piece.clone(),
                perm.region.clone(),
            )
            .simplify(&ctx.phi, &ctx.solver);
            if overlap.is_empty(&ctx.phi, &ctx.solver) {
                if piece.is_subregion_of(&perm.region, &ctx.phi, &ctx.solver) {
                    overlap = piece.clone();
                } else {
                    continue;
                }
            }

            coverage_bounds.push(perm.fraction.to_real_expr());
            let remainder = crate::logic::semantic::region_set::RegionSetExpr::difference(
                piece.clone(),
                overlap,
            )
            .simplify(&ctx.phi, &ctx.solver);
            if !remainder.is_empty(&ctx.phi, &ctx.solver) {
                regions_to_cover.push(remainder);
            }

            covered = true;
            break;
        }

        if !covered {
            return Err(format!(
                "{} cannot be justified from the available permissions: {}",
                label,
                render_permission(needed)
            ));
        }
    }

    let mut seen = HashSet::new();
    for bound in coverage_bounds {
        let key = format!("{bound:?}");
        if seen.insert(key) {
            let need = needed.fraction.to_real_expr();
            ctx.add_constraint(if strict_upper_bound {
                Atom::RealLt(need, bound)
            } else {
                Atom::RealLe(need, bound)
            });
        }
    }

    ensure_constraints_preserve_consistency(
        ctx,
        was_consistent,
        &format!("{label} witness constraints"),
    )?;

    Ok(())
}

fn phi_is_consistent(ctx: &CheckContext) -> bool {
    !ctx.solver
        .entails(&ctx.phi, &Atom::Lt(Idx::Const(1), Idx::Const(0)))
}

fn ensure_constraints_preserve_consistency(
    ctx: &CheckContext,
    was_consistent: bool,
    label: &str,
) -> Result<(), String> {
    if was_consistent && !phi_is_consistent(ctx) {
        return Err(format!(
            "{label} are inconsistent with the current path conditions"
        ));
    }
    Ok(())
}

fn validate_const_value<V: Variable>(value: &Val, output: &V, ctx: &mut CheckContext) {
    let ty = match value {
        Val::Int(n) if *n >= 0 => Ty::Int(Signedness::Unsigned),
        Val::Int(_) => Ty::Int(Signedness::Signed),
        Val::Bool(_) => Ty::Bool,
        Val::Unit => Ty::Unit,
    };
    if let Ty::Int(Signedness::Unsigned) = ty {
        ctx.add_constraint(Atom::Le(Idx::Const(0), Idx::Var(output.name().to_string())));
    }
    match value {
        Val::Int(n) => ctx.add_constraint(Atom::Eq(
            Idx::Var(output.name().to_string()),
            Idx::Const(*n),
        )),
        Val::Bool(true) => ctx.add_constraint(Atom::BoolVar(output.name().to_string())),
        Val::Bool(false) => ctx.add_constraint(Atom::Not(Box::new(Atom::BoolVar(
            output.name().to_string(),
        )))),
        Val::Unit => {}
    }
}

fn current_entry_total(ctx: &CheckContext) -> Result<PermExpr, String> {
    let (sync, garb) = ctx
        .current_fn_entry_perms()
        .cloned()
        .ok_or_else(|| "missing current function entry permissions".to_string())?;
    Ok(PermExpr::union([sync, garb]))
}

fn is_unique_fraction(frac: &FractionExpr) -> bool {
    matches!(frac, FractionExpr::Const(num, den) if *num == *den)
}
