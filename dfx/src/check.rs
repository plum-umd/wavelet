//! The core type checking logic for the restricted language.

use std::collections::BTreeMap;

use crate::env::{BoolFact, Ctx, FnRegistry};
use crate::error::TypeError;
use crate::ir::{Expr, FnDef, Op, Program, Stmt, Tail, Ty, Val, Var};
use crate::logic::CapabilityLogic;
use crate::logic::cap::{Cap, Delta};
use crate::logic::region::Region;
use crate::logic::semantic::solver::{Atom, Idx};
use crate::logic::semantic::{Interval, Phi};

/// Substitute variable names in an index expression according to a map.
fn substitute_idx(idx: &Idx, subst: &BTreeMap<String, String>) -> Idx {
    match idx {
        Idx::Const(n) => Idx::Const(*n),
        Idx::Var(v) => {
            if let Some(new_v) = subst.get(v) {
                Idx::Var(new_v.clone())
            } else {
                Idx::Var(v.clone())
            }
        }
        Idx::Add(a, b) => Idx::Add(
            Box::new(substitute_idx(a, subst)),
            Box::new(substitute_idx(b, subst)),
        ),
        Idx::Sub(a, b) => Idx::Sub(
            Box::new(substitute_idx(a, subst)),
            Box::new(substitute_idx(b, subst)),
        ),
    }
}

/// Substitute variable names in a region according to a map.
fn substitute_region(region: &Region, subst: &BTreeMap<String, String>) -> Region {
    let mut intervals = Vec::new();
    for interval in region.iter() {
        let new_lo = substitute_idx(&interval.lo, subst);
        let new_hi = interval.hi.as_ref().map(|hi| substitute_idx(hi, subst));
        intervals.push(Interval {
            lo: new_lo,
            hi: new_hi,
        });
    }
    Region::from_intervals(intervals)
}

/// Options controlling how the type checker behaves.
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckOptions {
    /// Emit detailed traces of the type checking context as it evolves.
    pub verbose: bool,
}

fn render_idx(idx: &Idx) -> String {
    match idx {
        Idx::Const(n) => n.to_string(),
        Idx::Var(v) => v.clone(),
        Idx::Add(a, b) => format!("({} + {})", render_idx(a), render_idx(b)),
        Idx::Sub(a, b) => format!("({} - {})", render_idx(a), render_idx(b)),
    }
}

fn render_atom(atom: &Atom) -> String {
    match atom {
        Atom::Le(a, b) => format!("{} <= {}", render_idx(a), render_idx(b)),
        Atom::Lt(a, b) => format!("{} < {}", render_idx(a), render_idx(b)),
        Atom::Eq(a, b) => format!("{} == {}", render_idx(a), render_idx(b)),
        Atom::And(lhs, rhs) => format!("({}) && ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Not(inner) => format!("!({})", render_atom(inner)),
    }
}

fn region_is_empty(region: &Region) -> bool {
    region.iter().next().is_none()
}

fn render_region(region: &Region) -> String {
    if region_is_empty(region) {
        "<empty>".to_string()
    } else {
        region
            .iter()
            .map(|interval| interval.to_string())
            .collect::<Vec<_>>()
            .join(" | ")
    }
}

fn render_cap(cap: &Cap) -> String {
    let shrd_empty = region_is_empty(&cap.shrd);
    let uniq_empty = region_is_empty(&cap.uniq);
    match (shrd_empty, uniq_empty) {
        (true, true) => "<empty>".to_string(),
        (false, true) => format!("shrd: {}", render_region(&cap.shrd)),
        (true, false) => format!("uniq: {}", render_region(&cap.uniq)),
        (false, false) => format!(
            "shrd: {}; uniq: {}",
            render_region(&cap.shrd),
            render_region(&cap.uniq)
        ),
    }
}

fn render_ty(ty: &Ty) -> String {
    TypeError::type_name(ty)
}

fn render_val(val: &Val) -> String {
    match val {
        Val::Int(n) => n.to_string(),
        Val::Bool(b) => b.to_string(),
        Val::Unit => "()".to_string(),
    }
}

fn render_array_len(len: &crate::ir::ArrayLen) -> String {
    len.display()
}

fn render_op(op: &Op, vars: &[Var]) -> String {
    match op {
        Op::Add => format!("{} = {} + {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Sub => format!("{} = {} - {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Mul => format!("{} = {} * {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Div => format!("{} = {} / {}", vars[2].0, vars[0].0, vars[1].0),
        Op::And => format!("{} = {} && {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Or => format!("{} = {} || {}", vars[2].0, vars[0].0, vars[1].0),
        Op::LessThan => format!("{} = {} < {}", vars[2].0, vars[0].0, vars[1].0),
        Op::LessEqual => format!("{} = {} <= {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Equal => format!("{} = {} == {}", vars[2].0, vars[0].0, vars[1].0),
        Op::IntoI32 => format!("{} = i32::from({})", vars[1].0, vars[0].0),
        Op::Load {
            array,
            index,
            len,
            fence,
        } => {
            let mut msg = format!(
                "{} = {}[{}] (len {})",
                vars[0].0,
                array.0,
                index.0,
                render_array_len(len)
            );
            if *fence {
                msg.push_str(" [fenced]");
            }
            msg
        }
        Op::Store {
            array,
            index,
            value,
            len,
            fence,
        } => {
            let mut msg = format!(
                "store {} -> {}[{}] (len {})",
                value.0,
                array.0,
                index.0,
                render_array_len(len)
            );
            if *fence {
                msg.push_str(" [fenced]");
            }
            msg
        }
    }
}

fn render_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::LetVal { var, val } => format!("let {} = {}", var.0, render_val(val)),
        Stmt::LetOp { vars, op } => render_op(op, vars),
        Stmt::LetCall {
            vars,
            func,
            args,
            fence,
        } => {
            let mut msg = String::new();
            if vars.is_empty() {
                msg.push_str("call ");
            } else {
                let dests = vars
                    .iter()
                    .map(|v| v.0.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                msg.push_str(&format!("let {} = ", dests));
            }
            let arg_list = args
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            msg.push_str(&format!("{}({})", func.0, arg_list));
            if *fence {
                msg.push_str(" [fenced]");
            }
            msg
        }
    }
}

fn render_tail(tail: &Tail) -> String {
    match tail {
        Tail::RetVar(var) => format!("return {}", var.0),
        Tail::IfElse { cond, .. } => format!("if {} {{ ... }} else {{ ... }}", cond.0),
        Tail::TailCall { func, args } => {
            let arg_list = args
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!("tail call {}({})", func.0, arg_list)
        }
    }
}

fn trace_context(ctx: &Ctx, stage: &str) {
    if !ctx.verbose {
        return;
    }

    println!("\n=== {} ===", stage);
    print_context_contents(ctx);
}

fn print_context_contents(ctx: &Ctx) {
    if ctx.gamma.0.is_empty() {
        println!("Gamma: <empty>");
    } else {
        println!("Gamma:");
        for (name, ty) in ctx.gamma.0.iter() {
            println!("  {}: {}", name, render_ty(ty));
        }
    }

    if ctx.delta.0.is_empty() {
        println!("Delta: <empty>");
    } else {
        println!("Delta:");
        for (name, cap) in ctx.delta.0.iter() {
            println!("  {}: {}", name, render_cap(cap));
        }
    }

    let atoms: Vec<_> = ctx.phi.iter().collect();
    if atoms.is_empty() {
        println!("Phi: <empty>");
    } else {
        println!("Phi:");
        for atom in atoms {
            println!("  {}", render_atom(atom));
        }
    }

    if ctx.bool_facts.is_empty() {
        println!("Bool facts: <empty>");
    } else {
        println!("Bool facts:");
        for (var, fact) in ctx.bool_facts.iter() {
            println!("  {}:", var);
            println!("    when true: {}", render_atom(&fact.when_true));
            if let Some(neg) = &fact.when_false {
                println!("    when false: {}", render_atom(neg));
            }
        }
    }

    println!();
}

fn log_after_statement(ctx: &Ctx, stmt: &Stmt) {
    if ctx.verbose {
        println!("After {}:", render_stmt(stmt));
        print_context_contents(ctx);
    }
}

fn push_atom(phi: &mut Phi, atom: Atom) {
    match atom {
        Atom::And(lhs, rhs) => {
            push_atom(phi, *lhs);
            push_atom(phi, *rhs);
        }
        other => phi.push(other),
    }
}

/// Check an entire program with the supplied options.
pub fn check_program_with_options(
    prog: &Program,
    logic: &dyn CapabilityLogic,
    options: CheckOptions,
) -> Result<(), TypeError> {
    // Build a registry of function definitions for lookups.
    let mut registry = FnRegistry::default();
    for def in &prog.defs {
        registry.insert(def.clone());
    }
    for def in &prog.defs {
        check_fn_with_options(def, &registry, logic, options)?;
    }
    Ok(())
}

/// Check an entire program.  Currently this simply iterates over
/// definitions and checks each in isolation.
pub fn check_program(prog: &Program, logic: &dyn CapabilityLogic) -> Result<(), TypeError> {
    check_program_with_options(prog, logic, CheckOptions::default())
}

/// Check a single function definition.
pub fn check_fn(
    def: &FnDef,
    registry: &FnRegistry,
    logic: &dyn CapabilityLogic,
) -> Result<(), TypeError> {
    check_fn_with_options(def, registry, logic, CheckOptions::default())
}

/// Check a single function definition with explicit options.
pub fn check_fn_with_options(
    def: &FnDef,
    registry: &FnRegistry,
    logic: &dyn CapabilityLogic,
    options: CheckOptions,
) -> Result<(), TypeError> {
    // Initialise context with parameter types.
    let mut ctx = Ctx::new(logic, options.verbose);
    for (var, ty) in &def.params {
        ctx.gamma.insert(var.clone(), ty.clone());
    }
    // Initialise capability environment from the function’s cap pattern.
    for cap_pat in &def.caps {
        let cap = cap_pat.instantiate(&ctx.phi, ctx.logic.solver());
        ctx.delta.0.insert(cap_pat.array.clone(), cap);
    }
    trace_context(&ctx, "Initial context after parameter and capability setup");

    // Check body.
    let result = check_expr(&mut ctx, &def.body, &def.returns, registry);
    if result.is_ok() {
        trace_context(&ctx, "Context after function body");
    }
    result
}

/// Check an expression and ensure it produces a value of the expected type.
fn check_expr(
    ctx: &mut Ctx,
    expr: &Expr,
    expected: &Ty,
    registry: &FnRegistry,
) -> Result<(), TypeError> {
    trace_context(ctx, "Entering expression");

    // Process statements sequentially.
    for stmt in &expr.stmts {
        if ctx.verbose {
            println!("Processing statement: {}", render_stmt(stmt));
        }
        check_stmt(ctx, stmt, registry)?;
    }

    if ctx.verbose {
        println!("Evaluating tail: {}", render_tail(&expr.tail));
        print_context_contents(ctx);
    }

    // Check tail.
    let ty = check_tail(ctx, &expr.tail, registry)?;

    if ctx.verbose {
        println!(
            "Tail {} produced type {}",
            render_tail(&expr.tail),
            render_ty(&ty)
        );
        print_context_contents(ctx);
    }

    if &ty != expected {
        return Err(TypeError::TypeMismatch {
            expected: TypeError::type_name(expected),
            found: TypeError::type_name(&ty),
        });
    }
    Ok(())
}

/// Infer the type of an expression (for use in if-else branches).
fn infer_expr_type(ctx: &mut Ctx, expr: &Expr, registry: &FnRegistry) -> Result<Ty, TypeError> {
    trace_context(ctx, "Inferring expression type");

    // Process statements sequentially.
    for stmt in &expr.stmts {
        if ctx.verbose {
            println!("Processing statement (infer): {}", render_stmt(stmt));
        }
        check_stmt(ctx, stmt, registry)?;
    }

    if ctx.verbose {
        println!("Inferring tail: {}", render_tail(&expr.tail));
        print_context_contents(ctx);
    }

    // Check tail and return its type.
    let ty = check_tail(ctx, &expr.tail, registry)?;

    if ctx.verbose {
        println!(
            "Inferred tail {} has type {}",
            render_tail(&expr.tail),
            render_ty(&ty)
        );
        print_context_contents(ctx);
    }

    Ok(ty)
}

/// Check a single statement.
fn check_stmt(ctx: &mut Ctx, stmt: &Stmt, registry: &FnRegistry) -> Result<(), TypeError> {
    match stmt {
        Stmt::LetVal { var, val } => {
            // Determine literal type and bind it.
            let ty = match val {
                Val::Int(_) => Ty::Int,
                Val::Bool(_) => Ty::Bool,
                Val::Unit => Ty::Unit,
            };
            ctx.gamma.insert(var.clone(), ty);
            ctx.bool_facts.remove(&var.0);
            // Add equality fact to Phi for integer constants.
            if let Val::Int(n) = val {
                ctx.phi
                    .push(Atom::Eq(Idx::Var(var.0.clone()), Idx::Const(*n)));
            }
            log_after_statement(ctx, stmt);
            Ok(())
        }
        Stmt::LetOp { vars, op } => {
            match op {
                Op::Add | Op::Sub | Op::Mul | Op::Div => {
                    // Binary integer arithmetic.  Expect two input vars and one output.
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.gamma.get(&vars[0])?;
                    let y_ty = ctx.gamma.get(&vars[1])?;
                    if !x_ty.is_int() || !y_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    // Add fact to Phi for Add/Sub operations.
                    let x_idx = Idx::Var(vars[0].0.clone());
                    let y_idx = Idx::Var(vars[1].0.clone());
                    let result_idx = Idx::Var(vars[2].0.clone());
                    let rhs = match op {
                        Op::Add => Idx::Add(Box::new(x_idx), Box::new(y_idx)),
                        Op::Sub => Idx::Sub(Box::new(x_idx), Box::new(y_idx)),
                        _ => result_idx.clone(), // Don't track Mul/Div as they're non-linear
                    };
                    if !matches!(op, Op::Mul | Op::Div) {
                        ctx.phi.push(Atom::Eq(result_idx, rhs));
                    }
                    ctx.gamma.insert(vars[2].clone(), Ty::Int);
                    ctx.bool_facts.remove(&vars[2].0);
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::And => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.gamma.get(&vars[0])?;
                    let y_ty = ctx.gamma.get(&vars[1])?;
                    if !matches!(x_ty, Ty::Bool) || !matches!(y_ty, Ty::Bool) {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.gamma.insert(vars[2].clone(), Ty::Bool);
                    let combined_fact = match (
                        ctx.bool_facts.get(&vars[0].0),
                        ctx.bool_facts.get(&vars[1].0),
                    ) {
                        (Some(lhs), Some(rhs)) => Some(BoolFact {
                            when_true: Atom::And(
                                Box::new(lhs.when_true.clone()),
                                Box::new(rhs.when_true.clone()),
                            ),
                            when_false: None,
                        }),
                        _ => None,
                    };
                    if let Some(fact) = combined_fact {
                        ctx.bool_facts.insert(vars[2].0.clone(), fact);
                    } else {
                        ctx.bool_facts.remove(&vars[2].0);
                    }
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::Or => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.gamma.get(&vars[0])?;
                    let y_ty = ctx.gamma.get(&vars[1])?;
                    if !matches!(x_ty, Ty::Bool) || !matches!(y_ty, Ty::Bool) {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.gamma.insert(vars[2].clone(), Ty::Bool);
                    ctx.bool_facts.remove(&vars[2].0);
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::LessThan | Op::LessEqual => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.gamma.get(&vars[0])?;
                    let y_ty = ctx.gamma.get(&vars[1])?;
                    if !x_ty.is_int() || !y_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    // Record the comparison as a fact in Phi.
                    let x_idx = Idx::Var(vars[0].0.clone());
                    let y_idx = Idx::Var(vars[1].0.clone());
                    ctx.bool_facts.remove(&vars[2].0);
                    let (true_atom, false_atom) = match op {
                        Op::LessThan => (
                            Atom::Lt(x_idx.clone(), y_idx.clone()),
                            Atom::Le(y_idx.clone(), x_idx.clone()),
                        ),
                        Op::LessEqual => (
                            Atom::Le(x_idx.clone(), y_idx.clone()),
                            Atom::Lt(y_idx.clone(), x_idx.clone()),
                        ),
                        _ => unreachable!(),
                    };
                    ctx.bool_facts.insert(
                        vars[2].0.clone(),
                        BoolFact {
                            when_true: true_atom,
                            when_false: Some(false_atom),
                        },
                    );
                    ctx.gamma.insert(vars[2].clone(), Ty::Bool);
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::Equal => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.gamma.get(&vars[0])?;
                    let y_ty = ctx.gamma.get(&vars[1])?;
                    if x_ty != y_ty {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.gamma.insert(vars[2].clone(), Ty::Bool);
                    ctx.bool_facts.remove(&vars[2].0);
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::IntoI32 => {
                    if vars.len() != 2 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.gamma.get(&vars[0])?;
                    if !x_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.gamma.insert(vars[1].clone(), Ty::Int);
                    ctx.bool_facts.remove(&vars[1].0);
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::Load {
                    array,
                    index,
                    len,
                    fence,
                } => {
                    // For a load we expect exactly one destination variable.
                    if vars.len() != 1 {
                        return Err(TypeError::InvalidOp {
                            op: "load destination arity".into(),
                        });
                    }
                    // Index must be int.
                    let idx_ty = ctx.gamma.get(index)?;
                    if !idx_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: "load index type".into(),
                        });
                    }
                    // Array must be a reference to the correct length.
                    let arr_ty = ctx.gamma.get(array)?;
                    let arr_len = match arr_ty {
                        Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => len.clone(),
                        _ => {
                            return Err(TypeError::InvalidOp {
                                op: "load non array".into(),
                            });
                        }
                    };
                    let op_len = len.clone();
                    if arr_len != op_len {
                        return Err(TypeError::InvalidOp {
                            op: format!(
                                "load length mismatch (have {}, need {})",
                                arr_len.display(),
                                op_len.display()
                            ),
                        });
                    }
                    // Required region [idx, idx+1).
                    let lo = Idx::Var(index.0.clone());
                    let hi = Idx::Add(Box::new(lo.clone()), Box::new(Idx::Const(1)));
                    let region = Region::from_bounded(lo.clone(), hi);
                    let mut req_cap = Cap::default();
                    req_cap.shrd = region.clone();
                    let arr_name = &array.0;
                    let have_cap = ctx.delta.0.get(arr_name).cloned().unwrap_or_default();
                    if !ctx.logic.cap_leq(&ctx.phi, &req_cap, &have_cap) {
                        return Err(TypeError::InsufficientCapability {
                            array: arr_name.clone(),
                            region: format!("{:?}", region),
                        });
                    }
                    if !*fence {
                        let mut delta_req = Delta::default();
                        delta_req.0.insert(arr_name.clone(), req_cap.clone());
                        ctx.delta = ctx
                            .logic
                            .delta_diff(&ctx.phi, &ctx.delta, &delta_req)
                            .ok_or_else(|| TypeError::CapabilitySubtractError {
                                array: arr_name.clone(),
                            })?;
                    }
                    // Bind result.
                    let dest = &vars[0];
                    ctx.gamma.insert(dest.clone(), Ty::Int);
                    ctx.bool_facts.remove(&dest.0);
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
                Op::Store {
                    array,
                    index,
                    value,
                    len,
                    fence,
                } => {
                    // For a store we expect no destination variables.
                    if !vars.is_empty() {
                        return Err(TypeError::InvalidOp {
                            op: "store destination arity".into(),
                        });
                    }
                    // Types of index and value.
                    let idx_ty = ctx.gamma.get(index)?;
                    let val_ty = ctx.gamma.get(value)?;
                    if !idx_ty.is_int() || !val_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: "store index/value type".into(),
                        });
                    }
                    // Array type.
                    let arr_ty = ctx.gamma.get(array)?;
                    let arr_len = match arr_ty {
                        Ty::RefUniq { len, .. } | Ty::RefShrd { len, .. } => len.clone(),
                        _ => {
                            return Err(TypeError::InvalidOp {
                                op: "store non array".into(),
                            });
                        }
                    };
                    let op_len = len.clone();
                    if arr_len != op_len {
                        return Err(TypeError::InvalidOp {
                            op: format!(
                                "store length mismatch (have {}, need {})",
                                arr_len.display(),
                                op_len.display()
                            ),
                        });
                    }
                    let lo = Idx::Var(index.0.clone());
                    let hi = Idx::Add(Box::new(lo.clone()), Box::new(Idx::Const(1)));
                    let region = Region::from_bounded(lo.clone(), hi);
                    let mut req_cap = Cap::default();
                    req_cap.uniq = region.clone();
                    let arr_name = &array.0;
                    let have_cap = ctx.delta.0.get(arr_name).cloned().unwrap_or_default();
                    if !ctx.logic.cap_leq(&ctx.phi, &req_cap, &have_cap) {
                        return Err(TypeError::InsufficientCapability {
                            array: arr_name.clone(),
                            region: format!("{:?}", region),
                        });
                    }
                    if !*fence {
                        let mut delta_req = Delta::default();
                        delta_req.0.insert(arr_name.clone(), req_cap.clone());
                        ctx.delta = ctx
                            .logic
                            .delta_diff(&ctx.phi, &ctx.delta, &delta_req)
                            .ok_or_else(|| TypeError::CapabilitySubtractError {
                                array: arr_name.clone(),
                            })?;
                    }
                    log_after_statement(ctx, stmt);
                    Ok(())
                }
            }
        }
        Stmt::LetCall {
            vars,
            func,
            args,
            fence,
        } => {
            // Look up function definition.
            let fn_def = registry
                .get(func)
                .ok_or_else(|| TypeError::UndefinedFunction(func.0.clone()))?;

            // Check that args match parameter types (value parameters only, not arrays).
            let value_params: Vec<_> = fn_def
                .params
                .iter()
                .filter(|(_, ty)| !matches!(ty, Ty::RefShrd { .. } | Ty::RefUniq { .. }))
                .collect();
            let array_params: Vec<_> = fn_def
                .params
                .iter()
                .filter(|(_, ty)| matches!(ty, Ty::RefShrd { .. } | Ty::RefUniq { .. }))
                .collect();

            // Build substitution map for indices (param names -> arg vars).
            let mut subst_map = std::collections::BTreeMap::new();

            // Check value parameters and build substitution.
            let expected_value_args = value_params.len();
            if args.len() < expected_value_args {
                return Err(TypeError::InvalidOp {
                    op: format!("function call to {} has too few arguments", func.0),
                });
            }
            for (i, (param_var, param_ty)) in value_params.iter().enumerate() {
                let arg_var = &args[i];
                let arg_ty = ctx.gamma.get(arg_var)?;
                if arg_ty != *param_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: TypeError::type_name(param_ty),
                        found: TypeError::type_name(&arg_ty),
                    });
                }
                // Record substitution for index expressions.
                subst_map.insert(param_var.0.clone(), arg_var.0.clone());
            }

            // Check array arguments and their capabilities.
            let array_args = &args[expected_value_args..];
            if array_args.len() != array_params.len() {
                return Err(TypeError::InvalidOp {
                    op: format!(
                        "function call to {} has wrong number of array arguments",
                        func.0
                    ),
                });
            }

            // Instantiate and check each capability pattern.
            let mut required_delta = Delta::default();
            for (cap_pat, arg_var) in fn_def.caps.iter().zip(array_args.iter()) {
                // Substitute indices in the capability pattern.
                let mut instantiated_cap = Cap::default();
                if let Some(uniq_region) = &cap_pat.uniq {
                    instantiated_cap.uniq = substitute_region(uniq_region, &subst_map);
                }
                if let Some(shrd_region) = &cap_pat.shrd {
                    instantiated_cap.shrd = substitute_region(shrd_region, &subst_map);
                }

                required_delta.0.insert(arg_var.0.clone(), instantiated_cap);
            }

            // Check that we have sufficient capabilities.
            if !ctx.logic.delta_leq(&ctx.phi, &required_delta, &ctx.delta) {
                return Err(TypeError::InsufficientCapability {
                    array: format!("function call to {}", func.0),
                    region: format!("{:?}", required_delta),
                });
            }

            // If not fenced, consume the capabilities.
            if !*fence {
                ctx.delta = ctx
                    .logic
                    .delta_diff(&ctx.phi, &ctx.delta, &required_delta)
                    .ok_or_else(|| TypeError::CapabilitySubtractError {
                        array: format!("function call to {}", func.0),
                    })?;
            }

            // Bind return variables. For now assume single return value.
            if vars.len() != 1 {
                return Err(TypeError::InvalidOp {
                    op: format!(
                        "function call to {} has wrong number of return bindings",
                        func.0
                    ),
                });
            }
            ctx.gamma.insert(vars[0].clone(), fn_def.returns.clone());
            ctx.bool_facts.remove(&vars[0].0);
            log_after_statement(ctx, stmt);
            Ok(())
        }
    }
}

/// Check a tail expression and return its type.
fn check_tail(ctx: &mut Ctx, tail: &Tail, registry: &FnRegistry) -> Result<Ty, TypeError> {
    match tail {
        Tail::RetVar(var) => ctx.gamma.get(var),
        Tail::IfElse {
            cond,
            then_e,
            else_e,
        } => {
            // Condition must be boolean.
            let cond_ty = ctx.gamma.get(cond)?;
            if !matches!(cond_ty, Ty::Bool) {
                return Err(TypeError::InvalidOp {
                    op: "if condition type".into(),
                });
            }
            // Save contexts for both branches.
            let mut ctx_th = Ctx {
                gamma: ctx.gamma.clone(),
                delta: ctx.delta.clone(),
                phi: ctx.phi.clone(),
                bool_facts: ctx.bool_facts.clone(),
                logic: ctx.logic,
                verbose: ctx.verbose,
            };
            // Add the assumption that cond is true in the then branch.
            if let Some(fact) = ctx.bool_facts.get(&cond.0) {
                push_atom(&mut ctx_th.phi, fact.when_true.clone());
            }

            let mut ctx_el = Ctx {
                gamma: ctx.gamma.clone(),
                delta: ctx.delta.clone(),
                phi: ctx.phi.clone(),
                bool_facts: ctx.bool_facts.clone(),
                logic: ctx.logic,
                verbose: ctx.verbose,
            };
            if let Some(fact) = ctx.bool_facts.get(&cond.0) {
                if let Some(neg) = &fact.when_false {
                    push_atom(&mut ctx_el.phi, neg.clone());
                }
            }
            // Type check both branches, allowing them to infer their return types.
            let ty_then = infer_expr_type(&mut ctx_th, then_e, registry)?;
            let ty_else = infer_expr_type(&mut ctx_el, else_e, registry)?;
            if ty_then != ty_else {
                return Err(TypeError::TypeMismatch {
                    expected: TypeError::type_name(&ty_then),
                    found: TypeError::type_name(&ty_else),
                });
            }
            Ok(ty_then)
        }
        Tail::TailCall { func, args } => {
            // Look up function definition.
            let fn_def = registry
                .get(func)
                .ok_or_else(|| TypeError::UndefinedFunction(func.0.clone()))?;

            // Check that args match parameter types (value parameters only, not arrays).
            let value_params: Vec<_> = fn_def
                .params
                .iter()
                .filter(|(_, ty)| !matches!(ty, Ty::RefShrd { .. } | Ty::RefUniq { .. }))
                .collect();
            let array_params: Vec<_> = fn_def
                .params
                .iter()
                .filter(|(_, ty)| matches!(ty, Ty::RefShrd { .. } | Ty::RefUniq { .. }))
                .collect();

            // Build substitution map for indices (param names -> arg vars).
            let mut subst_map = std::collections::BTreeMap::new();

            // Check value parameters and build substitution.
            let expected_value_args = value_params.len();
            if args.len() < expected_value_args {
                return Err(TypeError::InvalidOp {
                    op: format!("tail call to {} has too few arguments", func.0),
                });
            }
            for (i, (param_var, param_ty)) in value_params.iter().enumerate() {
                let arg_var = &args[i];
                let arg_ty = ctx.gamma.get(arg_var)?;
                if arg_ty != *param_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: TypeError::type_name(param_ty),
                        found: TypeError::type_name(&arg_ty),
                    });
                }
                // Record substitution for index expressions.
                subst_map.insert(param_var.0.clone(), arg_var.0.clone());
            }

            // Check array arguments and their capabilities.
            let array_args = &args[expected_value_args..];
            if array_args.len() != array_params.len() {
                return Err(TypeError::InvalidOp {
                    op: format!(
                        "tail call to {} has wrong number of array arguments",
                        func.0
                    ),
                });
            }

            // Instantiate and check each capability pattern.
            let mut required_delta = Delta::default();
            for (cap_pat, arg_var) in fn_def.caps.iter().zip(array_args.iter()) {
                // Substitute indices in the capability pattern.
                let mut instantiated_cap = Cap::default();
                if let Some(uniq_region) = &cap_pat.uniq {
                    instantiated_cap.uniq = substitute_region(uniq_region, &subst_map);
                }
                if let Some(shrd_region) = &cap_pat.shrd {
                    instantiated_cap.shrd = substitute_region(shrd_region, &subst_map);
                }

                required_delta.0.insert(arg_var.0.clone(), instantiated_cap);
            }

            // Check that we have sufficient capabilities.
            if !ctx.logic.delta_leq(&ctx.phi, &required_delta, &ctx.delta) {
                return Err(TypeError::InsufficientCapability {
                    array: format!("tail call to {}", func.0),
                    region: format!("{:?}", required_delta),
                });
            }

            // Tail calls don't consume (the caller's postcondition must match callee's precondition).
            // Return the function's return type.
            if ctx.verbose {
                println!("Tail call to {} verified", func.0);
                print_context_contents(ctx);
            }
            Ok(fn_def.returns.clone())
        }
    }
}
