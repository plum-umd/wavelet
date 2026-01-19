//! The core type checking logic for the restricted language.

use std::collections::BTreeMap;
use std::fmt;

use crate::env::{Ctx, FnRegistry};
use crate::error::TypeError;
use crate::ir::{Expr, FnDef, Op, Program, Signedness, Stmt, Tail, Ty, Val, Var};
use crate::logic::CapabilityLogic;
use crate::logic::cap::{Cap, Delta, RegionModel};
use crate::logic::region::Region;
use crate::logic::semantic::Interval;
use crate::logic::semantic::solver::{Atom, Idx, Phi};

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
        Idx::Mul(a, b) => Idx::Mul(
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
        let new_hi = substitute_idx(&interval.hi, subst);
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
    /// When true, log SMT queries issued to Z3.
    pub log_solver_queries: bool,
}

fn render_idx(idx: &Idx) -> String {
    match idx {
        Idx::Const(n) => n.to_string(),
        Idx::Var(v) => v.clone(),
        Idx::Add(a, b) => format!("({} + {})", render_idx(a), render_idx(b)),
        Idx::Sub(a, b) => format!("({} - {})", render_idx(a), render_idx(b)),
        Idx::Mul(a, b) => format!("({} * {})", render_idx(a), render_idx(b)),
    }
}

fn render_atom(atom: &Atom) -> String {
    match atom {
        Atom::Le(a, b) => format!("{} <= {}", render_idx(a), render_idx(b)),
        Atom::Lt(a, b) => format!("{} < {}", render_idx(a), render_idx(b)),
        Atom::Eq(a, b) => format!("{} == {}", render_idx(a), render_idx(b)),
        Atom::RealLe(_, _) | Atom::RealLt(_, _) | Atom::RealEq(_, _) => {
            // Real atoms are not expected in this context
            panic!("Real atoms are not supported in render_atom")
        }
        Atom::BoolVar(name) => name.clone(),
        Atom::And(lhs, rhs) => format!("({}) && ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Or(lhs, rhs) => format!("({}) || ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Implies(lhs, rhs) => format!("({}) => ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Not(inner) => format!("!({})", render_atom(inner)),
    }
}

fn bool_atom(name: &str) -> Atom {
    Atom::BoolVar(name.to_string())
}

fn implies(lhs: Atom, rhs: Atom) -> Atom {
    Atom::Implies(Box::new(lhs), Box::new(rhs))
}

fn and(lhs: Atom, rhs: Atom) -> Atom {
    Atom::And(Box::new(lhs), Box::new(rhs))
}

fn or(lhs: Atom, rhs: Atom) -> Atom {
    Atom::Or(Box::new(lhs), Box::new(rhs))
}

fn not(atom: Atom) -> Atom {
    Atom::Not(Box::new(atom))
}

fn combine_signedness(a: Signedness, b: Signedness) -> Signedness {
    match (a, b) {
        (Signedness::Unsigned, Signedness::Unsigned) => Signedness::Unsigned,
        _ => Signedness::Signed,
    }
}

impl<'logic, L: CapabilityLogic> Ctx<'logic, L>
where
    L::Region: RegionModel,
{
    fn bind_var(&mut self, var: &Var, ty: Ty) {
        if let Ty::Int(Signedness::Unsigned) = ty {
            self.phi
                .push(Atom::Le(Idx::Const(0), Idx::Var(var.0.clone())));
        }
        self.gamma.insert(var.clone(), ty);
    }

    fn record_initial_delta(&mut self) {
        self.initial_delta = self.delta.clone();
    }

    fn restore_initial_delta(&mut self) {
        self.delta = self.initial_delta.clone();
    }

    fn ensure_literal_binding(&mut self, var: &Var) -> Result<(), TypeError> {
        if self.gamma.0.contains_key(&var.0) {
            return Ok(());
        }
        // Special case for unit literal (rare, should be handled by LetVal now)
        if var.0 == "_unit_literal" || var.0 == "_unit_ret" {
            self.bind_var(var, Ty::Unit);
            return Ok(());
        }
        Err(TypeError::UndeclaredVar(var.0.clone()))
    }

    fn ty_of(&mut self, var: &Var) -> Result<Ty, TypeError> {
        if !self.gamma.0.contains_key(&var.0) {
            self.ensure_literal_binding(var)?;
        }
        self.gamma.get(var)
    }
}

fn render_cap<L: CapabilityLogic>(logic: &L, phi: &Phi, cap: &Cap<L::Region>) -> String
where
    L::Region: RegionModel,
{
    let solver = logic.solver();
    let shrd_empty = cap.shrd.is_empty(phi, solver);
    let uniq_empty = cap.uniq.is_empty(phi, solver);
    match (shrd_empty, uniq_empty) {
        (true, true) => "<empty>".to_string(),
        (false, true) => format!("shrd: {}", cap.shrd.display_with(phi, solver)),
        (true, false) => format!("uniq: {}", cap.uniq.display_with(phi, solver)),
        (false, false) => format!(
            "shrd: {}; uniq: {}",
            cap.shrd.display_with(phi, solver),
            cap.uniq.display_with(phi, solver)
        ),
    }
}

fn display_cap_with<'a, L: CapabilityLogic>(
    logic: &'a L,
    phi: &'a Phi,
    cap: &'a Cap<L::Region>,
) -> CapDisplay<'a, L>
where
    L::Region: RegionModel,
{
    CapDisplay { logic, phi, cap }
}

fn display_delta_with<'a, L: CapabilityLogic>(
    logic: &'a L,
    phi: &'a Phi,
    delta: &'a Delta<L::Region>,
) -> DeltaDisplay<'a, L>
where
    L::Region: RegionModel,
{
    DeltaDisplay { logic, phi, delta }
}

struct CapDisplay<'a, L: CapabilityLogic>
where
    L::Region: RegionModel,
{
    logic: &'a L,
    phi: &'a Phi,
    cap: &'a Cap<L::Region>,
}

impl<'a, L: CapabilityLogic> fmt::Display for CapDisplay<'a, L>
where
    L::Region: RegionModel,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", render_cap(self.logic, self.phi, self.cap))
    }
}

struct DeltaDisplay<'a, L: CapabilityLogic>
where
    L::Region: RegionModel,
{
    logic: &'a L,
    phi: &'a Phi,
    delta: &'a Delta<L::Region>,
}

impl<'a, L: CapabilityLogic> fmt::Display for DeltaDisplay<'a, L>
where
    L::Region: RegionModel,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.delta.0.is_empty() {
            return write!(f, "<empty>");
        }
        let mut first = true;
        write!(f, "{{")?;
        for (name, cap) in &self.delta.0 {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}: {}", name, render_cap(self.logic, self.phi, cap))?;
        }
        write!(f, "}}")
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
        Op::Not => format!("{} = !{}", vars[1].0, vars[0].0),
        Op::BitAnd => format!("{} = {} & {}", vars[2].0, vars[0].0, vars[1].0),
        Op::BitOr => format!("{} = {} | {}", vars[2].0, vars[0].0, vars[1].0),
        Op::BitXor => format!("{} = {} ^ {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Shl => format!("{} = {} << {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Shr => format!("{} = {} >> {}", vars[2].0, vars[0].0, vars[1].0),
        Op::LessThan => format!("{} = {} < {}", vars[2].0, vars[0].0, vars[1].0),
        Op::LessEqual => format!("{} = {} <= {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Equal => format!("{} = {} == {}", vars[2].0, vars[0].0, vars[1].0),
        Op::NotEqual => format!("{} = {} != {}", vars[2].0, vars[0].0, vars[1].0),
        Op::Load { array, index, len } => {
            format!(
                "{} = {}[{}] (len {})",
                vars[0].0,
                array.0,
                index.0,
                render_array_len(len)
            )
        }
        Op::Store {
            array,
            index,
            value,
            len,
        } => {
            format!(
                "store {} -> {}[{}] (len {})",
                value.0,
                array.0,
                index.0,
                render_array_len(len)
            )
        }
    }
}

fn render_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::LetVal { var, val, fence } => {
            let mut msg = format!("let {} = {}", var.0, render_val(val));
            if *fence {
                msg.push_str(" [fenced]");
            }
            msg
        }
        Stmt::LetOp { vars, op, fence } => {
            let mut msg = render_op(op, vars);
            if *fence {
                msg.push_str(" [fenced]");
            }
            msg
        }
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

fn trace_context<L: CapabilityLogic>(ctx: &Ctx<L>, stage: &str)
where
    L::Region: RegionModel,
{
    if !ctx.verbose {
        return;
    }

    println!("\n=== {} ===", stage);
    print_context_contents(ctx);
}

fn print_context_contents<L: CapabilityLogic>(ctx: &Ctx<L>)
where
    L::Region: RegionModel,
{
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
            println!("  {}: {}", name, render_cap(ctx.logic, &ctx.phi, cap));
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

    println!();
}

// Optionally restore the initial capability environment (if fenced)
fn finalize_statement<L: CapabilityLogic>(ctx: &mut Ctx<L>, stmt: &Stmt)
where
    L::Region: RegionModel,
{
    let fenced = matches!(
        stmt,
        Stmt::LetVal { fence: true, .. }
            | Stmt::LetOp { fence: true, .. }
            | Stmt::LetCall { fence: true, .. }
    );

    if fenced {
        ctx.restore_initial_delta();
    }

    if ctx.verbose {
        println!("After {}:", render_stmt(stmt));
        print_context_contents(ctx);
    }
}

/// Check an entire program with the supplied options.
pub fn check_program_with_options<L: CapabilityLogic>(
    prog: &Program,
    logic: &L,
    options: CheckOptions,
) -> Result<(), TypeError>
where
    L::Region: RegionModel,
{
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
pub fn check_program<L: CapabilityLogic>(prog: &Program, logic: &L) -> Result<(), TypeError>
where
    L::Region: RegionModel,
{
    check_program_with_options(prog, logic, CheckOptions::default())
}

/// Check a single function definition.
pub fn check_fn<L: CapabilityLogic>(
    def: &FnDef,
    registry: &FnRegistry,
    logic: &L,
) -> Result<(), TypeError>
where
    L::Region: RegionModel,
{
    check_fn_with_options(def, registry, logic, CheckOptions::default())
}

/// Check a single function definition with explicit options.
pub fn check_fn_with_options<L: CapabilityLogic>(
    def: &FnDef,
    registry: &FnRegistry,
    logic: &L,
    options: CheckOptions,
) -> Result<(), TypeError>
where
    L::Region: RegionModel,
{
    // Initialise context with parameter types.
    logic.set_query_logging(options.log_solver_queries);
    let mut ctx = Ctx::new(logic, options.verbose);
    for (var, ty) in &def.params {
        ctx.bind_var(var, ty.clone());
    }
    // Initialise capability environment from the function’s cap pattern.
    for cap_pat in &def.caps {
        let cap = cap_pat.initialize::<L::Region>();
        ctx.delta.0.insert(cap_pat.array.clone(), cap);
    }
    ctx.record_initial_delta();
    trace_context(&ctx, "Initial context after parameter and capability setup");

    // Check body.
    let result = check_expr(&mut ctx, &def.body, &def.returns, registry);
    if result.is_ok() {
        trace_context(&ctx, "Context after function body");
    }
    result
}

/// Check an expression and ensure it produces a value of the expected type.
fn check_expr<L: CapabilityLogic>(
    ctx: &mut Ctx<L>,
    expr: &Expr,
    expected: &Ty,
    registry: &FnRegistry,
) -> Result<(), TypeError>
where
    L::Region: RegionModel,
{
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
fn infer_expr_type<L: CapabilityLogic>(
    ctx: &mut Ctx<L>,
    expr: &Expr,
    registry: &FnRegistry,
) -> Result<Ty, TypeError>
where
    L::Region: RegionModel,
{
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
fn check_stmt<L: CapabilityLogic>(
    ctx: &mut Ctx<L>,
    stmt: &Stmt,
    registry: &FnRegistry,
) -> Result<(), TypeError>
where
    L::Region: RegionModel,
{
    match stmt {
        Stmt::LetVal { var, val, .. } => {
            // Determine literal type and bind it.
            let ty = match val {
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
            ctx.bind_var(var, ty);
            match val {
                Val::Int(n) => ctx
                    .phi
                    .push(Atom::Eq(Idx::Var(var.0.clone()), Idx::Const(*n))),
                Val::Bool(true) => ctx.phi.push(bool_atom(&var.0)),
                Val::Bool(false) => ctx.phi.push(not(bool_atom(&var.0))),
                Val::Unit => {}
            }
            finalize_statement(ctx, stmt);
            Ok(())
        }
        Stmt::LetOp { vars, op, fence } => {
            let fenced = *fence;
            match op {
                Op::Add | Op::Sub | Op::Mul | Op::Div => {
                    // Binary integer arithmetic.  Expect two input vars and one output.
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    let x_sign = x_ty.signedness().unwrap();
                    let y_sign = y_ty.signedness().unwrap();
                    let result_sign = combine_signedness(x_sign, y_sign);
                    // Add fact to Phi for Add/Sub/Mul operations.
                    let x_idx = Idx::Var(vars[0].0.clone());
                    let y_idx = Idx::Var(vars[1].0.clone());
                    let result_idx = Idx::Var(vars[2].0.clone());
                    let rhs = match op {
                        Op::Add => Idx::Add(Box::new(x_idx), Box::new(y_idx)),
                        Op::Sub => Idx::Sub(Box::new(x_idx), Box::new(y_idx)),
                        Op::Mul => Idx::Mul(Box::new(x_idx), Box::new(y_idx)),
                        _ => result_idx.clone(),
                    };
                    if !matches!(op, Op::Div) {
                        ctx.phi.push(Atom::Eq(result_idx, rhs));
                    }
                    ctx.bind_var(&vars[2], Ty::Int(result_sign));
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::And => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    if !matches!(x_ty, Ty::Bool) || !matches!(y_ty, Ty::Bool) {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.bind_var(&vars[2], Ty::Bool);
                    let lhs_atom = bool_atom(&vars[0].0);
                    let rhs_atom = bool_atom(&vars[1].0);
                    let res_atom = bool_atom(&vars[2].0);
                    let conjunction = and(lhs_atom.clone(), rhs_atom.clone());
                    ctx.phi.push(implies(res_atom.clone(), conjunction.clone()));
                    ctx.phi.push(implies(conjunction, res_atom));
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::Or => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    if !matches!(x_ty, Ty::Bool) || !matches!(y_ty, Ty::Bool) {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.bind_var(&vars[2], Ty::Bool);
                    let lhs_atom = bool_atom(&vars[0].0);
                    let rhs_atom = bool_atom(&vars[1].0);
                    let res_atom = bool_atom(&vars[2].0);
                    let disjunction = or(lhs_atom.clone(), rhs_atom.clone());
                    ctx.phi.push(implies(res_atom.clone(), disjunction.clone()));
                    ctx.phi.push(implies(disjunction, res_atom));
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::Not => {
                    if vars.len() != 2 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    if !matches!(x_ty, Ty::Bool) {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.bind_var(&vars[1], Ty::Bool);
                    let input_atom = bool_atom(&vars[0].0);
                    let res_atom = bool_atom(&vars[1].0);
                    let negation = not(input_atom.clone());
                    ctx.phi.push(implies(res_atom.clone(), negation.clone()));
                    ctx.phi.push(implies(negation, res_atom));
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::BitAnd | Op::BitOr | Op::BitXor => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    if !x_ty.is_int() || !y_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_sign = x_ty.signedness().unwrap();
                    let y_sign = y_ty.signedness().unwrap();
                    let result_sign = combine_signedness(x_sign, y_sign);
                    ctx.bind_var(&vars[2], Ty::Int(result_sign));
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::Shl | Op::Shr => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    if !x_ty.is_int() || !y_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_sign = x_ty.signedness().unwrap();
                    ctx.bind_var(&vars[2], Ty::Int(x_sign));
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::LessThan | Op::LessEqual => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    if !x_ty.is_int() || !y_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    // Record the comparison as a fact in Phi.
                    let x_idx = Idx::Var(vars[0].0.clone());
                    let y_idx = Idx::Var(vars[1].0.clone());
                    let comparison = match op {
                        Op::LessThan => Atom::Lt(x_idx, y_idx),
                        Op::LessEqual => Atom::Le(x_idx, y_idx),
                        _ => unreachable!(),
                    };
                    let result_atom = bool_atom(&vars[2].0);
                    ctx.phi
                        .push(implies(result_atom.clone(), comparison.clone()));
                    ctx.phi
                        .push(implies(not(result_atom.clone()), not(comparison)));
                    ctx.bind_var(&vars[2], Ty::Bool);
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::Equal | Op::NotEqual => {
                    if vars.len() != 3 {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    let x_ty = ctx.ty_of(&vars[0])?;
                    let y_ty = ctx.ty_of(&vars[1])?;
                    // Allow comparison between integers of different signedness
                    // or exact type equality for other types
                    let types_compatible = match (&x_ty, &y_ty) {
                        (Ty::Int(_), Ty::Int(_)) => true,
                        _ => x_ty == y_ty,
                    };
                    if !types_compatible {
                        return Err(TypeError::InvalidOp {
                            op: format!("{:?}", op),
                        });
                    }
                    ctx.bind_var(&vars[2], Ty::Bool);
                    let result_atom = bool_atom(&vars[2].0);
                    match x_ty {
                        Ty::Int(_) => match op {
                            Op::Equal => {
                                let eq_atom = Atom::Eq(
                                    Idx::Var(vars[0].0.clone()),
                                    Idx::Var(vars[1].0.clone()),
                                );
                                ctx.phi.push(implies(result_atom.clone(), eq_atom.clone()));
                                ctx.phi
                                    .push(implies(not(result_atom.clone()), not(eq_atom)));
                            }
                            Op::NotEqual => {
                                let eq_atom = Atom::Eq(
                                    Idx::Var(vars[0].0.clone()),
                                    Idx::Var(vars[1].0.clone()),
                                );
                                ctx.phi
                                    .push(implies(result_atom.clone(), not(eq_atom.clone())));
                                ctx.phi.push(implies(not(result_atom.clone()), eq_atom));
                            }
                            _ => unreachable!(),
                        },
                        Ty::Bool => match op {
                            Op::Equal => {
                                let lhs_atom = bool_atom(&vars[0].0);
                                let rhs_atom = bool_atom(&vars[1].0);
                                let both_true = and(lhs_atom.clone(), rhs_atom.clone());
                                let both_false = and(not(lhs_atom.clone()), not(rhs_atom.clone()));
                                let eq_formula = or(both_true, both_false);
                                ctx.phi
                                    .push(implies(result_atom.clone(), eq_formula.clone()));
                                ctx.phi.push(implies(eq_formula, result_atom));
                            }
                            Op::NotEqual => {
                                let lhs_atom = bool_atom(&vars[0].0);
                                let rhs_atom = bool_atom(&vars[1].0);
                                let lhs_true_rhs_false =
                                    and(lhs_atom.clone(), not(rhs_atom.clone()));
                                let lhs_false_rhs_true =
                                    and(not(lhs_atom.clone()), rhs_atom.clone());
                                let neq_formula = or(lhs_true_rhs_false, lhs_false_rhs_true);
                                ctx.phi
                                    .push(implies(result_atom.clone(), neq_formula.clone()));
                                ctx.phi.push(implies(neq_formula, result_atom));
                            }
                            _ => unreachable!(),
                        },
                        _ => {}
                    }
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::Load { array, index, len } => {
                    // For a load we expect exactly one destination variable.
                    if vars.len() != 1 {
                        return Err(TypeError::InvalidOp {
                            op: "load destination arity".into(),
                        });
                    }
                    // Index must be int.
                    let idx_ty = ctx.ty_of(index)?;
                    if !idx_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: "load index type".into(),
                        });
                    }
                    // Array must be a reference to the correct length.
                    let arr_ty = ctx.ty_of(array)?;
                    let (arr_len, elem_ty) = match arr_ty {
                        Ty::RefShrd { elem, len } | Ty::RefUniq { elem, len } => {
                            (len.clone(), elem.as_ref().clone())
                        }
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
                    let mut req_cap = Cap::<L::Region>::default();
                    req_cap.shrd = <L::Region as RegionModel>::from_region(&region);
                    let arr_name = &array.0;
                    let have_cap = ctx.delta.0.get(arr_name).cloned().unwrap_or_default();
                    if !ctx.logic.cap_leq(&ctx.phi, &req_cap, &have_cap) {
                        return Err(TypeError::InsufficientCapability {
                            array: arr_name.clone(),
                            required: format!(
                                "{}",
                                display_cap_with(ctx.logic, &ctx.phi, &req_cap)
                            ),
                            available: format!(
                                "{}",
                                display_cap_with(ctx.logic, &ctx.phi, &have_cap)
                            ),
                        });
                    }
                    if !fenced {
                        let mut delta_req = Delta::<L::Region>::default();
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
                    ctx.bind_var(dest, elem_ty);
                    finalize_statement(ctx, stmt);
                    Ok(())
                }
                Op::Store {
                    array,
                    index,
                    value,
                    len,
                } => {
                    // For a store we expect no destination variables.
                    if !vars.is_empty() {
                        return Err(TypeError::InvalidOp {
                            op: "store destination arity".into(),
                        });
                    }
                    // Types of index and value.
                    let idx_ty = ctx.ty_of(index)?;
                    if !idx_ty.is_int() {
                        return Err(TypeError::InvalidOp {
                            op: "store index type".into(),
                        });
                    }
                    let arr_ty = ctx.ty_of(array)?;
                    let (arr_len, elem_ty) = match arr_ty {
                        Ty::RefUniq { elem, len } | Ty::RefShrd { elem, len } => {
                            (len.clone(), elem.as_ref().clone())
                        }
                        _ => {
                            return Err(TypeError::InvalidOp {
                                op: "store non array".into(),
                            });
                        }
                    };
                    let val_ty = ctx.ty_of(value)?;
                    if val_ty != elem_ty {
                        match (&val_ty, &elem_ty) {
                            (Ty::Int(val_sign), Ty::Int(elem_sign))
                                if combine_signedness(*val_sign, *elem_sign) == *elem_sign => {}
                            _ => {
                                return Err(TypeError::InvalidOp {
                                    op: "store value type".into(),
                                });
                            }
                        }
                    }
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
                    let mut req_cap = Cap::<L::Region>::default();
                    req_cap.uniq = <L::Region as RegionModel>::from_region(&region);
                    let arr_name = &array.0;
                    let have_cap = ctx.delta.0.get(arr_name).cloned().unwrap_or_default();
                    if !ctx.logic.cap_leq(&ctx.phi, &req_cap, &have_cap) {
                        return Err(TypeError::InsufficientCapability {
                            array: arr_name.clone(),
                            required: format!(
                                "{}",
                                display_cap_with(ctx.logic, &ctx.phi, &req_cap)
                            ),
                            available: format!(
                                "{}",
                                display_cap_with(ctx.logic, &ctx.phi, &have_cap)
                            ),
                        });
                    }
                    if !fenced {
                        let mut delta_req = Delta::<L::Region>::default();
                        delta_req.0.insert(arr_name.clone(), req_cap.clone());
                        ctx.delta = ctx
                            .logic
                            .delta_diff(&ctx.phi, &ctx.delta, &delta_req)
                            .ok_or_else(|| TypeError::CapabilitySubtractError {
                                array: arr_name.clone(),
                            })?;
                    }
                    finalize_statement(ctx, stmt);
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
                let mut arg_ty = ctx.ty_of(arg_var)?;
                if arg_ty != *param_ty {
                    // Allow integer type coercion for literals or between signed/unsigned
                    let both_int = matches!(arg_ty, Ty::Int(_)) && matches!(param_ty, Ty::Int(_));
                    if both_int {
                        // If it's a literal binding, rebind it to the expected type
                        if arg_var.0.starts_with("_lit_") {
                            ctx.bind_var(arg_var, param_ty.clone());
                            arg_ty = param_ty.clone();
                        } else {
                            // For non-literal integers, allow implicit conversion between signed/unsigned
                            // This handles cases like `let x = 0; f(x)` where f expects i32
                            arg_ty = param_ty.clone();
                        }
                    }
                    if arg_ty != *param_ty {
                        return Err(TypeError::TypeMismatch {
                            expected: TypeError::type_name(param_ty),
                            found: TypeError::type_name(&arg_ty),
                        });
                    }
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
            let mut required_delta = Delta::<L::Region>::default();
            for (cap_pat, arg_var) in fn_def.caps.iter().zip(array_args.iter()) {
                // Substitute indices in the capability pattern.
                let mut instantiated_cap = Cap::<L::Region>::default();
                if let Some(uniq_region) = &cap_pat.uniq {
                    let substituted = substitute_region(uniq_region, &subst_map);
                    instantiated_cap.uniq = <L::Region as RegionModel>::from_region(&substituted);
                }
                if let Some(shrd_region) = &cap_pat.shrd {
                    let substituted = substitute_region(shrd_region, &subst_map);
                    instantiated_cap.shrd = <L::Region as RegionModel>::from_region(&substituted);
                }

                required_delta.0.insert(arg_var.0.clone(), instantiated_cap);
            }

            // Check that we have sufficient capabilities.
            if !ctx.logic.delta_leq(&ctx.phi, &required_delta, &ctx.delta) {
                return Err(TypeError::InsufficientCapability {
                    array: format!("function call to {}", func.0),
                    required: format!(
                        "{}",
                        display_delta_with(ctx.logic, &ctx.phi, &required_delta)
                    ),
                    available: format!("{}", display_delta_with(ctx.logic, &ctx.phi, &ctx.delta)),
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
            ctx.bind_var(&vars[0], fn_def.returns.clone());
            finalize_statement(ctx, stmt);
            Ok(())
        }
    }
}

/// Check a tail expression and return its type.
fn check_tail<L: CapabilityLogic>(
    ctx: &mut Ctx<L>,
    tail: &Tail,
    registry: &FnRegistry,
) -> Result<Ty, TypeError>
where
    L::Region: RegionModel,
{
    match tail {
        Tail::RetVar(var) => ctx.ty_of(var),
        Tail::IfElse {
            cond,
            then_e,
            else_e,
        } => {
            // Condition must be boolean.
            let cond_ty = ctx.ty_of(cond)?;
            if !matches!(cond_ty, Ty::Bool) {
                return Err(TypeError::InvalidOp {
                    op: "if condition type".into(),
                });
            }
            // Save contexts for both branches.
            let mut ctx_th = Ctx {
                gamma: ctx.gamma.clone(),
                delta: ctx.delta.clone(),
                initial_delta: ctx.initial_delta.clone(),
                phi: ctx.phi.clone(),
                logic: ctx.logic,
                verbose: ctx.verbose,
            };
            ctx_th.phi.push(bool_atom(&cond.0));

            let mut ctx_el = Ctx {
                gamma: ctx.gamma.clone(),
                delta: ctx.delta.clone(),
                initial_delta: ctx.initial_delta.clone(),
                phi: ctx.phi.clone(),
                logic: ctx.logic,
                verbose: ctx.verbose,
            };
            ctx_el.phi.push(not(bool_atom(&cond.0)));
            // Type check both branches, allowing them to infer their return types.
            let ty_then = infer_expr_type(&mut ctx_th, then_e, registry)?;
            let ty_else = infer_expr_type(&mut ctx_el, else_e, registry)?;
            if ty_then != ty_else {
                if ty_then.is_int() && ty_else.is_int() {
                    let combined = Ty::Int(combine_signedness(
                        ty_then.signedness().unwrap(),
                        ty_else.signedness().unwrap(),
                    ));
                    return Ok(combined);
                }
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
                let mut arg_ty = ctx.ty_of(arg_var)?;
                if arg_ty != *param_ty {
                    // Allow integer type coercion for literals or between signed/unsigned
                    let both_int = matches!(arg_ty, Ty::Int(_)) && matches!(param_ty, Ty::Int(_));
                    if both_int {
                        // If it's a literal binding, rebind it to the expected type
                        if arg_var.0.starts_with("_lit_") {
                            ctx.bind_var(arg_var, param_ty.clone());
                            arg_ty = param_ty.clone();
                        } else {
                            // For non-literal integers, allow implicit conversion between signed/unsigned
                            // This handles cases like `let x = 0; f(x)` where f expects i32
                            arg_ty = param_ty.clone();
                        }
                    }
                    if arg_ty != *param_ty {
                        return Err(TypeError::TypeMismatch {
                            expected: TypeError::type_name(param_ty),
                            found: TypeError::type_name(&arg_ty),
                        });
                    }
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
            let mut required_delta = Delta::<L::Region>::default();
            for (cap_pat, arg_var) in fn_def.caps.iter().zip(array_args.iter()) {
                // Substitute indices in the capability pattern.
                let mut instantiated_cap = Cap::<L::Region>::default();
                if let Some(uniq_region) = &cap_pat.uniq {
                    let substituted = substitute_region(uniq_region, &subst_map);
                    instantiated_cap.uniq = <L::Region as RegionModel>::from_region(&substituted);
                }
                if let Some(shrd_region) = &cap_pat.shrd {
                    let substituted = substitute_region(shrd_region, &subst_map);
                    instantiated_cap.shrd = <L::Region as RegionModel>::from_region(&substituted);
                }

                required_delta.0.insert(arg_var.0.clone(), instantiated_cap);
            }

            // Check that we have sufficient capabilities.
            if !ctx.logic.delta_leq(&ctx.phi, &required_delta, &ctx.delta) {
                return Err(TypeError::InsufficientCapability {
                    array: format!("tail call to {}", func.0),
                    required: format!(
                        "{}",
                        display_delta_with(ctx.logic, &ctx.phi, &required_delta)
                    ),
                    available: format!("{}", display_delta_with(ctx.logic, &ctx.phi, &ctx.delta)),
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
