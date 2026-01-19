use crate::Val;
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostProgram, GhostStmt, GhostTail, GhostVar};
use crate::ir::{Expr, FnDef, FnName, Op, Program, Stmt, Tail, Var};

/// Synthesize a ghost-level program from the typed IR.
pub fn synthesize_ghost_program(prog: &Program) -> GhostProgram {
    let mut prog = prog.clone();
    prog.desugar_tail_calls();
    prog.eliminate_array_params();
    let mut ghost = GhostProgram::new();
    for def in &prog.defs {
        ghost.add_fn(lower_fn(def));
    }
    ghost
}

fn lower_fn(fn_def: &FnDef) -> GhostFnDef {
    let mut lowerer = FunctionLowerer::new();

    let (ghost_params, initial_ctx) = {
        let sync = GhostVar("p_sync".into());
        let leftover = GhostVar("p_garb".into());
        (
            vec![sync.clone(), leftover.clone()],
            PermCtx::with(vec![sync], vec![leftover]),
        )
    };

    let body = lowerer.lower_expr(&fn_def.body, initial_ctx);

    GhostFnDef {
        name: fn_def.name.clone(),
        params: fn_def.params.clone(),
        ghost_params,
        caps: fn_def.caps.clone(), // Preserve capability patterns
        returns: fn_def.returns.clone(),
        body,
    }
}

#[derive(Clone, Default)]
struct PermCtx {
    sync: Vec<GhostVar>,
    restore: Vec<GhostVar>,
    garb: Vec<GhostVar>,
}

impl PermCtx {
    fn with(sync: Vec<GhostVar>, leftover: Vec<GhostVar>) -> Self {
        Self {
            sync,
            restore: Vec::new(),
            garb: leftover,
        }
    }

    fn sync_inputs(&self) -> Vec<GhostVar> {
        self.sync.clone()
    }

    fn clear_and_get_garb(&mut self) -> Vec<GhostVar> {
        let garb = self.garb.clone();
        // clear garb
        self.garb.clear();
        garb
    }

    fn all_inputs(&self) -> Vec<GhostVar> {
        let mut inputs = self.sync.clone();
        inputs.extend(self.restore.clone());
        inputs.extend(self.garb.clone());
        inputs
    }

    fn move_restore_to_sync(&mut self) {
        if !self.restore.is_empty() {
            self.sync.extend(self.restore.drain(..));
        }
    }

    fn move_restore_to_garb(&mut self) {
        if !self.restore.is_empty() {
            self.garb.extend(self.restore.drain(..));
        }
    }
}

struct FunctionLowerer {
    names: GhostNameGenerator,
}

impl FunctionLowerer {
    fn new() -> Self {
        Self {
            names: GhostNameGenerator::new(1),
        }
    }

    fn lower_expr(&mut self, expr: &Expr, mut ctx: PermCtx) -> GhostExpr {
        let mut stmts = Vec::new();
        for stmt in &expr.stmts {
            self.lower_stmt(stmt, &mut stmts, &mut ctx);
        }
        let tail = self.lower_tail(&expr.tail, &mut stmts, ctx);
        GhostExpr::new(stmts, tail)
    }

    fn lower_stmt(&mut self, stmt: &Stmt, builder: &mut Vec<GhostStmt>, ctx: &mut PermCtx) {
        match stmt {
            Stmt::LetVal { var, val, fence } => self.lower_const(var, val, *fence, builder, ctx),
            Stmt::LetOp { vars, op, fence } => self.lower_op(vars, op, *fence, builder, ctx),
            Stmt::LetCall {
                vars,
                func,
                args,
                fence,
            } => self.lower_call(vars, func, args, *fence, builder, ctx),
        }
    }

    fn lower_tail(&mut self, tail: &Tail, builder: &mut Vec<GhostStmt>, ctx: PermCtx) -> GhostTail {
        match tail {
            Tail::RetVar(var) => {
                let inputs = ctx.all_inputs();
                let (ret_perm, _eps) = self.join_split(builder, inputs);
                GhostTail::Return {
                    value: var.clone(),
                    perm: ret_perm,
                }
            }
            Tail::TailCall { func, args } => {
                let mut ctx = ctx;
                let (need_perm, left_perm) = self.split_sync(builder, &mut ctx);
                // for tail calls, we "garbage collect" any leftover permissions
                ctx.garb.push(left_perm);
                ctx.move_restore_to_garb();

                let (left_perm, _) = self.join_split(builder, ctx.clear_and_get_garb());

                GhostTail::TailCall {
                    func: func.clone(),
                    args: args.clone(),
                    ghost_need: need_perm,
                    ghost_left: left_perm,
                }
            }
            Tail::IfElse {
                cond,
                then_e,
                else_e,
            } => {
                let then_expr = self.lower_expr(then_e, ctx.clone());
                let else_expr = self.lower_expr(else_e, ctx);
                GhostTail::IfElse {
                    cond: cond.clone(),
                    then_expr: Box::new(then_expr),
                    else_expr: Box::new(else_expr),
                }
            }
        }
    }

    fn lower_const(
        &mut self,
        var: &Var,
        val: &Val,
        fenced: bool,
        builder: &mut Vec<GhostStmt>,
        ctx: &mut PermCtx,
    ) {
        let (ghost_in, _) = self.split_sync(builder, ctx);
        let ghost_out = self.fresh();
        builder.push(GhostStmt::Const {
            value: val.clone(),
            output: var.clone(),
            ghost_in,
            ghost_out: ghost_out.clone(),
        });

        // dummy zero token can be dropped
        // ctx.garb.push(ghost_out);
        if fenced {
            ctx.move_restore_to_sync();
        }
    }

    fn lower_op(
        &mut self,
        vars: &[Var],
        op: &Op,
        fenced: bool,
        builder: &mut Vec<GhostStmt>,
        ctx: &mut PermCtx,
    ) {
        match op {
            Op::Load { array, index, .. } => {
                let (ghost_in, _) = self.split_sync(builder, ctx);
                let ghost_out = self.fresh();
                builder.push(GhostStmt::Load {
                    output: vars.first().cloned().expect("load must produce an output"),
                    array: array.clone(),
                    index: index.clone(),
                    ghost_in,
                    ghost_out: ghost_out.clone(),
                });
                ctx.restore.push(ghost_out);
            }
            Op::Store {
                array,
                index,
                value,
                ..
            } => {
                let (ghost_in, _) = self.split_sync(builder, ctx);
                let ghost_out_real = self.fresh();
                let ghost_out_dummy = self.fresh_with_prefix("__store_dummy_");
                builder.push(GhostStmt::Store {
                    array: array.clone(),
                    index: index.clone(),
                    value: value.clone(),
                    ghost_in,
                    ghost_out: (ghost_out_dummy, ghost_out_real.clone()),
                });
                ctx.restore.push(ghost_out_real);
            }
            _ => {
                // NOTE: pureop needs no token and output a zero token
                // let (ghost_in, _) = self.split_sync(builder, ctx);
                let ghost_out = self.fresh();
                builder.push(GhostStmt::Pure {
                    inputs: pure_inputs(vars),
                    output: pure_output(vars),
                    op: op.clone(),
                    ghost_out: ghost_out.clone(),
                });
                // dummy zero token can be dropped
                // ctx.garb.push(ghost_out);
            }
        }
        if fenced {
            ctx.move_restore_to_sync();
        }
    }

    fn lower_call(
        &mut self,
        vars: &[Var],
        func: &FnName,
        args: &[Var],
        fence: bool,
        builder: &mut Vec<GhostStmt>,
        ctx: &mut PermCtx,
    ) {
        let (need_perm, _) = self.split_sync(builder, ctx);

        // a non-tail call might need to GC some of the pending tokens
        // so we "borrow" them into garb first
        ctx.move_restore_to_garb();
        let inputs = ctx.clear_and_get_garb();
        let (left_perm, right_perm) = self.join_split(builder, inputs);
        // then we "return" the left over garbage tokens back to the garbage context
        ctx.garb = vec![right_perm.clone()];

        let ret_perm = self.fresh();
        builder.push(GhostStmt::Call {
            outputs: vars.to_vec(),
            func: func.clone(),
            args: args.to_vec(),
            ghost_need: need_perm.clone(),
            ghost_left: left_perm.clone(),
            ghost_ret: ret_perm.clone(),
        });

        // the returned permission goes to back to restore, as they might be
        // needed later (fences will move them to sync)
        ctx.restore.push(ret_perm);
        if fence {
            ctx.move_restore_to_sync();
        }
    }

    fn split_sync(
        &mut self,
        builder: &mut Vec<GhostStmt>,
        ctx: &mut PermCtx,
    ) -> (GhostVar, GhostVar) {
        let (left, right) = self.join_split(builder, ctx.sync_inputs());
        ctx.sync = vec![right.clone()];
        (left, right)
    }

    fn join_split(
        &mut self,
        builder: &mut Vec<GhostStmt>,
        inputs: Vec<GhostVar>,
    ) -> (GhostVar, GhostVar) {
        let left = self.fresh();
        let right = self.fresh();
        builder.push(GhostStmt::JoinSplit {
            left: left.clone(),
            right: right.clone(),
            inputs,
        });
        (left, right)
    }

    fn fresh(&mut self) -> GhostVar {
        self.names.fresh()
    }

    fn fresh_with_prefix(&mut self, prefix: &str) -> GhostVar {
        self.names.fresh_with_prefix(prefix)
    }
}

struct GhostNameGenerator {
    next: usize,
}

impl GhostNameGenerator {
    fn new(start: usize) -> Self {
        Self { next: start }
    }

    fn fresh(&mut self) -> GhostVar {
        let name = format!("p{}", self.next);
        self.next += 1;
        GhostVar(name)
    }

    fn fresh_with_prefix(&mut self, prefix: &str) -> GhostVar {
        let name = format!("{}{}", prefix, self.next);
        self.next += 1;
        GhostVar(name)
    }
}

// all except the last
fn pure_inputs(vars: &[Var]) -> Vec<Var> {
    vars[..vars.len() - 1].to_vec()
}

fn pure_output(vars: &[Var]) -> Var {
    vars.last().cloned().expect("pure op must have an output")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse_program;
    use std::fs;
    use std::path::Path;

    fn lower_fixture(src: &str, fn_name: &str) -> GhostFnDef {
        let program = parse_program(src).expect("fixture should parse");
        let ghost = synthesize_ghost_program(&program);
        ghost
            .defs
            .into_iter()
            .find(|def| def.name.0 == fn_name)
            .expect("function should be lowered")
    }

    #[test]
    fn lowers_sum() {
        let ghost_fn = lower_fixture(include_str!("../../tests/test_files/sum.rs"), "sum");
        println!("Lowered ghost function:\n{}", ghost_fn);

        assert_eq!(
            ghost_fn.ghost_params,
            vec![GhostVar("p_sync".into()), GhostVar("p_garb".into())]
        );

        assert!(
            ghost_fn.body.stmts.iter().any(|stmt| matches!(
                stmt,
                GhostStmt::Pure {
                    op: Op::LessThan,
                    ..
                }
            )),
            "expected a guard comparison to lower to a pure less-than op"
        );

        let (cond, then_expr, else_expr) = match &ghost_fn.body.tail {
            GhostTail::IfElse {
                cond,
                then_expr,
                else_expr,
            } => (cond, then_expr, else_expr),
            other => panic!("unexpected top-level tail: {other:?}"),
        };

        assert_eq!(cond, &Var("c".into()));

        let has_load = then_expr
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, GhostStmt::Load { .. }));
        assert!(
            has_load,
            "expected lowering to emit a load in the then branch"
        );

        let add_count = then_expr
            .stmts
            .iter()
            .filter(|stmt| matches!(stmt, GhostStmt::Pure { op: Op::Add, .. }))
            .count();
        assert!(
            add_count >= 2,
            "expected two additions in the then branch; found {add_count}"
        );

        match &then_expr.tail {
            GhostTail::TailCall { func, .. } => assert_eq!(func.0, "sum"),
            other => panic!("unexpected then tail: {other:?}"),
        }

        match &else_expr.tail {
            GhostTail::Return { .. } => {}
            other => panic!("unexpected else tail: {other:?}"),
        }
    }

    #[test]
    fn lowers_zero_out() {
        let ghost_fn = lower_fixture(
            include_str!("../../tests/test_files/zero_out.rs"),
            "zero_out",
        );

        println!("Lowered ghost function:\n{}", ghost_fn);

        assert_eq!(
            ghost_fn.ghost_params,
            vec![GhostVar("p_sync".into()), GhostVar("p_garb".into())]
        );

        let (then_expr, else_expr) = match &ghost_fn.body.tail {
            GhostTail::IfElse {
                then_expr,
                else_expr,
                ..
            } => (then_expr, else_expr),
            other => panic!("unexpected top-level tail: {other:?}"),
        };

        let const_count = then_expr
            .stmts
            .iter()
            .filter(|stmt| matches!(stmt, GhostStmt::Const { .. }))
            .count();
        assert!(
            const_count >= 2,
            "expected constants for zero and one; found {const_count}"
        );

        let has_store = then_expr
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, GhostStmt::Store { .. }));
        assert!(
            has_store,
            "expected lowering to emit a store in the then branch"
        );

        match &then_expr.tail {
            GhostTail::TailCall { func, .. } => assert_eq!(func.0, "zero_out"),
            other => panic!("unexpected then tail: {other:?}"),
        }

        match &else_expr.tail {
            GhostTail::Return { .. } => {}
            other => panic!("unexpected else tail: {other:?}"),
        }
    }

    #[test]
    fn lowers_all_fixtures() {
        let fixtures_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("test_files");

        for entry in fs::read_dir(&fixtures_dir).expect("fixtures directory should exist") {
            let entry = entry.expect("fixture dir entry should be readable");
            let path = entry.path();
            if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
                continue;
            }

            let source = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("failed to read {:?}: {err}", path));
            let program = parse_program(&source)
                .unwrap_or_else(|err| panic!("failed to parse {:?}: {err}", path));
            let ghost = synthesize_ghost_program(&program);

            for ghost_fn in ghost.defs {
                println!("Lowered ghost function:\n{}", ghost_fn);
            }
        }
    }

    #[test]
    fn exports_sum_to_json() {
        use crate::ghost::json::export_program_json;

        let ghost = synthesize_ghost_program(
            &parse_program(include_str!("../../tests/test_files/sum.rs"))
                .expect("sum.rs should parse"),
        );

        let json = export_program_json(&ghost).expect("should serialize to JSON");
        println!("Exported JSON:\n{}", json);

        // Verify it's valid JSON
        let parsed: serde_json::Value = serde_json::from_str(&json).expect("should be valid JSON");
        assert!(parsed.get("fns").is_some(), "should have fns field");

        let fns = parsed["fns"].as_array().expect("fns should be an array");
        assert_eq!(fns.len(), 1, "should have exactly one function");

        let sum_fn = &fns[0];
        assert_eq!(sum_fn["name"], "sum");
        assert_eq!(sum_fn["outputs"], 2, "sum should have 2 outputs");

        let params = sum_fn["params"]
            .as_array()
            .expect("params should be an array");
        assert_eq!(
            params.len(),
            5,
            "sum should have 5 parameters (3 regular + 2 ghost, array param A eliminated)"
        );
        assert_eq!(params[0], "i");
        assert_eq!(params[1], "a");
        assert_eq!(params[2], "N");
        assert_eq!(params[3], "p_sync");
        assert_eq!(params[4], "p_garb");

        // Verify body structure
        assert!(
            sum_fn["body"].get("op").is_some(),
            "body should be an op expression"
        );
    }

    #[test]
    fn exports_all_op_types() {
        use crate::ghost::json::export_program_json;

        // Test with a fixture that has more operations
        let ghost = synthesize_ghost_program(
            &parse_program(include_str!("../../tests/test_files/zero_out.rs"))
                .expect("zero_out.rs should parse"),
        );

        let json = export_program_json(&ghost).expect("should serialize to JSON");
        println!(
            "Exported zero_out JSON (first 500 chars):\n{}",
            &json.chars().take(500).collect::<String>()
        );

        // Verify it's valid JSON
        let _parsed: serde_json::Value = serde_json::from_str(&json).expect("should be valid JSON");

        // Check that we have const and store operations in the JSON
        let json_str = json.to_lowercase();
        assert!(json_str.contains("const"), "should contain const operation");
        assert!(json_str.contains("store"), "should contain store operation");
    }
}
