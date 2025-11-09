//! Test cases from the specification: sum, zero_out, copy_array, increment, etc.

use dfx::SyntacticLogic;
use dfx::ir::*;
use dfx::logic::syntactic::CapPattern;
use dfx::logic::syntactic::phi::Idx;
use dfx::logic::syntactic::region::Region;
use dfx::*;

/// Helper to create a variable.
fn v(name: &str) -> Var {
    Var(name.to_string())
}

/// Helper to create a function name.
fn fname(name: &str) -> FnName {
    FnName(name.to_string())
}

/// Helper to create an integer type.
fn ty_int() -> Ty {
    Ty::Int
}

/// Helper to create a boolean type.
fn ty_bool() -> Ty {
    Ty::Bool
}

/// Helper to create a unit type.
fn ty_unit() -> Ty {
    Ty::Unit
}

/// Helper to create a shared reference to an array.
fn ty_ref_shrd(elem: Ty, len: usize) -> Ty {
    Ty::RefShrd {
        elem: Box::new(elem),
        len,
    }
}

/// Helper to create a mutable reference to an array.
fn ty_ref_uniq(elem: Ty, len: usize) -> Ty {
    Ty::RefUniq {
        elem: Box::new(elem),
        len,
    }
}

/// Helper to create an index from a variable.
fn idx_var(name: &str) -> Idx {
    Idx::Var(name.to_string())
}

/// Helper to create a constant index.
fn idx_const(n: i64) -> Idx {
    Idx::Const(n)
}

/// Helper to create a region from start to end (half-open interval).
fn region(lo: Idx, hi: Idx) -> Region {
    Region::from_bounded(lo, hi)
}

/// Helper to create a capability pattern with shared access.
fn cap_shrd(array: &str, lo: Idx, hi: Idx) -> CapPattern {
    CapPattern {
        array: array.to_string(),
        uniq: None,
        shrd: Some(Region::from_bounded(lo, hi)),
    }
}

/// Helper to create a capability pattern with unique access.
fn cap_uniq(array: &str, lo: Idx, hi: Idx) -> CapPattern {
    CapPattern {
        array: array.to_string(),
        uniq: Some(Region::from_bounded(lo, hi)),
        shrd: None,
    }
}

/// Helper to create a let-val statement.
fn let_val(var: Var, val: Val) -> Stmt {
    Stmt::LetVal { var, val }
}

/// Helper to create a let-op statement with binary operators.
fn let_op_binary(result: Var, op: Op, x: Var, y: Var) -> Stmt {
    Stmt::LetOp {
        vars: vec![x, y, result],
        op,
    }
}

/// Helper to create a less-than comparison.
fn let_lt(result: Var, x: Var, y: Var) -> Stmt {
    let_op_binary(result, Op::LessThan, x, y)
}

/// Helper to create an addition.
fn let_add(result: Var, x: Var, y: Var) -> Stmt {
    let_op_binary(result, Op::Add, x, y)
}

/// Helper to create a load operation.
fn let_load(result: Var, array: Var, index: Var, len: usize, fence: bool) -> Stmt {
    Stmt::LetOp {
        vars: vec![result],
        op: Op::Load {
            array,
            index,
            len,
            fence,
        },
    }
}

/// Helper to create a store operation (no result variable).
fn let_store(array: Var, index: Var, value: Var, len: usize, fence: bool) -> Stmt {
    Stmt::LetOp {
        vars: vec![],
        op: Op::Store {
            array,
            index,
            value,
            len,
            fence,
        },
    }
}

/// Helper to create a function call.
fn let_call(results: Vec<Var>, func: FnName, args: Vec<Var>, fence: bool) -> Stmt {
    Stmt::LetCall {
        vars: results,
        func,
        args,
        fence,
    }
}

/// Helper to create an if-else expression.
fn if_else(
    cond: Var,
    then_stmts: Vec<Stmt>,
    then_tail: Tail,
    else_stmts: Vec<Stmt>,
    else_tail: Tail,
) -> Tail {
    Tail::IfElse {
        cond,
        then_e: Box::new(Expr {
            stmts: then_stmts,
            tail: then_tail,
        }),
        else_e: Box::new(Expr {
            stmts: else_stmts,
            tail: else_tail,
        }),
    }
}

/// Helper to create a return tail.
fn ret(var: Var) -> Tail {
    Tail::RetVar(var)
}

/// Helper to create a tail call.
fn tail_call(func: FnName, args: Vec<Var>) -> Tail {
    Tail::TailCall { func, args }
}

#[test]
fn test_sum_array() {
    // fn sum<const N: usize>(i: u32, a: u32, A: &[u32; N]@{i..N}) -> u32
    const N: usize = 10;

    let fn_def = FnDef {
        name: fname("sum"),
        params: vec![
            (v("i"), ty_int()),
            (v("a"), ty_int()),
            (v("A"), ty_ref_shrd(ty_int(), N)),
        ],
        caps: vec![cap_shrd("A", idx_var("i"), idx_const(N as i64))],
        returns: ty_int(),
        body: Expr {
            stmts: vec![
                let_val(v("N_const"), Val::Int(N as i64)),
                let_lt(v("c"), v("i"), v("N_const")),
            ],
            tail: if_else(
                v("c"),
                // then branch: load and recurse
                vec![
                    let_load(v("val"), v("A"), v("i"), N, false),
                    let_val(v("one"), Val::Int(1)),
                    let_add(v("j"), v("i"), v("one")),
                    let_add(v("new_a"), v("a"), v("val")),
                ],
                tail_call(fname("sum"), vec![v("j"), v("new_a"), v("A")]),
                // else branch: return a
                vec![],
                ret(v("a")),
            ),
        },
    };

    let mut prog = Program::new();
    prog.add_fn(fn_def);

    let logic = SyntacticLogic::default();
    let result = check_program(&prog, &logic);

    match result {
        Ok(()) => println!("test_sum_array: PASS"),
        Err(e) => panic!("test_sum_array: FAIL - {}", e),
    }
}

#[test]
fn test_zero_out_array() {
    // fn f<const N: usize>(i: u32, A: &mut [u32; N]@{i..N})
    const N: usize = 10;

    let fn_def = FnDef {
        name: fname("f"),
        params: vec![(v("i"), ty_int()), (v("A"), ty_ref_uniq(ty_int(), N))],
        caps: vec![cap_uniq("A", idx_var("i"), idx_const(N as i64))],
        returns: ty_unit(),
        body: Expr {
            stmts: vec![
                let_val(v("N_const"), Val::Int(N as i64)),
                let_lt(v("c"), v("i"), v("N_const")),
            ],
            tail: if_else(
                v("c"),
                // then branch: store and recurse
                vec![
                    let_val(v("zero"), Val::Int(0)),
                    let_store(v("A"), v("i"), v("zero"), N, false),
                    let_val(v("one"), Val::Int(1)),
                    let_add(v("j"), v("i"), v("one")),
                ],
                tail_call(fname("f"), vec![v("j"), v("A")]),
                // else branch: return unit
                vec![let_val(v("unit"), Val::Unit)],
                ret(v("unit")),
            ),
        },
    };

    let mut prog = Program::new();
    prog.add_fn(fn_def);

    let logic = SyntacticLogic::default();
    let result = check_program(&prog, &logic);

    match result {
        Ok(()) => println!("test_zero_out_array: PASS"),
        Err(e) => panic!("test_zero_out_array: FAIL - {}", e),
    }
}

#[test]
fn test_copy_array() {
    // fn copy_array<const N: usize>(i: u32, A: &[u32; N]@{i..N}, B: &mut [u32; N]@{i..N})
    const N: usize = 10;

    let fn_def = FnDef {
        name: fname("copy_array"),
        params: vec![
            (v("i"), ty_int()),
            (v("A"), ty_ref_shrd(ty_int(), N)),
            (v("B"), ty_ref_uniq(ty_int(), N)),
        ],
        caps: vec![
            cap_shrd("A", idx_var("i"), idx_const(N as i64)),
            cap_uniq("B", idx_var("i"), idx_const(N as i64)),
        ],
        returns: ty_unit(),
        body: Expr {
            stmts: vec![
                let_val(v("N_const"), Val::Int(N as i64)),
                let_lt(v("c"), v("i"), v("N_const")),
            ],
            tail: if_else(
                v("c"),
                // then branch: load from A, store to B, and recurse
                vec![
                    let_load(v("val"), v("A"), v("i"), N, false),
                    let_store(v("B"), v("i"), v("val"), N, false),
                    let_val(v("one"), Val::Int(1)),
                    let_add(v("j"), v("i"), v("one")),
                ],
                tail_call(fname("copy_array"), vec![v("j"), v("A"), v("B")]),
                // else branch: return unit
                vec![let_val(v("unit"), Val::Unit)],
                ret(v("unit")),
            ),
        },
    };

    let mut prog = Program::new();
    prog.add_fn(fn_def);

    let logic = SyntacticLogic::default();
    let result = check_program(&prog, &logic);

    match result {
        Ok(()) => println!("test_copy_array: PASS"),
        Err(e) => panic!("test_copy_array: FAIL - {}", e),
    }
}

#[test]
fn test_increment_with_fence() {
    // fn increment<const N: usize>(i: u32, A: &mut [u32; N]@{i..N})
    // This test requires a fence between load and store.
    const N: usize = 10;

    let fn_def = FnDef {
        name: fname("increment"),
        params: vec![(v("i"), ty_int()), (v("A"), ty_ref_uniq(ty_int(), N))],
        caps: vec![cap_uniq("A", idx_var("i"), idx_const(N as i64))],
        returns: ty_unit(),
        body: Expr {
            stmts: vec![
                let_val(v("N_const"), Val::Int(N as i64)),
                let_lt(v("c"), v("i"), v("N_const")),
            ],
            tail: if_else(
                v("c"),
                // then branch: load with fence, store, and recurse
                vec![
                    let_load(v("val"), v("A"), v("i"), N, true), // FENCE!
                    let_val(v("one"), Val::Int(1)),
                    let_add(v("new_val"), v("val"), v("one")),
                    let_store(v("A"), v("i"), v("new_val"), N, false),
                    let_add(v("j"), v("i"), v("one")),
                ],
                tail_call(fname("increment"), vec![v("j"), v("A")]),
                // else branch: return unit
                vec![let_val(v("unit"), Val::Unit)],
                ret(v("unit")),
            ),
        },
    };

    let mut prog = Program::new();
    prog.add_fn(fn_def);

    let logic = SyntacticLogic::default();
    let result = check_program(&prog, &logic);

    match result {
        Ok(()) => println!("test_increment_with_fence: PASS"),
        Err(e) => panic!("test_increment_with_fence: FAIL - {}", e),
    }
}

// More test cases to be added for RAW, WAR, WAW, nn_relu, nn_fc, dmv...
