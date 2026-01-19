use dfx::logic::semantic::solver::{Atom, Idx, Phi, PhiSolver, RealExpr, SmtSolver};

fn idx_var(name: &str) -> Idx {
    Idx::Var(name.to_string())
}

fn idx_const(value: i64) -> Idx {
    Idx::Const(value)
}

fn idx_add(lhs: Idx, rhs: Idx) -> Idx {
    Idx::Add(Box::new(lhs), Box::new(rhs))
}

fn real_var(name: &str) -> RealExpr {
    RealExpr::Var(name.to_string())
}

#[test]
fn entails_infers_integer_equalities() {
    let solver = SmtSolver::new();

    let mut ctx = Phi::new();
    ctx.push(Atom::Eq(idx_var("x"), idx_const(4)));
    ctx.push(Atom::Eq(idx_var("y"), idx_add(idx_var("x"), idx_const(1))));

    assert!(solver.entails(&ctx, &Atom::Eq(idx_var("y"), idx_const(5))));
    assert!(!solver.entails(&ctx, &Atom::Lt(idx_var("y"), idx_const(5)),));
}

#[test]
fn entails_handles_real_arithmetic() {
    let solver = SmtSolver::new();

    let mut ctx = Phi::new();
    ctx.push(Atom::RealEq(real_var("a"), real_var("b")));
    ctx.push(Atom::RealEq(
        real_var("c"),
        RealExpr::sum(real_var("a"), real_var("b")),
    ));

    assert!(solver.entails(
        &ctx,
        &Atom::RealEq(real_var("c"), RealExpr::sum(real_var("a"), real_var("a")),),
    ));
    assert!(!solver.entails(
        &ctx,
        &Atom::RealLt(real_var("c"), RealExpr::sum(real_var("a"), real_var("a")),),
    ));
}

#[test]
fn entails_reasoning_over_boolean_connectives() {
    let solver = SmtSolver::new();

    let mut ctx = Phi::new();
    ctx.push(Atom::And(
        Box::new(Atom::BoolVar("p".to_string())),
        Box::new(Atom::Implies(
            Box::new(Atom::BoolVar("p".to_string())),
            Box::new(Atom::BoolVar("q".to_string())),
        )),
    ));

    assert!(solver.entails(&ctx, &Atom::BoolVar("q".to_string())));
    assert!(!solver.entails(&ctx, &Atom::Not(Box::new(Atom::BoolVar("q".to_string()))),));
}
