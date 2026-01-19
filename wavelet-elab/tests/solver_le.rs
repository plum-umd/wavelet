use dfx::logic::semantic::solver::{Atom, Idx, Phi, PhiSolver, SmtSolver};

#[test]
fn le_i_plus_one_leq_i_should_fail() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();
    phi.push(Atom::Lt(Idx::Var("i".into()), Idx::Var("N".into())));

    let expr = Atom::Le(
        Idx::Add(Box::new(Idx::Var("i".into())), Box::new(Idx::Const(1))),
        Idx::Var("i".into()),
    );

    assert!(!solver.entails(&phi, &expr));
}
