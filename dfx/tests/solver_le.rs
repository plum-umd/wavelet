use dfx::logic::syntactic::phi::{Atom, BasicSolver, Idx, Phi, PhiSolver};

#[test]
fn le_i_plus_one_leq_i_should_fail() {
    let solver = BasicSolver;
    let mut phi = Phi::new();
    phi.push(Atom::Lt(Idx::Var("i".into()), Idx::Var("N".into())));

    let expr = Atom::Le(
        Idx::Add(Box::new(Idx::Var("i".into())), Box::new(Idx::Const(1))),
        Idx::Var("i".into()),
    );

    assert!(!solver.entails(&phi, &expr));
}
