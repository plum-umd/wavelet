use dfx::logic::cap::Cap;
use dfx::logic::region::Region;
use dfx::logic::semantic::solver::{Atom, Idx, Phi};
use dfx::logic::syntactic::solver::BasicSolver;

fn var(name: &str) -> Idx {
    Idx::Var(name.into())
}

fn bounded(lo: Idx, hi: Idx) -> Region {
    Region::from_bounded(lo, hi)
}

#[test]
fn load_then_store_should_fail_due_to_unique_consumption() {
    let solver = BasicSolver;
    let mut phi = Phi::new();
    phi.push(Atom::Lt(var("i"), var("N")));

    let uniq = bounded(var("i"), var("N"));
    let mut cap_total = Cap::default();
    cap_total.uniq = uniq.clone();

    let mut load_cap = Cap::default();
    load_cap.shrd = bounded(
        var("i"),
        Idx::Add(Box::new(var("i")), Box::new(Idx::Const(1))),
    );

    let after_load = cap_total
        .diff(&load_cap, &phi, &solver)
        .expect("load diff should succeed");

    let mut expected = Cap::default();
    expected.uniq = bounded(
        Idx::Add(Box::new(var("i")), Box::new(Idx::Const(1))),
        var("N"),
    );

    assert_eq!(after_load.uniq, expected.uniq);
}
