//! Tests for the symbolic logic and region operations.

use dfx::logic::cap::{Cap, Delta};
use dfx::logic::region::{Interval, Region};
use dfx::logic::semantic::PhiSolver;
use dfx::logic::semantic::solver::{Atom, Idx, Phi};
use dfx::logic::syntactic::solver::BasicSolver;

fn const_idx(n: i64) -> Idx {
    Idx::Const(n)
}

fn var_idx(name: &str) -> Idx {
    Idx::Var(name.into())
}

#[test]
fn test_region_subset_with_equalities() {
    let solver = BasicSolver;
    let mut phi = Phi::new();
    // j = i + 1
    phi.push(Atom::Eq(
        Idx::Var("j".into()),
        Idx::Add(Box::new(Idx::Var("i".into())), Box::new(Idx::Const(1))),
    ));
    // Regions [j..10) and [i..10)
    let r_j = Region::from_bounded(Idx::Var("j".into()), Idx::Const(10));
    let r_i = Region::from_bounded(Idx::Var("i".into()), Idx::Const(10));
    assert!(r_j.is_subregion_of(&r_i, &phi, &solver));
}

#[test]
fn test_region_union_merges_adjacent() {
    let solver = BasicSolver;
    let phi = Phi::new();

    let left = Region::from_bounded(const_idx(0), const_idx(5));
    let right = Region::from_bounded(const_idx(5), const_idx(10));
    let union = left.union(&right, &phi, &solver);

    let expected = Region::from_bounded(const_idx(0), const_idx(10));
    assert_eq!(union, expected);
}

#[test]
fn test_region_diff_half_open_semantics() {
    let solver = BasicSolver;
    let phi = Phi::new();

    let source = Region::from_bounded(const_idx(0), const_idx(10));
    let remove = Region::from_bounded(const_idx(3), const_idx(5));
    let diff = source.diff(&remove, &phi, &solver);

    let expected = Region::from_intervals(vec![
        Interval::bounded(const_idx(0), const_idx(3)),
        Interval::bounded(const_idx(5), const_idx(10)),
    ]);

    assert_eq!(diff, expected);
}

#[test]
fn test_region_diff_removal_exhausts_source() {
    let solver = BasicSolver;
    let phi = Phi::new();

    let source = Region::from_bounded(const_idx(0), const_idx(10));
    let remove = Region::from_bounded(const_idx(0), const_idx(15));
    let diff = source.diff(&remove, &phi, &solver);

    assert_eq!(diff, Region::default());
}

#[test]
fn basic_solver_does_not_entail_unjustified_leq() {
    let solver = BasicSolver;
    let mut phi = Phi::new();

    let one = Idx::Var("one".into());
    phi.push(Atom::Eq(one.clone(), Idx::Const(1)));
    phi.push(Atom::Eq(
        Idx::Var("jp1".into()),
        Idx::Add(Box::new(Idx::Var("j".into())), Box::new(one.clone())),
    ));
    phi.push(Atom::Eq(
        Idx::Var("k".into()),
        Idx::Add(Box::new(Idx::Var("j".into())), Box::new(one.clone())),
    ));

    let lhs = Idx::Add(Box::new(Idx::Var("jp1".into())), Box::new(Idx::Const(1)));
    let rhs = Idx::Var("k".into());
    assert!(!solver.entails(&phi, &Atom::Le(lhs, rhs)));

    let available = Region::from_bounded(
        Idx::Add(Box::new(Idx::Var("jp1".into())), Box::new(Idx::Const(1))),
        Idx::Var("N".into()),
    );
    let required = Region::from_bounded(Idx::Var("k".into()), Idx::Var("N".into()));
    assert!(!required.is_subregion_of(&available, &phi, &solver));
}

#[test]
fn test_region_diff_with_solver_equated_bounds() {
    let solver = BasicSolver;
    let mut phi = Phi::new();

    phi.push(Atom::Eq(var_idx("i"), const_idx(0)));
    phi.push(Atom::Eq(
        var_idx("j"),
        Idx::Add(Box::new(var_idx("i")), Box::new(const_idx(2))),
    ));

    let source = Region::from_bounded(var_idx("i"), const_idx(10));
    let remove = Region::from_bounded(var_idx("j"), const_idx(6));
    let diff = source.diff(&remove, &phi, &solver);

    let expected = Region::from_intervals(vec![
        Interval::bounded(var_idx("i"), var_idx("j")),
        Interval::bounded(const_idx(6), const_idx(10)),
    ]);

    assert_eq!(diff, expected);
}

#[test]
fn test_region_diff_without_solver_proof_keeps_source() {
    let solver = BasicSolver;
    let phi = Phi::new();

    let source = Region::from_bounded(var_idx("i"), const_idx(8));
    let remove = Region::from_bounded(var_idx("j"), const_idx(6));

    let diff = source.diff(&remove, &phi, &solver);

    assert_eq!(diff, source);
}

#[test]
fn test_region_diff_singleton_removal_advances_lower_bound() {
    let solver = BasicSolver;
    let mut phi = Phi::new();

    phi.push(Atom::Eq(var_idx("i"), const_idx(4)));

    let source = Region::from_bounded(var_idx("i"), const_idx(10));
    let remove = Region::from_bounded(
        var_idx("i"),
        Idx::Add(Box::new(var_idx("i")), Box::new(const_idx(1))),
    );

    let diff = source.diff(&remove, &phi, &solver);

    let expected = Region::from_bounded(
        Idx::Add(Box::new(var_idx("i")), Box::new(const_idx(1))),
        const_idx(10),
    );

    assert_eq!(diff, expected);
}

#[test]
fn test_cap_diff_consumes_unique_but_accumulates_shared() {
    let solver = BasicSolver;
    let phi = Phi::new();

    let mut cap_total = Cap::<Region>::default();
    cap_total.uniq = Region::from_bounded(const_idx(0), const_idx(10));

    let mut cap_use = Cap::<Region>::default();
    cap_use.shrd = Region::from_bounded(const_idx(1), const_idx(3));
    cap_use.uniq = Region::from_bounded(const_idx(2), const_idx(4));

    assert!(cap_use.leq(&cap_total, &phi, &solver));

    let diff = cap_total
        .diff(&cap_use, &phi, &solver)
        .expect("cap diff should succeed");

    let expected_shrd = Region::from_bounded(const_idx(1), const_idx(3));
    let expected_uniq = Region::from_intervals(vec![
        Interval::bounded(const_idx(0), const_idx(1)),
        Interval::bounded(const_idx(4), const_idx(10)),
    ]);

    assert_eq!(diff.shrd, expected_shrd);
    assert_eq!(diff.uniq, expected_uniq);
}

#[test]
fn test_delta_diff_requires_subcapability() {
    let solver = BasicSolver;
    let phi = Phi::new();

    let mut cap_total = Cap::<Region>::default();
    cap_total.uniq = Region::from_bounded(const_idx(0), const_idx(10));

    let mut cap_inside = Cap::<Region>::default();
    cap_inside.uniq = Region::from_bounded(const_idx(2), const_idx(4));

    let mut cap_outside = Cap::<Region>::default();
    cap_outside.uniq = Region::from_bounded(const_idx(8), const_idx(12));

    let mut delta_total = Delta::<Region>::default();
    delta_total.0.insert("A".into(), cap_total.clone());

    let mut delta_inside = Delta::<Region>::default();
    delta_inside.0.insert("A".into(), cap_inside);

    let mut delta_outside = Delta::<Region>::default();
    delta_outside.0.insert("A".into(), cap_outside);

    let diff_ok = delta_total
        .diff(&delta_inside, &phi, &solver)
        .expect("delta diff should succeed");
    assert!(diff_ok.0.contains_key("A"));

    let diff_err = delta_total.diff(&delta_outside, &phi, &solver);
    assert!(
        diff_err.is_none(),
        "diff should fail when removing capability outside domain"
    );
}
