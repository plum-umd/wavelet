//! Tests for the permission checker.

use crate::ghost::fracperms::FractionExpr;
use crate::ir::Var;
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, Phi, RealExpr, SmtSolver};

use super::perm_env::PermissionEnv;
use super::permission::{PermExpr, Permission};
use super::program_checker::check_ghost_program_with_verbose;

fn make_perm(fraction: FractionExpr, array: &str, lo: i64, hi: i64) -> PermExpr {
    PermExpr::singleton(Permission::new(
        fraction,
        Var(array.to_string()),
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi)),
    ))
}

#[test]
fn test_perm_normalize_adjacent_partitions() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    phi.push(Atom::Le(Idx::Const(0), Idx::Var("i".to_string())));
    phi.push(Atom::Le(Idx::Const(0), Idx::Var("N".to_string())));
    phi.push(Atom::Lt(
        Idx::Var("i".to_string()),
        Idx::Var("N".to_string()),
    ));
    phi.push(Atom::Eq(
        Idx::Var("j".to_string()),
        Idx::Add(Box::new(Idx::Var("i".to_string())), Box::new(Idx::Const(1))),
    ));

    let dst = Var("dst".to_string());
    let total = RegionSetExpr::interval(Idx::Const(0), Idx::Var("N".to_string()));
    let region_i = RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string()));
    let region_j = RegionSetExpr::interval(Idx::Var("j".to_string()), Idx::Var("N".to_string()));

    let expr_i = PermExpr::Add(vec![
        PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            dst.clone(),
            RegionSetExpr::difference(total.clone(), region_i.clone()),
        )),
        PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            dst.clone(),
            region_i,
        )),
    ]);

    let expr_j = PermExpr::Add(vec![
        PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            dst.clone(),
            RegionSetExpr::difference(total.clone(), region_j.clone()),
        )),
        PermExpr::singleton(Permission::new(
            FractionExpr::from_int(1),
            dst.clone(),
            region_j,
        )),
    ]);

    let expected = PermExpr::singleton(Permission::new(FractionExpr::from_int(1), dst, total));

    assert_eq!(expr_i.normalize(&phi, &solver), Some(expected.clone()));
    assert_eq!(expr_j.normalize(&phi, &solver), Some(expected));
}

#[test]
fn test_permission_env() {
    use crate::ghost::ir::GhostVar;

    let mut env = PermissionEnv::new();
    let var = GhostVar("p1".to_string());
    let perm = Permission::new(
        FractionExpr::from_ratio(1, 2),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
    );

    env.bind(&var, PermExpr::singleton(perm.clone()));
    assert!(env.contains(&var));

    // Extract the permission from the stored expression
    if let PermExpr::Singleton(stored_perm) = env.lookup(&var).unwrap() {
        assert_eq!(stored_perm.fraction, perm.fraction);
    } else {
        panic!("Expected singleton permission");
    }
}

#[test]
fn test_region_substitution() {
    use super::permission::substitute_idx_in_region;

    // Test substituting i -> j in region {i..N}
    let region = RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string()));

    let substituted = substitute_idx_in_region(&region, "i", &Idx::Var("j".to_string()));

    match substituted {
        RegionSetExpr::Interval { lo, hi } => {
            assert_eq!(lo, Idx::Var("j".to_string()));
            assert_eq!(hi, Idx::Var("N".to_string()));
        }
        _ => panic!("Expected interval"),
    }
}

#[test]
fn test_permission_substitution() {
    // Test Permission::substitute_region
    let perm = Permission::new(
        FractionExpr::from_ratio(1, 2),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
    );

    let substituted = perm.substitute_region("i", &Idx::Var("j".to_string()));

    match substituted.region {
        RegionSetExpr::Interval { lo, hi } => {
            assert_eq!(lo, Idx::Var("j".to_string()));
            assert_eq!(hi, Idx::Var("N".to_string()));
        }
        _ => panic!("Expected interval"),
    }
    assert_eq!(substituted.fraction, perm.fraction);
    assert_eq!(substituted.array, perm.array);
}

#[test]
fn test_perm_sub_valid() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let rhs = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 5);

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_invalid_fraction() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    let lhs = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 10);
    let rhs = make_perm(FractionExpr::from_ratio(3, 4), "A", 0, 10);

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(!expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_invalid_region() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 5);
    let rhs = make_perm(FractionExpr::from_ratio(1, 2), "A", 4, 8);

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(!expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_nested() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    let inner_lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let inner_rhs = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);
    let lhs = PermExpr::Sub(Box::new(inner_lhs), Box::new(inner_rhs));

    let rhs_valid = make_perm(FractionExpr::from_ratio(3, 5), "A", 0, 10);
    let rhs_invalid = make_perm(FractionExpr::from_ratio(4, 5), "A", 0, 10);

    let expr_valid = PermExpr::Sub(Box::new(lhs.clone()), Box::new(rhs_valid));
    assert!(expr_valid.is_valid(&phi, &solver));

    let expr_invalid = PermExpr::Sub(Box::new(lhs), Box::new(rhs_invalid));
    assert!(!expr_invalid.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_symbolic_fraction_valid() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Create a symbolic fraction f where f ∈ (0, 1]
    let f = FractionExpr::Var("f".to_string());

    // Add constraint: 0 < f <= 1
    let zero = RealExpr::from_int(0);
    let one = RealExpr::from_int(1);
    let f_real = f.to_real_expr();
    phi.push(Atom::RealLt(zero, f_real.clone()));
    phi.push(Atom::RealLe(f_real.clone(), one));

    // Create permissions: lhs = 1.0 @ A{0..10}, rhs = f @ A{0..10}
    let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let rhs = PermExpr::singleton(Permission::new(
        f,
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_symbolic_fraction_invalid() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Create a symbolic fraction f where f > 1
    let f = FractionExpr::Var("f".to_string());

    let one = RealExpr::from_int(1);
    let f_real = f.to_real_expr();
    // Add constraint: f > 1 (invalid for a fraction)
    phi.push(Atom::RealLt(one, f_real));

    // Create permissions: lhs = 1.0 @ A{0..10}, rhs = f @ A{0..10}
    let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let rhs = PermExpr::singleton(Permission::new(
        f,
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(!expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_symbolic_region_variable_indices() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Add constraints: i < j < N (concrete values)
    phi.push(Atom::Lt(
        Idx::Var("i".to_string()),
        Idx::Var("j".to_string()),
    ));
    phi.push(Atom::Lt(
        Idx::Var("j".to_string()),
        Idx::Var("N".to_string()),
    ));

    // Create permissions: lhs = 1.0 @ A{i..N}, rhs = 1.0 @ A{j..N}
    let lhs = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
    ));
    let rhs = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("j".to_string()), Idx::Var("N".to_string())),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_symbolic_region_non_subset() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Add constraints: i < j < k < N
    phi.push(Atom::Lt(
        Idx::Var("i".to_string()),
        Idx::Var("j".to_string()),
    ));
    phi.push(Atom::Lt(
        Idx::Var("j".to_string()),
        Idx::Var("k".to_string()),
    ));
    phi.push(Atom::Lt(
        Idx::Var("k".to_string()),
        Idx::Var("N".to_string()),
    ));

    // Create permissions: lhs = 1.0 @ A{i..j}, rhs = 1.0 @ A{k..N}
    // Since i..j does not contain k..N, this should fail
    let lhs = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("j".to_string())),
    ));
    let rhs = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("k".to_string()), Idx::Var("N".to_string())),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(!expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_symbolic_fraction_and_region() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Add constraints: 0 < f <= 1, 0 < g <= 1/2, and g <= f, i < j < N
    let f = FractionExpr::Var("f".to_string());
    let g = FractionExpr::Var("g".to_string());

    let zero = RealExpr::from_int(0);
    let half = RealExpr::from_ratio(1, 2);
    let one = RealExpr::from_int(1);
    let f_real = f.to_real_expr();
    let g_real = g.to_real_expr();

    phi.push(Atom::RealLt(zero.clone(), f_real.clone()));
    phi.push(Atom::RealLe(f_real.clone(), one));
    phi.push(Atom::RealLt(zero, g_real.clone()));
    phi.push(Atom::RealLe(g_real.clone(), half));
    phi.push(Atom::RealLe(g_real, f_real)); // Ensure g <= f
    phi.push(Atom::Lt(
        Idx::Var("i".to_string()),
        Idx::Var("j".to_string()),
    ));
    phi.push(Atom::Lt(
        Idx::Var("j".to_string()),
        Idx::Var("N".to_string()),
    ));

    // Create permissions: lhs = f @ A{i..N}, rhs = g @ A{i..j}
    let lhs = PermExpr::singleton(Permission::new(
        f.clone(),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
    ));
    let rhs = PermExpr::singleton(Permission::new(
        g.clone(),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("j".to_string())),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_leftover_region() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Add constraints: i < j < N
    phi.push(Atom::Lt(
        Idx::Var("i".to_string()),
        Idx::Var("j".to_string()),
    ));
    phi.push(Atom::Lt(
        Idx::Var("j".to_string()),
        Idx::Var("N".to_string()),
    ));

    // Create permissions: lhs = 1.0 @ A{i..N}, rhs = 1.0 @ A{i..j}
    // After subtraction, we should have leftover region j..N
    let lhs = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("N".to_string())),
    ));
    let rhs = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Var("i".to_string()), Idx::Var("j".to_string())),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_fractional_leftover() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    // Create permissions: lhs = 1.0 @ A{0..10}, rhs = 1/3 @ A{0..10}
    // After subtraction, we should have leftover 2/3 on same region
    let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let rhs = make_perm(FractionExpr::from_ratio(1, 3), "A", 0, 10);

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_multiple_arrays() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    // Create permissions for different arrays
    // lhs = 1.0 @ A{0..10} + 1.0 @ B{0..5}
    // rhs = 1.0 @ A{0..5}
    let perm_a = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
    ));
    let perm_b = PermExpr::singleton(Permission::new(
        FractionExpr::from_int(1),
        Var("B".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(5)),
    ));
    let lhs = PermExpr::Add(vec![perm_a, perm_b]);

    let rhs = make_perm(FractionExpr::from_int(1), "A", 0, 5);

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_multiple_arrays_insufficient() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    // Create permissions for different arrays
    // lhs = 1.0 @ A{0..10}
    // rhs = 1.0 @ A{0..5} + 1.0 @ B{0..5} (needs B, but not available)
    let lhs = make_perm(FractionExpr::from_int(1), "A", 0, 10);

    let perm_a = make_perm(FractionExpr::from_int(1), "A", 0, 5);
    let perm_b = make_perm(FractionExpr::from_int(1), "B", 0, 5);
    let rhs = PermExpr::Add(vec![perm_a, perm_b]);

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(!expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_symbolic_both_decrease() {
    let solver = SmtSolver::new();
    let mut phi = Phi::new();

    // Create symbolic fractions f and g where 0 < g < f <= 1
    let f = FractionExpr::Var("f".to_string());
    let g = FractionExpr::Var("g".to_string());

    let zero = RealExpr::from_int(0);
    let one = RealExpr::from_int(1);
    let f_real = f.to_real_expr();
    let g_real = g.to_real_expr();

    phi.push(Atom::RealLt(zero.clone(), g_real.clone()));
    phi.push(Atom::RealLt(g_real, f_real.clone()));
    phi.push(Atom::RealLe(f_real, one));

    // Create permissions: lhs = f @ A{0..10}, rhs = g @ A{0..10}
    let lhs = PermExpr::singleton(Permission::new(
        f,
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
    ));
    let rhs = PermExpr::singleton(Permission::new(
        g,
        Var("A".to_string()),
        RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
    ));

    let expr = PermExpr::Sub(Box::new(lhs), Box::new(rhs));
    assert!(expr.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_deeply_nested() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    // Create nested subtractions: ((1.0 - 1/4) - 1/4) should still be valid
    let p1 = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let p2 = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);
    let p3 = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);

    let first_sub = PermExpr::Sub(Box::new(p1), Box::new(p2));
    let second_sub = PermExpr::Sub(Box::new(first_sub), Box::new(p3));

    assert!(second_sub.is_valid(&phi, &solver));
}

#[test]
fn test_perm_sub_deeply_nested_invalid() {
    let solver = SmtSolver::new();
    let phi = Phi::new();

    // Create nested subtractions: ((1.0 - 1/2) - 1/2) - 1/4 should be invalid
    // (trying to subtract 5/4 total from 1.0)
    let p1 = make_perm(FractionExpr::from_int(1), "A", 0, 10);
    let p2 = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 10);
    let p3 = make_perm(FractionExpr::from_ratio(1, 2), "A", 0, 10);
    let p4 = make_perm(FractionExpr::from_ratio(1, 4), "A", 0, 10);

    let first_sub = PermExpr::Sub(Box::new(p1), Box::new(p2));
    let second_sub = PermExpr::Sub(Box::new(first_sub), Box::new(p3));
    let third_sub = PermExpr::Sub(Box::new(second_sub), Box::new(p4));

    assert!(!third_sub.is_valid(&phi, &solver));
}

#[test]
fn ghost_check_all_fixtures() {
    let fixtures_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("test_files");

    // filter out "dmv.rs", "dmv_const.rs", and "nn_fc.rs" for now
    let filter = |path: &std::path::PathBuf| {
        path.file_name()
            .and_then(|name| name.to_str())
            .map_or(false, |name| {
                name == "dmv.rs" || name == "dmv_const.rs" || name == "nn_fc.rs"
            })
    };

    for entry in std::fs::read_dir(&fixtures_dir).expect("fixtures directory should exist") {
        let entry = entry.expect("fixture dir entry should be readable");
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
            continue;
        }
        if filter(&path) {
            continue;
        }

        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {:?}: {err}", path));
        let program = crate::parse_program(&source)
            .unwrap_or_else(|err| panic!("failed to parse {:?}: {err}", path));

        let logic = crate::SemanticLogic::new();
        if let Ok(()) = crate::check_program(&program, &logic) {
            let ghost = crate::synthesize_ghost_program(&program);

            if let Err(err) = check_ghost_program_with_verbose(&ghost, true) {
                panic!("ghost checker failed on {:?}: {}", path, err);
            }
        }
    }
}
