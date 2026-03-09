use crate::logic::semantic::solver::{Atom, Phi, RealExpr, SmtSolver};
use crate::logic::semantic::PhiSolver;

use super::FractionExpr;

/// Check whether a fractional permission is valid under the given context.
pub fn check_fraction_valid(phi: &Phi, expr: &FractionExpr, solver: &SmtSolver) -> bool {
    let real_expr = expr.to_real_expr();
    let zero = RealExpr::from_int(0);
    let one = RealExpr::from_int(1);

    solver.entails(phi, &Atom::RealLe(zero, real_expr.clone()))
        && solver.entails(phi, &Atom::RealLe(real_expr, one))
}

/// Check whether `lhs ≤ rhs` holds for two fractional expressions under `phi`.
pub fn check_fraction_leq(
    phi: &Phi,
    lhs: &FractionExpr,
    rhs: &FractionExpr,
    solver: &SmtSolver,
) -> bool {
    solver.entails(phi, &Atom::RealLe(lhs.to_real_expr(), rhs.to_real_expr()))
}

pub fn sum_fraction_list(exprs: &[FractionExpr]) -> FractionExpr {
    let mut iter = exprs.iter();
    let first = match iter.next() {
        Some(expr) => expr.clone(),
        None => return FractionExpr::from_int(0),
    };
    iter.fold(first, |acc, expr| FractionExpr::sum(acc, expr.clone()))
}

pub fn try_add_fractions(
    a: &FractionExpr,
    b: &FractionExpr,
    phi: &Phi,
    solver: &SmtSolver,
) -> Option<FractionExpr> {
    let sum = FractionExpr::sum(a.clone(), b.clone());
    if check_fraction_valid(phi, &sum, solver) {
        Some(sum)
    } else {
        None
    }
}

pub fn try_sub_fractions(
    a: &FractionExpr,
    b: &FractionExpr,
    phi: &Phi,
    solver: &SmtSolver,
) -> Option<FractionExpr> {
    if check_fraction_leq(phi, b, a, solver) {
        Some(FractionExpr::diff(a.clone(), b.clone()))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_solver() -> SmtSolver {
        SmtSolver::new()
    }

    #[test]
    fn test_fraction_valid_constant() {
        let solver = make_solver();
        let phi = Phi::new();
        assert!(check_fraction_valid(
            &phi,
            &FractionExpr::from_ratio(1, 2),
            &solver
        ));
        assert!(!check_fraction_valid(
            &phi,
            &FractionExpr::from_ratio(3, 2),
            &solver
        ));
        assert!(!check_fraction_valid(
            &phi,
            &FractionExpr::from_int(-1),
            &solver
        ));
    }

    #[test]
    fn test_fraction_leq_constants() {
        let solver = make_solver();
        let phi = Phi::new();
        let a = FractionExpr::from_ratio(1, 3);
        let b = FractionExpr::from_ratio(2, 3);
        let c = FractionExpr::from_ratio(3, 3);
        assert!(check_fraction_leq(&phi, &a, &b, &solver));
        assert!(check_fraction_leq(&phi, &b, &c, &solver));
        assert!(!check_fraction_leq(&phi, &c, &b, &solver));
    }

    #[test]
    fn test_fraction_symbolic_leq() {
        let solver = make_solver();
        let phi = Phi::new();
        let g = FractionExpr::Var("g".into());
        let f = FractionExpr::Var("f".into());
        assert!(!check_fraction_leq(&phi, &g, &f, &solver));
        assert!(!check_fraction_leq(&phi, &f, &g, &solver));
        assert!(check_fraction_leq(&phi, &g, &g, &solver));

        let half = FractionExpr::from_ratio(1, 2);
        let three_quarters = FractionExpr::from_ratio(3, 4);
        assert!(check_fraction_leq(&phi, &half, &three_quarters, &solver));
        assert!(!check_fraction_leq(&phi, &three_quarters, &half, &solver));
    }

    #[test]
    fn test_fraction_symbolic_with_real_constraints() {
        use crate::logic::semantic::solver::{Atom, RealExpr};

        let solver = make_solver();
        let mut phi = Phi::new();
        let zero = RealExpr::from_int(0);
        let one = RealExpr::from_int(1);
        let g_real = RealExpr::Var("g".into());
        let f_real = RealExpr::Var("f".into());

        phi.push(Atom::RealLt(zero.clone(), g_real.clone()));
        phi.push(Atom::RealLe(g_real.clone(), f_real.clone()));
        phi.push(Atom::RealLe(f_real.clone(), one));

        let g_frac = FractionExpr::Var("g".into());
        let f_frac = FractionExpr::Var("f".into());
        assert!(check_fraction_leq(&phi, &g_frac, &f_frac, &solver));
        assert!(!check_fraction_leq(&phi, &f_frac, &g_frac, &solver));
        assert!(check_fraction_valid(&phi, &g_frac, &solver));
        assert!(check_fraction_valid(&phi, &f_frac, &solver));
    }

    #[test]
    fn test_try_add_fractions() {
        let solver = make_solver();
        let phi = Phi::new();
        let a = FractionExpr::from_ratio(1, 4);
        let b = FractionExpr::from_ratio(1, 2);
        assert!(try_add_fractions(&a, &b, &phi, &solver).is_some());
        let c = FractionExpr::from_ratio(3, 4);
        assert!(try_add_fractions(&b, &c, &phi, &solver).is_none());
    }
}
