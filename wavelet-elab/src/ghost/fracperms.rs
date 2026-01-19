use crate::logic::semantic::PhiSolver;
use crate::logic::semantic::solver::{Atom, Phi, RealExpr, SmtSolver};

/// A symbolic representation of a fractional value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FractionExpr {
    /// A rational constant, encoded as a numerator/denominator pair.
    Const(i64, i64),
    /// A named fractional variable. The associated SMT sort is `Real`.
    Var(String),
    /// An addition of two fractional expressions.
    Add(Box<FractionExpr>, Box<FractionExpr>),
    /// A subtraction of two fractional expressions.
    Sub(Box<FractionExpr>, Box<FractionExpr>),
}

impl FractionExpr {
    /// Create a constant fractional expression from a numerator and
    /// denominator.  The denominator must be non‑zero.
    pub fn from_ratio(num: i64, den: i64) -> Self {
        assert!(
            den != 0,
            "denominator of a fractional constant must not be zero"
        );
        let (n, d) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd_i64(n.abs(), d);
        FractionExpr::Const(n / g, d / g)
    }

    /// A helper to create a constant representing an integer.  This is
    /// equivalent to `n/1`.
    pub fn from_int(n: i64) -> Self {
        FractionExpr::from_ratio(n, 1)
    }

    /// Convert this FractionExpr to a RealExpr for use with the solver's Encoder.
    pub fn to_real_expr(&self) -> RealExpr {
        match self {
            FractionExpr::Const(n, d) => RealExpr::Const(*n, *d),
            FractionExpr::Var(v) => RealExpr::Var(v.clone()),
            FractionExpr::Add(lhs, rhs) => {
                RealExpr::Add(Box::new(lhs.to_real_expr()), Box::new(rhs.to_real_expr()))
            }
            FractionExpr::Sub(lhs, rhs) => {
                RealExpr::Sub(Box::new(lhs.to_real_expr()), Box::new(rhs.to_real_expr()))
            }
        }
    }

    /// Construct a new expression representing the sum of `a` and `b`.
    pub fn sum(a: FractionExpr, b: FractionExpr) -> Self {
        FractionExpr::Add(Box::new(a), Box::new(b))
    }

    /// Construct a new expression representing the difference `a - b`.
    pub fn diff(a: FractionExpr, b: FractionExpr) -> Self {
        FractionExpr::Sub(Box::new(a), Box::new(b))
    }
}

fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.abs()
}

/// Check whether a fractional permission is valid under the given
/// context.  A permission is valid if it lies in the closed interval
/// `[0, 1]`.  Any additional program constraints in `phi` (for
/// example inequalities on symbolic variables) are taken into
/// account.
pub fn check_fraction_valid(phi: &Phi, expr: &FractionExpr, solver: &SmtSolver) -> bool {
    let real_expr = expr.to_real_expr();
    let zero = RealExpr::from_int(0);
    let one = RealExpr::from_int(1);

    let ge_zero = Atom::RealLe(zero, real_expr.clone());
    let le_one = Atom::RealLe(real_expr.clone(), one);

    solver.entails(phi, &ge_zero) && solver.entails(phi, &le_one)
    // entails_with_real_arith(phi, &ge_zero, solver) && entails_with_real_arith(phi, &le_one, solver)
}

/// Check whether `lhs ≤ rhs` holds for two fractional expressions under
/// the context `phi`.  This corresponds directly to the PCM
/// definition of `≤`, which requires that `rhs` can be obtained by
/// adding some other permission to `lhs`.  In the arithmetic setting
/// this simply means `lhs` must be less than or equal to `rhs`.
pub fn check_fraction_leq(
    phi: &Phi,
    lhs: &FractionExpr,
    rhs: &FractionExpr,
    solver: &SmtSolver,
) -> bool {
    let lhs_real = lhs.to_real_expr();
    let rhs_real = rhs.to_real_expr();
    let leq_atom = Atom::RealLe(lhs_real, rhs_real);

    solver.entails(phi, &leq_atom)
    // entails_with_real_arith(phi, &leq_atom, solver)
}

/// Combine a list of fractional permissions by summing them pairwise.
/// The result is a new symbolic expression representing their sum.
/// This helper folds the list using the `FractionExpr::sum` operation.
/// Use `check_fraction_valid` on the result to ensure that the sum
/// does not exceed 1 under the program context.
pub fn sum_fraction_list(exprs: &[FractionExpr]) -> FractionExpr {
    let mut iter = exprs.iter();
    let first = match iter.next() {
        Some(e) => e.clone(),
        None => return FractionExpr::from_int(0),
    };
    iter.fold(first, |acc, e| FractionExpr::sum(acc, e.clone()))
}

/// Attempt to add two fractional permissions together.
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

/// Attempt to subtract one fractional permission from another.
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
    use crate::logic::semantic::solver::{Phi, SmtSolver};

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
        // Test with an empty phi context - the symbolic variables g and f
        // are unconstrained, so we cannot prove any inequality between them.
        let phi = Phi::new();
        let g = FractionExpr::Var("g".into());
        let f = FractionExpr::Var("f".into());
        // Without constraints, we cannot prove g <= f
        assert!(!check_fraction_leq(&phi, &g, &f, &solver));
        // Similarly, we cannot prove f <= g
        assert!(!check_fraction_leq(&phi, &f, &g, &solver));

        // Test that a variable is less than or equal to itself (reflexivity)
        assert!(check_fraction_leq(&phi, &g, &g, &solver));

        // Test that a constant is less than or equal to a larger constant
        let half = FractionExpr::from_ratio(1, 2);
        let three_quarters = FractionExpr::from_ratio(3, 4);
        assert!(check_fraction_leq(&phi, &half, &three_quarters, &solver));
        assert!(!check_fraction_leq(&phi, &three_quarters, &half, &solver));
    }

    #[test]
    fn test_fraction_symbolic_with_real_constraints() {
        use crate::logic::semantic::solver::{Atom, RealExpr};

        let solver = make_solver();
        // Create a phi context with real constraints: 0 < g <= f <= 1
        let mut phi = Phi::new();
        let zero = RealExpr::from_int(0);
        let one = RealExpr::from_int(1);
        let g_real = RealExpr::Var("g".into());
        let f_real = RealExpr::Var("f".into());

        phi.push(Atom::RealLt(zero.clone(), g_real.clone()));
        phi.push(Atom::RealLe(g_real.clone(), f_real.clone()));
        phi.push(Atom::RealLe(f_real.clone(), one));

        // Now test with FractionExpr variables that match the names
        let g_frac = FractionExpr::Var("g".into());
        let f_frac = FractionExpr::Var("f".into());

        // With the constraints, g <= f should hold
        assert!(check_fraction_leq(&phi, &g_frac, &f_frac, &solver));
        // But f <= g should not
        assert!(!check_fraction_leq(&phi, &f_frac, &g_frac, &solver));

        // Both g and f should be valid (in [0, 1])
        assert!(check_fraction_valid(&phi, &g_frac, &solver));
        assert!(check_fraction_valid(&phi, &f_frac, &solver));
    }

    #[test]
    fn test_try_add_fractions() {
        let solver = make_solver();
        let phi = Phi::new();
        let a = FractionExpr::from_ratio(1, 4);
        let b = FractionExpr::from_ratio(1, 2);
        // 1/4 + 1/2 = 3/4 <= 1
        assert!(try_add_fractions(&a, &b, &phi, &solver).is_some());
        // 3/4 + 1/2 = 5/4 > 1
        let c = FractionExpr::from_ratio(3, 4);
        assert!(try_add_fractions(&b, &c, &phi, &solver).is_none());
    }
}
