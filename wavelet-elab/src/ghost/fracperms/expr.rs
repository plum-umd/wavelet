use crate::logic::semantic::solver::RealExpr;

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
    /// Create a constant fractional expression from a numerator and denominator.
    pub fn from_ratio(num: i64, den: i64) -> Self {
        assert!(
            den != 0,
            "denominator of a fractional constant must not be zero"
        );
        let (n, d) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd_i64(n.abs(), d);
        FractionExpr::Const(n / g, d / g)
    }

    pub fn from_int(n: i64) -> Self {
        FractionExpr::from_ratio(n, 1)
    }

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

    pub fn sum(a: FractionExpr, b: FractionExpr) -> Self {
        FractionExpr::Add(Box::new(a), Box::new(b))
    }

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
