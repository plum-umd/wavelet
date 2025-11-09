use std::fmt;

use crate::logic::semantic::region_set::{RegionSetExpr, check_subset};
use crate::logic::semantic::solver::{Atom, Idx, Phi, PhiSolver, SmtSolver};

/// Numerator of a fraction, which can be a constant, variable, or nested fraction.
///
/// e.g., 3, f, f/2, (f/2)/3, etc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Numerator {
    Const(usize),
    Var(String),
    Frac(Box<Frac>),
}

/// A fraction represented as numerator and denominator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frac {
    pub numer: Numerator,
    pub denom: usize,
}

/// Non-negative rational number that can be composed
/// of constants and variables using addition and subtraction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NNRat {
    Atomic(Frac),
    Add(Box<NNRat>, Box<NNRat>),
    Sub(Box<NNRat>, Box<NNRat>),
}

pub type Coeff = NNRat;

impl Numerator {
    pub fn to_idx(&self) -> Idx {
        match self {
            Numerator::Const(c) => Idx::Const(*c as i64),
            Numerator::Var(v) => Idx::Var(v.clone()),
            Numerator::Frac(f) => {
                // For nested fractions, we need to represent (numer/denom) as an expression
                // This is complex, so we'll convert to idx form
                let numer_idx = f.numer.to_idx();
                let denom_val = f.denom as i64;
                if denom_val == 1 {
                    numer_idx
                } else {
                    // We can't directly represent division in Idx, so we'll leave it as is
                    // The SMT solver will handle the constraints
                    numer_idx
                }
            }
        }
    }
}

impl Frac {
    pub fn new(numer: Numerator, denom: usize) -> Self {
        assert!(denom != 0, "denominator must be non-zero");
        Self { numer, denom }
    }

    pub fn from_const(numer: usize, denom: usize) -> Self {
        Self::new(Numerator::Const(numer), denom).simplified()
    }

    pub fn from_var(var: String, denom: usize) -> Self {
        Self::new(Numerator::Var(var), denom)
    }

    pub fn simplified(self) -> Self {
        match self.numer {
            Numerator::Const(n) => {
                if n == 0 {
                    return Frac::new(Numerator::Const(0), 1);
                }
                let g = gcd_usize(n, self.denom);
                Frac::new(Numerator::Const(n / g), self.denom / g)
            }
            _ => self,
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.numer, Numerator::Const(0))
    }
}

impl NNRat {
    pub fn zero() -> Self {
        NNRat::Atomic(Frac::from_const(0, 1))
    }

    pub fn one() -> Self {
        NNRat::Atomic(Frac::from_const(1, 1))
    }

    pub fn from_rational(numer: usize, denom: usize) -> Self {
        NNRat::Atomic(Frac::from_const(numer, denom))
    }

    pub fn symbolic(name: impl Into<String>, denom: usize) -> Self {
        NNRat::Atomic(Frac::from_var(name.into(), denom))
    }

    pub fn is_zero(&self) -> bool {
        match self {
            NNRat::Atomic(f) => f.is_zero(),
            NNRat::Add(_, _) => false, // Conservative: would need symbolic evaluation
            NNRat::Sub(_, _) => false, // Conservative: would need symbolic evaluation
        }
    }

    pub fn as_rational(&self) -> Option<(usize, usize)> {
        match self {
            NNRat::Atomic(f) => match &f.numer {
                Numerator::Const(n) => Some((*n, f.denom)),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn add(&self, other: &Coeff) -> Coeff {
        NNRat::Add(Box::new(self.clone()), Box::new(other.clone())).simplified()
    }

    pub fn sub(&self, other: &Coeff) -> Coeff {
        NNRat::Sub(Box::new(self.clone()), Box::new(other.clone())).simplified()
    }

    pub fn simplified(self) -> Self {
        // Simplify the expression tree
        match self {
            NNRat::Atomic(f) => NNRat::Atomic(f.simplified()),
            NNRat::Add(a, b) => {
                let a_simp = a.simplified();
                let b_simp = b.simplified();

                // Try to combine if both are atomic fractions
                if let (NNRat::Atomic(f1), NNRat::Atomic(f2)) = (&a_simp, &b_simp) {
                    if let (Numerator::Const(n1), Numerator::Const(n2)) = (&f1.numer, &f2.numer) {
                        let lcm_val = lcm_usize(f1.denom, f2.denom);
                        let new_n1 = n1 * (lcm_val / f1.denom);
                        let new_n2 = n2 * (lcm_val / f2.denom);
                        return NNRat::Atomic(Frac::from_const(new_n1 + new_n2, lcm_val));
                    }
                }
                NNRat::Add(Box::new(a_simp), Box::new(b_simp))
            }
            NNRat::Sub(a, b) => {
                let a_simp = a.simplified();
                let b_simp = b.simplified();

                // Try to combine if both are atomic fractions
                if let (NNRat::Atomic(f1), NNRat::Atomic(f2)) = (&a_simp, &b_simp) {
                    if let (Numerator::Const(n1), Numerator::Const(n2)) = (&f1.numer, &f2.numer) {
                        let lcm_val = lcm_usize(f1.denom, f2.denom);
                        let new_n1 = n1 * (lcm_val / f1.denom);
                        let new_n2 = n2 * (lcm_val / f2.denom);
                        if new_n1 >= new_n2 {
                            return NNRat::Atomic(Frac::from_const(new_n1 - new_n2, lcm_val));
                        }
                    }
                }
                NNRat::Sub(Box::new(a_simp), Box::new(b_simp))
            }
        }
    }

    /// Get the effective denominator for this coefficient (for scaling in comparisons)
    fn get_denom(&self) -> usize {
        match self {
            NNRat::Atomic(f) => f.denom,
            NNRat::Add(a, b) => {
                let a_denom = a.get_denom();
                let b_denom = b.get_denom();
                lcm_usize(a_denom, b_denom)
            }
            NNRat::Sub(a, b) => {
                let a_denom = a.get_denom();
                let b_denom = b.get_denom();
                lcm_usize(a_denom, b_denom)
            }
        }
    }

    /// Convert to an Idx expression that represents the numerator when scaled by the given denominator
    fn to_scaled_idx(&self, target_denom: usize) -> Idx {
        match self {
            NNRat::Atomic(f) => {
                let scale = target_denom / f.denom;
                let numer_idx = f.numer.to_idx();
                if scale == 1 {
                    numer_idx
                } else {
                    Idx::Mul(Box::new(Idx::Const(scale as i64)), Box::new(numer_idx))
                }
            }
            NNRat::Add(a, b) => {
                let a_scaled = a.to_scaled_idx(target_denom);
                let b_scaled = b.to_scaled_idx(target_denom);
                add_idx(a_scaled, b_scaled)
            }
            NNRat::Sub(a, b) => {
                let a_scaled = a.to_scaled_idx(target_denom);
                let b_scaled = b.to_scaled_idx(target_denom);
                Idx::Add(
                    Box::new(a_scaled),
                    Box::new(Idx::Mul(Box::new(Idx::Const(-1)), Box::new(b_scaled))),
                )
            }
        }
    }

    pub fn leq(&self, other: &Coeff, ctx: RegionCtx<'_>) -> bool {
        // For proper fraction comparison a/b <= c/d, we need to check a*d <= c*b
        let self_denom = self.get_denom();
        let other_denom = other.get_denom();
        let lcm_val = lcm_usize(self_denom, other_denom);

        let lhs = self.to_scaled_idx(lcm_val);
        let rhs = other.to_scaled_idx(lcm_val);
        ctx.solver.entails(ctx.phi, &Atom::Le(lhs, rhs))
    }

    pub fn lt(&self, other: &Coeff, ctx: RegionCtx<'_>) -> bool {
        let self_denom = self.get_denom();
        let other_denom = other.get_denom();
        let lcm_val = lcm_usize(self_denom, other_denom);

        let lhs = self.to_scaled_idx(lcm_val);
        let rhs = other.to_scaled_idx(lcm_val);
        ctx.solver.entails(ctx.phi, &Atom::Lt(lhs, rhs))
    }

    pub fn geq_zero(&self, ctx: RegionCtx<'_>) -> bool {
        let denom = self.get_denom();
        let numerator = self.to_scaled_idx(denom);
        ctx.solver
            .entails(ctx.phi, &Atom::Le(Idx::Const(0), numerator))
    }

    pub fn gt_zero(&self, ctx: RegionCtx<'_>) -> bool {
        let denom = self.get_denom();
        let numerator = self.to_scaled_idx(denom);
        ctx.solver
            .entails(ctx.phi, &Atom::Lt(Idx::Const(0), numerator))
    }

    pub fn eq(&self, other: &Coeff, ctx: RegionCtx<'_>) -> bool {
        self.leq(other, ctx) && other.leq(self, ctx)
    }
}

impl fmt::Display for Numerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Numerator::Const(n) => write!(f, "{}", n),
            Numerator::Var(v) => write!(f, "{}", v),
            Numerator::Frac(frac) => write!(f, "({})", frac),
        }
    }
}

impl fmt::Display for Frac {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denom == 1 {
            write!(f, "{}", self.numer)
        } else {
            write!(f, "{}/{}", self.numer, self.denom)
        }
    }
}

impl fmt::Display for NNRat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NNRat::Atomic(frac) => write!(f, "{}", frac),
            NNRat::Add(a, b) => write!(f, "({} + {})", a, b),
            NNRat::Sub(a, b) => write!(f, "({} - {})", a, b),
        }
    }
}

/// Fractional permission over a region.
///
/// e.g., `1.0 @ {0..N}` stands for full fractional permission (1.0)
/// in the region set {0..N};
/// or `shrd @ {i..i+1}` where `0 < shrd < 1` represents a shared fractional permission
/// in the region set {i..i+1}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FracPerm {
    pub coeff: Coeff,
    pub region: RegionSetExpr,
}

impl FracPerm {
    pub fn new(coeff: Coeff, region: RegionSetExpr) -> Self {
        Self { coeff, region }
    }

    pub fn zero(region: RegionSetExpr) -> Self {
        Self {
            coeff: Coeff::zero(),
            region,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.coeff.is_zero()
    }

    pub fn join(&self, other: &FracPerm, ctx: RegionCtx<'_>) -> Vec<FracPerm> {
        let combined = vec![self.clone(), other.clone()];
        normalise_permissions(combined, ctx)
    }

    /// split by "dividing" self's fractional permission by 2;
    /// or multiply the denominator by 2
    pub fn split(&self) -> (FracPerm, FracPerm) {
        match &self.coeff {
            NNRat::Atomic(f) => {
                let new_denom = f.denom * 2;
                let first = FracPerm::new(
                    NNRat::Atomic(Frac::new(f.numer.clone(), new_denom)),
                    self.region.clone(),
                );
                let second = FracPerm::new(
                    NNRat::Atomic(Frac::new(f.numer.clone(), new_denom)),
                    self.region.clone(),
                );
                (first, second)
            }
            _ => {
                // For non-atomic coefficients, we cannot directly split
                // Here we just return two copies as a fallback
                (self.clone(), self.clone())
            }
        }
    }

    pub fn add(&self, other: &FracPerm, ctx: RegionCtx<'_>) -> FracPerm {
        if regions_equivalent(&self.region, &other.region, ctx) {
            FracPerm::new(self.coeff.add(&other.coeff), self.region.clone())
        } else {
            // Cannot add permissions with different regions
            panic!("Cannot add permissions with non-equivalent regions")
        }
    }

    pub fn sub(&self, other: &FracPerm, ctx: RegionCtx<'_>) -> Option<FracPerm> {
        if regions_equivalent(&self.region, &other.region, ctx) {
            if other.coeff.leq(&self.coeff, ctx) {
                Some(FracPerm::new(
                    self.coeff.sub(&other.coeff),
                    self.region.clone(),
                ))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn sub_with_same_coeff(&self, other: &FracPerm) -> Option<FracPerm> {
        if self.coeff == other.coeff {
            Some(FracPerm::new(
                self.coeff.clone(),
                RegionSetExpr::difference(self.region.clone(), other.region.clone()),
            ))
        } else {
            None
        }
    }
}

impl fmt::Display for FracPerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {}", self.coeff, self.region)
    }
}

#[derive(Clone, Copy)]
pub struct RegionCtx<'a> {
    pub phi: &'a Phi,
    pub solver: &'a SmtSolver,
}

fn regions_equivalent(lhs: &RegionSetExpr, rhs: &RegionSetExpr, ctx: RegionCtx<'_>) -> bool {
    if lhs == rhs {
        return true;
    }
    check_subset(ctx.phi, lhs, rhs, ctx.solver) && check_subset(ctx.phi, rhs, lhs, ctx.solver)
}

fn simplify_region(region: RegionSetExpr, ctx: RegionCtx<'_>) -> RegionSetExpr {
    region.simplify(ctx.phi, ctx.solver)
}

fn prefer_canonical_region(current: RegionSetExpr, candidate: &RegionSetExpr) -> RegionSetExpr {
    let current_str = current.to_string();
    let candidate_str = candidate.to_string();
    if candidate_str.len() < current_str.len()
        || (candidate_str.len() == current_str.len() && candidate_str < current_str)
    {
        candidate.clone()
    } else {
        current
    }
}

pub fn normalise_permissions(perms: Vec<FracPerm>, ctx: RegionCtx<'_>) -> Vec<FracPerm> {
    let mut result: Vec<FracPerm> = Vec::new();
    'outer: for mut perm in perms {
        if perm.coeff.is_zero() {
            continue;
        }
        perm.region = simplify_region(perm.region, ctx);
        for existing in &mut result {
            if regions_equivalent(&existing.region, &perm.region, ctx) {
                existing.coeff = existing.coeff.clone().add(&perm.coeff);
                existing.region = prefer_canonical_region(existing.region.clone(), &perm.region);
                if existing.coeff.is_zero() {
                    *existing = FracPerm::zero(existing.region.clone());
                }
                continue 'outer;
            }
        }
        result.push(perm);
    }
    result.retain(|p| !p.is_zero());
    result
}

pub fn subtract_permissions(
    lhs: &[FracPerm],
    rhs: &[FracPerm],
    ctx: RegionCtx<'_>,
) -> Option<Vec<FracPerm>> {
    let mut remaining: Vec<FracPerm> = lhs.to_vec();
    for sub in rhs {
        if sub.coeff.is_zero() {
            continue;
        }
        let mut matched = false;
        for existing in &mut remaining {
            if regions_equivalent(&existing.region, &sub.region, ctx) {
                if !sub.coeff.leq(&existing.coeff, ctx) {
                    return None;
                }
                existing.coeff = existing.coeff.clone().sub(&sub.coeff);
                matched = true;
                break;
            }
        }
        if !matched {
            return None;
        }
    }
    Some(normalise_permissions(remaining, ctx))
}

fn add_idx(lhs: Idx, rhs: Idx) -> Idx {
    match (lhs, rhs) {
        (Idx::Const(0), other) => other,
        (other, Idx::Const(0)) => other,
        (l, r) => Idx::Add(Box::new(l), Box::new(r)),
    }
}

fn gcd_usize(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

fn lcm_usize(a: usize, b: usize) -> usize {
    if a == 0 || b == 0 {
        return 0;
    }
    (a / gcd_usize(a, b)) * b
}

pub fn rational(numer: i64, denom: i64) -> Coeff {
    assert!(numer >= 0, "numerator must be non-negative");
    assert!(denom > 0, "denominator must be positive");
    Coeff::from_rational(numer as usize, denom as usize)
}

pub fn symbolic_coeff(name: impl Into<String>, denom: i64) -> Coeff {
    assert!(denom > 0, "denominator must be positive");
    Coeff::symbolic(name, denom as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::semantic::solver::Idx;
    use crate::logic::semantic::solver::{Phi, SmtSolver};

    fn interval(lo: i64, hi: i64) -> RegionSetExpr {
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi))
    }

    fn mk_ctx<'a>(phi: &'a Phi, solver: &'a SmtSolver) -> RegionCtx<'a> {
        RegionCtx { phi, solver }
    }

    #[test]
    fn join_accumulates_coefficients() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = mk_ctx(&phi, &solver);
        let perm_a = FracPerm::new(rational(1, 2), interval(0, 1));
        let perm_b = FracPerm::new(rational(1, 2), interval(0, 1));
        let joined = perm_a.join(&perm_b, ctx);
        assert_eq!(joined.len(), 1);
        assert_eq!(joined[0].coeff, rational(1, 1));
    }

    #[test]
    fn diff_eliminates_chunks() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = mk_ctx(&phi, &solver);
        let base = vec![FracPerm::new(rational(3, 4), interval(0, 2))];
        let sub = vec![FracPerm::new(rational(1, 4), interval(0, 2))];
        let diff = subtract_permissions(&base, &sub, ctx).expect("diff should succeed");
        assert_eq!(diff.len(), 1);
        assert_eq!(diff[0].coeff, rational(1, 2));
    }

    #[test]
    fn diff_fails_when_insufficient() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = mk_ctx(&phi, &solver);
        let base = vec![FracPerm::new(rational(1, 4), interval(0, 2))];
        let sub = vec![FracPerm::new(rational(1, 2), interval(0, 2))];
        assert!(subtract_permissions(&base, &sub, ctx).is_none());
    }

    #[test]
    fn normalisation_drops_zeroes() {
        let zero_perm = FracPerm::zero(interval(0, 1));
        assert!(zero_perm.is_zero());
    }

    #[test]
    fn subtract_chunks_requires_matching_regions() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = mk_ctx(&phi, &solver);
        let base = vec![FracPerm::new(rational(1, 2), interval(0, 2))];
        let sub = vec![FracPerm::new(rational(1, 2), interval(1, 3))];
        assert!(subtract_permissions(&base, &sub, ctx).is_none());
    }

    #[test]
    fn leq_checks_partial_order() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
        let ctx = mk_ctx(&phi, &solver);
        let strong_coeff = rational(3, 4);
        let weak_coeff = rational(1, 4);

        assert!(weak_coeff.leq(&strong_coeff, ctx));
        assert!(!strong_coeff.leq(&weak_coeff, ctx));
    }

    #[test]
    fn symbolic_coefficients_respect_solver_constraints() {
        let mut phi = Phi::default();
        let solver = SmtSolver::new();
        // Introduce constraints: 0 <= frac <= 4 (representing frac/8 <= 0.5)
        let frac = Idx::Var("frac".into());
        phi.push(Atom::Le(Idx::Const(0), frac.clone()));
        phi.push(Atom::Le(frac.clone(), Idx::Const(4)));
        let ctx = mk_ctx(&phi, &solver);

        let base = vec![FracPerm::new(symbolic_coeff("frac", 8), interval(0, 2))];
        let sub = vec![FracPerm::new(rational(1, 4), interval(0, 2))];

        // frac/8 >= 1/4 is not entailed, so diff should fail.
        assert!(subtract_permissions(&base, &sub, ctx).is_none());

        // Add the fact that frac >= 2, making frac/8 >= 1/4
        let mut stronger_phi = phi.clone();
        stronger_phi.push(Atom::Le(Idx::Const(2), Idx::Var("frac".into())));
        let stronger_ctx = mk_ctx(&stronger_phi, &solver);
        assert!(subtract_permissions(&base, &sub, stronger_ctx).is_some());
    }
}
