use std::{collections::BTreeMap, fmt};

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::logic::semantic::region_set::{check_subset, RegionSetExpr};
use crate::logic::semantic::solver::{Atom, Idx, Phi, PhiSolver, SmtSolver};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coeff {
    denom: BigInt,
    constant: BigInt,
    symbols: BTreeMap<String, BigInt>,
}

impl Coeff {
    pub fn zero() -> Self {
        Self {
            denom: BigInt::one(),
            constant: BigInt::zero(),
            symbols: BTreeMap::new(),
        }
    }

    pub fn one() -> Self {
        Self::from_rational(1, 1)
    }

    pub fn from_rational(numer: i64, denom: i64) -> Self {
        let denom = BigInt::from(denom);
        assert!(!denom.is_zero(), "denominator must be non-zero");
        let mut coeff = Self {
            denom,
            constant: BigInt::from(numer),
            symbols: BTreeMap::new(),
        };
        coeff.normalise();
        coeff
    }

    pub fn symbolic(name: impl Into<String>, denom: i64) -> Self {
        let denom = BigInt::from(denom);
        assert!(!denom.is_zero(), "denominator must be non-zero");
        let mut symbols = BTreeMap::new();
        symbols.insert(name.into(), BigInt::one());
        let mut coeff = Self {
            denom,
            constant: BigInt::zero(),
            symbols,
        };
        coeff.normalise();
        coeff
    }

    pub fn is_zero(&self) -> bool {
        self.constant.is_zero() && self.symbols.values().all(BigInt::is_zero)
    }

    pub fn as_rational(&self) -> Option<BigRational> {
        if self.symbols.is_empty() {
            Some(BigRational::new(self.constant.clone(), self.denom.clone()))
        } else {
            None
        }
    }

    pub fn add(&self, other: &Coeff) -> Coeff {
        self.add_internal(other, false)
    }

    pub fn sub(&self, other: &Coeff) -> Coeff {
        self.add_internal(other, true)
    }

    pub fn leq(&self, other: &Coeff, ctx: RegionCtx<'_>) -> bool {
        let lhs = self.scaled_numerator_idx(&other.denom);
        let rhs = other.scaled_numerator_idx(&self.denom);
        ctx.solver.entails(ctx.phi, &Atom::Le(lhs, rhs))
    }

    pub fn lt(&self, other: &Coeff, ctx: RegionCtx<'_>) -> bool {
        let lhs = self.scaled_numerator_idx(&other.denom);
        let rhs = other.scaled_numerator_idx(&self.denom);
        ctx.solver.entails(ctx.phi, &Atom::Lt(lhs, rhs))
    }

    pub fn geq_zero(&self, ctx: RegionCtx<'_>) -> bool {
        let numerator = self.numerator_idx();
        ctx.solver
            .entails(ctx.phi, &Atom::Le(Idx::Const(0), numerator))
    }

    pub fn gt_zero(&self, ctx: RegionCtx<'_>) -> bool {
        let numerator = self.numerator_idx();
        ctx.solver
            .entails(ctx.phi, &Atom::Lt(Idx::Const(0), numerator))
    }

    pub fn eq(&self, other: &Coeff, ctx: RegionCtx<'_>) -> bool {
        self.leq(other, ctx) && other.leq(self, ctx)
    }

    fn add_internal(&self, other: &Coeff, subtract: bool) -> Coeff {
        let lcm = self.denom.lcm(&other.denom);
        let self_factor = &lcm / &self.denom;
        let other_factor = &lcm / &other.denom;

        let mut constant = &self.constant * &self_factor;
        let mut symbols = scale_symbol_map(&self.symbols, &self_factor);

        let mut other_const = &other.constant * &other_factor;
        if subtract {
            other_const = -other_const;
        }
        constant += other_const;

        for (sym, coeff) in &other.symbols {
            let mut scaled = coeff * &other_factor;
            if subtract {
                scaled = -scaled;
            }
            *symbols.entry(sym.clone()).or_insert_with(BigInt::zero) += scaled;
        }

        let mut result = Coeff {
            denom: lcm,
            constant,
            symbols,
        };
        result.normalise();
        result
    }

    fn numerator_idx(&self) -> Idx {
        let mut acc: Option<Idx> = None;
        if !self.constant.is_zero() {
            acc = Some(idx_from_bigint(&self.constant));
        }
        for (sym, coeff) in &self.symbols {
            if coeff.is_zero() {
                continue;
            }
            let term = mul_idx_by_int(Idx::Var(sym.clone()), coeff);
            acc = Some(match acc {
                Some(current) => add_idx(current, term),
                None => term,
            });
        }
        acc.unwrap_or_else(|| Idx::Const(0))
    }

    fn scaled_numerator_idx(&self, scale: &BigInt) -> Idx {
        mul_idx_by_int(self.numerator_idx(), scale)
    }

    fn normalise(&mut self) {
        if self.denom.is_zero() {
            panic!("denominator must be non-zero");
        }
        if self.denom.is_negative() {
            self.denom = -self.denom.clone();
            self.constant = -self.constant.clone();
            for value in self.symbols.values_mut() {
                *value = -value.clone();
            }
        }
        self.symbols.retain(|_, v| !v.is_zero());
        if self.constant.is_zero() && self.symbols.is_empty() {
            self.denom = BigInt::one();
            return;
        }

        let mut numerator_gcd = self.constant.abs();
        for coeff in self.symbols.values() {
            let abs = coeff.abs();
            if numerator_gcd.is_zero() {
                numerator_gcd = abs;
            } else {
                numerator_gcd = numerator_gcd.gcd(&abs);
            }
        }
        if numerator_gcd.is_zero() {
            numerator_gcd = BigInt::one();
        }
        let gcd = numerator_gcd.gcd(&self.denom);
        if gcd > BigInt::one() {
            self.denom /= &gcd;
            self.constant /= &gcd;
            for coeff in self.symbols.values_mut() {
                *coeff /= &gcd;
            }
        }
        self.symbols.retain(|_, v| !v.is_zero());
    }
}

impl fmt::Display for Coeff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.symbols.is_empty() {
            write!(f, "{}/{}", self.constant, self.denom)
        } else {
            let mut parts: Vec<String> = Vec::new();
            if !self.constant.is_zero() {
                parts.push(self.constant.to_string());
            }
            for (sym, coeff) in &self.symbols {
                if coeff == &BigInt::one() {
                    parts.push(sym.clone());
                } else {
                    parts.push(format!("{}*{}", coeff, sym));
                }
            }
            write!(f, "({})/{}", parts.join(" + "), self.denom)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermChunk {
    pub coeff: Coeff,
    pub region: RegionSetExpr,
}

impl PermChunk {
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
}

impl fmt::Display for PermChunk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {}", self.coeff, self.region)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Permission {
    chunks: Vec<PermChunk>,
}

impl Permission {
    pub fn empty() -> Self {
        Self { chunks: Vec::new() }
    }

    pub fn singleton(chunk: PermChunk) -> Self {
        Self { chunks: vec![chunk] }
    }

    pub fn is_empty(&self) -> bool {
        self.chunks.iter().all(PermChunk::is_zero)
    }

    pub fn chunks(&self) -> &[PermChunk] {
        &self.chunks
    }

    pub fn join(&self, other: &Permission, ctx: RegionCtx<'_>) -> Permission {
        let mut combined = self.chunks.clone();
        combined.extend(other.chunks.iter().cloned());
        Permission { chunks: combined }.normalised(ctx)
    }

    pub fn leq(&self, other: &Permission, ctx: RegionCtx<'_>) -> bool {
        other.diff(self, ctx).is_some()
    }

    pub fn diff(&self, other: &Permission, ctx: RegionCtx<'_>) -> Option<Permission> {
        subtract_chunks(&self.chunks, &other.chunks, ctx).map(|chunks| Permission { chunks })
    }

    pub fn normalised(mut self, ctx: RegionCtx<'_>) -> Permission {
        self.chunks = normalise_chunks(self.chunks, ctx);
        self
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

fn normalise_chunks(chunks: Vec<PermChunk>, ctx: RegionCtx<'_>) -> Vec<PermChunk> {
    let mut result: Vec<PermChunk> = Vec::new();
    'outer: for mut chunk in chunks {
        if chunk.coeff.is_zero() {
            continue;
        }
        chunk.region = simplify_region(chunk.region, ctx);
        for existing in &mut result {
            if regions_equivalent(&existing.region, &chunk.region, ctx) {
                existing.coeff = existing.coeff.clone().add(&chunk.coeff);
                existing.region =
                    prefer_canonical_region(existing.region.clone(), &chunk.region);
                if existing.coeff.is_zero() {
                    *existing = PermChunk::zero(existing.region.clone());
                }
                continue 'outer;
            }
        }
        result.push(chunk);
    }
    result.retain(|c| !c.is_zero());
    result
}

fn subtract_chunks(
    lhs: &[PermChunk],
    rhs: &[PermChunk],
    ctx: RegionCtx<'_>,
) -> Option<Vec<PermChunk>> {
    let mut remaining: Vec<PermChunk> = lhs.to_vec();
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
    Some(normalise_chunks(remaining, ctx))
}

fn scale_symbol_map(
    source: &BTreeMap<String, BigInt>,
    factor: &BigInt,
) -> BTreeMap<String, BigInt> {
    let mut result = BTreeMap::new();
    for (sym, value) in source {
        if value.is_zero() || factor.is_zero() {
            continue;
        }
        result.insert(sym.clone(), value * factor);
    }
    result
}

fn bigint_to_i64(value: &BigInt) -> i64 {
    value
        .to_i64()
        .expect("coefficient exceeds supported numeric range")
}

fn idx_from_bigint(value: &BigInt) -> Idx {
    Idx::Const(bigint_to_i64(value))
}

fn mul_idx_by_int(expr: Idx, factor: &BigInt) -> Idx {
    if factor.is_zero() {
        return Idx::Const(0);
    }
    if factor == &BigInt::one() {
        return expr;
    }
    if factor == &BigInt::from(-1) {
        return Idx::Mul(Box::new(Idx::Const(-1)), Box::new(expr));
    }
    Idx::Mul(Box::new(Idx::Const(bigint_to_i64(factor))), Box::new(expr))
}

fn add_idx(lhs: Idx, rhs: Idx) -> Idx {
    match (lhs, rhs) {
        (Idx::Const(0), other) => other,
        (other, Idx::Const(0)) => other,
        (l, r) => Idx::Add(Box::new(l), Box::new(r)),
    }
}

pub fn rational(numer: i64, denom: i64) -> Coeff {
    Coeff::from_rational(numer, denom)
}

pub fn symbolic_coeff(name: impl Into<String>, denom: i64) -> Coeff {
    Coeff::symbolic(name, denom)
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
        let chunk_a = PermChunk::new(rational(1, 2), interval(0, 1));
        let chunk_b = PermChunk::new(rational(1, 2), interval(0, 1));
        let joined = Permission::singleton(chunk_a)
            .normalised(ctx)
            .join(&Permission::singleton(chunk_b).normalised(ctx), ctx);
        assert_eq!(joined.chunks.len(), 1);
        assert_eq!(joined.chunks[0].coeff, rational(1, 1));
    }

    #[test]
    fn diff_eliminates_chunks() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
    let ctx = mk_ctx(&phi, &solver);
        let base = Permission::singleton(PermChunk::new(rational(3, 4), interval(0, 2))).normalised(ctx);
        let sub = Permission::singleton(PermChunk::new(rational(1, 4), interval(0, 2))).normalised(ctx);
        let diff = base.diff(&sub, ctx).expect("diff should succeed");
        assert_eq!(diff.chunks.len(), 1);
        assert_eq!(diff.chunks[0].coeff, rational(1, 2));
    }

    #[test]
    fn diff_fails_when_insufficient() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
    let ctx = mk_ctx(&phi, &solver);
        let base = Permission::singleton(PermChunk::new(rational(1, 4), interval(0, 2))).normalised(ctx);
        let sub = Permission::singleton(PermChunk::new(rational(1, 2), interval(0, 2))).normalised(ctx);
        assert!(base.diff(&sub, ctx).is_none());
    }

    #[test]
    fn normalisation_drops_zeroes() {
        let zero_chunk = PermChunk::zero(interval(0, 1));
        let perm = Permission::singleton(zero_chunk);
        assert!(perm.is_empty());
    }

    #[test]
    fn subtract_chunks_requires_matching_regions() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
    let ctx = mk_ctx(&phi, &solver);
        let base = Permission::singleton(PermChunk::new(rational(1, 2), interval(0, 2))).normalised(ctx);
        let sub = Permission::singleton(PermChunk::new(rational(1, 2), interval(1, 3))).normalised(ctx);
        assert!(base.diff(&sub, ctx).is_none());
    }

    #[test]
    fn leq_checks_partial_order() {
        let phi = Phi::default();
        let solver = SmtSolver::new();
    let ctx = mk_ctx(&phi, &solver);
        let strong = Permission::singleton(PermChunk::new(rational(3, 4), interval(0, 2))).normalised(ctx);
        let weak = Permission::singleton(PermChunk::new(rational(1, 4), interval(0, 2))).normalised(ctx);
        assert!(weak.leq(&strong, ctx));
        assert!(!strong.leq(&weak, ctx));
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

        let base = Permission::singleton(PermChunk::new(symbolic_coeff("frac", 8), interval(0, 2)));
        let sub = Permission::singleton(PermChunk::new(rational(1, 4), interval(0, 2)));

        // frac/8 >= 1/4 is not entailed, so diff should fail.
        assert!(base.diff(&sub, ctx).is_none());

        // Add the fact that frac >= 2, making frac/8 >= 1/4
        let mut stronger_phi = phi.clone();
        stronger_phi.push(Atom::Le(Idx::Const(2), Idx::Var("frac".into())));
    let stronger_ctx = mk_ctx(&stronger_phi, &solver);
        assert!(base.diff(&sub, stronger_ctx).is_some());
    }
}
