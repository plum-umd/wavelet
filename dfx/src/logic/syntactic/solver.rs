//! Lightweight logic for reasoning about index expressions used by the
//! syntactic capability backend.

use std::collections::{BTreeMap, BTreeSet};

use crate::logic::semantic::{Atom, Idx, Phi};

/// Linearised form of an index expression: a mapping from variable
/// names to coefficients plus a constant term.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct LinearExpr {
    /// Mapping from variable name to its coefficient.
    pub coeffs: BTreeMap<String, i64>,
    /// The constant offset.
    pub constant: i64,
}

impl LinearExpr {
    /// Evaluate the linear expression at a concrete assignment.  Any
    /// variables not present in the assignment are treated as zero.
    pub fn eval(&self, assignments: &BTreeMap<String, i64>) -> i64 {
        let mut sum = self.constant;
        for (v, c) in &self.coeffs {
            if let Some(val) = assignments.get(v) {
                sum += c * *val;
            }
        }
        sum
    }

    /// Negate the linear expression.
    fn neg(self) -> LinearExpr {
        LinearExpr {
            coeffs: self.coeffs.iter().map(|(k, v)| (k.clone(), -*v)).collect(),
            constant: -self.constant,
        }
    }
}

/// Convert an `Idx` into a linear expression, if possible.
///
/// If the index expression involves constructs outside addition and
/// subtraction it cannot be linearised and will return `None`.
pub fn linearise(idx: &Idx) -> Option<LinearExpr> {
    match idx {
        Idx::Const(n) => Some(LinearExpr {
            coeffs: BTreeMap::new(),
            constant: *n,
        }),
        Idx::Var(v) => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(v.clone(), 1);
            Some(LinearExpr {
                coeffs,
                constant: 0,
            })
        }
        Idx::Add(a, b) => {
            let la = linearise(a)?;
            let lb = linearise(b)?;
            let mut coeffs = la.coeffs.clone();
            for (k, v) in lb.coeffs.iter() {
                *coeffs.entry(k.clone()).or_insert(0) += *v;
            }
            Some(LinearExpr {
                constant: la.constant + lb.constant,
                coeffs,
            })
        }
        Idx::Sub(a, b) => {
            let la = linearise(a)?;
            let lb = linearise(b)?;
            let mut coeffs = la.coeffs.clone();
            for (k, v) in lb.coeffs.iter() {
                *coeffs.entry(k.clone()).or_insert(0) -= *v;
            }
            Some(LinearExpr {
                constant: la.constant - lb.constant,
                coeffs,
            })
        }
    }
}

/// A very basic solver which handles only direct equalities of the
/// form `x = y + c` or `x = c`.
pub struct BasicSolver;

impl BasicSolver {
    /// Collect simple equalities of the form `var = expr + k` from the
    /// context.  Returns a map of variable names to the corresponding
    /// index expression.
    fn collect_equalities(ctx: &Phi) -> BTreeMap<String, Idx> {
        let mut equalities = BTreeMap::new();
        for atom in &ctx.atoms {
            if let Atom::Eq(lhs, rhs) = atom {
                if let Idx::Var(var) = lhs {
                    equalities.insert(var.clone(), rhs.clone());
                } else if let Idx::Var(var) = rhs {
                    equalities.insert(var.clone(), lhs.clone());
                }
            }
        }
        equalities
    }

    /// Recursively apply simple equalities to an index expression.
    fn rewrite_idx(idx: &Idx, eqs: &BTreeMap<String, Idx>, seen: &mut BTreeSet<String>) -> Idx {
        match idx {
            Idx::Const(_) => idx.clone(),
            Idx::Var(v) => {
                if seen.contains(v) {
                    return Idx::Var(v.clone());
                }
                if let Some(rhs) = eqs.get(v) {
                    seen.insert(v.clone());
                    let rewritten = BasicSolver::rewrite_idx(rhs, eqs, seen);
                    seen.remove(v);
                    rewritten
                } else {
                    Idx::Var(v.clone())
                }
            }
            Idx::Add(a, b) => Idx::Add(
                Box::new(BasicSolver::rewrite_idx(a, eqs, seen)),
                Box::new(BasicSolver::rewrite_idx(b, eqs, seen)),
            ),
            Idx::Sub(a, b) => Idx::Sub(
                Box::new(BasicSolver::rewrite_idx(a, eqs, seen)),
                Box::new(BasicSolver::rewrite_idx(b, eqs, seen)),
            ),
        }
    }
}

impl crate::logic::semantic::PhiSolver for BasicSolver {
    fn entails(
        &self,
        ctx: &crate::logic::semantic::Phi,
        atom: &crate::logic::semantic::Atom,
    ) -> bool {
        use crate::logic::semantic::Atom;
        match atom {
            Atom::Le(a, b) => {
                let eqs = BasicSolver::collect_equalities(ctx);
                let mut seen = BTreeSet::new();
                let a_rew = BasicSolver::rewrite_idx(a, &eqs, &mut seen);
                let mut seen = BTreeSet::new();
                let b_rew = BasicSolver::rewrite_idx(b, &eqs, &mut seen);
                if let (Some(la), Some(lb)) = (linearise(&a_rew), linearise(&b_rew)) {
                    let mut diff = la.coeffs.clone();
                    for (k, v) in lb.coeffs.iter() {
                        *diff.entry(k.clone()).or_insert(0) -= *v;
                    }
                    let diff_const = la.constant - lb.constant;
                    if diff.values().all(|c| *c == 0) {
                        return diff_const <= 0;
                    }
                    for fact in ctx.iter() {
                        match fact {
                            Atom::Lt(fx, fy) => {
                                let mut seen = BTreeSet::new();
                                let fx_rew = BasicSolver::rewrite_idx(fx, &eqs, &mut seen);
                                let mut seen = BTreeSet::new();
                                let fy_rew = BasicSolver::rewrite_idx(fy, &eqs, &mut seen);
                                if let (Some(lfx), Some(lfy)) =
                                    (linearise(&fx_rew), linearise(&fy_rew))
                                {
                                    let mut a_minus_fx = la.coeffs.clone();
                                    for (k, v) in lfx.coeffs.iter() {
                                        *a_minus_fx.entry(k.clone()).or_insert(0) -= *v;
                                    }
                                    let a_minus_fx_const = la.constant - lfx.constant;

                                    let mut b_minus_fy = lb.coeffs.clone();
                                    for (k, v) in lfy.coeffs.iter() {
                                        *b_minus_fy.entry(k.clone()).or_insert(0) -= *v;
                                    }
                                    let b_minus_fy_const = lb.constant - lfy.constant;

                                    if a_minus_fx.values().all(|c| *c == 0)
                                        && b_minus_fy.values().all(|c| *c == 0)
                                        && a_minus_fx_const <= b_minus_fy_const + 1
                                    {
                                        return true;
                                    }
                                }
                            }
                            Atom::Le(fx, fy) => {
                                let mut seen = BTreeSet::new();
                                let fx_rew = BasicSolver::rewrite_idx(fx, &eqs, &mut seen);
                                let mut seen = BTreeSet::new();
                                let fy_rew = BasicSolver::rewrite_idx(fy, &eqs, &mut seen);

                                if let (Some(lfx), Some(lfy)) =
                                    (linearise(&fx_rew), linearise(&fy_rew))
                                {
                                    let mut a_minus_fx = la.coeffs.clone();
                                    for (k, v) in lfx.coeffs.iter() {
                                        *a_minus_fx.entry(k.clone()).or_insert(0) -= *v;
                                    }
                                    let a_minus_fx_const = la.constant - lfx.constant;

                                    let mut b_minus_fy = lb.coeffs.clone();
                                    for (k, v) in lfy.coeffs.iter() {
                                        *b_minus_fy.entry(k.clone()).or_insert(0) -= *v;
                                    }
                                    let b_minus_fy_const = lb.constant - lfy.constant;

                                    if a_minus_fx.values().all(|c| *c == 0)
                                        && b_minus_fy.values().all(|c| *c == 0)
                                        && a_minus_fx_const <= b_minus_fy_const
                                    {
                                        return true;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                false
            }
            Atom::Lt(a, b) => {
                let eqs = BasicSolver::collect_equalities(ctx);
                let mut seen = BTreeSet::new();
                let a_rew = BasicSolver::rewrite_idx(a, &eqs, &mut seen);
                let mut seen = BTreeSet::new();
                let b_rew = BasicSolver::rewrite_idx(b, &eqs, &mut seen);
                if let (Some(la), Some(lb)) = (linearise(&a_rew), linearise(&b_rew)) {
                    let mut diff = la.coeffs.clone();
                    for (k, v) in lb.coeffs.iter() {
                        *diff.entry(k.clone()).or_insert(0) -= *v;
                    }
                    let diff_const = la.constant - lb.constant;
                    if diff.values().all(|c| *c == 0) {
                        return diff_const < 0;
                    }
                }
                for fact in ctx.iter() {
                    if let Atom::Lt(fx, fy) = fact {
                        let mut seen = BTreeSet::new();
                        let fx_rew = BasicSolver::rewrite_idx(fx, &eqs, &mut seen);
                        let mut seen = BTreeSet::new();
                        let fy_rew = BasicSolver::rewrite_idx(fy, &eqs, &mut seen);
                        if fx_rew == a_rew && fy_rew == b_rew {
                            return true;
                        }
                    }
                }
                false
            }
            Atom::Eq(a, b) => {
                let eqs = BasicSolver::collect_equalities(ctx);
                let mut seen = BTreeSet::new();
                let a_rew = BasicSolver::rewrite_idx(a, &eqs, &mut seen);
                let mut seen = BTreeSet::new();
                let b_rew = BasicSolver::rewrite_idx(b, &eqs, &mut seen);
                if let (Some(la), Some(lb)) = (linearise(&a_rew), linearise(&b_rew)) {
                    let mut diff = la.coeffs.clone();
                    for (k, v) in lb.coeffs.iter() {
                        *diff.entry(k.clone()).or_insert(0) -= *v;
                    }
                    let diff_const = la.constant - lb.constant;
                    if diff.values().all(|c| *c == 0) {
                        return diff_const == 0;
                    }
                }
                false
            }
            Atom::And(p, q) => self.entails(ctx, p) && self.entails(ctx, q),
            Atom::Not(_) => false,
        }
    }
}
