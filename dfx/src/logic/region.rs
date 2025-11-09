//! Symbolic regions over index expressions for the semantic backend.

use std::fmt;

use crate::logic::cap::RegionModel;
use crate::logic::semantic::Atom;
use crate::logic::semantic::solver::{Idx, Phi, PhiSolver};
use crate::logic::syntactic::solver::BasicSolver;

/// A half-open interval `[lo, hi)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interval {
    pub lo: Idx,
    pub hi: Idx,
}

impl Interval {
    pub fn bounded(lo: Idx, hi: Idx) -> Self {
        Self { lo, hi }
    }
}

/// A finite set of half-open intervals.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Region {
    intervals: Vec<Interval>,
}

impl Region {
    pub fn from_bounded(lo: Idx, hi: Idx) -> Self {
        Self {
            intervals: vec![Interval::bounded(lo, hi)],
        }
    }

    pub fn from_intervals(intervals: Vec<Interval>) -> Self {
        Self { intervals }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Interval> {
        self.intervals.iter()
    }

    // explain the union operation implementation
    pub fn union(
        &self,
        other: &Region,
        phi: &Phi,
        solver: &dyn PhiSolver<Region = Region>,
    ) -> Region {
        let mut intervals = Vec::new();
        let mut curr: Option<Interval> = None;
        let push_interval =
            |curr: &mut Option<Interval>, dst: &mut Vec<Interval>, next: Interval| {
                if let Some(cur) = curr.as_mut() {
                    let overlaps = solver.entails(phi, &Atom::Le(next.lo.clone(), cur.hi.clone()));
                    if overlaps {
                        if solver.entails(phi, &Atom::Le(cur.hi.clone(), next.hi.clone())) {
                            cur.hi = next.hi.clone();
                        }
                    } else {
                        let cur_clone = cur.clone();
                        dst.push(cur_clone);
                        *cur = next;
                    }
                } else {
                    *curr = Some(next);
                }
            };

        let mut left = self.intervals.iter();
        let mut right = other.intervals.iter();
        let mut peek_left = left.next();
        let mut peek_right = right.next();
        loop {
            let next = match (peek_left, peek_right) {
                (Some(lint), Some(rint)) => {
                    let le = solver.entails(phi, &Atom::Le(lint.lo.clone(), rint.lo.clone()));
                    if le {
                        let res = lint.clone();
                        peek_left = left.next();
                        Some(res)
                    } else {
                        let res = rint.clone();
                        peek_right = right.next();
                        Some(res)
                    }
                }
                (Some(lint), None) => {
                    let res = lint.clone();
                    peek_left = left.next();
                    Some(res)
                }
                (None, Some(rint)) => {
                    let res = rint.clone();
                    peek_right = right.next();
                    Some(res)
                }
                (None, None) => None,
            };
            if let Some(intvl) = next {
                push_interval(&mut curr, &mut intervals, intvl);
            } else {
                break;
            }
        }
        if let Some(cur) = curr {
            intervals.push(cur);
        }
        Region { intervals }
    }

    pub fn diff(
        &self,
        other: &Region,
        phi: &Phi,
        solver: &dyn PhiSolver<Region = Region>,
    ) -> Region {
        let mut result = Vec::new();
        'outer: for s in &self.intervals {
            let mut current = s.clone();
            for o in &other.intervals {
                let mut overlaps = solver.entails(phi, &Atom::Lt(current.lo.clone(), o.hi.clone()))
                    && solver.entails(phi, &Atom::Lt(o.lo.clone(), current.hi.clone()));

                if !overlaps {
                    let lo_within =
                        solver.entails(phi, &Atom::Le(current.lo.clone(), o.lo.clone()));
                    let hi_within =
                        solver.entails(phi, &Atom::Le(o.hi.clone(), current.hi.clone()));
                    let non_empty = solver.entails(phi, &Atom::Lt(o.lo.clone(), o.hi.clone()));
                    overlaps = lo_within && hi_within && non_empty;
                }

                if !overlaps {
                    continue;
                }

                if solver.entails(phi, &Atom::Lt(current.lo.clone(), o.lo.clone())) {
                    result.push(Interval::bounded(current.lo.clone(), o.lo.clone()));
                }

                if solver.entails(phi, &Atom::Le(current.hi.clone(), o.hi.clone())) {
                    continue 'outer;
                }

                current = Interval::bounded(o.hi.clone(), current.hi.clone());
            }

            result.push(current);
        }
        Region { intervals: result }
    }

    pub fn is_subregion_of(
        &self,
        other: &Region,
        phi: &Phi,
        solver: &dyn PhiSolver<Region = Region>,
    ) -> bool {
        for a in &self.intervals {
            let mut covered = false;
            for b in &other.intervals {
                let lo_ok = solver.entails(phi, &Atom::Le(b.lo.clone(), a.lo.clone()));
                let hi_ok = solver.entails(phi, &Atom::Le(a.hi.clone(), b.hi.clone()));
                if lo_ok && hi_ok {
                    covered = true;
                    break;
                }
            }
            if !covered {
                return false;
            }
        }
        true
    }
}

impl RegionModel for Region {
    type Solver = BasicSolver;

    fn from_region(region: &Region) -> Self {
        region.clone()
    }

    fn union(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> Self {
        Region::union(self, other, phi, solver)
    }

    fn diff(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> Self {
        Region::diff(self, other, phi, solver)
    }

    fn is_subregion_of(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> bool {
        Region::is_subregion_of(self, other, phi, solver)
    }

    fn is_empty(&self, _phi: &Phi, _solver: &Self::Solver) -> bool {
        self.intervals.is_empty()
    }

    fn display(&self) -> String {
        format!("{}", self)
    }
}

impl fmt::Display for Idx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Idx::Const(n) => write!(f, "{}", n),
            Idx::Var(v) => write!(f, "{}", v),
            Idx::Add(a, b) => write!(f, "({} + {})", a, b),
            Idx::Sub(a, b) => write!(f, "({} - {})", a, b),
            Idx::Mul(a, b) => write!(f, "({} * {})", a, b),
        }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}..{})", &self.lo, &self.hi)
    }
}

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.intervals.is_empty() {
            write!(f, "<empty>")
        } else {
            let parts: Vec<String> = self.intervals.iter().map(|iv| iv.to_string()).collect();
            write!(f, "{{{}}}", parts.join(" | "))
        }
    }
}
