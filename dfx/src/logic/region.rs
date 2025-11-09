//! Symbolic regions over index expressions for the semantic backend.

use std::fmt;

use crate::logic::semantic::Atom;

use crate::logic::semantic::solver::{Idx, Phi, PhiSolver};

/// A half-open interval `[lo, hi)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interval {
    pub lo: Idx,
    pub hi: Option<Idx>,
}

impl Interval {
    pub fn bounded(lo: Idx, hi: Idx) -> Self {
        Self { lo, hi: Some(hi) }
    }

    pub fn unbounded(lo: Idx) -> Self {
        Self { lo, hi: None }
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

    pub fn from_unbounded(lo: Idx) -> Self {
        Self {
            intervals: vec![Interval::unbounded(lo)],
        }
    }

    pub fn from_intervals(intervals: Vec<Interval>) -> Self {
        Self { intervals }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Interval> {
        self.intervals.iter()
    }

    pub fn union(&self, other: &Region, phi: &Phi, solver: &dyn PhiSolver) -> Region {
        let mut intervals = Vec::new();
        let push_interval = |curr: &mut Option<Interval>,
                             dst: &mut Vec<Interval>,
                             next: Interval| match curr {
            Some(cur) => {
                let overlaps = match &cur.hi {
                    None => true,
                    Some(hi_cur) => solver.entails(phi, &Atom::Le(next.lo.clone(), hi_cur.clone())),
                };
                if overlaps {
                    match (&cur.hi, &next.hi) {
                        (None, _) => {}
                        (Some(_), None) => {
                            cur.hi = None;
                        }
                        (Some(hc), Some(hn)) => {
                            if !solver.entails(phi, &Atom::Le(hn.clone(), hc.clone())) {
                                cur.hi = Some(hn.clone());
                            }
                        }
                    }
                } else {
                    dst.push(cur.clone());
                    *curr = Some(next);
                }
            }
            None => {
                *curr = Some(next);
            }
        };

        let mut curr = None;
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

    pub fn diff(&self, other: &Region, phi: &Phi, solver: &dyn PhiSolver) -> Region {
        let mut result = Vec::new();
        'outer: for s in &self.intervals {
            let mut current = s.clone();
            for o in &other.intervals {
                let cur_hi = &current.hi;
                let o_hi = &o.hi;
                let cur_lo_lt_o_hi = match o_hi {
                    None => true,
                    Some(ohi) => solver.entails(phi, &Atom::Lt(current.lo.clone(), ohi.clone())),
                };
                let o_lo_lt_cur_hi = match cur_hi {
                    None => true,
                    Some(chi) => solver.entails(phi, &Atom::Lt(o.lo.clone(), chi.clone())),
                };
                let mut intervals_overlap = cur_lo_lt_o_hi && o_lo_lt_cur_hi;
                if !intervals_overlap {
                    let lo_within =
                        solver.entails(phi, &Atom::Le(current.lo.clone(), o.lo.clone()));
                    let non_empty = match o_hi {
                        None => true,
                        Some(ohi) => solver.entails(phi, &Atom::Lt(o.lo.clone(), ohi.clone())),
                    };
                    let hi_within = match (cur_hi, o_hi) {
                        (None, _) => true,
                        (Some(_), None) => false,
                        (Some(chi), Some(ohi)) => {
                            solver.entails(phi, &Atom::Le(ohi.clone(), chi.clone()))
                        }
                    };
                    intervals_overlap = lo_within && hi_within && non_empty;
                }

                if intervals_overlap {
                    if solver.entails(phi, &Atom::Lt(current.lo.clone(), o.lo.clone())) {
                        result.push(Interval {
                            lo: current.lo.clone(),
                            hi: Some(o.lo.clone()),
                        });
                    }
                    match (&current.hi, &o.hi) {
                        (None, None) => continue 'outer,
                        (None, Some(ohi)) => {
                            current = Interval {
                                lo: ohi.clone(),
                                hi: None,
                            };
                            continue;
                        }
                        (Some(_), None) => continue 'outer,
                        (Some(chi), Some(ohi)) => {
                            if solver.entails(phi, &Atom::Le(ohi.clone(), chi.clone())) {
                                current = Interval {
                                    lo: ohi.clone(),
                                    hi: Some(chi.clone()),
                                };
                                continue;
                            } else {
                                continue 'outer;
                            }
                        }
                    }
                }
            }
            result.push(current);
        }
        Region { intervals: result }
    }

    pub fn is_subregion_of(&self, other: &Region, phi: &Phi, solver: &dyn PhiSolver) -> bool {
        for a in &self.intervals {
            let mut covered = false;
            for b in &other.intervals {
                let lo_ok = solver.entails(phi, &Atom::Le(b.lo.clone(), a.lo.clone()));
                let hi_ok = match (&a.hi, &b.hi) {
                    (_, None) => true,
                    (None, Some(_)) => false,
                    (Some(ahi), Some(bhi)) => {
                        solver.entails(phi, &Atom::Le(ahi.clone(), bhi.clone()))
                    }
                };
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

fn format_idx(idx: &Idx) -> String {
    match idx {
        Idx::Const(n) => n.to_string(),
        Idx::Var(v) => v.clone(),
        Idx::Add(a, b) => format!("({} + {})", format_idx(a), format_idx(b)),
        Idx::Sub(a, b) => format!("({} - {})", format_idx(a), format_idx(b)),
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.hi {
            Some(hi) => write!(f, "[{}..{})", format_idx(&self.lo), format_idx(hi)),
            None => write!(f, "[{}..)", format_idx(&self.lo)),
        }
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
