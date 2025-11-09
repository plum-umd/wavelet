use std::collections::BTreeSet;
use std::fmt;

use smtlib_lowlevel::{
    Driver, Storage,
    ast::{CheckSatResponse, Command, GeneralResponse, SpecificSuccessResponse},
    backend::z3_binary::Z3Binary,
};

use super::{Atom, Idx, Phi, SmtSolver};
use crate::logic::cap::RegionModel;
use crate::logic::region::Region;

/// Boolean region expressions interpreted as sets of integer indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegionSetExpr {
    /// The empty set.
    Empty,
    /// Half-open interval `[lo, hi)`.
    Interval { lo: Idx, hi: Idx },
    /// Finite union of region expressions.
    Union(Vec<RegionSetExpr>),
    /// Set difference `lhs \\ rhs`.
    Difference(Box<RegionSetExpr>, Box<RegionSetExpr>),
    /// Intersection `lhs ∩ rhs`.
    Intersection(Box<RegionSetExpr>, Box<RegionSetExpr>),
}

impl Default for RegionSetExpr {
    fn default() -> Self {
        RegionSetExpr::Empty
    }
}

impl RegionSetExpr {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn interval(lo: Idx, hi: Idx) -> Self {
        Self::Interval { lo, hi }
    }

    pub fn union<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = RegionSetExpr>,
    {
        let mut items: Vec<_> = iter.into_iter().collect();
        if items.len() == 1 {
            items.pop().unwrap()
        } else {
            Self::Union(items)
        }
    }

    pub fn difference(lhs: RegionSetExpr, rhs: RegionSetExpr) -> Self {
        Self::Difference(Box::new(lhs), Box::new(rhs))
    }

    pub fn intersection(lhs: RegionSetExpr, rhs: RegionSetExpr) -> Self {
        Self::Intersection(Box::new(lhs), Box::new(rhs))
    }

    pub fn from_region(region: &Region) -> Self {
        let items: Vec<_> = region
            .iter()
            .map(|interval| RegionSetExpr::interval(interval.lo.clone(), interval.hi.clone()))
            .collect();
        if items.is_empty() {
            RegionSetExpr::Empty
        } else {
            RegionSetExpr::Union(items)
        }
    }

    fn collect_idx_vars(&self, set: &mut BTreeSet<String>) {
        match self {
            RegionSetExpr::Empty => {}
            RegionSetExpr::Interval { lo, hi } => {
                collect_idx_vars(lo, set);
                collect_idx_vars(hi, set);
            }
            RegionSetExpr::Union(items) => {
                for item in items {
                    item.collect_idx_vars(set);
                }
            }
            RegionSetExpr::Difference(lhs, rhs) => {
                lhs.collect_idx_vars(set);
                rhs.collect_idx_vars(set);
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                lhs.collect_idx_vars(set);
                rhs.collect_idx_vars(set);
            }
        }
    }

    /// Convert the set expression into a Boolean SMT predicate over the witness variable.
    ///
    /// Conceptually this produces a formula that is true exactly when `var` lies in the
    /// represented set. The translation follows these cases:
    fn encode(&self, var: &str) -> String {
        match self {
            RegionSetExpr::Empty => "false".into(),
            RegionSetExpr::Interval { lo, hi } => format!(
                "(and (<= {lo} {var}) (< {var} {hi}))",
                lo = encode_idx(lo),
                hi = encode_idx(hi),
                var = var,
            ),
            RegionSetExpr::Union(items) => match items.as_slice() {
                [] => "false".into(),
                [single] => single.encode(var),
                many => {
                    let parts: Vec<String> = many.iter().map(|it| it.encode(var)).collect();
                    format!("(or {})", parts.join(" "))
                }
            },
            RegionSetExpr::Difference(lhs, rhs) => {
                let left = lhs.encode(var);
                let right = rhs.encode(var);
                format!("(and {left} (not {right}))")
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                let left = lhs.encode(var);
                let right = rhs.encode(var);
                format!("(and {left} {right})")
            }
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            RegionSetExpr::Empty | RegionSetExpr::Interval { .. } => 3,
            RegionSetExpr::Intersection(_, _) => 2,
            RegionSetExpr::Difference(_, _) => 1,
            RegionSetExpr::Union(_) => 0,
        }
    }

    fn fmt_with_prec(&self, f: &mut fmt::Formatter<'_>, parent_prec: u8) -> fmt::Result {
        let prec = self.precedence();
        let needs_paren = prec < parent_prec;
        if needs_paren {
            write!(f, "(")?;
        }

        match self {
            RegionSetExpr::Empty => write!(f, "∅")?,
            RegionSetExpr::Interval { lo, hi } => write!(f, "[{}..{})", lo, hi)?,
            RegionSetExpr::Union(items) => {
                if items.is_empty() {
                    write!(f, "∅")?
                } else {
                    let mut first = true;
                    for item in items {
                        if first {
                            first = false;
                        } else {
                            write!(f, " ∪ ")?;
                        }
                        item.fmt_with_prec(f, prec)?;
                    }
                }
            }
            RegionSetExpr::Difference(lhs, rhs) => {
                lhs.fmt_with_prec(f, prec)?;
                write!(f, " \\ ")?;
                rhs.fmt_with_prec(f, prec + 1)?;
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                lhs.fmt_with_prec(f, prec)?;
                write!(f, " ∩ ")?;
                rhs.fmt_with_prec(f, prec)?;
            }
        }

        if needs_paren {
            write!(f, ")")?;
        }

        Ok(())
    }

    pub fn simplify(&self, phi: &Phi, solver: &SmtSolver) -> RegionSetExpr {
        let mut current = self.clone();
        loop {
            let next = current.simplify_once(phi, solver);
            if next == current {
                return next;
            }
            current = next;
        }
    }

    fn simplify_once(&self, phi: &Phi, solver: &SmtSolver) -> RegionSetExpr {
        match self {
            RegionSetExpr::Empty => RegionSetExpr::Empty,
            RegionSetExpr::Interval { .. } => self.clone(),
            RegionSetExpr::Union(items) => {
                let mut flat: Vec<RegionSetExpr> = Vec::new();
                for item in items {
                    let simplified = item.simplify(phi, solver);
                    match simplified {
                        RegionSetExpr::Union(inner) => flat.extend(inner),
                        other => flat.push(other),
                    }
                }

                flat.retain(|expr| !is_empty_expr(expr, phi, solver));

                let mut normalized: Vec<RegionSetExpr> = Vec::new();
                'outer: for expr in flat {
                    let mut to_remove = Vec::new();
                    for (idx, existing) in normalized.iter().enumerate() {
                        if is_subset_expr(&expr, existing, phi, solver) {
                            continue 'outer;
                        }
                        if is_subset_expr(existing, &expr, phi, solver) {
                            to_remove.push(idx);
                        }
                    }
                    for idx in to_remove.into_iter().rev() {
                        normalized.remove(idx);
                    }
                    normalized.push(expr);
                }

                if normalized.is_empty() {
                    RegionSetExpr::Empty
                } else if normalized.len() == 1 {
                    normalized.pop().unwrap()
                } else {
                    normalized.sort_by(|a, b| format!("{}", a).cmp(&format!("{}", b)));
                    RegionSetExpr::Union(normalized)
                }
            }
            RegionSetExpr::Difference(lhs, rhs) => {
                let left = lhs.simplify(phi, solver);
                let right = rhs.simplify(phi, solver);

                if is_empty_expr(&left, phi, solver) {
                    return RegionSetExpr::Empty;
                }
                if is_empty_expr(&right, phi, solver) {
                    return left;
                }
                if is_subset_expr(&left, &right, phi, solver) {
                    return RegionSetExpr::Empty;
                }

                let mut base = left;
                let mut subtracts = vec![right];
                loop {
                    match base {
                        RegionSetExpr::Difference(inner_lhs, inner_rhs) => {
                            subtracts.push(*inner_rhs);
                            base = *inner_lhs;
                        }
                        _ => break,
                    }
                }

                let subtraction = RegionSetExpr::union(subtracts).simplify(phi, solver);

                if is_empty_expr(&subtraction, phi, solver) {
                    return base;
                }
                if is_subset_expr(&base, &subtraction, phi, solver) {
                    return RegionSetExpr::Empty;
                }

                RegionSetExpr::Difference(Box::new(base), Box::new(subtraction))
            }
            RegionSetExpr::Intersection(lhs, rhs) => {
                let left = lhs.simplify(phi, solver);
                let right = rhs.simplify(phi, solver);

                if is_empty_expr(&left, phi, solver) || is_empty_expr(&right, phi, solver) {
                    return RegionSetExpr::Empty;
                }
                if is_subset_expr(&left, &right, phi, solver) {
                    return left;
                }
                if is_subset_expr(&right, &left, phi, solver) {
                    return right;
                }

                RegionSetExpr::Intersection(Box::new(left), Box::new(right))
            }
        }
    }
}

impl fmt::Display for RegionSetExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_prec(f, 0)
    }
}

fn is_empty_expr(expr: &RegionSetExpr, phi: &Phi, solver: &SmtSolver) -> bool {
    check_subset(phi, expr, &RegionSetExpr::Empty, solver)
}

fn is_subset_expr(lhs: &RegionSetExpr, rhs: &RegionSetExpr, phi: &Phi, solver: &SmtSolver) -> bool {
    check_subset(phi, lhs, rhs, solver)
}

impl RegionModel for RegionSetExpr {
    type Solver = SmtSolver;

    fn from_region(region: &Region) -> Self {
        RegionSetExpr::from_region(region)
    }

    fn union(&self, other: &Self, _phi: &Phi, _solver: &Self::Solver) -> Self {
        RegionSetExpr::union([self.clone(), other.clone()])
    }

    fn diff(&self, other: &Self, _phi: &Phi, _solver: &Self::Solver) -> Self {
        RegionSetExpr::difference(self.clone(), other.clone())
    }

    fn is_subregion_of(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> bool {
        check_subset(phi, self, other, solver)
    }

    fn is_empty(&self, phi: &Phi, solver: &Self::Solver) -> bool {
        check_subset(phi, self, &RegionSetExpr::Empty, solver)
    }

    fn display(&self) -> String {
        format!("{}", self)
    }

    fn display_with(&self, phi: &Phi, solver: &Self::Solver) -> String {
        self.simplify(phi, solver).to_string()
    }
}

/// Decide whether `lhs ⊆ rhs` holds by asking the SMT solver for a counterexample.
pub fn check_subset(
    phi: &Phi,
    lhs: &RegionSetExpr,
    rhs: &RegionSetExpr,
    solver: &SmtSolver,
) -> bool {
    let logging = solver.is_query_logging_enabled();
    let mut log_trace = Vec::new();

    let mut int_vars = BTreeSet::new();
    let mut bool_vars = BTreeSet::new();

    for atom in phi.iter() {
        collect_atom_vars(atom, &mut int_vars, &mut bool_vars);
    }
    lhs.collect_idx_vars(&mut int_vars);
    rhs.collect_idx_vars(&mut int_vars);

    if let Some(conflict) = int_vars
        .iter()
        .find(|var| bool_vars.contains(*var))
        .cloned()
    {
        if logging {
            log_trace.push(format!(
                "; variable `{}` used as both int and bool; aborting set encodings",
                conflict
            ));
            flush_trace(&log_trace);
        }
        return false;
    }

    let witness_name = choose_witness_name(&int_vars);

    let mut commands = Vec::new();
    commands.push("(set-logic QF_NIA)".to_string());
    if let Some(timeout) = solver.timeout_ms() {
        commands.push(format!("(set-option :timeout {timeout})"));
    }
    for var in &int_vars {
        commands.push(format!("(declare-const {var} Int)"));
    }
    for var in &bool_vars {
        commands.push(format!("(declare-const {var} Bool)"));
    }
    commands.push(format!("(declare-const {witness_name} Int)"));

    for atom in phi.iter() {
        commands.push(format!("(assert {})", encode_atom(atom)));
    }

    commands.push(format!("(assert {})", lhs.encode(&witness_name)));
    commands.push(format!("(assert (not {}))", rhs.encode(&witness_name)));
    commands.push("(check-sat)".to_string());

    let storage = Storage::new();
    let backend = match Z3Binary::new(solver.z3_path()) {
        Ok(backend) => backend,
        Err(err) => {
            if logging {
                log_trace.push(format!("; failed to spawn z3 backend: {err}"));
                flush_trace(&log_trace);
            }
            eprintln!("failed to initialise z3 backend: {err}");
            return false;
        }
    };

    let mut driver = match Driver::new(&storage, backend) {
        Ok(driver) => driver,
        Err(err) => {
            if logging {
                log_trace.push(format!("; failed to construct SMT driver: {err}"));
                flush_trace(&log_trace);
            }
            eprintln!("failed to construct SMT driver: {err}");
            return false;
        }
    };

    let mut result = None;
    let last = commands.len().saturating_sub(1);

    for (idx, text) in commands.iter().enumerate() {
        if logging {
            log_trace.push(text.clone());
        }
        let cmd = match Command::parse(&storage, text) {
            Ok(cmd) => cmd,
            Err(err) => {
                if logging {
                    log_trace.push(format!("; failed to parse command `{text}`: {err}"));
                    flush_trace(&log_trace);
                }
                eprintln!("failed to parse SMT-LIB command `{text}`: {err}");
                return false;
            }
        };

        let response = match driver.exec(cmd) {
            Ok(resp) => resp,
            Err(err) => {
                if logging {
                    log_trace.push(format!("; solver error for `{text}`: {err}"));
                    flush_trace(&log_trace);
                }
                eprintln!("solver failure while executing `{text}`: {err}");
                return false;
            }
        };

        if idx == last {
            match response {
                GeneralResponse::SpecificSuccessResponse(
                    SpecificSuccessResponse::CheckSatResponse(outcome),
                ) => {
                    if logging {
                        log_trace.push(format!("; result: {outcome:?}"));
                        flush_trace(&log_trace);
                    }
                    result = Some(matches!(outcome, CheckSatResponse::Unsat));
                }
                GeneralResponse::SpecificSuccessResponse(_) => {
                    if logging {
                        log_trace.push("; unexpected solver response to check-sat".to_string());
                        flush_trace(&log_trace);
                    }
                    eprintln!("unexpected solver response to check-sat");
                    return false;
                }
                GeneralResponse::Success => {
                    if logging {
                        log_trace.push("; unexpected bare success for check-sat".to_string());
                        flush_trace(&log_trace);
                    }
                    eprintln!("expected check-sat result, received bare success");
                    return false;
                }
                GeneralResponse::Unsupported => {
                    if logging {
                        log_trace.push("; solver reported unsupported for check-sat".to_string());
                        flush_trace(&log_trace);
                    }
                    eprintln!("solver reported unsupported for check-sat");
                    return false;
                }
                GeneralResponse::Error(msg) => {
                    if logging {
                        log_trace.push(format!("; solver error: {msg}"));
                        flush_trace(&log_trace);
                    }
                    eprintln!("solver reported error: {msg}");
                    return false;
                }
            }
        } else if !matches!(response, GeneralResponse::Success) {
            let message = match response {
                GeneralResponse::Unsupported => "solver reported unsupported",
                GeneralResponse::Error(_) => "solver reported error",
                GeneralResponse::SpecificSuccessResponse(_) => "unexpected solver payload",
                GeneralResponse::Success => unreachable!(),
            };
            if logging {
                log_trace.push(format!("; {message} while executing `{text}`"));
                flush_trace(&log_trace);
            }
            if let GeneralResponse::Error(msg) = response {
                eprintln!("solver error: {msg}");
            } else {
                eprintln!("{message} for command `{text}`");
            }
            return false;
        }
    }

    result.unwrap_or(false)
}

/// Determine whether two region expressions are equivalent under `phi`.
pub fn check_equivalent(
    phi: &Phi,
    lhs: &RegionSetExpr,
    rhs: &RegionSetExpr,
    solver: &SmtSolver,
) -> bool {
    check_subset(phi, lhs, rhs, solver) && check_subset(phi, rhs, lhs, solver)
}

/// Determine whether two region expressions overlap under `phi`.
pub fn overlaps(phi: &Phi, lhs: &RegionSetExpr, rhs: &RegionSetExpr, solver: &SmtSolver) -> bool {
    let intersection = RegionSetExpr::intersection(lhs.clone(), rhs.clone());
    !check_subset(phi, &intersection, &RegionSetExpr::Empty, solver)
}

fn choose_witness_name(int_vars: &BTreeSet<String>) -> String {
    let mut candidate = "__region_elem".to_string();
    let mut serial = 0usize;
    while int_vars.contains(&candidate) {
        serial += 1;
        candidate = format!("__region_elem{serial}");
    }
    candidate
}

fn collect_atom_vars(atom: &Atom, ints: &mut BTreeSet<String>, bools: &mut BTreeSet<String>) {
    match atom {
        Atom::Le(lhs, rhs) | Atom::Lt(lhs, rhs) | Atom::Eq(lhs, rhs) => {
            collect_idx_vars(lhs, ints);
            collect_idx_vars(rhs, ints);
        }
        Atom::BoolVar(name) => {
            bools.insert(name.clone());
        }
        Atom::And(lhs, rhs) | Atom::Or(lhs, rhs) | Atom::Implies(lhs, rhs) => {
            collect_atom_vars(lhs, ints, bools);
            collect_atom_vars(rhs, ints, bools);
        }
        Atom::Not(inner) => collect_atom_vars(inner, ints, bools),
    }
}

fn collect_idx_vars(idx: &Idx, set: &mut BTreeSet<String>) {
    match idx {
        Idx::Const(_) => {}
        Idx::Var(name) => {
            set.insert(name.clone());
        }
        Idx::Add(lhs, rhs) | Idx::Sub(lhs, rhs) | Idx::Mul(lhs, rhs) => {
            collect_idx_vars(lhs, set);
            collect_idx_vars(rhs, set);
        }
    }
}

fn encode_idx(idx: &Idx) -> String {
    match idx {
        Idx::Const(n) => n.to_string(),
        Idx::Var(name) => name.clone(),
        Idx::Add(lhs, rhs) => format!("(+ {} {})", encode_idx(lhs), encode_idx(rhs)),
        Idx::Sub(lhs, rhs) => format!("(- {} {})", encode_idx(lhs), encode_idx(rhs)),
        Idx::Mul(lhs, rhs) => format!("(* {} {})", encode_idx(lhs), encode_idx(rhs)),
    }
}

fn encode_atom(atom: &Atom) -> String {
    match atom {
        Atom::Le(lhs, rhs) => format!("(<= {} {})", encode_idx(lhs), encode_idx(rhs)),
        Atom::Lt(lhs, rhs) => format!("(< {} {})", encode_idx(lhs), encode_idx(rhs)),
        Atom::Eq(lhs, rhs) => format!("(= {} {})", encode_idx(lhs), encode_idx(rhs)),
        Atom::BoolVar(name) => name.clone(),
        Atom::And(lhs, rhs) => format!("(and {} {})", encode_atom(lhs), encode_atom(rhs)),
        Atom::Or(lhs, rhs) => format!("(or {} {})", encode_atom(lhs), encode_atom(rhs)),
        Atom::Implies(lhs, rhs) => format!("(=> {} {})", encode_atom(lhs), encode_atom(rhs)),
        Atom::Not(inner) => format!("(not {})", encode_atom(inner)),
    }
}

fn flush_trace(lines: &[String]) {
    for line in lines {
        println!("{line}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::cap::RegionModel;
    use crate::logic::region::{Interval, Region};

    fn const_interval(lo: i64, hi: i64) -> RegionSetExpr {
        RegionSetExpr::interval(Idx::Const(lo), Idx::Const(hi))
    }

    #[test]
    fn subset_simple_interval() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let left = const_interval(0, 8);
        let right = const_interval(0, 16);
        assert!(check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn subset_detects_counterexample() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let left = const_interval(0, 8);
        let right = const_interval(2, 6);
        assert!(!check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn subset_respects_phi() {
        let solver = SmtSolver::new();
        let mut phi = Phi::new();
        phi.push(Atom::Le(Idx::Var("a".into()), Idx::Var("b".into())));
        let left = RegionSetExpr::interval(Idx::Var("a".into()), Idx::Var("b".into()));
        let right = RegionSetExpr::interval(Idx::Var("a".into()), Idx::Var("b".into()));
        assert!(check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn difference_support() {
        let solver = SmtSolver::new();
        // solver.set_query_logging(true);
        let phi = Phi::new();
        let left = RegionSetExpr::difference(
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(10)),
            RegionSetExpr::interval(Idx::Const(2), Idx::Const(5)),
        );
        let right = RegionSetExpr::union([
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(2)),
            RegionSetExpr::interval(Idx::Const(5), Idx::Const(10)),
        ]);
        assert!(check_subset(&phi, &left, &right, &solver));
    }

    #[test]
    fn equivalence_helper_round_trip() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let region = Region::from_intervals(vec![
            Interval::bounded(Idx::Const(0), Idx::Const(4)),
            Interval::bounded(Idx::Const(6), Idx::Const(9)),
        ]);
        let expr = RegionSetExpr::from_region(&region);
        let manual = RegionSetExpr::union([
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(4)),
            RegionSetExpr::interval(Idx::Const(6), Idx::Const(9)),
        ]);
        assert!(check_equivalent(&phi, &expr, &manual, &solver));
    }

    #[test]
    fn overlap_detection() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let left = const_interval(0, 8);
        let right = const_interval(5, 12);
        assert!(overlaps(&phi, &left, &right, &solver));

        let disjoint_left = const_interval(0, 3);
        let disjoint_right = const_interval(5, 7);
        assert!(!overlaps(&phi, &disjoint_left, &disjoint_right, &solver));
    }

    #[test]
    fn display_handles_primitives() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        assert_eq!(RegionSetExpr::Empty.display_with(&phi, &solver), "∅");

        let interval = RegionSetExpr::interval(Idx::Const(0), Idx::Const(4));
        assert_eq!(interval.display_with(&phi, &solver), "[0..4)");
    }

    #[test]
    fn display_formats_composite() {
        let solver = SmtSolver::new();
        let phi = Phi::new();

        let first = RegionSetExpr::interval(Idx::Const(0), Idx::Const(2));
        let second = RegionSetExpr::interval(Idx::Const(4), Idx::Const(6));
        let union = RegionSetExpr::union([first.clone(), second.clone()]);
        assert_eq!(union.display_with(&phi, &solver), "[0..2) ∪ [4..6)");

        let diff = RegionSetExpr::difference(
            RegionSetExpr::interval(Idx::Const(0), Idx::Const(8)),
            RegionSetExpr::interval(Idx::Const(2), Idx::Const(3)),
        );
        let expr = RegionSetExpr::intersection(diff, second);
        assert_eq!(expr.display_with(&phi, &solver), "[4..6)");
    }

    #[test]
    fn display_drops_empty_unions() {
        let solver = SmtSolver::new();
        let phi = Phi::new();
        let expr = RegionSetExpr::union([
            RegionSetExpr::Empty,
            RegionSetExpr::Empty,
            RegionSetExpr::interval(Idx::Const(10), Idx::Const(11)),
        ]);

        assert_eq!(expr.display_with(&phi, &solver), "[10..11)");
    }
}
