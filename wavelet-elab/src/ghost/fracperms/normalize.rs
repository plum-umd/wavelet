use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use super::FractionExpr;

pub fn normalize_fraction_expr(expr: FractionExpr) -> FractionExpr {
    fn is_structural_zero(expr: &FractionExpr) -> bool {
        matches!(expr, FractionExpr::Const(n, _) if *n == 0)
    }

    fn hash_fraction(expr: &FractionExpr) -> u64 {
        let mut hasher = DefaultHasher::new();
        expr.hash(&mut hasher);
        hasher.finish()
    }

    fn normalize_once(expr: FractionExpr) -> FractionExpr {
        match expr {
            FractionExpr::Const(_, _) | FractionExpr::Var(_) => expr,
            FractionExpr::Add(lhs, rhs) => {
                let lhs = normalize_fraction_expr(*lhs);
                let rhs = normalize_fraction_expr(*rhs);

                if is_structural_zero(&lhs) {
                    return rhs;
                }
                if is_structural_zero(&rhs) {
                    return lhs;
                }

                if let (FractionExpr::Const(n1, d1), FractionExpr::Const(n2, d2)) = (&lhs, &rhs) {
                    let num = (*n1 as i128) * (*d2 as i128) + (*n2 as i128) * (*d1 as i128);
                    let den = (*d1 as i128) * (*d2 as i128);
                    return FractionExpr::from_ratio(num as i64, den as i64);
                }

                if let FractionExpr::Sub(a, b) = &lhs {
                    if **b == rhs {
                        return (**a).clone();
                    }
                }
                if let FractionExpr::Sub(a, b) = &rhs {
                    if **b == lhs {
                        return (**a).clone();
                    }
                }

                FractionExpr::Add(Box::new(lhs), Box::new(rhs))
            }
            FractionExpr::Sub(lhs, rhs) => {
                let lhs = normalize_fraction_expr(*lhs);
                let rhs = normalize_fraction_expr(*rhs);

                if lhs == rhs {
                    return FractionExpr::from_int(0);
                }
                if is_structural_zero(&rhs) {
                    return lhs;
                }

                if let (FractionExpr::Const(n1, d1), FractionExpr::Const(n2, d2)) = (&lhs, &rhs) {
                    let num = (*n1 as i128) * (*d2 as i128) - (*n2 as i128) * (*d1 as i128);
                    let den = (*d1 as i128) * (*d2 as i128);
                    return FractionExpr::from_ratio(num as i64, den as i64);
                }

                if let FractionExpr::Add(a, b) = &lhs {
                    if **a == rhs {
                        return (**b).clone();
                    }
                    if **b == rhs {
                        return (**a).clone();
                    }
                }

                if let FractionExpr::Sub(a, b) = &lhs {
                    if **b == rhs {
                        return (**a).clone();
                    }
                }

                if let FractionExpr::Sub(a, b) = &rhs {
                    if **a == lhs {
                        return (**b).clone();
                    }
                }

                FractionExpr::Sub(Box::new(lhs), Box::new(rhs))
            }
        }
    }

    let mut current = expr;
    let mut seen: HashSet<u64> = HashSet::new();
    loop {
        let fingerprint = hash_fraction(&current);
        if !seen.insert(fingerprint) {
            return current;
        }
        let next = normalize_once(current.clone());
        if next == current {
            return next;
        }
        let next_fingerprint = hash_fraction(&next);
        if seen.contains(&next_fingerprint) {
            return next;
        }
        current = next;
    }
}
