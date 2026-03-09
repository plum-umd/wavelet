//! Fractional ghost permissions.
//!
//! `expr` and `normalize` are pure Rust-side syntax manipulation.
//! `solver` contains the SMT-backed validity and ordering queries.

mod expr;
mod normalize;
mod solver;

pub use expr::FractionExpr;
pub use normalize::normalize_fraction_expr;
pub use solver::{
    check_fraction_leq, check_fraction_valid, sum_fraction_list, try_add_fractions,
    try_sub_fractions,
};
