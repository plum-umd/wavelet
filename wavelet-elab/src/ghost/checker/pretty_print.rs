//! Pretty printing utilities for permissions and ghost expressions.

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::{GhostStmt, GhostTail};
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx};

use super::context::CheckContext;
use super::permission::{PermExpr, Permission};

pub fn render_idx(idx: &Idx) -> String {
    match idx {
        Idx::Const(n) => n.to_string(),
        Idx::Var(v) => v.clone(),
        Idx::Add(a, b) => format!("({} + {})", render_idx(a), render_idx(b)),
        Idx::Sub(a, b) => format!("({} - {})", render_idx(a), render_idx(b)),
        Idx::Mul(a, b) => format!("({} * {})", render_idx(a), render_idx(b)),
    }
}

pub fn render_atom(atom: &Atom) -> String {
    match atom {
        Atom::Le(a, b) => format!("{} <= {}", render_idx(a), render_idx(b)),
        Atom::Lt(a, b) => format!("{} < {}", render_idx(a), render_idx(b)),
        Atom::Eq(a, b) => format!("{} == {}", render_idx(a), render_idx(b)),
        Atom::RealLe(a, b) => format!("{} <= {}", a, b),
        Atom::RealLt(a, b) => format!("{} < {}", a, b),
        Atom::RealEq(a, b) => format!("{} == {}", a, b),
        Atom::BoolVar(name) => name.clone(),
        Atom::And(lhs, rhs) => format!("({}) && ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Or(lhs, rhs) => format!("({}) || ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Implies(lhs, rhs) => format!("({}) => ({})", render_atom(lhs), render_atom(rhs)),
        Atom::Not(inner) => format!("!({})", render_atom(inner)),
    }
}

pub fn render_region(region: &RegionSetExpr) -> String {
    match region {
        RegionSetExpr::Empty => "∅".to_string(),
        RegionSetExpr::Interval { lo, hi } => format!("{{{}..{}}}", render_idx(lo), render_idx(hi)),
        RegionSetExpr::Union(items) => {
            if items.is_empty() {
                "∅".to_string()
            } else {
                let rendered: Vec<_> = items.iter().map(render_region).collect();
                format!("({})", rendered.join(" ∪ "))
            }
        }
        RegionSetExpr::Difference(lhs, rhs) => {
            format!("({} \\ {})", render_region(lhs), render_region(rhs))
        }
        RegionSetExpr::Intersection(lhs, rhs) => {
            format!("({} ∩ {})", render_region(lhs), render_region(rhs))
        }
    }
}

pub fn render_fraction(frac: &FractionExpr) -> String {
    match frac {
        FractionExpr::Const(n, d) => {
            if *d == 1 {
                n.to_string()
            } else {
                format!("{}/{}", n, d)
            }
        }
        FractionExpr::Var(name) => name.clone(),
        FractionExpr::Add(lhs, rhs) => {
            format!("({} + {})", render_fraction(lhs), render_fraction(rhs))
        }
        FractionExpr::Sub(lhs, rhs) => {
            format!("({} - {})", render_fraction(lhs), render_fraction(rhs))
        }
    }
}

pub fn render_permission(perm: &Permission) -> String {
    format!(
        "{}@{}{}",
        render_fraction(&perm.fraction),
        perm.array.0,
        render_region(&perm.region)
    )
}

pub fn render_perm_expr(expr: &PermExpr) -> String {
    match expr {
        PermExpr::Empty => "ε".to_string(),
        PermExpr::Singleton(perm) => render_permission(perm),
        PermExpr::Add(items) => {
            if items.is_empty() {
                "ε".to_string()
            } else {
                let rendered: Vec<_> = items.iter().map(render_perm_expr).collect();
                format!("({})", rendered.join(" + "))
            }
        }
        PermExpr::Sub(lhs, rhs) => {
            format!("({} - {})", render_perm_expr(lhs), render_perm_expr(rhs))
        }
    }
}

pub fn render_ghost_stmt(stmt: &GhostStmt) -> String {
    match stmt {
        GhostStmt::Pure {
            inputs,
            output,
            op,
            ghost_out,
        } => {
            let inputs_str = inputs
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!("({} = {}({}), [{}])", output.0, op, inputs_str, ghost_out.0)
        }
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => {
            let inputs_str = inputs
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}, {} ← [{}]", left.0, right.0, inputs_str)
        }
        GhostStmt::Const {
            value,
            output,
            ghost_in,
            ghost_out,
        } => {
            format!(
                "{} = {}, [{} → {}])",
                output.0, value, ghost_in.0, ghost_out.0
            )
        }
        GhostStmt::Load {
            array,
            index,
            output,
            ghost_in,
            ghost_out,
        } => {
            format!(
                "{} = {}[{}], [{} → {}]",
                output.0, array.0, index.0, ghost_in.0, ghost_out.0
            )
        }
        GhostStmt::Store {
            array,
            index,
            value,
            ghost_in,
            ghost_out,
        } => {
            format!(
                "{}[{}] := {}, [{} → ({}, {})]",
                array.0, index.0, value.0, ghost_in.0, ghost_out.0.0, ghost_out.1.0
            )
        }
        GhostStmt::Call {
            outputs,
            func,
            args,
            ghost_need,
            ghost_left,
            ghost_ret,
        } => {
            let outputs_str = outputs
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            let args_str = args
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "{} = {}({}); [need={}, left={}, ret={}]",
                outputs_str, func.0, args_str, ghost_need.0, ghost_left.0, ghost_ret.0
            )
        }
    }
}

pub fn render_ghost_tail(tail: &GhostTail) -> String {
    match tail {
        GhostTail::Return { value, perm } => {
            format!("ret({}, perm: {})", value.0, perm.0)
        }
        GhostTail::IfElse { cond, .. } => {
            format!("IfElse({})", cond.0)
        }
        GhostTail::TailCall {
            func,
            args,
            ghost_need,
            ghost_left,
        } => {
            let args_str = args
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "{}({}), [need={}, left={}]",
                func.0, args_str, ghost_need.0, ghost_left.0
            )
        }
    }
}

pub fn trace_context(ctx: &CheckContext, stage: &str) {
    if !ctx.verbose {
        return;
    }

    println!("\n=== {} ===", stage);
    print_context_contents(ctx);
}

pub fn print_context_contents(ctx: &CheckContext) {
    // Print permission environment
    if ctx.penv.iter().count() == 0 {
        println!("PermEnv: <empty>");
    } else {
        println!("PermEnv:");
        for (name, perm) in ctx.penv.iter() {
            println!("  {}: {}", name, render_perm_expr(perm));
        }
    }

    // Print logical constraints
    let atoms: Vec<_> = ctx.phi.iter().collect();
    if atoms.is_empty() {
        println!("Φ: <empty>");
    } else {
        println!("Φ:");
        for atom in atoms {
            println!("  {}", render_atom(atom));
        }
    }

    println!();
}
