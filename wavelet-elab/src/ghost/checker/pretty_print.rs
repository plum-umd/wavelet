//! Pretty printing utilities for permissions and ghost expressions.

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostStmt, GhostTail, GhostVar};
use crate::ir::{Op, Variable};
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx};

use super::permission::{PermExpr, Permission};

fn render_var<V: Variable>(var: &V) -> String {
    var.name().to_string()
}

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
            let rendered: Vec<_> = items
                .iter()
                .map(render_perm_expr)
                .filter(|item| item != "ε")
                .collect();
            match rendered.len() {
                0 => "ε".to_string(),
                1 => rendered[0].clone(),
                _ => format!("({})", rendered.join(" + ")),
            }
        }
        PermExpr::Sub(lhs, rhs) => {
            let lhs = render_perm_expr(lhs);
            let rhs = render_perm_expr(rhs);
            if rhs == "ε" {
                lhs
            } else if lhs == "ε" && rhs == "ε" {
                "ε".to_string()
            } else {
                format!("({} - {})", lhs, rhs)
            }
        }
    }
}

pub fn render_permission_target(array: &str, region: &RegionSetExpr) -> String {
    format!("{}{}", array, render_region(region))
}

pub fn render_named_perm_expr(name: impl Into<String>, expr: &PermExpr) -> String {
    format!("{} = {}", name.into(), render_perm_expr(expr))
}

pub fn render_relation(lhs: impl Into<String>, op: &str, rhs: impl Into<String>) -> String {
    format!("{} {} {}", lhs.into(), op, rhs.into())
}

pub fn render_fraction_of(name: impl Into<String>) -> String {
    format!("frac({})", name.into())
}

pub fn render_perm_target_check(var: &GhostVar, array: &str, region: &RegionSetExpr) -> String {
    render_relation(
        format!("target({})", var.0),
        "=",
        render_permission_target(array, region),
    )
}

pub fn render_perm_sum(vars: &[GhostVar]) -> String {
    format!(
        "sum({})",
        vars.iter()
            .map(|var| var.0.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub fn render_join_split_check(inputs: &[GhostVar], left: &GhostVar, right: &GhostVar) -> String {
    render_relation(
        render_perm_sum(inputs),
        "=",
        format!("{} + {}", left.0, right.0),
    )
}

pub fn render_consistency_check(label: impl Into<String>) -> String {
    format!("consistent(Φ + assumptions({}))", label.into())
}

fn render_pure_stmt<V: Variable>(inputs: &[V], output: &V, op: &Op<V>) -> String {
    match op {
        Op::Add if inputs.len() == 2 => format!(
            "{} = {} + {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Sub if inputs.len() == 2 => format!(
            "{} = {} - {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Mul if inputs.len() == 2 => format!(
            "{} = {} * {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Sdiv if inputs.len() == 2 => format!(
            "{} = {} s/ {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Udiv if inputs.len() == 2 => format!(
            "{} = {} u/ {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::SignedLessThan if inputs.len() == 2 => format!(
            "{} = {} s< {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::SignedLessEqual if inputs.len() == 2 => format!(
            "{} = {} s<= {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::UnsignedLessThan if inputs.len() == 2 => format!(
            "{} = {} u< {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::UnsignedLessEqual if inputs.len() == 2 => format!(
            "{} = {} u<= {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Equal if inputs.len() == 2 => format!(
            "{} = {} == {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::NotEqual if inputs.len() == 2 => format!(
            "{} = {} != {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::And if inputs.len() == 2 => format!(
            "{} = {} && {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Or if inputs.len() == 2 => format!(
            "{} = {} || {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Not if inputs.len() == 1 => {
            format!("{} = !{}", render_var(output), render_var(&inputs[0]))
        }
        Op::BitAnd if inputs.len() == 2 => format!(
            "{} = {} & {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::BitOr if inputs.len() == 2 => format!(
            "{} = {} | {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::BitXor if inputs.len() == 2 => format!(
            "{} = {} ^ {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Shl if inputs.len() == 2 => format!(
            "{} = {} << {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Ashr if inputs.len() == 2 => format!(
            "{} = {} a>> {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        Op::Lshr if inputs.len() == 2 => format!(
            "{} = {} l>> {}",
            render_var(output),
            render_var(&inputs[0]),
            render_var(&inputs[1])
        ),
        _ => {
            let inputs_str = inputs.iter().map(render_var).collect::<Vec<_>>().join(", ");
            format!("{} = {:?}({})", render_var(output), op, inputs_str)
        }
    }
}

pub fn render_ghost_stmt<V: Variable>(stmt: &GhostStmt<V>) -> String {
    match stmt {
        GhostStmt::Pure { inputs, output, op } => render_pure_stmt(inputs, output, op),
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
            format!("{}, {} = jnsplt([{}])", left.0, right.0, inputs_str)
        }
        GhostStmt::Const {
            value,
            output,
            ghost_in,
        } => {
            format!("{} = const({}) [{}]", render_var(output), value, ghost_in.0)
        }
        GhostStmt::Load {
            array,
            index,
            output,
            ghost_in,
            ghost_out,
        } => {
            format!(
                "{} = {}[{}] [{} -> {}]",
                render_var(output),
                render_var(array),
                render_var(index),
                ghost_in.0,
                ghost_out.0
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
                "store {}[{}] = {} [{} -> ({}, {})]",
                render_var(array),
                render_var(index),
                render_var(value),
                ghost_in.0,
                ghost_out.0 .0,
                ghost_out.1 .0
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
                .map(render_var)
                .collect::<Vec<_>>()
                .join(", ");
            let args_str = args.iter().map(render_var).collect::<Vec<_>>().join(", ");
            format!(
                "{} = {}({}); [need={}, left={}, ret={}]",
                outputs_str, func.0, args_str, ghost_need.0, ghost_left.0, ghost_ret.0
            )
        }
    }
}

pub fn render_ghost_tail<V: Variable>(tail: &GhostTail<V>) -> String {
    match tail {
        GhostTail::Return { value, perm } => {
            format!("return {} [perm={}]", render_var(value), perm.0)
        }
        GhostTail::IfElse { cond, .. } => {
            format!("if {} {{ ... }} else {{ ... }}", render_var(cond))
        }
        GhostTail::TailCall {
            func,
            args,
            ghost_need,
            ghost_left,
        } => {
            let args_str = args.iter().map(render_var).collect::<Vec<_>>().join(", ");
            format!(
                "tail call {}({}) [need={}, left={}]",
                func.0, args_str, ghost_need.0, ghost_left.0
            )
        }
    }
}

pub fn render_ghost_expr<V: Variable>(expr: &GhostExpr<V>) -> String {
    let mut out = String::new();
    write_expr(&mut out, expr, 0);
    out.trim_end().to_string()
}

pub fn render_ghost_function<V: Variable>(def: &GhostFnDef<V>) -> String {
    let params = def
        .params
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let ghost_params = def
        .ghost_params
        .iter()
        .map(|var| var.0.as_str())
        .collect::<Vec<_>>()
        .join(", ");

    let mut out = String::new();
    out.push_str(&format!("fn {}(", def.name.0));
    out.push_str(&params);
    if !ghost_params.is_empty() {
        out.push_str("; ");
        out.push_str(&ghost_params);
    }
    out.push_str(&format!(") -> {} {{\n", def.returns));
    for line in render_ghost_expr(&def.body).lines() {
        out.push_str("  ");
        out.push_str(line);
        out.push('\n');
    }
    out.push('}');
    out
}

fn write_expr<V: Variable>(out: &mut String, expr: &GhostExpr<V>, indent: usize) {
    for stmt in &expr.stmts {
        write_line(out, indent, &render_ghost_stmt(stmt));
    }
    write_tail(out, &expr.tail, indent);
}

fn write_tail<V: Variable>(out: &mut String, tail: &GhostTail<V>, indent: usize) {
    match tail {
        GhostTail::IfElse {
            cond,
            then_expr,
            else_expr,
        } => {
            write_line(out, indent, &format!("if {} {{", render_var(cond)));
            write_expr(out, then_expr, indent + 2);
            write_line(out, indent, "} else {");
            write_expr(out, else_expr, indent + 2);
            write_line(out, indent, "}");
        }
        _ => write_line(out, indent, &render_ghost_tail(tail)),
    }
}

fn write_line(out: &mut String, indent: usize, line: &str) {
    out.push_str(&" ".repeat(indent));
    out.push_str(line);
    out.push('\n');
}
