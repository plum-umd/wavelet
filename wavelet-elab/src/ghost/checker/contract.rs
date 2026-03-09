//! Capability contracts for the ghost permission checker.

use crate::ghost::fracperms::FractionExpr;
use crate::ir::{TypedVar, UntypedVar, Variable};
use crate::logic::cap::CapPattern;
use crate::logic::semantic::region_set::RegionSetExpr;
use crate::logic::semantic::solver::{Atom, Idx, RealExpr};

use super::permission::{
    substitute_atom_with_maps, substitute_fraction_in_perm_expr, substitute_perm_expr_with_maps,
    PermExpr, Permission,
};

#[derive(Clone, Debug)]
pub struct PermissionContract {
    pub sync: PermExpr,
    pub garb: PermExpr,
    pub assumptions: Vec<Atom>,
}

#[derive(Clone, Debug)]
pub struct FunctionSignature {
    pub params: Vec<TypedVar>,
    pub contract: PermissionContract,
}

pub fn build_function_signature(params: &[TypedVar], caps: &[CapPattern]) -> FunctionSignature {
    FunctionSignature {
        params: params.to_vec(),
        contract: contract_from_caps(caps),
    }
}

pub fn contract_from_caps(caps: &[CapPattern]) -> PermissionContract {
    let mut sync_perms = Vec::new();
    let mut assumptions = Vec::new();

    for cap in caps {
        let array = UntypedVar(cap.array.clone());
        let len_idx = match &cap.len {
            crate::ir::ArrayLen::Const(n) => Idx::Const(*n as i64),
            crate::ir::ArrayLen::Symbol(name) => Idx::Var(name.clone()),
            crate::ir::ArrayLen::Expr(expr) => expr.clone(),
        };

        let mut record_bounds = |region: &crate::logic::region::Region| {
            for interval in region.iter() {
                assumptions.push(Atom::Le(Idx::Const(0), interval.lo.clone()));
                assumptions.push(Atom::Le(interval.lo.clone(), interval.hi.clone()));
                assumptions.push(Atom::Le(interval.hi.clone(), len_idx.clone()));
            }
        };

        if let Some(uniq_region) = &cap.uniq {
            record_bounds(uniq_region);
            sync_perms.push(PermExpr::singleton(Permission::new(
                FractionExpr::from_int(1),
                array.clone(),
                RegionSetExpr::from_region(uniq_region),
            )));
        }

        if let Some(shrd_region) = &cap.shrd {
            record_bounds(shrd_region);
            let frac = FractionExpr::Var(shared_fraction_name(&cap.array));
            assumptions.extend(fraction_validity_atoms(&frac));
            sync_perms.push(PermExpr::singleton(Permission::new(
                frac,
                array.clone(),
                RegionSetExpr::from_region(shrd_region),
            )));
        }
    }

    PermissionContract {
        sync: PermExpr::union(sync_perms),
        garb: PermExpr::empty(),
        assumptions,
    }
}

pub fn build_index_substitutions<V: Variable>(
    params: &[TypedVar],
    args: &[V],
) -> Result<Vec<(String, Idx)>, String> {
    if params.len() != args.len() {
        return Err(format!(
            "expected {} arguments, received {}",
            params.len(),
            args.len()
        ));
    }

    let mut substitutions = Vec::new();
    for (param, arg) in params.iter().zip(args.iter()) {
        if param.ty.is_int() {
            substitutions.push((param.name.clone(), Idx::Var(arg.name().to_string())));
        }
    }
    substitutions.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(substitutions)
}

pub fn instantiate_contract(
    contract: &PermissionContract,
    idx_substitutions: &[(String, Idx)],
    fraction_prefix: &str,
) -> PermissionContract {
    let fraction_substitutions = contract_fraction_substitutions(contract, fraction_prefix);

    PermissionContract {
        sync: substitute_fraction_in_perm_expr(
            &substitute_perm_expr_with_maps(&contract.sync, idx_substitutions),
            &fraction_substitutions,
        ),
        garb: substitute_fraction_in_perm_expr(
            &substitute_perm_expr_with_maps(&contract.garb, idx_substitutions),
            &fraction_substitutions,
        ),
        assumptions: contract
            .assumptions
            .iter()
            .map(|atom| {
                let atom = substitute_atom_with_maps(atom, idx_substitutions);
                substitute_fraction_vars_in_atom(&atom, &fraction_substitutions)
            })
            .collect(),
    }
}

pub fn instantiate_call_contract<V: Variable>(
    signature: &FunctionSignature,
    args: &[V],
    site_id: &str,
) -> Result<PermissionContract, String> {
    let idx_substitutions = build_index_substitutions(&signature.params, args)?;
    Ok(instantiate_contract(
        &signature.contract,
        &idx_substitutions,
        &call_fraction_prefix(site_id),
    ))
}

pub fn call_fraction_prefix(site_id: &str) -> String {
    format!("__call_{}__", site_id)
}

pub fn load_fraction_name(ghost_var: &str) -> String {
    format!("__load_{}", ghost_var)
}

pub fn shared_fraction_name(array: &str) -> String {
    format!("f_shrd_{}", array)
}

pub fn fraction_validity_atoms(frac: &FractionExpr) -> [Atom; 2] {
    let frac_real = frac.to_real_expr();
    [
        Atom::RealLt(RealExpr::from_int(0), frac_real.clone()),
        Atom::RealLe(frac_real, RealExpr::from_int(1)),
    ]
}

fn contract_fraction_substitutions(
    contract: &PermissionContract,
    prefix: &str,
) -> std::collections::HashMap<String, FractionExpr> {
    let mut substitutions = std::collections::HashMap::new();

    fn collect(expr: &PermExpr, names: &mut Vec<String>) {
        match expr {
            PermExpr::Empty => {}
            PermExpr::Singleton(perm) => collect_fraction_expr(&perm.fraction, names),
            PermExpr::Add(items) => {
                for item in items {
                    collect(item, names);
                }
            }
            PermExpr::Sub(lhs, rhs) => {
                collect(lhs, names);
                collect(rhs, names);
            }
        }
    }

    let mut names = Vec::new();
    collect(&contract.sync, &mut names);
    collect(&contract.garb, &mut names);
    for atom in &contract.assumptions {
        collect_fraction_vars_from_atom(atom, &mut names);
    }

    names.sort();
    names.dedup();

    for name in names {
        if name.starts_with("f_shrd_") {
            substitutions.insert(
                name.clone(),
                FractionExpr::Var(format!("{}{}", prefix, name)),
            );
        }
    }

    substitutions
}

fn collect_fraction_expr(expr: &FractionExpr, names: &mut Vec<String>) {
    match expr {
        FractionExpr::Const(_, _) => {}
        FractionExpr::Var(name) => names.push(name.clone()),
        FractionExpr::Add(lhs, rhs) | FractionExpr::Sub(lhs, rhs) => {
            collect_fraction_expr(lhs, names);
            collect_fraction_expr(rhs, names);
        }
    }
}

fn collect_fraction_vars_from_real_expr(expr: &RealExpr, names: &mut Vec<String>) {
    match expr {
        RealExpr::Const(_, _) => {}
        RealExpr::Var(name) => names.push(name.clone()),
        RealExpr::Add(lhs, rhs) | RealExpr::Sub(lhs, rhs) => {
            collect_fraction_vars_from_real_expr(lhs, names);
            collect_fraction_vars_from_real_expr(rhs, names);
        }
    }
}

fn collect_fraction_vars_from_atom(atom: &Atom, names: &mut Vec<String>) {
    match atom {
        Atom::RealLe(lhs, rhs) | Atom::RealLt(lhs, rhs) | Atom::RealEq(lhs, rhs) => {
            collect_fraction_vars_from_real_expr(lhs, names);
            collect_fraction_vars_from_real_expr(rhs, names);
        }
        Atom::And(lhs, rhs) | Atom::Or(lhs, rhs) | Atom::Implies(lhs, rhs) => {
            collect_fraction_vars_from_atom(lhs, names);
            collect_fraction_vars_from_atom(rhs, names);
        }
        Atom::Not(inner) => collect_fraction_vars_from_atom(inner, names),
        _ => {}
    }
}

fn substitute_fraction_vars_in_real_expr(
    expr: &RealExpr,
    substitutions: &std::collections::HashMap<String, FractionExpr>,
) -> RealExpr {
    match expr {
        RealExpr::Const(_, _) => expr.clone(),
        RealExpr::Var(name) => substitutions
            .get(name)
            .map(FractionExpr::to_real_expr)
            .unwrap_or_else(|| RealExpr::Var(name.clone())),
        RealExpr::Add(lhs, rhs) => RealExpr::Add(
            Box::new(substitute_fraction_vars_in_real_expr(lhs, substitutions)),
            Box::new(substitute_fraction_vars_in_real_expr(rhs, substitutions)),
        ),
        RealExpr::Sub(lhs, rhs) => RealExpr::Sub(
            Box::new(substitute_fraction_vars_in_real_expr(lhs, substitutions)),
            Box::new(substitute_fraction_vars_in_real_expr(rhs, substitutions)),
        ),
    }
}

fn substitute_fraction_vars_in_atom(
    atom: &Atom,
    substitutions: &std::collections::HashMap<String, FractionExpr>,
) -> Atom {
    match atom {
        Atom::RealLe(lhs, rhs) => Atom::RealLe(
            substitute_fraction_vars_in_real_expr(lhs, substitutions),
            substitute_fraction_vars_in_real_expr(rhs, substitutions),
        ),
        Atom::RealLt(lhs, rhs) => Atom::RealLt(
            substitute_fraction_vars_in_real_expr(lhs, substitutions),
            substitute_fraction_vars_in_real_expr(rhs, substitutions),
        ),
        Atom::RealEq(lhs, rhs) => Atom::RealEq(
            substitute_fraction_vars_in_real_expr(lhs, substitutions),
            substitute_fraction_vars_in_real_expr(rhs, substitutions),
        ),
        Atom::And(lhs, rhs) => Atom::And(
            Box::new(substitute_fraction_vars_in_atom(lhs, substitutions)),
            Box::new(substitute_fraction_vars_in_atom(rhs, substitutions)),
        ),
        Atom::Or(lhs, rhs) => Atom::Or(
            Box::new(substitute_fraction_vars_in_atom(lhs, substitutions)),
            Box::new(substitute_fraction_vars_in_atom(rhs, substitutions)),
        ),
        Atom::Implies(lhs, rhs) => Atom::Implies(
            Box::new(substitute_fraction_vars_in_atom(lhs, substitutions)),
            Box::new(substitute_fraction_vars_in_atom(rhs, substitutions)),
        ),
        Atom::Not(inner) => Atom::Not(Box::new(substitute_fraction_vars_in_atom(
            inner,
            substitutions,
        ))),
        _ => atom.clone(),
    }
}
