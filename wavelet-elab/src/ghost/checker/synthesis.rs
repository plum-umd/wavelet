//! Symbolic permission synthesis for lowered ghost programs.

use std::collections::HashMap;

use crate::ghost::fracperms::FractionExpr;
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostProgram, GhostStmt, GhostTail, GhostVar};
use crate::ir::Variable;

use super::contract::{
    build_function_signature, instantiate_call_contract, load_fraction_name, FunctionSignature,
};
use super::perm_env::PermissionEnv;
use super::permission::PermExpr;
use super::pretty_print::{render_ghost_stmt, render_ghost_tail};
use super::trace::{trace_synth_bindings, trace_synthesis_function, trace_synthesis_step};
use super::utils::{access_perm_expr, join_parts};

#[derive(Clone, Debug)]
pub struct FunctionPermissionModel {
    pub bindings: PermissionEnv,
}

#[derive(Clone, Debug)]
pub struct ProgramPermissionModel {
    pub signatures: HashMap<String, FunctionSignature>,
    pub functions: HashMap<String, FunctionPermissionModel>,
}

pub fn synthesize_permissions<V: Variable>(
    program: &GhostProgram<V>,
    verbose: bool,
) -> Result<ProgramPermissionModel, String> {
    let mut signatures = HashMap::new();
    for def in &program.defs {
        signatures.insert(
            def.name.0.clone(),
            build_function_signature(&def.params, &def.caps),
        );
    }

    let mut functions = HashMap::new();
    for def in &program.defs {
        let mut synth = FunctionSynthesizer::new(&signatures, verbose);
        let model = synth.synthesize_function(def)?;
        functions.insert(def.name.0.clone(), model);
    }

    Ok(ProgramPermissionModel {
        signatures,
        functions,
    })
}

struct FunctionSynthesizer<'a> {
    signatures: &'a HashMap<String, FunctionSignature>,
    bindings: PermissionEnv,
    verbose: bool,
}

impl<'a> FunctionSynthesizer<'a> {
    fn new(signatures: &'a HashMap<String, FunctionSignature>, verbose: bool) -> Self {
        Self {
            signatures,
            bindings: PermissionEnv::new(),
            verbose,
        }
    }

    fn synthesize_function<V: Variable>(
        &mut self,
        def: &GhostFnDef<V>,
    ) -> Result<FunctionPermissionModel, String> {
        trace_synthesis_function(self.verbose, def);

        let signature = self
            .signatures
            .get(&def.name.0)
            .ok_or_else(|| format!("missing synthesized signature for {}", def.name.0))?
            .clone();

        if def.ghost_params.len() < 2 {
            return Err(format!(
                "ghost function {} is missing entry permission parameters",
                def.name.0
            ));
        }

        self.bindings = PermissionEnv::new();
        self.bind(&def.ghost_params[0], signature.contract.sync.clone());
        self.bind(&def.ghost_params[1], signature.contract.garb.clone());
        trace_synthesis_step(self.verbose, "function entry permissions");
        self.trace_bindings([&def.ghost_params[0], &def.ghost_params[1]]);
        self.synthesize_expr(&def.body)?;

        Ok(FunctionPermissionModel {
            bindings: self.bindings.clone(),
        })
    }

    fn synthesize_expr<V: Variable>(&mut self, expr: &GhostExpr<V>) -> Result<(), String> {
        let mut i = 0;
        while i < expr.stmts.len() {
            match &expr.stmts[i] {
                GhostStmt::Pure { .. } => {
                    i += 1;
                }
                GhostStmt::JoinSplit { .. } => {
                    if i + 1 >= expr.stmts.len() {
                        self.synthesize_tail_after_join(&expr.stmts[i], &expr.tail)?;
                        return Ok(());
                    }

                    match &expr.stmts[i + 1] {
                        GhostStmt::Const { .. } => {
                            self.synthesize_join_const(&expr.stmts[i], &expr.stmts[i + 1])?;
                            i += 2;
                        }
                        GhostStmt::Load { .. } => {
                            self.synthesize_join_load(&expr.stmts[i], &expr.stmts[i + 1])?;
                            i += 2;
                        }
                        GhostStmt::Store { .. } => {
                            self.synthesize_join_store(&expr.stmts[i], &expr.stmts[i + 1])?;
                            i += 2;
                        }
                        GhostStmt::JoinSplit { .. } => {
                            if i + 2 >= expr.stmts.len() {
                                self.synthesize_tail_after_two_joins(
                                    &expr.stmts[i],
                                    &expr.stmts[i + 1],
                                    &expr.tail,
                                )?;
                                return Ok(());
                            }

                            match &expr.stmts[i + 2] {
                                GhostStmt::Call { .. } => {
                                    self.synthesize_join_join_call(
                                        &expr.stmts[i],
                                        &expr.stmts[i + 1],
                                        &expr.stmts[i + 2],
                                    )?;
                                    i += 3;
                                }
                                other => {
                                    return Err(format!(
                                        "two join/splits must be followed by a call or tail call, found {}",
                                        render_ghost_stmt(other)
                                    ));
                                }
                            }
                        }
                        other => {
                            return Err(format!(
                                "join/split must be followed by a const/load/store/call site, found {}",
                                render_ghost_stmt(other)
                            ));
                        }
                    }
                }
                other => {
                    return Err(format!(
                        "malformed lowered program: {} is missing its leading join/split",
                        render_ghost_stmt(other)
                    ));
                }
            }
        }

        match &expr.tail {
            GhostTail::IfElse {
                then_expr,
                else_expr,
                ..
            } => {
                let saved = self.bindings.clone();
                self.synthesize_expr(then_expr)?;
                let then_bindings = self.bindings.clone();
                self.bindings = saved.clone();
                self.synthesize_expr(else_expr)?;
                let else_bindings = self.bindings.clone();
                self.bindings = saved;
                self.bindings.extend_from(&then_bindings);
                self.bindings.extend_from(&else_bindings);
                Ok(())
            }
            other => Err(format!(
                "tail {} must be preceded by lowering-introduced join/split statements",
                render_ghost_tail(other)
            )),
        }
    }

    fn synthesize_join_const<V: Variable>(
        &mut self,
        join_stmt: &GhostStmt<V>,
        const_stmt: &GhostStmt<V>,
    ) -> Result<(), String> {
        let (left, right, inputs) = join_parts(join_stmt)?;
        let joined = self.join_inputs(inputs)?;
        self.bind(left, PermExpr::empty());
        self.bind(right, joined.clone());

        if let GhostStmt::Const { ghost_in, .. } = const_stmt {
            if ghost_in.0 != left.0 {
                return Err(format!(
                    "const expects {}, but the preceding join/split synthesized {}",
                    ghost_in.0, left.0
                ));
            }
        }

        trace_synthesis_step(
            self.verbose,
            &format!(
                "{}; {}",
                render_ghost_stmt(join_stmt),
                render_ghost_stmt(const_stmt)
            ),
        );
        self.trace_bindings([left, right]);
        Ok(())
    }

    fn synthesize_join_load<V: Variable>(
        &mut self,
        join_stmt: &GhostStmt<V>,
        load_stmt: &GhostStmt<V>,
    ) -> Result<(), String> {
        let (left, right, inputs) = join_parts(join_stmt)?;
        let joined = self.join_inputs(inputs)?;
        let (array, index, ghost_in, ghost_out) = match load_stmt {
            GhostStmt::Load {
                array,
                index,
                ghost_in,
                ghost_out,
                ..
            } => (array, index, ghost_in, ghost_out),
            _ => unreachable!(),
        };

        if ghost_in.0 != left.0 {
            return Err(format!(
                "load expects {}, but the preceding join/split synthesized {}",
                ghost_in.0, left.0
            ));
        }

        let load_expr = access_perm_expr(
            FractionExpr::Var(load_fraction_name(&ghost_out.0)),
            array.name(),
            index.name(),
        );

        self.bind(left, load_expr.clone());
        self.bind(
            right,
            PermExpr::Sub(Box::new(joined), Box::new(load_expr.clone())),
        );
        self.bind(ghost_out, load_expr);

        trace_synthesis_step(
            self.verbose,
            &format!(
                "{}; {}",
                render_ghost_stmt(join_stmt),
                render_ghost_stmt(load_stmt)
            ),
        );
        self.trace_bindings([left, right, ghost_out]);
        Ok(())
    }

    fn synthesize_join_store<V: Variable>(
        &mut self,
        join_stmt: &GhostStmt<V>,
        store_stmt: &GhostStmt<V>,
    ) -> Result<(), String> {
        let (left, right, inputs) = join_parts(join_stmt)?;
        let joined = self.join_inputs(inputs)?;
        let (array, index, ghost_in, ghost_out) = match store_stmt {
            GhostStmt::Store {
                array,
                index,
                ghost_in,
                ghost_out,
                ..
            } => (array, index, ghost_in, ghost_out),
            _ => unreachable!(),
        };

        if ghost_in.0 != left.0 {
            return Err(format!(
                "store expects {}, but the preceding join/split synthesized {}",
                ghost_in.0, left.0
            ));
        }

        let store_expr = access_perm_expr(FractionExpr::from_int(1), array.name(), index.name());

        self.bind(left, store_expr.clone());
        self.bind(
            right,
            PermExpr::Sub(Box::new(joined), Box::new(store_expr.clone())),
        );
        self.bind(&ghost_out.0, PermExpr::empty());
        self.bind(&ghost_out.1, store_expr);

        trace_synthesis_step(
            self.verbose,
            &format!(
                "{}; {}",
                render_ghost_stmt(join_stmt),
                render_ghost_stmt(store_stmt)
            ),
        );
        self.trace_bindings([left, right, &ghost_out.0, &ghost_out.1]);
        Ok(())
    }

    fn synthesize_join_join_call<V: Variable>(
        &mut self,
        join_stmt_1: &GhostStmt<V>,
        join_stmt_2: &GhostStmt<V>,
        call_stmt: &GhostStmt<V>,
    ) -> Result<(), String> {
        let (left_1, right_1, inputs_1) = join_parts(join_stmt_1)?;
        let joined_1 = self.join_inputs(inputs_1)?;
        let (left_2, right_2, inputs_2) = join_parts(join_stmt_2)?;

        let (func, args, ghost_need, ghost_left, ghost_ret) = match call_stmt {
            GhostStmt::Call {
                func,
                args,
                ghost_need,
                ghost_left,
                ghost_ret,
                ..
            } => (func, args, ghost_need, ghost_left, ghost_ret),
            _ => unreachable!(),
        };

        if ghost_need.0 != left_1.0 || ghost_left.0 != left_2.0 {
            return Err(format!(
                "call {} does not line up with its synthesized join/splits",
                func.0
            ));
        }

        let signature = self
            .signatures
            .get(&func.0)
            .ok_or_else(|| format!("call to unknown function {}", func.0))?;
        let contract = instantiate_call_contract(signature, args, &ghost_need.0)?;

        self.bind(left_1, contract.sync.clone());
        self.bind(
            right_1,
            PermExpr::Sub(Box::new(joined_1), Box::new(contract.sync.clone())),
        );

        let joined_2 = self.join_inputs(inputs_2)?;
        self.bind(left_2, contract.garb.clone());
        self.bind(
            right_2,
            PermExpr::Sub(Box::new(joined_2), Box::new(contract.garb.clone())),
        );
        self.bind(
            ghost_ret,
            PermExpr::union([contract.sync.clone(), contract.garb.clone()]),
        );

        trace_synthesis_step(
            self.verbose,
            &format!(
                "{}; {}; {}",
                render_ghost_stmt(join_stmt_1),
                render_ghost_stmt(join_stmt_2),
                render_ghost_stmt(call_stmt)
            ),
        );
        self.trace_bindings([left_1, right_1, left_2, right_2, ghost_ret]);
        Ok(())
    }

    fn synthesize_tail_after_join<V: Variable>(
        &mut self,
        join_stmt: &GhostStmt<V>,
        tail: &GhostTail<V>,
    ) -> Result<(), String> {
        match tail {
            GhostTail::Return { perm, .. } => {
                let (left, right, inputs) = join_parts(join_stmt)?;
                let joined = self.join_inputs(inputs)?;
                self.bind(left, joined.clone());
                self.bind(right, PermExpr::empty());
                self.bind(perm, joined);
                trace_synthesis_step(
                    self.verbose,
                    &format!(
                        "{}; {}",
                        render_ghost_stmt(join_stmt),
                        render_ghost_tail(tail)
                    ),
                );
                self.trace_bindings([left, right, perm]);
                Ok(())
            }
            other => Err(format!(
                "single trailing join/split must feed a return, found {}",
                render_ghost_tail(other)
            )),
        }
    }

    fn synthesize_tail_after_two_joins<V: Variable>(
        &mut self,
        join_stmt_1: &GhostStmt<V>,
        join_stmt_2: &GhostStmt<V>,
        tail: &GhostTail<V>,
    ) -> Result<(), String> {
        match tail {
            GhostTail::TailCall {
                func,
                args,
                ghost_need,
                ghost_left,
            } => {
                let (left_1, right_1, inputs_1) = join_parts(join_stmt_1)?;
                let joined_1 = self.join_inputs(inputs_1)?;
                let (left_2, right_2, inputs_2) = join_parts(join_stmt_2)?;

                if ghost_need.0 != left_1.0 || ghost_left.0 != left_2.0 {
                    return Err(format!(
                        "tail call {} does not line up with its synthesized join/splits",
                        func.0
                    ));
                }

                let signature = self
                    .signatures
                    .get(&func.0)
                    .ok_or_else(|| format!("tail call to unknown function {}", func.0))?;
                let contract = instantiate_call_contract(signature, args, &ghost_need.0)?;

                self.bind(left_1, contract.sync.clone());
                self.bind(
                    right_1,
                    PermExpr::Sub(Box::new(joined_1), Box::new(contract.sync)),
                );

                let joined_2 = self.join_inputs(inputs_2)?;
                self.bind(left_2, joined_2.clone());
                self.bind(right_2, PermExpr::empty());

                trace_synthesis_step(
                    self.verbose,
                    &format!(
                        "{}; {}; {}",
                        render_ghost_stmt(join_stmt_1),
                        render_ghost_stmt(join_stmt_2),
                        render_ghost_tail(tail)
                    ),
                );
                self.trace_bindings([left_1, right_1, left_2, right_2]);
                Ok(())
            }
            other => Err(format!(
                "two trailing join/splits must feed a tail call, found {}",
                render_ghost_tail(other)
            )),
        }
    }

    fn bind(&mut self, var: &GhostVar, perm: PermExpr) {
        self.bindings.bind(var, perm);
    }

    fn lookup(&self, var: &GhostVar) -> Result<PermExpr, String> {
        self.bindings
            .lookup(var)
            .cloned()
            .ok_or_else(|| format!("permission variable {} has no synthesized value", var.0))
    }

    fn join_inputs(&self, inputs: &[GhostVar]) -> Result<PermExpr, String> {
        let mut perms = Vec::with_capacity(inputs.len());
        for input in inputs {
            perms.push(self.lookup(input)?);
        }
        Ok(PermExpr::union(perms))
    }

    fn trace_bindings<'b>(&self, vars: impl IntoIterator<Item = &'b GhostVar>) {
        trace_synth_bindings(self.verbose, &self.bindings, vars);
    }
}
