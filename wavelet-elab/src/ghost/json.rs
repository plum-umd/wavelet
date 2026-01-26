use crate::ghost::affine;
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostProgram, GhostStmt, GhostTail, GhostVar};
use crate::ir::{ArrayLen, ArrayLenError, Op, Variable};
use crate::{FnDef, Ty, TypedVar, UntypedVar, Val};

use serde::ser::{SerializeMap, Serializer};
use serde::Serialize;
use serde_json::{self, Value};
use std::collections::HashMap;
use thiserror::Error;

/// Errors that can occur while serializing the ghost IR to the Lean-facing JSON format.
#[derive(Error, Debug)]
pub enum ExportError {
    /// A required portion of the serializer has not been implemented yet.
    #[error("unsupported: {0}")]
    Unsupported(String),
    /// Wrapper around JSON encoding failures.
    #[error("JSON serialization error: {0}")]
    Serde(#[from] serde_json::Error),
    #[error("failed to evaluate array length `{0:?}`: {1}")]
    ArrayLenEvalError(ArrayLen, #[source] ArrayLenError),
    #[error("negative array length `{0:?} = {1}`")]
    NegativeArrayLength(ArrayLen, i64),
}

/// High-level entry point: serialize the ghost program into a JSON string
/// that is intended to match the Lean `RawProg` schema.
pub fn export_program_json<V: Variable + Serialize + From<GhostVar>>(
    arrays: Vec<RawArrayDecl>,
    prog: &GhostProgram<V>,
) -> Result<String, ExportError> {
    let raw = RawProg::try_from(arrays, prog)?;
    let raw = affine::enforce_affine(raw);
    serde_json::to_string_pretty(&raw).map_err(ExportError::from)
}

/// A global array declaration.
#[derive(Debug, Serialize)]

pub struct RawArrayDecl {
    pub loc: String,
    pub elem: Ty,
    pub size: usize,
    pub external: bool,
}

/// Structured representation mirroring the Lean `RawProg` definition.
#[derive(Debug, Serialize)]
pub struct RawProg<V> {
    pub arrays: Vec<RawArrayDecl>,
    pub fns: Vec<RawFn<V>>,
}

impl<V: Variable + From<GhostVar>> RawProg<V> {
    pub fn try_from(
        arrays: Vec<RawArrayDecl>,
        prog: &GhostProgram<V>,
    ) -> Result<Self, ExportError> {
        let mut fns = Vec::with_capacity(prog.defs.len());
        for def in &prog.defs {
            fns.push(RawFn::try_from(def)?);
        }
        Ok(RawProg { arrays, fns })
    }
}

/// Structured representation mirroring the Lean `RawFn` definition.
#[derive(Debug, Serialize)]
pub struct RawFn<V> {
    pub name: String,
    pub params: Vec<TypedVar>,
    pub rets: Vec<TypedVar>,
    pub body: RawExpr<V>,
}

impl<V: Variable + From<GhostVar>> TryFrom<&GhostFnDef<V>> for RawFn<V> {
    type Error = ExportError;

    fn try_from(def: &GhostFnDef<V>) -> Result<Self, Self::Error> {
        let name = def.name.0.clone();
        // Include both regular params and ghost params
        let mut params = def.params.clone();
        params.extend(def.ghost_params.iter().map(|gv| gv.clone().into()));
        let body = serialize_body(&def.body)?;
        Ok(RawFn {
            name,
            params,
            // Fixed to 2: value + permission token
            rets: vec![
                TypedVar::new("ret".to_string(), def.returns.clone()),
                TypedVar::new("perm".to_string(), Ty::Unit),
            ],
            body,
        })
    }
}

impl<V> FnDef<V> {
    /// Returns all array declarations used in the function
    pub fn get_array_decls(
        &self,
        bindings: &HashMap<String, i64>,
    ) -> Result<Vec<RawArrayDecl>, ExportError> {
        let mut arrays = Vec::new();
        for param in &self.params {
            match &param.ty {
                Ty::RefShrd { elem, len } | Ty::RefUniq { elem, len } => {
                    let eval_len = len
                        .eval(&bindings)
                        .map_err(|e| ExportError::ArrayLenEvalError(len.clone(), e))?;

                    if eval_len < 0 {
                        return Err(ExportError::NegativeArrayLength(len.clone(), eval_len));
                    }

                    arrays.push(RawArrayDecl {
                        loc: param.name.clone(),
                        elem: elem.as_ref().clone(),
                        size: eval_len as usize,
                        external: !self.alloc_arrays.contains(&param.name),
                    });
                }
                _ => {}
            }
        }
        Ok(arrays)
    }
}

fn serialize_body<V: Variable + From<GhostVar>>(
    expr: &GhostExpr<V>,
) -> Result<RawExpr<V>, ExportError> {
    let tail = serialize_tail(&expr.tail)?;
    expr.stmts
        .iter()
        .rev()
        .try_fold(tail, |acc, stmt| wrap_stmt(stmt, acc))
}

fn serialize_tail<V: Variable + From<GhostVar>>(
    tail: &GhostTail<V>,
) -> Result<RawExpr<V>, ExportError> {
    match tail {
        GhostTail::Return { value, perm } => {
            Ok(RawExpr::Ret(vec![value.clone(), perm.clone().into()]))
        }
        GhostTail::TailCall {
            func: _,
            args,
            ghost_need,
            ghost_left,
        } => {
            let mut tail_args = args.iter().map(|v| v.clone()).collect::<Vec<_>>();
            tail_args.push(ghost_need.clone().into());
            tail_args.push(ghost_left.clone().into());
            Ok(RawExpr::Tail(tail_args))
        }
        GhostTail::IfElse {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = cond.clone();
            let left = serialize_body(then_expr)?;
            let right = serialize_body(else_expr)?;
            Ok(RawExpr::Br {
                cond,
                left: Box::new(left),
                right: Box::new(right),
            })
        }
    }
}

fn wrap_stmt<V: Variable + From<GhostVar>>(
    stmt: &GhostStmt<V>,
    cont: RawExpr<V>,
) -> Result<RawExpr<V>, ExportError> {
    match stmt {
        GhostStmt::Pure { inputs, output, op } => {
            let op = WithCall::Op(WithSpec::Spec {
                ghost: false,
                op: map_sync_op(op)?,
            });
            let args: Vec<V> = inputs.clone();
            let outputs = vec![output.clone()];
            Ok(RawExpr::Op {
                op,
                args,
                rets: outputs,
                cont: Box::new(cont),
            })
        }
        GhostStmt::Const {
            value,
            output,
            ghost_in,
        } => {
            let val = match value {
                Val::Int(i) => ConstValue::Int(32, *i as u64),
                Val::Bool(b) => {
                    if *b {
                        ConstValue::Int(1, 1)
                    } else {
                        ConstValue::Int(1, 0)
                    }
                }
                Val::Unit => ConstValue::Int(0, 0),
            };
            let op = WithCall::Op(WithSpec::Spec {
                ghost: false,
                op: SyncOp::Const { value: val },
            });
            let args = vec![ghost_in.clone().into()];
            let outputs = vec![output.clone()];
            Ok(RawExpr::Op {
                op,
                args,
                rets: outputs,
                cont: Box::new(cont),
            })
        }
        GhostStmt::Load {
            output,
            array,
            index,
            ghost_in,
            ghost_out,
        } => {
            let op = WithCall::Op(WithSpec::Spec {
                ghost: true,
                op: SyncOp::Load {
                    loc: array.name().to_string(),
                },
            });
            let args = vec![index.clone(), ghost_in.clone().into()];
            let outputs = vec![output.clone(), ghost_out.clone().into()];
            Ok(RawExpr::Op {
                op,
                args,
                rets: outputs,
                cont: Box::new(cont),
            })
        }
        GhostStmt::Store {
            array,
            index,
            value,
            ghost_in,
            ghost_out,
        } => {
            let op = WithCall::Op(WithSpec::Spec {
                ghost: true,
                op: SyncOp::Store {
                    loc: array.name().to_string(),
                },
            });
            let args = vec![index.clone(), value.clone(), ghost_in.clone().into()];
            let outputs = vec![ghost_out.0.clone().into(), ghost_out.1.clone().into()];
            Ok(RawExpr::Op {
                op,
                args,
                rets: outputs,
                cont: Box::new(cont),
            })
        }
        GhostStmt::JoinSplit {
            left,
            right,
            inputs,
        } => {
            let toks = inputs.len();
            let deps = 0; // No value dependencies for join/split
            let op = WithCall::Op(WithSpec::Join { toks, deps });
            let args: Vec<V> = inputs.iter().map(|v| v.clone().into()).collect();
            let outputs = vec![left.clone().into(), right.clone().into()];
            Ok(RawExpr::Op {
                op,
                args,
                rets: outputs,
                cont: Box::new(cont),
            })
        }
        GhostStmt::Call {
            outputs,
            func,
            args,
            ghost_need,
            ghost_left,
            ghost_ret,
        } => {
            let op = WithCall::Call(func.0.clone());
            let mut call_args: Vec<V> = args.clone();
            call_args.push(ghost_need.clone().into());
            call_args.push(ghost_left.clone().into());
            let rets: Vec<V> = outputs.clone();
            let mut all_rets = rets;
            all_rets.push(ghost_ret.clone().into());
            Ok(RawExpr::Op {
                op,
                args: call_args,
                rets: all_rets,
                cont: Box::new(cont),
            })
        }
    }
}

#[derive(Debug)]
pub enum RawExpr<V> {
    Ret(Vec<V>),
    Tail(Vec<V>),
    Op {
        op: WithCall,
        args: Vec<V>,
        rets: Vec<V>,
        cont: Box<RawExpr<V>>,
    },
    Br {
        cond: V,
        left: Box<RawExpr<V>>,
        right: Box<RawExpr<V>>,
    },
}

impl<V: Serialize> Serialize for RawExpr<V> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            RawExpr::Ret(values) => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("ret", values)?;
                map.end()
            }
            RawExpr::Tail(values) => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("tail", values)?;
                map.end()
            }
            RawExpr::Op {
                op,
                args,
                rets,
                cont,
            } => {
                let mut payload = Vec::<Value>::with_capacity(4);
                payload.push(serde_json::to_value(op).map_err(serde::ser::Error::custom)?);
                payload.push(serde_json::to_value(args).map_err(serde::ser::Error::custom)?);
                payload.push(serde_json::to_value(rets).map_err(serde::ser::Error::custom)?);
                payload.push(serde_json::to_value(cont).map_err(serde::ser::Error::custom)?);
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("op", &payload)?;
                map.end()
            }
            RawExpr::Br { cond, left, right } => {
                let mut payload = Vec::<Value>::with_capacity(3);
                payload.push(serde_json::to_value(cond).map_err(serde::ser::Error::custom)?);
                payload.push(serde_json::to_value(left).map_err(serde::ser::Error::custom)?);
                payload.push(serde_json::to_value(right).map_err(serde::ser::Error::custom)?);
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("br", &payload)?;
                map.end()
            }
        }
    }
}

#[derive(Debug)]
pub enum WithCall {
    Op(WithSpec),
    Call(String),
}

impl Serialize for WithCall {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(1))?;
        match self {
            WithCall::Op(spec) => {
                map.serialize_entry("op", spec)?;
            }
            WithCall::Call(name) => {
                map.serialize_entry("call", name)?;
            }
        }
        map.end()
    }
}

#[derive(Debug)]
pub enum WithSpec {
    Spec { ghost: bool, op: SyncOp },
    Join { toks: usize, deps: usize },
}

impl Serialize for WithSpec {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(1))?;
        match self {
            WithSpec::Spec { ghost, op } => {
                let key = if *ghost { "op_ghost" } else { "op" };
                map.serialize_entry(key, op)?;
            }
            WithSpec::Join { toks, deps } => {
                #[derive(Serialize)]
                struct JoinPayload {
                    toks: usize,
                    deps: usize,
                }
                map.serialize_entry(
                    "join",
                    &JoinPayload {
                        toks: *toks,
                        deps: *deps,
                    },
                )?;
            }
        }
        map.end()
    }
}

#[derive(Debug)]
pub enum ConstValue {
    Int(usize, u64),
}

#[derive(Debug)]
pub enum SyncOp {
    Add,
    Sub,
    Mul,
    Sdiv,
    Udiv,
    Shl,
    Ashr,
    Lshr,
    Eq,
    Neq,
    BitAnd,
    BitOr,
    BitXor,
    Slt,
    Sle,
    Ult,
    Ule,
    And,
    Or,
    Load { loc: String },
    Store { loc: String },
    Sel,
    Const { value: ConstValue },
    Copy { n: usize },
}

impl Serialize for ConstValue {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            ConstValue::Int(w, v) => {
                let mut map = serializer.serialize_map(Some(1))?;
                let mut inner = serde_json::Map::with_capacity(2);
                inner.insert("width".to_string(), serde_json::Value::from(*w));
                inner.insert("value".to_string(), serde_json::Value::from(*v));
                map.serialize_entry("int", &inner)?;
                map.end()
            }
        }
    }
}

impl Serialize for SyncOp {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            SyncOp::Add => serializer.serialize_str("add"),
            SyncOp::Sub => serializer.serialize_str("sub"),
            SyncOp::Mul => serializer.serialize_str("mul"),
            SyncOp::Sdiv => serializer.serialize_str("sdiv"),
            SyncOp::Udiv => serializer.serialize_str("udiv"),
            SyncOp::Shl => serializer.serialize_str("shl"),
            SyncOp::Ashr => serializer.serialize_str("ashr"),
            SyncOp::Lshr => serializer.serialize_str("lshr"),
            SyncOp::Eq => serializer.serialize_str("eq"),
            SyncOp::Neq => serializer.serialize_str("neq"),
            SyncOp::BitAnd => serializer.serialize_str("bitand"),
            SyncOp::BitOr => serializer.serialize_str("bitor"),
            SyncOp::BitXor => serializer.serialize_str("bitxor"),
            SyncOp::Slt => serializer.serialize_str("slt"),
            SyncOp::Sle => serializer.serialize_str("sle"),
            SyncOp::Ult => serializer.serialize_str("ult"),
            SyncOp::Ule => serializer.serialize_str("ule"),
            SyncOp::And => serializer.serialize_str("and"),
            SyncOp::Or => serializer.serialize_str("or"),
            SyncOp::Sel => serializer.serialize_str("sel"),
            SyncOp::Const { value } => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("const", value)?;
                map.end()
            }
            SyncOp::Copy { n } => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("copy", &(n - 1))?;
                map.end()
            }
            SyncOp::Load { loc } => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("load", loc)?;
                map.end()
            }
            SyncOp::Store { loc } => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("store", loc)?;
                map.end()
            }
        }
    }
}

/// BUG: Div/LessThan/LessEqual should not always map to signed versions.
fn map_sync_op<V: Variable>(op: &Op<V>) -> Result<SyncOp, ExportError> {
    match op {
        Op::Add => Ok(SyncOp::Add),
        Op::Sub => Ok(SyncOp::Sub),
        Op::Mul => Ok(SyncOp::Mul),
        Op::Sdiv => Ok(SyncOp::Sdiv),
        Op::Udiv => Ok(SyncOp::Udiv),
        Op::And => Ok(SyncOp::And),
        Op::Or => Ok(SyncOp::Or),
        Op::Shl => Ok(SyncOp::Shl),
        Op::Ashr => Ok(SyncOp::Ashr),
        Op::Lshr => Ok(SyncOp::Lshr),
        Op::Equal => Ok(SyncOp::Eq),
        Op::NotEqual => Ok(SyncOp::Neq),
        Op::BitAnd => Ok(SyncOp::BitAnd),
        Op::BitOr => Ok(SyncOp::BitOr),
        Op::BitXor => Ok(SyncOp::BitXor),
        Op::SignedLessThan => Ok(SyncOp::Slt),
        Op::SignedLessEqual => Ok(SyncOp::Sle),
        Op::UnsignedLessThan => Ok(SyncOp::Ult),
        Op::UnsignedLessEqual => Ok(SyncOp::Ule),
        _ => Err(ExportError::Unsupported(format!(
            "pure operation {:?} not yet supported for serialization",
            op
        ))),
    }
}

impl Serialize for UntypedVar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl Serialize for TypedVar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(2))?;
        map.serialize_entry("name", &self.name)?;
        map.serialize_entry("ty", &self.ty)?;
        map.end()
    }
}

impl Serialize for Ty {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Ty::Int(..) => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("int", &32)?;
                map.end()
            }
            Ty::Bool => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("int", &1)?;
                map.end()
            }
            Ty::Unit | Ty::RefShrd { .. } | Ty::RefUniq { .. } => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("int", &0)?;
                map.end()
            }
        }
    }
}
