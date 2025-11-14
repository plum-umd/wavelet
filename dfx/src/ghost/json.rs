use crate::Val;
use crate::ghost::affine;
use crate::ghost::ir::{GhostExpr, GhostFnDef, GhostProgram, GhostStmt, GhostTail};
use crate::ir::Op;
use serde::Serialize;
use serde::ser::{SerializeMap, Serializer};
use serde_json::{self, Value};
use std::fmt;

/// Errors that can occur while serializing the ghost IR to the Lean-facing JSON format.
#[derive(Debug)]
pub enum ExportError {
    /// A required portion of the serializer has not been implemented yet.
    Unsupported(String),
    /// Wrapper around JSON encoding failures.
    Serde(serde_json::Error),
}

impl fmt::Display for ExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExportError::Unsupported(msg) => write!(f, "serialization not implemented: {msg}"),
            ExportError::Serde(err) => write!(f, "failed to encode JSON: {err}"),
        }
    }
}

impl std::error::Error for ExportError {}

impl From<serde_json::Error> for ExportError {
    fn from(err: serde_json::Error) -> Self {
        ExportError::Serde(err)
    }
}

/// High-level entry point: serialize the ghost program into a JSON string
/// that is intended to match the Lean `RawProg` schema.
pub fn export_program_json(prog: &GhostProgram) -> Result<String, ExportError> {
    let raw = RawProg::try_from(prog)?;
    let raw = affine::enforce_affine(raw);
    serde_json::to_string_pretty(&raw).map_err(ExportError::from)
}

/// Structured representation mirroring the Lean `RawProg` definition.
#[derive(Debug, Serialize)]
pub struct RawProg {
    pub fns: Vec<RawFn>,
}

impl TryFrom<&GhostProgram> for RawProg {
    type Error = ExportError;

    fn try_from(prog: &GhostProgram) -> Result<Self, Self::Error> {
        let mut fns = Vec::with_capacity(prog.defs.len());
        for def in &prog.defs {
            fns.push(RawFn::try_from(def)?);
        }
        Ok(RawProg { fns })
    }
}

/// Structured representation mirroring the Lean `RawFn` definition.
#[derive(Debug, Serialize)]
pub struct RawFn {
    pub name: String,
    pub params: Vec<String>,
    pub outputs: usize,
    pub body: RawExpr,
}

impl TryFrom<&GhostFnDef> for RawFn {
    type Error = ExportError;

    fn try_from(def: &GhostFnDef) -> Result<Self, Self::Error> {
        let name = def.name.0.clone();
        // Include both regular params and ghost params
        let mut params: Vec<String> = def.params.iter().map(|(var, _)| var.0.clone()).collect();
        params.extend(def.ghost_params.iter().map(|gv| gv.0.clone()));
        let outputs = 2; // Fixed to 2: value + permission token
        let body = serialize_body(&def.body)?;
        Ok(RawFn {
            name,
            params,
            outputs,
            body,
        })
    }
}

fn serialize_body(expr: &GhostExpr) -> Result<RawExpr, ExportError> {
    let tail = serialize_tail(&expr.tail)?;
    expr.stmts
        .iter()
        .rev()
        .try_fold(tail, |acc, stmt| wrap_stmt(stmt, acc))
}

fn serialize_tail(tail: &GhostTail) -> Result<RawExpr, ExportError> {
    match tail {
        GhostTail::Return { value, perm } => {
            Ok(RawExpr::Ret(vec![value.0.clone(), perm.0.clone()]))
        }
        GhostTail::TailCall {
            func: _,
            args,
            ghost_need,
            ghost_left,
        } => {
            let mut tail_args = args.iter().map(|v| v.0.clone()).collect::<Vec<_>>();
            tail_args.push(ghost_need.0.clone());
            tail_args.push(ghost_left.0.clone());
            Ok(RawExpr::Tail(tail_args))
        }
        GhostTail::IfElse {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = cond.0.clone();
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

fn wrap_stmt(stmt: &GhostStmt, cont: RawExpr) -> Result<RawExpr, ExportError> {
    match stmt {
        GhostStmt::Pure {
            inputs,
            output,
            op,
            ghost_out,
        } => {
            let op = WithCall::Op(WithSpec::Spec {
                ghost: false,
                op: map_sync_op(op)?,
            });
            let args: Vec<String> = inputs.iter().map(|v| v.0.clone()).collect();
            let outputs = vec![output.0.clone(), ghost_out.0.clone()];
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
            ghost_out,
        } => {
            let val = match value {
                Val::Int(i) => *i as i64,
                Val::Bool(b) => {
                    if *b {
                        1
                    } else {
                        0
                    }
                }
                Val::Unit => 0,
            };
            let op = WithCall::Op(WithSpec::Spec {
                ghost: false,
                op: SyncOp::Const { value: val },
            });
            let args = vec![ghost_in.0.clone()];
            let outputs = vec![output.0.clone(), ghost_out.0.clone()];
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
                    loc: array.0.clone(),
                },
            });
            let args = vec![index.0.clone(), ghost_in.0.clone()];
            let outputs = vec![output.0.clone(), ghost_out.0.clone()];
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
                    loc: array.0.clone(),
                },
            });
            let args = vec![index.0.clone(), value.0.clone(), ghost_in.0.clone()];
            let outputs = vec![ghost_out.0.0.clone(), ghost_out.1.0.clone()];
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
            let args: Vec<String> = inputs.iter().map(|v| v.0.clone()).collect();
            let outputs = vec![left.0.clone(), right.0.clone()];
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
            let mut call_args: Vec<String> = args.iter().map(|v| v.0.clone()).collect();
            call_args.push(ghost_need.0.clone());
            call_args.push(ghost_left.0.clone());
            let rets: Vec<String> = outputs.iter().map(|v| v.0.clone()).collect();
            let mut all_rets = rets;
            all_rets.push(ghost_ret.0.clone());
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
pub enum RawExpr {
    Ret(Vec<String>),
    Tail(Vec<String>),
    Op {
        op: WithCall,
        args: Vec<String>,
        rets: Vec<String>,
        cont: Box<RawExpr>,
    },
    Br {
        cond: String,
        left: Box<RawExpr>,
        right: Box<RawExpr>,
    },
}

impl Serialize for RawExpr {
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
pub enum SyncOp {
    Add,
    Sub,
    Mul,
    Div,
    Shl,
    Ashr,
    Lshr,
    Eq,
    Neq,
    BitAnd,
    BitOr,
    BitXor,
    Lt,
    Le,
    And,
    Or,
    Load { loc: String },
    Store { loc: String },
    Sel,
    Const { value: i64 },
    Copy { n: usize },
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
            SyncOp::Div => serializer.serialize_str("div"),
            SyncOp::Shl => serializer.serialize_str("shl"),
            SyncOp::Ashr => serializer.serialize_str("ashr"),
            SyncOp::Lshr => serializer.serialize_str("lshr"),
            SyncOp::Eq => serializer.serialize_str("eq"),
            SyncOp::Neq => serializer.serialize_str("neq"),
            SyncOp::BitAnd => serializer.serialize_str("bitand"),
            SyncOp::BitOr => serializer.serialize_str("bitor"),
            SyncOp::BitXor => serializer.serialize_str("bitxor"),
            SyncOp::Lt => serializer.serialize_str("lt"),
            SyncOp::Le => serializer.serialize_str("le"),
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
                map.serialize_entry("copy", &(n - 2))?;
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

fn map_sync_op(op: &Op) -> Result<SyncOp, ExportError> {
    match op {
        Op::Add => Ok(SyncOp::Add),
        Op::Sub => Ok(SyncOp::Sub),
        Op::Mul => Ok(SyncOp::Mul),
        Op::Div => Ok(SyncOp::Div),
        Op::And => Ok(SyncOp::And),
        Op::Or => Ok(SyncOp::Or),
        Op::Shl => Ok(SyncOp::Shl),
        Op::Shr => Ok(SyncOp::Ashr),
        Op::Equal => Ok(SyncOp::Eq),
        Op::NotEqual => Ok(SyncOp::Neq),
        Op::BitAnd => Ok(SyncOp::BitAnd),
        Op::BitOr => Ok(SyncOp::BitOr),
        Op::BitXor => Ok(SyncOp::BitXor),
        Op::LessThan => Ok(SyncOp::Lt),
        Op::LessEqual => Ok(SyncOp::Le),
        _ => Err(ExportError::Unsupported(format!(
            "pure operation {} not yet supported for serialization",
            op
        ))),
    }
}
