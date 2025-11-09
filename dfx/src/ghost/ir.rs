use crate::ir::{FnName, Ty, Var};

/// Ghost permission variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GhostVar(pub String);

/// Ghost-level statements.
#[derive(Clone, Debug, PartialEq)]
pub enum GhostStmt {
    JoinSplit {
        left: GhostVar,
        right: GhostVar,
        inputs: Vec<GhostVar>,
    },
    Pure {
        outputs: Vec<Var>,
        op: crate::ir::Op,
        ghost_in: GhostVar,
        ghost_out: GhostVar,
    },
    Const {
        output: Var,
        ghost_in: GhostVar,
        ghost_out: GhostVar,
    },
    Load {
        output: Var,
        array: Var,
        index: Var,
        ghost_in: GhostVar,
        ghost_out: GhostVar,
    },
    Store {
        array: Var,
        index: Var,
        value: Var,
        ghost_in: GhostVar,
        ghost_out: GhostVar,
    },
    Call {
        outputs: Vec<Var>,
        func: FnName,
        args: Vec<Var>,
        ghost_need: GhostVar,
        ghost_left: GhostVar,
        ghost_ret: GhostVar,
    },
}

/// Tail expressions in the ghost IR.
#[derive(Clone, Debug, PartialEq)]
pub enum GhostTail {
    Return {
        value: Var,
        perm: GhostVar,
    },
    TailCall {
        func: FnName,
        args: Vec<Var>,
        ghost_need: GhostVar,
        ghost_left: GhostVar,
    },
    IfElse {
        cond: Var,
        then_expr: Box<GhostExpr>,
        else_expr: Box<GhostExpr>,
    },
}

/// Sequenced ghost statements plus a tail.
#[derive(Clone, Debug, PartialEq)]
pub struct GhostExpr {
    pub stmts: Vec<GhostStmt>,
    pub tail: GhostTail,
}

impl GhostExpr {
    pub fn new(stmts: Vec<GhostStmt>, tail: GhostTail) -> Self {
        Self { stmts, tail }
    }
}

/// Ghost function definition.
#[derive(Clone, Debug, PartialEq)]
pub struct GhostFnDef {
    pub name: FnName,
    pub params: Vec<(Var, Ty)>,
    pub ghost_params: Vec<GhostVar>,
    pub returns: Ty,
    pub body: GhostExpr,
}

/// Ghost program consisting of ghost functions.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GhostProgram {
    pub defs: Vec<GhostFnDef>,
}

impl GhostProgram {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    pub fn add_fn(&mut self, def: GhostFnDef) {
        self.defs.push(def);
    }
}
