use crate::{
    Val,
    ir::{FnName, Ty, Var},
};

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
        inputs: Vec<Var>,
        output: Var,
        op: crate::ir::Op,
        // ghost_in: GhostVar, // pureops now need no token to fire
        ghost_out: GhostVar,
    },
    Const {
        value: Val,
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
        ghost_out: (GhostVar, GhostVar),
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
    pub caps: Vec<crate::logic::cap::CapPattern>,
    pub returns: Ty,
    pub body: GhostExpr,
}

/// Ghost program consisting of ghost functions.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GhostProgram {
    pub defs: Vec<GhostFnDef>,
}

impl std::fmt::Display for GhostProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, def) in self.defs.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{}", def)?;
        }
        Ok(())
    }
}

impl std::fmt::Display for GhostFnDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}(", self.name.0)?;
        for (i, (var, ty)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", var.0, ty)?;
        }
        write!(f, "; ")?;
        for (i, gv) in self.ghost_params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", gv.0)?;
        }
        writeln!(f, ") -> {} {{", self.returns)?;
        write!(f, "{}", self.body)?;
        writeln!(f, "}}")
    }
}

impl std::fmt::Display for GhostExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "    {}", stmt)?;
        }
        write!(f, "    {}", self.tail)
    }
}

impl std::fmt::Display for GhostStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GhostStmt::JoinSplit {
                left,
                right,
                inputs,
            } => {
                write!(f, "{}, {} <- ", left.0, right.0)?;
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", input.0)?;
                }
                Ok(())
            }
            GhostStmt::Pure {
                inputs,
                output,
                op,
                ghost_out,
            } => {
                // output should look like: out = op(inp1, inp2, ...) [-> ghost_out]
                write!(f, "{} = {}(", output.0, op)?;
                for (i, inp) in inputs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", inp.0)?;
                }
                write!(f, ") [->{}]", ghost_out.0)
            }
            GhostStmt::Const {
                value,
                output,
                ghost_in,
                ghost_out,
            } => {
                write!(
                    f,
                    "{} = const({}) [{}->{}]",
                    output.0, value, ghost_in.0, ghost_out.0
                )
            }
            GhostStmt::Load {
                output,
                array,
                index,
                ghost_in,
                ghost_out,
            } => {
                write!(
                    f,
                    "{} = load {}[{}] [{}->{}]",
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
                write!(
                    f,
                    "store {}[{}] = {} [{}->({}, {})]",
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
                for (i, out) in outputs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", out.0)?;
                }
                write!(f, " = {}(", func.0)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg.0)?;
                }
                write!(f, "; {}, {} ->{})", ghost_need.0, ghost_left.0, ghost_ret.0)
            }
        }
    }
}

impl std::fmt::Display for GhostTail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GhostTail::Return { value, perm } => {
                write!(f, "return {} [{}]", value.0, perm.0)
            }
            GhostTail::TailCall {
                func,
                args,
                ghost_need,
                ghost_left,
            } => {
                write!(f, "{}(", func.0)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg.0)?;
                }
                write!(f, "; {}, {})", ghost_need.0, ghost_left.0)
            }
            GhostTail::IfElse {
                cond,
                then_expr,
                else_expr,
            } => {
                writeln!(f, "if {} {{", cond.0)?;
                write!(f, "{}", then_expr)?;
                writeln!(f, "\n    }} else {{")?;
                write!(f, "{}", else_expr)?;
                write!(f, "\n    }}")
            }
        }
    }
}

impl GhostProgram {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    pub fn add_fn(&mut self, def: GhostFnDef) {
        self.defs.push(def);
    }
}
