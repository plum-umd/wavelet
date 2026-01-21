use crate::{
    ir::{FnName, Ty, TypedVar, UntypedVar},
    Val,
};

/// Ghost permission variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GhostVar(pub String);

impl From<GhostVar> for TypedVar {
    fn from(gv: GhostVar) -> Self {
        TypedVar {
            name: gv.0,
            ty: Ty::Unit,
        }
    }
}

impl From<GhostVar> for UntypedVar {
    fn from(gv: GhostVar) -> Self {
        UntypedVar(gv.0)
    }
}

/// Ghost-level statements.
#[derive(Clone, Debug, PartialEq)]
pub enum GhostStmt<V> {
    JoinSplit {
        left: GhostVar,
        right: GhostVar,
        inputs: Vec<GhostVar>,
    },
    Pure {
        inputs: Vec<V>,
        output: V,
        op: crate::ir::Op<V>,
        // ghost_in: GhostVar, // pureops now need no token to fire
        ghost_out: GhostVar,
    },
    Const {
        value: Val,
        output: V,
        ghost_in: GhostVar,
        ghost_out: GhostVar,
    },
    Load {
        output: V,
        array: V,
        index: V,
        ghost_in: GhostVar,
        ghost_out: GhostVar,
    },
    Store {
        array: V,
        index: V,
        value: V,
        ghost_in: GhostVar,
        ghost_out: (GhostVar, GhostVar),
    },
    Call {
        outputs: Vec<V>,
        func: FnName,
        args: Vec<V>,
        ghost_need: GhostVar,
        ghost_left: GhostVar,
        ghost_ret: GhostVar,
    },
}

/// Tail expressions in the ghost IR.
#[derive(Clone, Debug, PartialEq)]
pub enum GhostTail<V> {
    Return {
        value: V,
        perm: GhostVar,
    },
    TailCall {
        func: FnName,
        args: Vec<V>,
        ghost_need: GhostVar,
        ghost_left: GhostVar,
    },
    IfElse {
        cond: V,
        then_expr: Box<GhostExpr<V>>,
        else_expr: Box<GhostExpr<V>>,
    },
}

/// Sequenced ghost statements plus a tail.
#[derive(Clone, Debug, PartialEq)]
pub struct GhostExpr<V> {
    pub stmts: Vec<GhostStmt<V>>,
    pub tail: GhostTail<V>,
}

impl<V> GhostExpr<V> {
    pub fn new(stmts: Vec<GhostStmt<V>>, tail: GhostTail<V>) -> Self {
        Self { stmts, tail }
    }
}

/// Ghost function definition.
#[derive(Clone, Debug, PartialEq)]
pub struct GhostFnDef<V> {
    pub name: FnName,
    pub params: Vec<TypedVar>,
    pub ghost_params: Vec<GhostVar>,
    pub caps: Vec<crate::logic::cap::CapPattern>,
    pub returns: Ty,
    pub body: GhostExpr<V>,
}

/// Ghost program consisting of ghost functions.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GhostProgram<V> {
    pub defs: Vec<GhostFnDef<V>>,
}

const GHOST_DISPLAY_INDENT: usize = 2;

impl<V: std::fmt::Display> std::fmt::Display for GhostProgram<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, def) in self.defs.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            writeln!(f, "{}", def)?;
        }
        Ok(())
    }
}

impl<V: std::fmt::Display> std::fmt::Display for GhostFnDef<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}(", self.name.0)?;
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param)?;
        }
        write!(f, "; ")?;
        for (i, gv) in self.ghost_params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", gv.0)?;
        }
        writeln!(f, ") -> {} {{", self.returns)?;
        for line in format!("{}", self.body).lines() {
            writeln!(f, "{:indent$}{}", "", line, indent = GHOST_DISPLAY_INDENT)?;
        }
        write!(f, "}}")
    }
}

impl<V: std::fmt::Display> std::fmt::Display for GhostExpr<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{}", stmt)?;
        }
        write!(f, "{}", self.tail)
    }
}

impl<V: std::fmt::Display> std::fmt::Display for GhostStmt<V> {
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
                write!(f, "{} = {}(", output, op)?;
                for (i, inp) in inputs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", inp)?;
                }
                write!(f, ") [-> {}]", ghost_out.0)
            }
            GhostStmt::Const {
                value,
                output,
                ghost_in,
                ghost_out,
            } => {
                write!(
                    f,
                    "{} = const({}) [{} -> {}]",
                    output, value, ghost_in.0, ghost_out.0
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
                    "{} = load {}[{}] [{} -> {}]",
                    output, array, index, ghost_in.0, ghost_out.0
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
                    "store {}[{}] = {} [{} -> {}, {}]",
                    array, index, value, ghost_in.0, ghost_out.0 .0, ghost_out.1 .0
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
                    write!(f, "{}", out)?;
                }
                write!(f, " = {}(", func.0)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(
                    f,
                    "; {}, {} -> {})",
                    ghost_need.0, ghost_left.0, ghost_ret.0
                )
            }
        }
    }
}

impl<V: std::fmt::Display> std::fmt::Display for GhostTail<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GhostTail::Return { value, perm } => {
                write!(f, "return {} [{}]", value, perm.0)
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
                    write!(f, "{}", arg)?;
                }
                write!(f, "; {}, {})", ghost_need.0, ghost_left.0)
            }
            GhostTail::IfElse {
                cond,
                then_expr,
                else_expr,
            } => {
                writeln!(f, "if {} {{", cond)?;
                for line in format!("{}", then_expr).lines() {
                    writeln!(f, "{:indent$}{}", "", line, indent = GHOST_DISPLAY_INDENT)?;
                }
                writeln!(f, "}} else {{")?;
                for line in format!("{}", else_expr).lines() {
                    writeln!(f, "{:indent$}{}", "", line, indent = GHOST_DISPLAY_INDENT)?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl<V> GhostProgram<V> {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    pub fn add_fn(&mut self, def: GhostFnDef<V>) {
        self.defs.push(def);
    }
}
