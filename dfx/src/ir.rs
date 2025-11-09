//! Intermediate representation for the restricted language.

use crate::logic::cap::CapPattern;

/// A variable name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub String);

/// A function name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnName(pub String);

/// Length of a fixed-size array.  Either a concrete literal length or
/// a symbolic identifier originating from a const generic parameter.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ArrayLen {
    /// Statically known constant length.
    Const(usize),
    /// Symbolic length (e.g. a const generic parameter `N`).
    Symbol(String),
}

impl ArrayLen {
    /// Return a human-readable representation used in error messages.
    pub fn display(&self) -> String {
        match self {
            ArrayLen::Const(n) => n.to_string(),
            ArrayLen::Symbol(name) => name.clone(),
        }
    }
}

impl From<usize> for ArrayLen {
    fn from(len: usize) -> Self {
        ArrayLen::Const(len)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Signedness {
    Signed,
    Unsigned,
}

/// Types in the language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// Integer type.
    Int(Signedness),
    /// Boolean type.
    Bool,
    /// Unit type.
    Unit,
    /// Shared reference to a fixed-size array.
    RefShrd { elem: Box<Ty>, len: ArrayLen },
    /// Unique (mutable) reference to a fixed-size array.
    RefUniq { elem: Box<Ty>, len: ArrayLen },
}

impl Ty {
    /// Check if this type is an integer type.
    pub fn is_int(&self) -> bool {
        matches!(self, Ty::Int(_))
    }

    /// Return the signedness for integer types.
    pub fn signedness(&self) -> Option<Signedness> {
        match self {
            Ty::Int(sign) => Some(*sign),
            _ => None,
        }
    }
}

/// Literal values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    /// Integer literal.
    Int(i64),
    /// Boolean literal.
    Bool(bool),
    /// Unit value.
    Unit,
}

/// Primitive operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    /// Integer addition: x + y
    Add,
    /// Integer subtraction: x - y
    Sub,
    /// Integer multiplication: x * y
    Mul,
    /// Integer division: x / y
    Div,
    /// Boolean conjunction: x && y
    And,
    /// Boolean disjunction: x || y
    Or,
    /// Bitwise and: x & y
    BitAnd,
    /// Bitwise or: x | y
    BitOr,
    /// Bitwise xor: x ^ y
    BitXor,
    /// Left shift: x << y
    Shl,
    /// Right shift: x >> y
    Shr,
    /// Integer less-than comparison: x < y
    LessThan,
    /// Integer less-than-or-equal comparison: x <= y
    LessEqual,
    /// Equality comparison: x == y
    Equal,
    /// Integer cast between widths.
    Cast,
    /// Load from array.
    Load {
        /// Array variable to load from.
        array: Var,
        /// Index variable.
        index: Var,
        /// Length of the array.
        len: ArrayLen,
        /// Whether this is a fenced operation (fence doesn't consume capability).
        fence: bool,
    },
    /// Store to array.
    Store {
        /// Array variable to store to.
        array: Var,
        /// Index variable.
        index: Var,
        /// Value variable to store.
        value: Var,
        /// Length of the array.
        len: ArrayLen,
        /// Whether this is a fenced operation (fence doesn't consume capability).
        fence: bool,
    },
}

/// Statements in the language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    /// Bind a variable to a literal value.
    LetVal { var: Var, val: Val },
    /// Bind variables to the result of a primitive operation.
    LetOp { vars: Vec<Var>, op: Op },
    /// Bind variables to the result of a function call.
    LetCall {
        /// Result variables.
        vars: Vec<Var>,
        /// Function to call.
        func: FnName,
        /// Argument variables.
        args: Vec<Var>,
        /// Whether this is a fenced call (fence doesn't consume capabilities).
        fence: bool,
    },
}

/// Tail expressions that determine control flow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tail {
    /// Return a variable.
    RetVar(Var),
    /// Conditional expression.
    IfElse {
        /// Condition variable (must be boolean).
        cond: Var,
        /// Then branch.
        then_e: Box<Expr>,
        /// Else branch.
        else_e: Box<Expr>,
    },
    /// Tail call to a function.
    TailCall {
        /// Function to call.
        func: FnName,
        /// Argument variables.
        args: Vec<Var>,
    },
}

/// An expression consists of a sequence of statements followed by a tail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    /// Statements executed in sequence.
    pub stmts: Vec<Stmt>,
    /// Tail expression that determines the result.
    pub tail: Tail,
}

impl Expr {
    /// Create a new expression from statements and a tail.
    pub fn new(stmts: Vec<Stmt>, tail: Tail) -> Self {
        Self { stmts, tail }
    }

    /// Create an expression that simply returns a variable.
    pub fn ret(var: Var) -> Self {
        Self {
            stmts: Vec::new(),
            tail: Tail::RetVar(var),
        }
    }
}

/// A function definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDef {
    /// Function name.
    pub name: FnName,
    /// Parameter list: (variable, type) pairs.
    pub params: Vec<(Var, Ty)>,
    /// Capability patterns required by this function.
    pub caps: Vec<CapPattern>,
    /// Return type.
    pub returns: Ty,
    /// Function body.
    pub body: Expr,
}

/// A complete program consists of a list of function definitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    /// Function definitions.
    pub defs: Vec<FnDef>,
}

impl std::fmt::Display for Program {
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

impl std::fmt::Display for FnDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (i, (var, ty)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", var, ty)?;
        }
        write!(f, ")")?;
        if !self.caps.is_empty() {
            write!(f, " requires [")?;
            for (i, cap) in self.caps.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?}", cap)?;
            }
            write!(f, "]")?;
        }
        writeln!(f, " -> {} {{", self.returns)?;
        write!(f, "{}", self.body)?;
        writeln!(f, "}}")
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "  {}", stmt)?;
        }
        writeln!(f, "  {}", self.tail)
    }
}

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::LetVal { var, val } => write!(f, "let {} = {};", var, val),
            Stmt::LetOp { vars, op } => {
                write!(f, "let ")?;
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, " = {};", op)
            }
            Stmt::LetCall {
                vars,
                func,
                args,
                fence,
            } => {
                write!(f, "let ")?;
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, " = {}{}(", if *fence { "@" } else { "" }, func)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ");")
            }
        }
    }
}

impl std::fmt::Display for Tail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Tail::RetVar(var) => write!(f, "return {};", var),
            Tail::IfElse {
                cond,
                then_e,
                else_e,
            } => {
                writeln!(f, "if {} {{", cond)?;
                write!(f, "{}", then_e)?;
                writeln!(f, "}} else {{")?;
                write!(f, "{}", else_e)?;
                write!(f, "}}")
            }
            Tail::TailCall { func, args } => {
                write!(f, "{}(", func)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ");")
            }
        }
    }
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Add => write!(f, "+"),
            Op::Sub => write!(f, "-"),
            Op::Mul => write!(f, "*"),
            Op::Div => write!(f, "/"),
            Op::And => write!(f, "&&"),
            Op::Or => write!(f, "||"),
            Op::BitAnd => write!(f, "&"),
            Op::BitOr => write!(f, "|"),
            Op::BitXor => write!(f, "^"),
            Op::Shl => write!(f, "<<"),
            Op::Shr => write!(f, ">>"),
            Op::LessThan => write!(f, "<"),
            Op::LessEqual => write!(f, "<="),
            Op::Equal => write!(f, "=="),
            Op::Cast => write!(f, "cast"),
            Op::Load {
                array,
                index,
                len,
                fence,
            } => {
                write!(
                    f,
                    "{}{}[{}:{}]",
                    if *fence { "@" } else { "" },
                    array,
                    index,
                    len.display()
                )
            }
            Op::Store {
                array,
                index,
                value,
                len,
                fence,
            } => {
                write!(
                    f,
                    "{}{}[{}:{}] = {}",
                    if *fence { "@" } else { "" },
                    array,
                    index,
                    len.display(),
                    value
                )
            }
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Int(Signedness::Signed) => write!(f, "int"),
            Ty::Int(Signedness::Unsigned) => write!(f, "uint"),
            Ty::Bool => write!(f, "bool"),
            Ty::Unit => write!(f, "()"),
            Ty::RefShrd { elem, len } => write!(f, "&[{}; {}]", elem, len.display()),
            Ty::RefUniq { elem, len } => write!(f, "&mut [{}; {}]", elem, len.display()),
        }
    }
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::Int(n) => write!(f, "{}", n),
            Val::Bool(b) => write!(f, "{}", b),
            Val::Unit => write!(f, "()"),
        }
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for FnName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Program {
    /// Create a new empty program.
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    /// Add a function definition to the program.
    pub fn add_fn(&mut self, def: FnDef) {
        self.defs.push(def);
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}
