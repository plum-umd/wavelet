//! Intermediate representation for the restricted language.

use crate::logic::syntactic::cap::CapPattern;

/// A variable name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub String);

/// A function name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnName(pub String);

/// Types in the language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// Integer type.
    Int,
    /// Boolean type.
    Bool,
    /// Unit type.
    Unit,
    /// Fixed-size array type.
    Array { elem: Box<Ty>, len: usize },
    /// Shared reference to a fixed-size array.
    RefShrd { elem: Box<Ty>, len: usize },
    /// Unique (mutable) reference to a fixed-size array.
    RefUniq { elem: Box<Ty>, len: usize },
}

impl Ty {
    /// Check if this type is an integer type.
    pub fn is_int(&self) -> bool {
        matches!(self, Ty::Int)
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
    /// Integer less-than comparison: x < y
    LessThan,
    /// Integer less-than-or-equal comparison: x <= y
    LessEqual,
    /// Equality comparison: x == y
    Equal,
    /// Conversion to i32
    IntoI32,
    /// Load from array.
    Load {
        /// Array variable to load from.
        array: Var,
        /// Index variable.
        index: Var,
        /// Length of the array.
        len: usize,
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
        len: usize,
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
