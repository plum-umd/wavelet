//! Intermediate representation for the restricted language.

use crate::logic::cap::CapPattern;
use crate::logic::semantic::solver::Idx;

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
    /// Symbolic identifier (e.g. a const generic parameter `N`).
    Symbol(String),
    /// General index expression (e.g. `M * N`).
    Expr(Idx),
}

impl ArrayLen {
    /// Return a human-readable representation used in error messages.
    pub fn display(&self) -> String {
        match self {
            ArrayLen::Const(n) => n.to_string(),
            ArrayLen::Symbol(name) => name.clone(),
            ArrayLen::Expr(expr) => format!("{}", expr),
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
            Ty::Bool => Some(Signedness::Unsigned),
            _ => None,
        }
    }

    /// Check if this type is an array reference (shared or unique).
    pub fn is_array_ref(&self) -> bool {
        matches!(self, Ty::RefShrd { .. } | Ty::RefUniq { .. })
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
    /// Boolean negation: !x
    Not,
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
    /// Inequality comparison: x != y
    NotEqual,
    /// Load from array.
    Load {
        /// Array variable to load from.
        array: Var,
        /// Index variable.
        index: Var,
        /// Length of the array.
        len: ArrayLen,
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
    },
}

/// Statements in the language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    /// Bind a variable to a literal value.
    LetVal {
        var: Var,
        val: Val,
        /// Indicates that this binding is immediately followed by a `fence!()` marker.
        fence: bool,
    },
    /// Bind variables to the result of a primitive operation.
    LetOp {
        vars: Vec<Var>,
        op: Op,
        /// Indicates that this binding is immediately followed by a `fence!()` marker.
        fence: bool,
    },
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
            Stmt::LetVal { var, val, fence } => {
                write!(f, "let {} = {}{};", var, if *fence { "@" } else { "" }, val)
            }
            Stmt::LetOp { vars, op, fence } => {
                write!(f, "let ")?;
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, " = {}{};", if *fence { "@" } else { "" }, op)
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
            Op::Not => write!(f, "!"),
            Op::BitAnd => write!(f, "&"),
            Op::BitOr => write!(f, "|"),
            Op::BitXor => write!(f, "^"),
            Op::Shl => write!(f, "<<"),
            Op::Shr => write!(f, ">>"),
            Op::LessThan => write!(f, "<"),
            Op::LessEqual => write!(f, "<="),
            Op::Equal => write!(f, "=="),
            Op::NotEqual => write!(f, "!="),
            Op::Load { array, index, len } => {
                write!(f, "{}[{}:{}]", array, index, len.display())
            }
            Op::Store {
                array,
                index,
                value,
                len,
            } => {
                write!(f, "{}[{}:{}] = {}", array, index, len.display(), value)
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

impl Program {
    /// Desugar tail calls to other functions into let-call followed by returns.
    /// This transforms `f(x, y)` at tail position into `let ret = f(x, y); return ret`.
    pub fn desugar_tail_calls(&mut self) {
        for def in &mut self.defs {
            def.desugar_tail_calls();
        }
    }

    /// Array references (both shared and unique) are removed from parameter lists
    /// and argument lists, as they are assumed to be globally available.
    pub fn eliminate_array_params(&mut self) {
        let mut fn_array_indices: std::collections::HashMap<String, Vec<usize>> =
            std::collections::HashMap::new();

        // collect array parameter indices for all functions
        for def in &self.defs {
            let array_indices: Vec<usize> = def
                .params
                .iter()
                .enumerate()
                .filter_map(|(i, (_, ty))| if ty.is_array_ref() { Some(i) } else { None })
                .collect();
            fn_array_indices.insert(def.name.0.clone(), array_indices);
        }

        for def in &mut self.defs {
            def.eliminate_array_params_with_map(&fn_array_indices);
        }
    }
}

impl FnDef {
    pub fn desugar_tail_calls(&mut self) {
        let fn_name = &self.name;
        self.body.desugar_tail_calls(fn_name);
    }

    pub fn eliminate_array_params(&mut self) {
        let mut fn_array_indices = std::collections::HashMap::new();
        let array_param_indices: Vec<usize> = self
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, (_, ty))| if ty.is_array_ref() { Some(i) } else { None })
            .collect();
        fn_array_indices.insert(self.name.0.clone(), array_param_indices);

        self.body.eliminate_array_args_with_map(&fn_array_indices);

        self.params.retain(|(_, ty)| !ty.is_array_ref());
    }

    fn eliminate_array_params_with_map(
        &mut self,
        fn_array_indices: &std::collections::HashMap<String, Vec<usize>>,
    ) {
        self.body.eliminate_array_args_with_map(fn_array_indices);

        // Filter out array parameters from the parameter list
        self.params.retain(|(_, ty)| !ty.is_array_ref());
    }
}

impl Expr {
    fn desugar_tail_calls(&mut self, current_fn: &FnName) {
        for stmt in &mut self.stmts {
            stmt.desugar_tail_calls(current_fn);
        }
        self.tail.desugar_tail_calls(current_fn);

        // Check if the tail is a non-recursive tail call
        if let Tail::TailCall { func, args } = &self.tail {
            if func != current_fn {
                let ret_var = self.fresh_var("_tail_ret");

                // TailCall -> LetCall + RetVar
                let call_stmt = Stmt::LetCall {
                    vars: vec![ret_var.clone()],
                    func: func.clone(),
                    args: args.clone(),
                    fence: false,
                };

                self.stmts.push(call_stmt);
                self.tail = Tail::RetVar(ret_var);
            }
        }
    }

    fn fresh_var(&self, base: &str) -> Var {
        let mut used_vars = std::collections::HashSet::new();
        self.collect_vars(&mut used_vars);

        let mut candidate = Var(base.to_string());
        let mut counter = 0;

        while used_vars.contains(&candidate) {
            counter += 1;
            candidate = Var(format!("{}_{}", base, counter));
        }

        candidate
    }

    fn collect_vars(&self, vars: &mut std::collections::HashSet<Var>) {
        for stmt in &self.stmts {
            stmt.collect_vars(vars);
        }
        self.tail.collect_vars(vars);
    }

    fn eliminate_array_args_with_map(
        &mut self,
        fn_array_indices: &std::collections::HashMap<String, Vec<usize>>,
    ) {
        for stmt in &mut self.stmts {
            stmt.eliminate_array_args_with_map(fn_array_indices);
        }
        self.tail.eliminate_array_args_with_map(fn_array_indices);
    }
}

impl Stmt {
    fn desugar_tail_calls(&mut self, _current_fn: &FnName) {}

    fn collect_vars(&self, vars: &mut std::collections::HashSet<Var>) {
        match self {
            Stmt::LetVal { var, .. } => {
                vars.insert(var.clone());
            }
            Stmt::LetOp { vars: vs, op, .. } => {
                for v in vs {
                    vars.insert(v.clone());
                }
                op.collect_vars(vars);
            }
            Stmt::LetCall { vars: vs, args, .. } => {
                for v in vs {
                    vars.insert(v.clone());
                }
                for arg in args {
                    vars.insert(arg.clone());
                }
            }
        }
    }

    fn eliminate_array_args_with_map(
        &mut self,
        fn_array_indices: &std::collections::HashMap<String, Vec<usize>>,
    ) {
        if let Stmt::LetCall { args, func, .. } = self {
            if let Some(array_indices) = fn_array_indices.get(&func.0) {
                // Filter out arguments at positions corresponding to array parameters
                let mut i = 0;
                args.retain(|_| {
                    let keep = !array_indices.contains(&i);
                    i += 1;
                    keep
                });
            }
        }
    }
}

impl Tail {
    fn desugar_tail_calls(&mut self, current_fn: &FnName) {
        match self {
            Tail::IfElse { then_e, else_e, .. } => {
                then_e.desugar_tail_calls(current_fn);
                else_e.desugar_tail_calls(current_fn);
            }
            Tail::RetVar(_) | Tail::TailCall { .. } => {}
        }
    }

    fn collect_vars(&self, vars: &mut std::collections::HashSet<Var>) {
        match self {
            Tail::RetVar(var) => {
                vars.insert(var.clone());
            }
            Tail::IfElse {
                cond,
                then_e,
                else_e,
            } => {
                vars.insert(cond.clone());
                then_e.collect_vars(vars);
                else_e.collect_vars(vars);
            }
            Tail::TailCall { args, .. } => {
                for arg in args {
                    vars.insert(arg.clone());
                }
            }
        }
    }

    fn eliminate_array_args_with_map(
        &mut self,
        fn_array_indices: &std::collections::HashMap<String, Vec<usize>>,
    ) {
        match self {
            Tail::IfElse { then_e, else_e, .. } => {
                then_e.eliminate_array_args_with_map(fn_array_indices);
                else_e.eliminate_array_args_with_map(fn_array_indices);
            }
            Tail::TailCall { args, func, .. } => {
                if let Some(array_indices) = fn_array_indices.get(&func.0) {
                    // Filter out arguments at positions corresponding to array parameters
                    let mut i = 0;
                    args.retain(|_| {
                        let keep = !array_indices.contains(&i);
                        i += 1;
                        keep
                    });
                }
            }
            Tail::RetVar(_) => {}
        }
    }
}

impl Op {
    fn collect_vars(&self, vars: &mut std::collections::HashSet<Var>) {
        match self {
            Op::Load { array, index, .. } => {
                vars.insert(array.clone());
                vars.insert(index.clone());
            }
            Op::Store {
                array,
                index,
                value,
                ..
            } => {
                vars.insert(array.clone());
                vars.insert(index.clone());
                vars.insert(value.clone());
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_desugar_tail_call() {
        // Create a simple program with a non-recursive tail call
        // fn foo() { bar(); }
        let foo_body = Expr::new(
            vec![],
            Tail::TailCall {
                func: FnName("bar".into()),
                args: vec![Var("x".into()), Var("y".into())],
            },
        );

        let mut foo_def = FnDef {
            name: FnName("foo".into()),
            params: vec![
                (Var("x".into()), Ty::Int(Signedness::Signed)),
                (Var("y".into()), Ty::Int(Signedness::Signed)),
            ],
            caps: vec![],
            returns: Ty::Int(Signedness::Signed),
            body: foo_body,
        };

        // Desugar
        foo_def.desugar_tail_calls();

        // Check that the tail call was transformed
        assert_eq!(foo_def.body.stmts.len(), 1);

        match &foo_def.body.stmts[0] {
            Stmt::LetCall {
                vars, func, args, ..
            } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(func.0, "bar");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected LetCall statement"),
        }

        match &foo_def.body.tail {
            Tail::RetVar(var) => {
                assert!(var.0.starts_with("_tail_ret"));
            }
            _ => panic!("Expected RetVar tail"),
        }
    }

    #[test]
    fn test_preserves_recursive_tail_call() {
        // Create a recursive function
        // fn factorial(n) { if n == 0 { 1 } else { factorial(n-1) } }
        let recursive_body = Expr::new(
            vec![],
            Tail::TailCall {
                func: FnName("factorial".into()),
                args: vec![Var("n".into())],
            },
        );

        let mut factorial_def = FnDef {
            name: FnName("factorial".into()),
            params: vec![(Var("n".into()), Ty::Int(Signedness::Signed))],
            caps: vec![],
            returns: Ty::Int(Signedness::Signed),
            body: recursive_body,
        };

        // Desugar
        factorial_def.desugar_tail_calls();

        // Check that the recursive tail call was NOT transformed
        assert_eq!(factorial_def.body.stmts.len(), 0);

        match &factorial_def.body.tail {
            Tail::TailCall { func, .. } => {
                assert_eq!(func.0, "factorial");
            }
            _ => panic!("Expected TailCall to be preserved"),
        }
    }

    #[test]
    fn test_desugar_nested_in_if_else() {
        // fn foo(cond) { if cond { bar() } else { baz() } }
        let then_branch = Expr::new(
            vec![],
            Tail::TailCall {
                func: FnName("bar".into()),
                args: vec![],
            },
        );

        let else_branch = Expr::new(
            vec![],
            Tail::TailCall {
                func: FnName("baz".into()),
                args: vec![],
            },
        );

        let foo_body = Expr::new(
            vec![],
            Tail::IfElse {
                cond: Var("cond".into()),
                then_e: Box::new(then_branch),
                else_e: Box::new(else_branch),
            },
        );

        let mut foo_def = FnDef {
            name: FnName("foo".into()),
            params: vec![(Var("cond".into()), Ty::Bool)],
            caps: vec![],
            returns: Ty::Unit,
            body: foo_body,
        };

        // Desugar
        foo_def.desugar_tail_calls();

        // Check that tail calls in both branches were transformed
        match &foo_def.body.tail {
            Tail::IfElse { then_e, else_e, .. } => {
                assert_eq!(then_e.stmts.len(), 1);
                assert_eq!(else_e.stmts.len(), 1);

                match (&then_e.tail, &else_e.tail) {
                    (Tail::RetVar(_), Tail::RetVar(_)) => {}
                    _ => panic!("Expected both branches to end with RetVar"),
                }
            }
            _ => panic!("Expected IfElse tail"),
        }
    }

    #[test]
    fn test_fresh_var_avoids_conflicts() {
        let expr = Expr::new(
            vec![Stmt::LetVal {
                var: Var("_tail_ret".into()),
                val: Val::Int(42),
                fence: false,
            }],
            Tail::RetVar(Var("_tail_ret".into())),
        );

        let fresh = expr.fresh_var("_tail_ret");
        assert_ne!(fresh.0, "_tail_ret");
        assert!(fresh.0.starts_with("_tail_ret_"));
    }

    #[test]
    fn test_eliminate_array_args_in_call() {
        // fn foo(i: uint, A: &mut [int; 10]) {
        //     let _ = foo(i, A);  // recursive call
        // }
        let foo_call = Stmt::LetCall {
            vars: vec![Var("_".into())],
            func: FnName("foo".into()),
            args: vec![Var("i".into()), Var("A".into())],
            fence: false,
        };

        let mut foo_def = FnDef {
            name: FnName("foo".into()),
            params: vec![
                (Var("i".into()), Ty::Int(Signedness::Unsigned)),
                (
                    Var("A".into()),
                    Ty::RefUniq {
                        elem: Box::new(Ty::Int(Signedness::Signed)),
                        len: ArrayLen::Const(10),
                    },
                ),
            ],
            caps: vec![],
            returns: Ty::Unit,
            body: Expr::new(vec![foo_call], Tail::RetVar(Var("_".into()))),
        };

        foo_def.eliminate_array_params();

        assert_eq!(foo_def.params.len(), 1);

        // Check that array argument was removed from the call
        match &foo_def.body.stmts[0] {
            Stmt::LetCall { args, .. } => {
                assert_eq!(args.len(), 1);
                assert_eq!(args[0].0, "i");
            }
            _ => panic!("Expected LetCall statement"),
        }
    }
}
