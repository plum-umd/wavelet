pub mod check;
pub mod env;
pub mod error;
pub mod ir;
pub mod logic;
pub mod parse;
pub mod ghost;

// Re-export commonly used types
pub use check::{check_fn, check_program};
pub use env::{Ctx, FnRegistry, Gamma};
pub use error::TypeError;
pub use ir::{Expr, FnDef, FnName, Op, Program, Stmt, Tail, Ty, Val, Var};
pub use logic::{CapabilityLogic, semantic::SemanticLogic};
pub use parse::{ParseError, parse_fn_def};
pub use ghost::synthesize_ghost_program;
