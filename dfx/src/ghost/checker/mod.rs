//! Permission-based checker for GhostProgram using fractional permissions PCM.

mod context;
mod expr_checker;
mod perm_env;
mod permission;
mod pretty_print;
mod program_checker;
mod stmt_checker;
mod tail_checker;

pub use context::{CheckContext, FunctionSignature};
pub use perm_env::PermissionEnv;
pub use permission::{PermExpr, Permission};
pub use program_checker::{check_ghost_program, check_ghost_program_with_verbose};

#[cfg(test)]
mod tests;
