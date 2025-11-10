//! Permission-based checker for GhostProgram using fractional permissions PCM.

mod permission;
mod perm_env;
mod context;
mod stmt_checker;
mod tail_checker;
mod expr_checker;
mod program_checker;
mod pretty_print;

pub use permission::{Permission, PermExpr};
pub use perm_env::PermissionEnv;
pub use context::{CheckContext, FunctionSignature};
pub use program_checker::{check_ghost_program, check_ghost_program_with_verbose};

#[cfg(test)]
mod tests;
