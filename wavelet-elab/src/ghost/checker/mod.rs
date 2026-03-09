//! Permission synthesis and SMT-backed validation for lowered ghost programs.

mod context;
mod contract;
mod perm_env;
mod permission;
mod pretty_print;
mod program_checker;
mod synthesis;
mod trace;
mod utils;
mod validation;

pub use context::CheckContext;
pub use contract::{FunctionSignature, PermissionContract};
pub use perm_env::PermissionEnv;
pub use permission::{PermExpr, Permission};
pub use program_checker::{
    check_ghost_program, check_ghost_program_with_solver,
    check_ghost_program_with_solver_and_verbose, check_ghost_program_with_verbose,
};
pub use synthesis::{FunctionPermissionModel, ProgramPermissionModel};

#[cfg(test)]
mod tests;
