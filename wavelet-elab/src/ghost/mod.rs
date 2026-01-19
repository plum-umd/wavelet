pub mod affine;
pub mod checker;
pub mod fracperms;
pub mod ir;
pub mod json;
pub mod lower;

pub use checker::{
    check_ghost_program, check_ghost_program_with_verbose, CheckContext, Permission, PermissionEnv,
};
pub use lower::synthesize_ghost_program;
