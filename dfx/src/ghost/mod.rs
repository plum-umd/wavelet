pub mod affine;
pub mod checker;
pub mod fracperms;
pub mod ir;
pub mod json;
pub mod lower;

pub use checker::{
    CheckContext, Permission, PermissionEnv, check_ghost_program, check_ghost_program_with_verbose,
};
pub use lower::synthesize_ghost_program;
