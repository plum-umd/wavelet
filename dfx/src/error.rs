//! Error types for the `dfx` type checker.

use thiserror::Error;

/// High level error produced when type checking a program.
#[derive(Debug, Error)]
pub enum TypeError {
    /// A variable was used but not declared in the current scope.
    #[error("undeclared variable '{0}'")]
    UndeclaredVar(String),

    /// A function was called that is not defined.
    #[error("undefined function '{0}'")]
    UndefinedFunction(String),

    /// A type mismatch occurred between an expression and its expected type.
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch { expected: String, found: String },

    /// A primitive operation was applied to arguments of the wrong type.
    #[error("invalid operand types for operation '{op}'")]
    InvalidOp { op: String },

    /// A capability required for an operation or call was not present.
    #[error(
        "insufficient capability on array '{array}': required {required}, available {available}"
    )]
    InsufficientCapability {
        array: String,
        required: String,
        available: String,
    },

    /// A subtraction of capabilities failed because the minuend did not
    /// contain the subtrahend.
    #[error("capability subtraction failed on array '{array}'")]
    CapabilitySubtractError { array: String },

    /// A logical entailment could not be proven.
    #[error("failed to prove logical fact: {0}")]
    LogicError(String),

    /// Divergent capabilities between two branches of a conditional.
    #[error("capability contexts differ between branches")]
    CapabilityMismatch,
}

impl TypeError {
    /// Helper to convert a type into a readable string for error messages.
    pub fn type_name(ty: &crate::ir::Ty) -> String {
        match ty {
            crate::ir::Ty::Int(crate::ir::Signedness::Signed) => "int".to_string(),
            crate::ir::Ty::Int(crate::ir::Signedness::Unsigned) => "uint".to_string(),
            crate::ir::Ty::Bool => "bool".to_string(),
            crate::ir::Ty::Unit => "unit".to_string(),
            crate::ir::Ty::RefShrd { elem, len } => {
                format!("&[{}; {}]", TypeError::type_name(elem), len.display())
            }
            crate::ir::Ty::RefUniq { elem, len } => {
                format!("&mut [{}; {}]", TypeError::type_name(elem), len.display())
            }
        }
    }
}
