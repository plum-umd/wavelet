//! FFI bindings for the core compiler in Lean,
//! specialized to RipTide.

use libc::size_t;
use thiserror::Error;
use lean_sys::{lean_obj_arg, lean_obj_res};

use crate::ffi::{ensure_init_lean, LeanObject, LeanObjectError};

// Raw FFI bindings to exported functions declared in `lean/Wavelet/FFI.lean`.
#[link(name = "Wavelet", kind = "static")]
unsafe extern "C" {
    fn wavelet_riptide_prog_from_json(arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_proc_from_json(arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_proc_to_json(arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_proc_to_dot(arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_prog_lower_control_flow(arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_proc_sink_last_n_outputs(n: size_t, arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_proc_optimize(arg: lean_obj_arg) -> lean_obj_res;

    fn wavelet_riptide_proc_num_atoms(arg: lean_obj_arg) -> size_t;

    fn wavelet_riptide_proc_num_non_trivial_atoms(arg: lean_obj_arg) -> size_t;

    fn wavelet_riptide_proc_num_inputs(arg: lean_obj_arg) -> size_t;

    fn wavelet_riptide_proc_num_outputs(arg: lean_obj_arg) -> size_t;
}

#[derive(Debug, Error)]
pub enum RipTideError {
    #[error("lean object error: {0}")]
    LeanObjectError(#[from] LeanObjectError),
    #[error("program parsing error: {0}")]
    ProgParseError(String),
    #[error("dataflow graph parsing error: {0}")]
    ProcParseError(String),
    #[error("dot format generation error: {0}")]
    DotFormatError(String),
    #[error("control-flow lowering failed: {0}")]
    ControlFlowLoweringError(String),
}

/// An opaque wrapper for `Wavelet.RipTide.EncapProg`.
pub struct Prog(LeanObject);

/// An opaque wrapper for `Wavelet.RipTide.EncapProc`.
pub struct Proc(LeanObject);

impl Prog {
    /// Parses a `Prog` from its JSON representation.
    pub fn from_json(json: &str) -> Result<Self, RipTideError> {
        ensure_init_lean();
        let json = LeanObject::from_str(json);
        let res = LeanObject::from_lean_obj_res(unsafe { wavelet_riptide_prog_from_json(json.to_lean_obj_arg()) });
        match res.as_except()? {
            Ok(prog) => Ok(Prog(prog)),
            Err(err) => Err(RipTideError::ProgParseError(err.as_str()?.to_string())),
        }
    }

    /// Compiles to a `Proc` by lowering control-flow.
    pub fn lower_control_flow(&self) -> Result<Proc, RipTideError> {
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_prog_lower_control_flow(self.0.clone().to_lean_obj_arg())
        });
        match res.as_except()? {
            Ok(proc) => Ok(Proc(proc)),
            Err(err) => Err(RipTideError::ControlFlowLoweringError(err.as_str()?.to_string())),
        }
    }
}

impl Proc {
    /// Gets the number of atoms
    pub fn num_atoms(&self) -> usize {
        ensure_init_lean();
        unsafe {
            wavelet_riptide_proc_num_atoms(self.0.clone().to_lean_obj_arg()) as usize
        }
    }

    /// Gets the number of non-trivial atoms
    pub fn num_non_trivial_atoms(&self) -> usize {
        ensure_init_lean();
        unsafe {
            wavelet_riptide_proc_num_non_trivial_atoms(self.0.clone().to_lean_obj_arg()) as usize
        }
    }

    /// Gets the number of inputs
    pub fn num_inputs(&self) -> usize {
        ensure_init_lean();
        unsafe {
            wavelet_riptide_proc_num_inputs(self.0.clone().to_lean_obj_arg()) as usize
        }
    }

    /// Gets the number of outputs
    pub fn num_outputs(&self) -> usize {
        ensure_init_lean();
        unsafe {
            wavelet_riptide_proc_num_outputs(self.0.clone().to_lean_obj_arg()) as usize
        }
    }

    /// Parses a `Proc` from its JSON representation.
    pub fn from_json(json: &str) -> Result<Self, RipTideError> {
        ensure_init_lean();
        let json = LeanObject::from_str(json);
        let res = LeanObject::from_lean_obj_res(unsafe { wavelet_riptide_proc_from_json(json.to_lean_obj_arg()) });
        match res.as_except()? {
            Ok(proc) => Ok(Proc(proc)),
            Err(err) => Err(RipTideError::ProcParseError(err.as_str()?.to_string())),
        }
    }

    /// Serializes the `Proc` to its JSON representation.
    pub fn to_json(&self) -> String {
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_to_json(self.0.clone().to_lean_obj_arg())
        });
        res.as_str().unwrap().to_string()
    }

    /// Serializes the `Proc` to Graphviz DOT format.
    pub fn to_dot(&self) -> Result<String, RipTideError> {
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_to_dot(self.0.clone().to_lean_obj_arg())
        });
        match res.as_except()? {
            Ok(dot) => Ok(dot.as_str()?.to_string()),
            Err(err) => Err(RipTideError::DotFormatError(err.as_str()?.to_string())),
        }
    }

    /// Sinks the last `n` outputs.
    pub fn sink_last_n_outputs(&self, n: usize) -> Proc {
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_sink_last_n_outputs(n as size_t, self.0.clone().to_lean_obj_arg())
        });
        Proc(res)
    }

    /// Performs various legalizations and optimizations on the dataflow process.
    pub fn optimize(&self) -> Proc {
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_optimize(self.0.clone().to_lean_obj_arg())
        });
        Proc(res)
    }
}
