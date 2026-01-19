//! FFI bindings for the core Lean module.

use lean_sys::{lean_dec, lean_dec_ref, lean_initialize_runtime_module_locked, lean_io_result_is_ok, lean_io_result_show_error, lean_obj_arg, lean_obj_res};

#[link(name = "Batteries", kind = "static")]
#[link(name = "Wavelet", kind = "static")]
unsafe extern "C" {
    fn initialize_Wavelet(builtin: u8) -> lean_obj_res;

    pub fn wavelet_riptide_compile(arg: lean_obj_arg) -> lean_obj_res;
}

pub struct WaveletFfi;

impl WaveletFfi {
    /// Initializes Lean FFI.
    /// See: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/#ffi
    pub fn new() -> Self {
        unsafe {
            lean_initialize_runtime_module_locked();
            let res = initialize_Wavelet(1);
            if lean_io_result_is_ok(res) {
                lean_dec_ref(res);
            } else {
                lean_io_result_show_error(res);
                lean_dec(res);
            }
        }
        WaveletFfi
    }
}
