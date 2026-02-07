//! Utilities for dealing with Lean FFI.

use std::{
    ffi::{c_char, CStr},
    sync::OnceLock,
};

use lean_sys::{
    lean_alloc_ctor, lean_array_get_core, lean_array_push, lean_array_size, lean_box,
    lean_box_usize, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc,
    lean_initialize_runtime_module_locked, lean_io_result_is_ok, lean_io_result_show_error,
    lean_is_array, lean_is_scalar, lean_is_string, lean_mk_empty_array_with_capacity,
    lean_mk_string_from_bytes, lean_obj_res, lean_object, lean_ptr_tag, lean_string_cstr,
    lean_unbox,
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LeanObjectError {
    #[error("expected string")]
    ExpectedString,
    #[error("expected array")]
    ExpectedArray,
    #[error("expected constructor")]
    ExpectedConstructor,
    #[error("unknown constructor tag")]
    UnknownConstructorTag,
    #[error("UTF-8 error: {0}")]
    Utf8Error(#[from] std::str::Utf8Error),
}

/// A safe wrapper around owned `lean_object`,
/// adapted from [Cedar](https://github.com/cedar-policy/cedar-spec/blob/3eceb3c38836ffa13cef2e480af3bd092cc79e11/cedar-lean-ffi/src/lean_object.rs)
#[derive(Debug)]
pub struct LeanObject {
    raw: *mut lean_object,
}

impl Drop for LeanObject {
    fn drop(&mut self) {
        unsafe {
            lean_dec(self.raw);
        }
    }
}

impl Clone for LeanObject {
    fn clone(&self) -> Self {
        unsafe {
            lean_inc(self.raw);
        }
        LeanObject { raw: self.raw }
    }
}

impl LeanObject {
    /// Returns the tag of the constructor
    /// (e.g., 0 for the first constructor in an inductive type).
    pub fn tag(&self) -> u8 {
        unsafe { lean_ptr_tag(self.raw) }
    }

    pub fn is_array(&self) -> bool {
        unsafe { lean_is_array(self.raw) }
    }

    pub fn to_str(&self) -> Result<&str, LeanObjectError> {
        let s: &str = self.try_into()?;
        Ok(s)
    }

    /// `lean_obj_arg` requires an owned `*mut lean_object`.
    pub fn to_lean_obj_arg(self) -> lean_sys::lean_obj_arg {
        let raw = self.raw;
        // Do not decrement the reference counter
        // since we are transferring ownership.
        std::mem::forget(self);
        raw
    }

    /// `lean_obj_res` contains an owned `*mut lean_object`.
    pub fn from_lean_obj_res(raw: lean_sys::lean_obj_res) -> Self {
        LeanObject { raw }
    }

    pub fn from_b_lean_obj_res(raw: lean_sys::b_lean_obj_res) -> Self {
        unsafe {
            lean_inc(raw);
        }
        LeanObject { raw }
    }
}

impl TryFrom<LeanObject> for bool {
    type Error = LeanObjectError;

    fn try_from(obj: LeanObject) -> Result<Self, Self::Error> {
        // TODO: Check if there is a way to check the type
        Ok(lean_unbox(obj.raw) != 0)
    }
}

impl TryFrom<LeanObject> for i32 {
    type Error = LeanObjectError;

    fn try_from(obj: LeanObject) -> Result<Self, Self::Error> {
        Ok(lean_unbox(obj.raw) as i32)
    }
}

impl From<usize> for LeanObject {
    fn from(n: usize) -> Self {
        LeanObject {
            raw: unsafe { lean_box_usize(n) },
        }
    }
}

impl From<&str> for LeanObject {
    fn from(s: &str) -> Self {
        unsafe {
            LeanObject {
                raw: lean_mk_string_from_bytes(s.as_ptr(), s.len()),
            }
        }
    }
}

impl<'a> TryFrom<&'a LeanObject> for &'a str {
    type Error = LeanObjectError;

    fn try_from(obj: &'a LeanObject) -> Result<Self, Self::Error> {
        if !unsafe { lean_is_string(obj.raw) } {
            return Err(LeanObjectError::ExpectedString);
        }
        let cstr = unsafe { CStr::from_ptr(lean_string_cstr(obj.raw) as *const c_char) };
        Ok(cstr.to_str()?)
    }
}

impl<'a> TryFrom<&'a LeanObject> for Result<LeanObject, LeanObject> {
    type Error = LeanObjectError;

    /// NOTE: Due to polymorphism, the field of the constructors of Lean `Except`
    /// should always be boxed, even if it's a scalar.
    /// <https://gist.github.com/ydewit/7ab62be1bd0fea5bd53b48d23914dd6b#boxed-values>
    ///
    /// Also note that this function does NOT actually check if the value
    /// is of the `Except` type, but it simply reads, e.g., the first field
    /// of the first constructor as the error value.
    fn try_from(obj: &'a LeanObject) -> Result<Self, Self::Error> {
        match obj.tag() {
            0 => {
                let raw = unsafe { lean_ctor_get(obj.raw, 0) };
                let field = LeanObject { raw };
                unsafe { lean_inc(raw) };
                Ok(Err(field))
            }
            1 => {
                let raw = unsafe { lean_ctor_get(obj.raw, 0) };
                let field = LeanObject { raw };
                unsafe { lean_inc(raw) };
                Ok(Ok(field))
            }
            _ => Err(LeanObjectError::UnknownConstructorTag),
        }
    }
}

impl From<Option<LeanObject>> for LeanObject {
    fn from(opt: Option<LeanObject>) -> Self {
        match opt {
            None => unsafe {
                LeanObject {
                    raw: lean_alloc_ctor(0, 0, 0),
                }
            },
            Some(obj) => unsafe {
                let raw = lean_alloc_ctor(1, 1, 0);
                lean_ctor_set(raw, 0, obj.to_lean_obj_arg());
                lean_inc(raw);
                LeanObject { raw }
            },
        }
    }
}

impl<'a> TryFrom<&'a LeanObject> for Option<LeanObject> {
    type Error = LeanObjectError;

    fn try_from(obj: &'a LeanObject) -> Result<Self, Self::Error> {
        // For some reason (maybe due to the `attribute [unbox] Option` instruction),
        // the `None` variant of `Option` is represented as a scalar 0.
        if lean_is_scalar(obj.raw) && lean_unbox(obj.raw) == 0 {
            return Ok(None);
        }

        match obj.tag() {
            0 => Ok(None),
            1 => {
                let raw = unsafe { lean_ctor_get(obj.raw, 0) };
                let field = LeanObject { raw };
                unsafe { lean_inc(raw) };
                Ok(Some(field))
            }
            _ => Err(LeanObjectError::UnknownConstructorTag),
        }
    }
}

impl<'a> TryFrom<&'a LeanObject> for (LeanObject, LeanObject) {
    type Error = LeanObjectError;

    fn try_from(obj: &'a LeanObject) -> Result<Self, Self::Error> {
        if obj.tag() != 0 {
            return Err(LeanObjectError::UnknownConstructorTag);
        }
        let first_raw = unsafe { lean_ctor_get(obj.raw, 0) };
        let second_raw = unsafe { lean_ctor_get(obj.raw, 1) };
        unsafe {
            lean_inc(first_raw);
            lean_inc(second_raw);
        }
        Ok((
            LeanObject { raw: first_raw },
            LeanObject { raw: second_raw },
        ))
    }
}

impl From<Vec<LeanObject>> for LeanObject {
    fn from(objs: Vec<LeanObject>) -> Self {
        let arr = unsafe {
            let capacity = lean_box(objs.len());
            let mut arr = lean_mk_empty_array_with_capacity(capacity);
            lean_dec(capacity);
            for obj in objs.into_iter() {
                arr = lean_array_push(arr, obj.to_lean_obj_arg());
            }
            arr
        };
        LeanObject::from_lean_obj_res(arr)
    }
}

impl TryFrom<&LeanObject> for Vec<LeanObject> {
    type Error = LeanObjectError;

    fn try_from(obj: &LeanObject) -> Result<Self, Self::Error> {
        if !obj.is_array() {
            return Err(LeanObjectError::ExpectedArray);
        }
        let len = unsafe { lean_array_size(obj.raw) };
        let mut vec = Vec::with_capacity(len);
        for i in 0..len {
            vec.push(LeanObject::from_b_lean_obj_res(unsafe {
                lean_array_get_core(obj.raw, i)
            }));
        }
        Ok(vec)
    }
}

/// Ensures that the Lean FFI is initialized.
/// See: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/#ffi
pub fn ensure_init_lean() {
    extern "C" {
        /// Auto-generated by Lean to initialize the Wavelet module.
        fn initialize_Wavelet(builtin: u8) -> lean_obj_res;
    }
    static INIT: OnceLock<()> = OnceLock::new();
    INIT.get_or_init(|| unsafe {
        lean_initialize_runtime_module_locked();
        let res = initialize_Wavelet(1);
        if lean_io_result_is_ok(res) {
            lean_dec_ref(res);
        } else {
            lean_io_result_show_error(res);
            lean_dec(res);
        }
    });
}
