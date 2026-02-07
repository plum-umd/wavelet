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
        !lean_is_scalar(self.raw) && unsafe { lean_is_array(self.raw) }
    }

    pub fn to_str(&self) -> Result<&str, LeanObjectError> {
        if lean_is_scalar(self.raw) || !unsafe { lean_is_string(self.raw) } {
            return Err(LeanObjectError::ExpectedString);
        }
        let cstr = unsafe { CStr::from_ptr(lean_string_cstr(self.raw) as *const c_char) };
        Ok(cstr.to_str()?)
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

impl From<Result<LeanObject, LeanObject>> for LeanObject {
    fn from(result: Result<LeanObject, LeanObject>) -> Self {
        let (tag, inner) = match result {
            Err(e) => (0, e),
            Ok(v) => (1, v),
        };
        unsafe {
            let raw = lean_alloc_ctor(tag, 1, 0);
            lean_ctor_set(raw, 0, inner.to_lean_obj_arg());
            lean_inc(raw);
            LeanObject { raw }
        }
    }
}

impl From<Option<LeanObject>> for LeanObject {
    fn from(opt: Option<LeanObject>) -> Self {
        match opt {
            // Nullary constructors (0 fields, 0 scalar bytes) are represented
            // as scalars in Lean: `lean_box(tag)`.
            // <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive-types-runtime-special-support>
            None => LeanObject { raw: lean_box(0) },
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

impl From<(LeanObject, LeanObject)> for LeanObject {
    /// Builds a Lean `Prod` value (tag 0, 2 fields).
    fn from((a, b): (LeanObject, LeanObject)) -> Self {
        unsafe {
            let raw = lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(raw, 0, a.to_lean_obj_arg());
            lean_ctor_set(raw, 1, b.to_lean_obj_arg());
            lean_inc(raw);
            LeanObject { raw }
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

#[cfg(test)]
mod tests {
    use super::*;
    use lean_sys::lean_obj_arg;

    // Scalar conversions

    #[test]
    fn test_bool_unbox() {
        ensure_init_lean();
        let t = LeanObject { raw: lean_box(1) };
        let f = LeanObject { raw: lean_box(0) };
        assert!(bool::try_from(t).unwrap());
        assert!(!bool::try_from(f).unwrap());
    }

    #[test]
    fn test_i32_unbox() {
        ensure_init_lean();
        for val in [0i32, 1, -1, 42, -42, i32::MAX, i32::MIN] {
            let obj = LeanObject {
                raw: lean_box(val as u32 as usize),
            };
            assert_eq!(i32::try_from(obj).unwrap(), val);
        }
    }

    // String conversions

    #[test]
    fn test_string_roundtrip() {
        ensure_init_lean();
        for s in ["", "hello", "hello world", "café", "你好世界", "🎉🎊"] {
            let obj = LeanObject::from(s);
            assert_eq!(obj.to_str().unwrap(), s);
        }
    }

    #[test]
    fn test_string_clone() {
        ensure_init_lean();
        let obj = LeanObject::from("shared");
        let clone = obj.clone();
        assert_eq!(obj.to_str().unwrap(), "shared");
        assert_eq!(clone.to_str().unwrap(), "shared");
        drop(obj);
        assert_eq!(clone.to_str().unwrap(), "shared");
    }

    #[test]
    fn test_to_str_on_non_string() {
        ensure_init_lean();
        let scalar = LeanObject { raw: lean_box(42) };
        assert!(matches!(
            scalar.to_str(),
            Err(LeanObjectError::ExpectedString)
        ));
        let none = LeanObject::from(None::<LeanObject>);
        assert!(matches!(
            none.to_str(),
            Err(LeanObjectError::ExpectedString)
        ));
        let arr = LeanObject::from(Vec::<LeanObject>::new());
        assert!(matches!(arr.to_str(), Err(LeanObjectError::ExpectedString)));
        let some = LeanObject::from(Some(LeanObject::from("inner")));
        assert!(matches!(
            some.to_str(),
            Err(LeanObjectError::ExpectedString)
        ));
    }

    // Array/Vec conversions

    #[test]
    fn test_vec_roundtrip_empty() {
        ensure_init_lean();
        let obj = LeanObject::from(Vec::<LeanObject>::new());
        assert!(obj.is_array());
        let vec: Vec<LeanObject> = (&obj).try_into().unwrap();
        assert!(vec.is_empty());
    }

    #[test]
    fn test_vec_roundtrip_strings() {
        ensure_init_lean();
        let items = vec!["alpha", "beta", "gamma"];
        let obj = LeanObject::from(
            items
                .iter()
                .map(|s| LeanObject::from(*s))
                .collect::<Vec<_>>(),
        );
        let vec: Vec<LeanObject> = (&obj).try_into().unwrap();
        assert_eq!(vec.len(), 3);
        for (got, expected) in vec.iter().zip(items.iter()) {
            assert_eq!(got.to_str().unwrap(), *expected);
        }
    }

    #[test]
    fn test_vec_clone_and_multiple_reads() {
        ensure_init_lean();
        let obj = LeanObject::from(
            vec!["a", "b"]
                .into_iter()
                .map(LeanObject::from)
                .collect::<Vec<_>>(),
        );
        let clone = obj.clone();
        let v1: Vec<LeanObject> = (&obj).try_into().unwrap();
        let v2: Vec<LeanObject> = (&clone).try_into().unwrap();
        assert_eq!(v1.len(), 2);
        assert_eq!(v2.len(), 2);
        assert_eq!(v1[0].to_str().unwrap(), "a");
        assert_eq!(v2[1].to_str().unwrap(), "b");
    }

    #[test]
    fn test_vec_from_non_array() {
        ensure_init_lean();
        let string = LeanObject::from("not an array");
        assert!(matches!(
            Vec::<LeanObject>::try_from(&string),
            Err(LeanObjectError::ExpectedArray)
        ));
        let scalar = LeanObject { raw: lean_box(0) };
        assert!(matches!(
            Vec::<LeanObject>::try_from(&scalar),
            Err(LeanObjectError::ExpectedArray)
        ));
        let none = LeanObject::from(None::<LeanObject>);
        assert!(matches!(
            Vec::<LeanObject>::try_from(&none),
            Err(LeanObjectError::ExpectedArray)
        ));
        let some = LeanObject::from(Some(LeanObject::from("x")));
        assert!(matches!(
            Vec::<LeanObject>::try_from(&some),
            Err(LeanObjectError::ExpectedArray)
        ));
    }

    #[test]
    fn test_array_to_lean() {
        extern "C" {
            fn wavelet_test_array_string_join(arr: lean_obj_arg, sep: lean_obj_arg)
                -> lean_obj_res;
        }
        ensure_init_lean();
        let arr = LeanObject::from(
            vec!["hello", "world", "!"]
                .into_iter()
                .map(LeanObject::from)
                .collect::<Vec<_>>(),
        );
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_array_string_join(
                arr.to_lean_obj_arg(),
                LeanObject::from(", ").to_lean_obj_arg(),
            )
        });
        assert_eq!(res.to_str().unwrap(), "hello, world, !");
    }

    #[test]
    fn test_array_empty_to_lean() {
        extern "C" {
            fn wavelet_test_array_string_join(arr: lean_obj_arg, sep: lean_obj_arg)
                -> lean_obj_res;
        }
        ensure_init_lean();
        let arr = LeanObject::from(Vec::<LeanObject>::new());
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_array_string_join(
                arr.to_lean_obj_arg(),
                LeanObject::from(",").to_lean_obj_arg(),
            )
        });
        assert_eq!(res.to_str().unwrap(), "");
    }

    // Option conversions

    #[test]
    fn test_option_none_roundtrip() {
        ensure_init_lean();
        let obj = LeanObject::from(None::<LeanObject>);
        let decoded: Option<LeanObject> = (&obj).try_into().unwrap();
        assert!(decoded.is_none());
    }

    #[test]
    fn test_option_some_roundtrip() {
        ensure_init_lean();
        let inner = LeanObject::from("payload");
        let obj = LeanObject::from(Some(inner));
        let decoded: Option<LeanObject> = (&obj).try_into().unwrap();
        assert_eq!(decoded.unwrap().to_str().unwrap(), "payload");
    }

    #[test]
    fn test_option_some_from_lean() {
        extern "C" {
            fn wavelet_test_option_some_string(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_option_some_string(LeanObject::from("test").to_lean_obj_arg())
        });
        let decoded: Option<LeanObject> = (&res).try_into().unwrap();
        assert_eq!(decoded.unwrap().to_str().unwrap(), "test");
    }

    #[test]
    fn test_option_none_from_lean() {
        extern "C" {
            static wavelet_test_option_none_string: lean_obj_res;
        }
        ensure_init_lean();
        let res = unsafe {
            lean_inc(wavelet_test_option_none_string);
            LeanObject::from_lean_obj_res(wavelet_test_option_none_string)
        };
        let decoded: Option<LeanObject> = (&res).try_into().unwrap();
        assert!(decoded.is_none());
    }

    #[test]
    fn test_option_some_to_lean() {
        extern "C" {
            fn wavelet_test_option_string_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let opt = LeanObject::from(Some(LeanObject::from("hello")));
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_option_string_show(opt.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "some:hello");
    }

    #[test]
    fn test_option_none_to_lean() {
        extern "C" {
            fn wavelet_test_option_string_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let opt = LeanObject::from(None::<LeanObject>);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_option_string_show(opt.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "none");
    }

    // Except/Result conversions

    #[test]
    fn test_except_ok_from_lean() {
        extern "C" {
            fn wavelet_test_except_ok_string(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_except_ok_string(LeanObject::from("success").to_lean_obj_arg())
        });
        let decoded: Result<LeanObject, LeanObject> = (&res).try_into().unwrap();
        assert_eq!(decoded.unwrap().to_str().unwrap(), "success");
    }

    #[test]
    fn test_except_error_from_lean() {
        extern "C" {
            fn wavelet_test_except_error_string(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_except_error_string(LeanObject::from("failure").to_lean_obj_arg())
        });
        let decoded: Result<LeanObject, LeanObject> = (&res).try_into().unwrap();
        assert_eq!(decoded.unwrap_err().to_str().unwrap(), "failure");
    }

    #[test]
    fn test_except_ok_to_lean() {
        extern "C" {
            fn wavelet_test_except_string_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let ok_obj = LeanObject::from(Ok(LeanObject::from("hello")) as Result<_, LeanObject>);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_except_string_show(ok_obj.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "ok:hello");
    }

    #[test]
    fn test_except_error_to_lean() {
        extern "C" {
            fn wavelet_test_except_string_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let err_obj = LeanObject::from(Err(LeanObject::from("oops")) as Result<LeanObject, _>);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_except_string_show(err_obj.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "err:oops");
    }

    // Pair conversions

    #[test]
    fn test_pair_from_lean() {
        extern "C" {
            fn wavelet_test_pair_strings(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_pair_strings(
                LeanObject::from("first").to_lean_obj_arg(),
                LeanObject::from("second").to_lean_obj_arg(),
            )
        });
        let (a, b): (LeanObject, LeanObject) = (&res).try_into().unwrap();
        assert_eq!(a.to_str().unwrap(), "first");
        assert_eq!(b.to_str().unwrap(), "second");
    }

    #[test]
    fn test_pair_string_array_from_lean() {
        extern "C" {
            fn wavelet_test_pair_string_array(s: lean_obj_arg, arr: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let arr = LeanObject::from(
            vec!["x", "y", "z"]
                .into_iter()
                .map(LeanObject::from)
                .collect::<Vec<_>>(),
        );
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_pair_string_array(
                LeanObject::from("label").to_lean_obj_arg(),
                arr.to_lean_obj_arg(),
            )
        });
        let (s, a): (LeanObject, LeanObject) = (&res).try_into().unwrap();
        assert_eq!(s.to_str().unwrap(), "label");
        let elems: Vec<LeanObject> = (&a).try_into().unwrap();
        assert_eq!(elems.len(), 3);
        assert_eq!(elems[0].to_str().unwrap(), "x");
        assert_eq!(elems[1].to_str().unwrap(), "y");
        assert_eq!(elems[2].to_str().unwrap(), "z");
    }

    #[test]
    fn test_pair_to_lean() {
        extern "C" {
            fn wavelet_test_pair_string_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let pair = LeanObject::from((LeanObject::from("ab"), LeanObject::from("cd")));
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_pair_string_show(pair.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "(ab,cd)");
    }

    // USize composite type tests

    #[test]
    fn test_option_usize_some_to_lean() {
        extern "C" {
            fn wavelet_test_option_usize_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let opt = LeanObject::from(Some(LeanObject::from(42usize)));
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_option_usize_show(opt.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "some:42");
    }

    #[test]
    fn test_option_usize_none_to_lean() {
        extern "C" {
            fn wavelet_test_option_usize_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let opt = LeanObject::from(None::<LeanObject>);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_option_usize_show(opt.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "none");
    }

    #[test]
    fn test_except_usize_ok_to_lean() {
        extern "C" {
            fn wavelet_test_except_usize_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let obj = LeanObject::from(Ok(LeanObject::from(7usize)) as Result<_, LeanObject>);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_except_usize_show(obj.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "ok:7");
    }

    #[test]
    fn test_except_usize_error_to_lean() {
        extern "C" {
            fn wavelet_test_except_usize_show(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let obj = LeanObject::from(Err(LeanObject::from(99usize)) as Result<LeanObject, _>);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_test_except_usize_show(obj.to_lean_obj_arg())
        });
        assert_eq!(res.to_str().unwrap(), "err:99");
    }

    #[test]
    fn test_pair_usize_to_lean() {
        extern "C" {
            fn wavelet_test_pair_usize_sum(arg: lean_obj_arg) -> usize;
        }
        ensure_init_lean();
        let pair = LeanObject::from((LeanObject::from(30usize), LeanObject::from(12usize)));
        let sum = unsafe { wavelet_test_pair_usize_sum(pair.to_lean_obj_arg()) };
        assert_eq!(sum, 42);
    }
}
