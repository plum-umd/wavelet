mod ffi;

fn main() {
    unsafe {
        let input = "hello";
        let _ = ffi::WaveletFfi::new();
        let output = ffi::wavelet_riptide_compile(lean_sys::lean_mk_string_from_bytes(
            input.as_ptr(),
            input.len(),
        ));
        let cstr = lean_sys::lean_string_cstr(output);
        let len = lean_sys::lean_string_len(output);
        let slice = std::slice::from_raw_parts(cstr as *const u8, len);
        let result = std::str::from_utf8(slice).unwrap();
        println!("output: {}", result);
    }
}
