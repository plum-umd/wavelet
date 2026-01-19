
mod ffi;
mod riptide;

use crate::riptide::Proc;

fn main() {
    // unsafe {
    //     let input = "hello";
    //     let _ = ffi::WaveletFfi::new();
    //     let output = ffi::wavelet_riptide_compile(lean_sys::lean_mk_string_from_bytes(
    //         input.as_ptr(),
    //         input.len(),
    //     ));
    //     let cstr = lean_sys::lean_string_cstr(output);
    //     let len = lean_sys::lean_string_len(output);
    //     let slice = std::slice::from_raw_parts(cstr as *const u8, len);
    //     let result = std::str::from_utf8(slice).unwrap();
    //     println!("output: {}", result);
    // }

    let proc = Proc::from_json(include_str!("../../eval/wavelet-output/nn_fc.dfg.json")).unwrap();
    println!("num_atoms: {}", proc.num_atoms());
}
