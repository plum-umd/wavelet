use lean_sys::lean_obj_res;

#[link(name = "Wavelet", kind = "static")]
unsafe extern "C" {
    pub fn test(i: lean_obj_res) -> lean_obj_res;
}
