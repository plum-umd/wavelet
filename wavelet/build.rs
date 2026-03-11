fn main() {
    #[cfg(target_os = "linux")]
    {
        // Fixes a linking issue on Linux with GNU ld.
        println!("cargo::rustc-link-arg=-Wl,-Bstatic");
        println!("cargo::rustc-link-arg=-lleanrt");
    }
}
