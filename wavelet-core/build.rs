use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap())
        .display()
        .to_string();

    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-changed=lean/Wavelet");
    println!("cargo::rerun-if-changed=lean/Wavelet.lean");
    println!("cargo::rerun-if-changed=lean/lake-manifest.json");
    println!("cargo::rerun-if-changed=lean/lakefile.lean");
    println!("cargo::rerun-if-changed=lean/lean-toolchain");
    println!("cargo::rerun-if-changed=lean/.lake/packages/batteries/.lake/build/lib");

    // The executable part of Wavelet only depends on Batteries,
    // so we can skip fetching the cache for the entire mathlib.
    // let status = Command::new("lake")
    //     .current_dir("lean")
    //     .args(["exec", "cache", "get"])
    //     .status()
    //     .expect("failed to run `lake exec cache get`");
    // assert!(status.success(), "`lake exec cache` get failed");

    // Find Lean library paths
    let output = Command::new("lean")
        .current_dir("lean")
        .args(["--print-prefix"])
        .output()
        .expect("failed to run `lean --print-prefix`");
    assert!(
        output.status.success(),
        "`lean --print-prefix` failed with status {}:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let lean_dir = PathBuf::from(
        String::from_utf8(output.stdout)
            .expect("invalid lean library path")
            .trim(),
    );
    assert!(
        lean_dir.exists(),
        "lean prefix does not exist: {}",
        lean_dir.display()
    );

    // Build `libWavelet` and `libBatteries`
    let status = Command::new("lake")
        .current_dir("lean")
        .args(["build", "--wfail", "Wavelet", "Batteries:static"])
        .status()
        .expect("failed to run `lake build`");
    assert!(status.success(), "`lake build` failed");

    // Include various linking search paths for Lean and Wavelet
    println!("cargo::rustc-link-search=native={}/lib", lean_dir.display());
    if cfg!(target_os = "windows") {
        println!(
            "cargo::rustc-link-search=native={}",
            lean_dir.join("bin").display()
        );
    } else {
        println!(
            "cargo::rustc-link-search=native={}",
            lean_dir.join("lib/lean").display()
        );
    }
    println!("cargo::rustc-link-search=native={manifest_dir}/lean/.lake/build/lib");
    println!("cargo::rustc-link-search=native={manifest_dir}/lean/.lake/packages/batteries/.lake/build/lib");

    // Link against various required libraries
    for lib in [
        "Wavelet",
        "Batteries",
        "Lean",
        "Std",
        "Init",
        "leanrt",
        "leancpp",
        "uv",
    ] {
        println!("cargo::rustc-link-lib=static={lib}");
    }

    if cfg!(target_os = "macos") {
        // macOS does not have static libc++
        println!("cargo::rustc-link-lib=dylib=c++");
        println!("cargo::rustc-link-lib=dylib=c++abi");
    } else {
        println!("cargo::rustc-link-lib=static=c++");
        println!("cargo::rustc-link-lib=static=c++abi");
    }

    for lib in ["m", "dl", "gmp"] {
        println!("cargo::rustc-link-lib=dylib={lib}");
    }
}
