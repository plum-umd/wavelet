use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=lean/Wavelet");
    println!("cargo:rerun-if-changed=lean/Wavelet.lean");
    println!("cargo:rerun-if-changed=lean/lake-manifest.json");
    println!("cargo:rerun-if-changed=lean/lakefile.lean");
    println!("cargo:rerun-if-changed=lean/lean-toolchain");

    // Find and dynamically link against `leanshared`
    // Adapted from `lean-sys`'s `build.rs`
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

    let lean_dir = PathBuf::from(String::from_utf8(output.stdout)
        .expect("invalid lean library path")
        .trim());

    let lib_dir = if cfg!(target_os = "windows") {
        lean_dir.join("bin")
    } else {
        lean_dir.join("lib/lean")
    };

    let mut shared_lib = lib_dir.clone();
    let exists = if cfg!(target_os = "windows") {
        shared_lib.push("libleanshared.dll");
        shared_lib.exists()
    } else if cfg!(target_os = "macos") {
        shared_lib.push("libleanshared.dylib");
        shared_lib.exists()
    } else {
        shared_lib.push("libleanshared.so");
        shared_lib.exists()
    };

    assert!(exists, "lean shared library does not exist: {}", shared_lib.display());

    println!("cargo:rustc-link-search={}", lib_dir.display());
    println!("cargo:rustc-link-lib=leanshared");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_dir.display());

    let status = Command::new("lake")
        .current_dir("lean")
        .args(["exec", "cache", "get"])
        .status()
        .expect("failed to run `lake exec cache get`");
    assert!(status.success(), "`lake exec cache` get failed");

    // Build `libBatteries`
    let output = Command::new("lake")
        .current_dir("lean")
        .args(["build", "Batteries:static"])
        .output()
        .expect("failed to run `lake build Batteries:static`");
    assert!(output.status.success(), "`lake build Batteries:static` failed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    for line in stdout.lines() {
        println!("cargo:warning=[lake build Batteries:static] {}", line);
    }
    for line in stderr.lines() {
        println!("cargo:warning=[lake build Batteries:static] {}", line);
    }

    // Build `libWavelet`
    let output = Command::new("lake")
        .current_dir("lean")
        .args(["build", "Wavelet"])
        .output()
        .expect("failed to run `lake build Wavelet`");
    assert!(output.status.success(), "`lake build Wavelet` failed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    for line in stdout.lines() {
        println!("cargo:warning=[lake build Wavelet] {}", line);
    }
    for line in stderr.lines() {
        println!("cargo:warning=[lake build Wavelet] {}", line);
    }

    // Statically link `libWavelet`
    println!("cargo:rustc-link-search=lean/.lake/build/lib");
    println!("cargo:rustc-link-search=lean/.lake/packages/batteries/.lake/build/lib");
}
