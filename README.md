Formally Verified Asynchronous Dataflow Compiler
---

## Build

First install prerequisites:
- [Lean 4](https://lean-lang.org/install/)
- [Cargo](https://doc.rust-lang.org/cargo/getting-started/installation.html)

Then simply run
```
cargo build
```
which will produce the CLI binary at `target/debug/wavelet`.

## Developing and Verifying Proofs

All of the Lean formalization can be found in `wavelet-core/lean`,
and by default, the `cargo build` command above does not check any proofs.
To actually verify all proofs:
```
cd wavelet-core/lean
lake exec cache get
lake build Thm
```
