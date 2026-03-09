Wavelet is a formally verified compiler targeting asynchronous dataflow.

## Build

Please first install the following dependencies:
- [Elan (Lean version manager)](https://github.com/leanprover/elan)
- [Cargo](https://doc.rust-lang.org/cargo/getting-started/installation.html)
- [cvc5-1.3.3](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.3)

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

## Notes on LLM use

While the initial stage of this project (the first ~450 commits) was done manually, we have started using AI-based coding assistants in our workflow.

All commits that were primarily authored by a coding assistant (under human guidance) are marked with prefixes such as `[claude]`; for PRs that are squashed into one commit, these prefixes can be found in the specific pull request page.

So far, the use of LLM has been limited to:
- Integration test harnesses
- GitHub Actions
