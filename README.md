Let it Flow: A Formally Verified Compilation Framework for Asynchronous Dataflow
---

Thank you for evaluating our artifact!
Our artifact is a formally verified dataflow compiler called Wavelet,
along with test harnesses to compare with two other unverified dataflow
compilers in [RipTide](https://ieeexplore.ieee.org/document/9923793) and
[LLVM CIRCT](https://circt.llvm.org/).

We begin with some quick steps to set up everything correctly,
followed by more detailed instructions to evaluate our artifact.

## Getting Started Guide [10 min]

Please follow these steps to download and start our Docker image:

1. Make sure you have [Docker installed](https://docs.docker.com/engine/install/).
   Our artifact is tested using Docker 27, but other versions should work too.
2. Download the artifact image matching your machine's architecture
   (i.e., `wavelet-artifact-x64.tar.gz` or `wavelet-artifact-aarch64.tar.gz`).
3. Load the image. This should add a local image called `wavelet-artifact`.
   ```sh
   docker load -i wavelet-artifact-<arch>.tar.gz
   ```
4. To start the image, choose one of the following two options: 
   - (Recommended) If your machine has a browser, you can start the image as a VS Code server:
     ```sh
     docker run -p 127.0.0.1:8080:8080 wavelet-artifact server
     ```
     Then in your local browser, visit `localhost:8080` to view the artifact
     in an in-browser VS Code editor.

     This helps with exploring the Lean code base in the next section,
     since it has the Lean 4 extension installed.
   - If you prefer only using the terminal, simply run
     ```sh
     docker run -it wavelet-artifact
     ```

5. Both options above should provide you with a terminal window in the right directory.
   Then as a final sanity check, run
   ```sh
   cd integration-tests && make sanity-check
   ```
   and you should see the expected output in less than a minute:
   ```
   [wavelet] simple ... PASS
   [wavelet-noopt] simple ... PASS
   [circt] simple ... PASS
   [riptide] simple ... PASS
   [riptide-nostream] simple ... PASS
   ```
   This step runs all evaluations on a single test program.

The rest of the guide assumes that you have started the Docker image following the steps above.

## Step-by-Step Instructions [1 hour]

In this section, we first describe steps to reproduce Figures 11-14 in the paper,
and then we show the correspondence between our Lean formalization and theorems in the paper.

### Evaluation Results (Section 6)

The following commands will run all the benchmarks mentioned in Section 6,
and then produce Figures 11-14 in LaTeX:
```sh
cd integration-tests
make eval-compile    # 3 min
make eval -j<N>      # 7.5 min with -j10
python3 sim/stats.py
```
The reference time was recorded on our test machine with Apple M1 Pro CPU and 32 GiB of RAM.

The last command will produce the following output:
```latex
%%%%%%%% CGRA Table %%%%%%%%
<Figure 11>

%%%%%%%% HLS Table %%%%%%%%
<Figure 12>

%%%%%%%% Compiler Perf Table %%%%%%%%
<Figure 13>

%%%%%%%% LoC Table %%%%%%%%
<Figure 14>
```

**Understanding the Results.**
The commands above will compile/test/synthesize 10 test cases in `integration-tests/tests`,
using each of the following compilation pipelines:
1. Wavelet with full optimizations (`wavelet`)
2. Wavelet without unverified graph rewrites (`wavelet-noopt`)
3. RipTide with full optimizations (`riptide`)
4. RipTide without streamification (`riptide-nostream`)
5. CIRCT (`circt`)

For 1 and 2, the source files are `integration-tests/tests/*/test.rs`,
which contain our L_let DSL source code embedded in Rust.
For 3, 4, and 5, the source files are `integration-tests/tests/*/test.c`.
Note that since RipTide is not open-sourced, we directly provide their
compiled dataflow graphs named `test.riptide.json` and `test.riptide.nostream.json`.
The Python files `integration-tests/tests/*/test.py` are reference implementations
and test cases that will be tested against every output dataflow graph and SystemVerilog design.

You can also find various compilation results and logs in each test folder
(e.g., `integration-tests/tests/dither`), and all output files will be tagged
with the pipeline identifier.

For example,
- `test.wavelet.json` is the output dataflow graph compiled using Wavelet.
- `test.wavelet.handshake.mlir` is the same graph but encoded in CIRCT's `handshake` MLIR dialect.
- `test.wavelet.sv` is the SystemVerilog design lowered from the `handshake` source code.
- `test.wavelet.log` is the Verilator simulation results on the design.
- `test.wavelet.netlist.json.log` and `test.wavelet.nextpnr.json.log` are logs from
  Yosys and nextpnr for synthesis/placement/routing on the design.

### Lean Formalization (Section 5)

This section describes the correspondence between our Lean formalization
and various definitions and results in Section 5.

For this step, it is recommended to start our image as a VS Code server
and use the in-browser editor to view our source code (see Step 4 in the **Getting Started Guide**).

Alternatively, you can also download our source code zip file (`wavelet-src.zip`)
or clone our [GitHub repository](https://github.com/plum-umd/wavelet/tree/pldi-ae).
Some instructions below assume that you are using VS Code with the
[Lean 4 extension](https://lean-lang.org/install/) installed (which is already the case
if you are using the in-browser editor).

Our entire Lean formalization is in `wavelet-core/lean`, and all paths in this section
are relative to it.

To verify all the proofs, run
```
cd wavelet-core/lean
lake exec cache get
lake build Thm
```
This might take a while since it needs to fetch the right Lean toolchain and build caches for
[mathlib](https://github.com/leanprover-community/mathlib4).

Below are the pointers to all key definitions and theorems in Section 5.
If you started our image as a VS Code server, you can open these files
in `wavelet-core/lean` using the in-browser editor.

- Section 5.1
  - Syntax and semantics of L_flow: `Wavelet/Dataflow/Proc.lean`.
  - Syntax and semantics of L_let: `Wavelet/Seq/Fn.lean` and `Wavelet/Seq/Prog.lean`.
  - Common definitions of LTS and simulation: `Wavelet/Semantics/Defs.lean` and `Wavelet/Semantics/Lts.lean`.
- Section 5.2
  - Control flow conversion implementation: `Wavelet/Compile/Fn.lean`.
  - Control flow conversion forward simulation (Theorem 5.2): `sim_compile_fn` in `Wavelet/Thm/Compile/Fn/Simulation.lean`.
  - Linking implementation: `Wavelet/Compile/Prog.lean` and `Wavelet/Compile/MapChans.lean`.
  - Linking forward simulation (Theorem 5.5): `sim_compile_prog` in `Wavelet/Thm/Compile/Prog/Simulation.lean`.
- Section 5.3
  - Theorem 5.7: `proc_interp_guarded_hetero_terminal_confl` in `Wavelet/Thm/Determinacy/Hetero.lean`.
  - Theorem 5.9: `compile_strong_norm` in `Wavelet/Thm/HighLevel.lean`.
- Section 5.4
  - Most rewrite rules are implemented in `Wavelet/Compile/Rewrite.lean`,
    and they are currently unverified.

The structure of the `Wavelet` directory:
- `Wavelet/Backend`: Lowering pass to CIRCT `handshake`.
- `Wavelet/Compile`: Various compilation passes.
- `Wavelet/Data`: Basic data structures and lemmas.
- `Wavelet/Dataflow`: Syntax and semantics of our dataflow calculus L_flow.
- `Wavelet/Determinacy`: Basic definitions for the determinacy results.
- `Wavelet/Frontend`: Formats to interface with the Rust frontend.
- `Wavelet/Semantics`: Common semantic utilities.
- `Wavelet/Seq`: Syntax and semantics of L_let.
- `Wavelet/Thm`: All proofs and specifications of Wavelet.

## (Optional) Using Wavelet

If you are interested in trying out Wavelet on your own programs,
please use the pre-built standalone CLI at `target/release/wavelet`,
or re-build it within the image with `cargo build --release`.

Say you want to test Wavelet on the example program at
`integration-tests/tests/simple/test.rs`:
- To compile it to a Wavelet dataflow graph in JSON:
  ```sh
  target/release/wavelet compile integration-tests/tests/simple/test.rs > dfg.json
  ```
- To generate a visualization of the compiled graph in Graphviz DOT format:
  ```sh
  target/release/wavelet plot dfg.json
  ```
  You can copy and paste it into an online Graphviz renderer such as
  [this one](https://dreampuf.github.io/GraphvizOnline).
- To convert the dataflow graph to [CIRCT's `handshake` dialect](https://circt.llvm.org/docs/Dialects/Handshake/):
  ```sh
  target/release/wavelet handshake dfg.json
  ```
  The output can then be further compiled using CIRCT (e.g., using the pre-built
  `integration-tests/build/circt/bin/hlstool`).
- To simulate the dataflow graph's execution:
  ```sh
  target/release/wavelet exec dfg.json --args 0,10,0
  ```

Note that, as a prototype, Wavelet's input Rust DSL (embedding of the L_let language
in our paper) has limited functionality, and your input program must have correct
capability and fence annotations, and satisfy the static control flow restrictions
in Section 4.3 (e.g., only branching and tail recursion are allowed).

You can look at other examples in `integration-tests/tests/*/test.rs` for how to specify
capability and fences, as well as to satisfy the control-flow constraints.
