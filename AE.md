[Artifact Evaluation] Let it Flow: A Formally Verified Compilation Framework for Asynchronous Dataflow
---

Thank you for evaluating our artifact!
Our artifact is a formally verified dataflow compiler called Wavelet, along with test harnesses to compare with two other unverified dataflow compilers in [RipTide](https://ieeexplore.ieee.org/document/9923793) and [LLVM CIRCT](https://circt.llvm.org/).

We begin with some quick steps to set up everything correctly, followed by more detailed instructions to evaluate our artifact.

## Getting Started [10 min]

Please follow these steps to download and start our Docker image:

1. Make sure you have [Docker installed](https://docs.docker.com/engine/install/). Our artifact is tested using Docker 27, but other versions should work too.
2. Download the artifact image matching your machine's architecture (i.e., `artifact-image-x64.tar.gz` or `artifact-image-aarch64.tar.gz`).
3. Load the image. This should add a local image called `wavelet-artifact`.
    ```sh
    docker load -i artifact-image-<arch>.tar.gz
    ```
4. To start the image, choose one of the following two options: 
    - (Recommended) If your machine has a browser, you can start the image as a VS Code server:
        ```sh
        docker run -p 127.0.0.1:8080:8080 wavelet-artifact <TODO>
        ```
        Then in your local browser, visit `localhost:8080` to view the artifact in an in-browser VS Code editor.

        This helps with exploring the Lean code base in the next section, since it has the Lean 4 extension installed.
    - If you prefer only using the terminal, simply run `docker run -it wavelet-artifact`

5. Both options above should provide you with a terminal window in the right directory. Then as a final sanity check, run
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
    This step essentially runs all evaluations on a single test program.

The rest of the guide assumes that you have started the Docker image following the steps above.

## Step-by-Step Instructions [1 hour]

In this section, we first describe steps to reproduce the statistics in Figures 11-14 in the paper (E1),
and then we show the correspondence between the Lean formalization and various on-paper theorems (E2).

### (E1) Evaluation Results in Section 6

The following commands will run all the benchmarks mentioned in Section 6, and then produce Figures 11-14 in LaTeX:
```sh
cd integration-tests
make eval-compile    # 3 min
make eval -j<N>      # 7.5 min with -j10
python3 sim/stats.py
```
The reference time is recorded on our test machine with Apple M1 Pro CPU and 32 GiB of RAM.

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
The commands above will compile/test/synthesize 10 test cases in `integration-tests/tests`, using each of the following compilation pipelines:
1. Wavelet with full optimizations (`wavelet`)
2. Wavelet without unverified graph rewrites (`wavelet-noopt`)
3. RipTide with full optimizations (`riptide`)
4. RipTide without streamification (`riptide-nostream`)
5. CIRCT (`circt`)

For 1 and 2, the source files are `integration-tests/tests/*/test.rs`, which contain our L_let DSL source code embedded in Rust.
For 3, 4, and 5, the source files are `integration-tests/tests/*/test.c`.
The Python files `integration-tests/tests/*/test.py` are reference implementations and test cases that will be tested against every output dataflow graph and SystemVerilog design.

You can also find various compilation results and logs in each test folder (e.g., `integration-tests/tests/dither`), and all output files will be tagged with the pipeline identifier.

For example,
- `test.wavelet.json` is the output dataflow graph compiled using Wavelet
- `test.wavelet.handshake.mlir` is the same graph but encoded in CIRCT's `handshake` MLIR dialect.
- `test.wavelet.sv` is the SystemVerilog design lowered from the `handshake` source code
- `test.wavelet.log` is the Verilator simulation results on the design.
- `test.wavelet.netlist.json.log` and `test.wavelet.nextpnr.json.log` are logs from Yosys and nextpnr for synthesis/placement/routing on the design.

### (E2) Lean Formalization's Correspondence to Section 5
