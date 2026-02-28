"""
A utility CLI to run a collection of functional equivalence tests
on a compiled design/dataflow graph against a reference implementation.
"""

import os
import sys
import shutil
import argparse

from pathlib import Path
from tempfile import TemporaryDirectory

from cocotb_tools.runner import get_runner

TEST_MODULE_NAME = "tests"

def sim_verilog(args):
    """Run tests on a compiled SystemVerilog design."""

    with TemporaryDirectory() as tmp_dir:
        # Copy all the reference test to a new temp dir
        test_module_path = Path(tmp_dir) / TEST_MODULE_NAME
        test_module_path.mkdir()
        test_path = Path(args.reference)
        shutil.copy(test_path, test_module_path / test_path.name)

        # cocotb runner propagates `sys.path` to the test subprocess
        sys.path.insert(0, tmp_dir)

        if args.sim == "verilator":
            os.environ["CXXFLAGS"] = "-std=c++17 -Wno-unknown-warning-option"

        runner = get_runner(args.sim)
        args.top = args.top.replace("-", "_")
        runner.build(sources=[args.design], hdl_toplevel=args.top, timescale=("1ns", "1ps"))
        result_path = runner.test(
            hdl_toplevel=args.top,
            test_module=[ f"{TEST_MODULE_NAME}.{test_path.stem}" ],
            extra_env={
                "DUT_INTERFACE": args.interface,
                "DUT_DESIGN": str(Path(args.design).resolve()),
            },
        )

        # TODO: This is a bit hacky.
        with open(result_path) as f:
            if "<failure" in f.read():
                sys.exit(1)

def sim_wavelet(args):
    """Run high-level simulation on a compiled Wavelet dataflow graph."""

    design_path = Path(args.design).resolve()
    assert design_path.suffix == ".json", f"expected a Wavelet dataflow graph in JSON format, but got {args.design}"

    os.environ["DUT_INTERFACE"] = "wavelet-sim"
    os.environ["DUT_DESIGN"] = str(design_path)

    # Execute the test Python file
    test_path = Path(args.reference).resolve()
    assert test_path.suffix == ".py", f"expected a Python source file for the reference implementation, but got {args.reference}"

    with open(test_path) as f:
        exec(f.read())
    
def main():
    parser = argparse.ArgumentParser(description="Run tests on the compiled design.")
    parser.add_argument("design", help="Path to the compiled SystemVerilog design or Wavelet dataflow graph.")
    parser.add_argument("reference", help="Path to the reference Python source file.")
    parser.add_argument("--top", default="top", help="Name of the top-level module in the design.")
    parser.add_argument("--sim", default="verilator", help="Simulator to use for cocotb.")
    parser.add_argument("--interface", default="wavelet", help="Which compiler produced the DUT (wavelet/wavelet-sim/circt).")
    args = parser.parse_args()

    if args.interface == "wavelet-sim":
        sim_wavelet(args)
    else:
        sim_verilog(args)

if __name__ == "__main__":
    main()
