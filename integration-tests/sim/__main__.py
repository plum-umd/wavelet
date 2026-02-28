"""
A utility CLI to run a collection of cocotb tests on a compiled design,
primarily used for testing functional equivalence between a Python reference
and the input design.
"""

import os
import sys
import shutil
import argparse

from pathlib import Path
from tempfile import TemporaryDirectory

from cocotb_tools.runner import get_runner

TEST_MODULE_NAME = "tests"

def main():
    parser = argparse.ArgumentParser(description="Run tests on the compiled design.")
    parser.add_argument("design", help="Path to the compiled SystemVerilog design.")
    parser.add_argument("reference", help="Path to the reference Python source file.")
    parser.add_argument("--top", default="top", help="Name of the top-level module in the design.")
    parser.add_argument("--sim", default="verilator", help="Simulator to use for cocotb.")
    parser.add_argument("--interface", default="wavelet", help="Which compiler produced the DUT (wavelet or circt).")
    args = parser.parse_args()

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

if __name__ == "__main__":
    main()
