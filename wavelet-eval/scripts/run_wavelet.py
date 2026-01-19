"""
Run the Wavelet compiler on a list of Seq programs
(in JSON format produced by dfx), and collects some
compiler statistics.

Make sure you run `lake build` in `lean` first before
running this script.
"""

import os
import sys
import time
import argparse
import tempfile
import subprocess

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
WAVELET_PATH = f"{SCRIPT_DIR}/../../lean/.lake/build/bin/wavelet"

TRACE_LOG = None

def trace(msg: str):
    print(f"[trace] {msg}", file=sys.stderr, flush=True)
    if TRACE_LOG is not None:
        TRACE_LOG.write(f"{msg}\n")
        TRACE_LOG.flush()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", help="A list of input seq programs")
    parser.add_argument("--output", "-o", help="Output directory")
    args = parser.parse_args()


    if args.output is not None:
        assert not os.path.exists(args.output), f"output directory {args.output} already exists"
        output_dir = args.output
        os.mkdir(output_dir)
    else:
        output_dir = tempfile.mkdtemp()

    output_dir = os.path.abspath(output_dir)

    with open(f"{output_dir}/trace.log", "w") as f:
        global TRACE_LOG
        TRACE_LOG = f

        trace(f"storing output to {output_dir}")

        for input_path in args.inputs:
            trace(f"============== compiling {input_path} ==============")
            input_file_name = os.path.basename(input_path)
            assert input_file_name.endswith(".json"), "input files must be in JSON format"
            input_name = input_file_name[:-5]  # remove .json extension
            output_path = os.path.join(output_dir, f"{input_name}.dfg.json")

            # Run wavelet and capture stderr and stdout
            start_time = time.time()
            result = subprocess.run(
                [
                    WAVELET_PATH, input_path,
                    "--format", "json",
                    "--output", output_path,
                    "--no-out",
                    "--stats",
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            end_time = time.time()

            if result.returncode != 0:
                trace(f"compilation failed for {input_path}")
            
            trace(f"stdout:\n{result.stdout}")
            trace(f"stderr:\n{result.stderr}")
            trace(f"time: {end_time - start_time:.2f} seconds")

            trace(f"============== end {input_path} ==============")

if __name__ == "__main__":
    main()
