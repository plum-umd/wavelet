"""
Helper functions for the cocotb tests.
"""

from __future__ import annotations
from dataclasses import dataclass

import os
import re
import sys
import json
import inspect
import subprocess
import cocotb
import cocotb.clock

from pathlib import Path
from .wavelet import WaveletDut
from .circt import CirctDut
from .common import MemoryState
from .riptide import run as riptide_run

@dataclass
class InputArg:
    param: str
    value: None | int | list[int]

    def is_array(self) -> bool:
        return isinstance(self.value, list)
    
    def copy(self) -> InputArg:
        if self.is_array():
            return InputArg(self.param, self.value.copy())
        else:
            return self
    
    def encode_for_wavelet_sim(self) -> str:
        if self.is_array():
            return f"{self.param}={','.join(map(str, self.value))}"
        elif self.value is None:
            return "()"
        else:
            return str(self.value)

@dataclass    
class OutputMemoryState:
    param: str
    value: MemoryState
    
def run_python_ref(f, args: list[InputArg]) -> tuple[None | int, list[OutputMemoryState]]:
    """
    Runs the Python reference function on the input arguments (including initial memory states)
    and returns the output and modified memory states.
    """
    args = [ arg.copy() for arg in args ]
    res = f(*[ arg.value for arg in args ])
    return res, [ OutputMemoryState(arg.param, MemoryState.from_list(arg.value)) for arg in args if arg.is_array() ]

async def run_wavelet_dut(dut, args: list[InputArg]) -> tuple[None | int, list[OutputMemoryState]]:
    """
    Runs the DUT on the input arguments (including initial memory states)
    assuming that it is compiled from Wavelet.
    """
    dut = WaveletDut(dut)
    await dut.init()

    array_params = [ arg.param for arg in args if arg.is_array() ]

    # Memory names should correspond exactly to the argument
    # names of the decorated Python reference function that
    # receive array inputs.
    assert set(dut.memories.keys()) == set(array_params), \
        f"DUT memories do not match array parameters: got {set(dut.memories.keys())}, expected {set(array_params)}"

    dut_args = [ arg.value for arg in args if not arg.is_array() ]
    dut_mems = { arg.param: MemoryState.from_list(arg.value) for arg in args if arg.is_array() }
    dut_res, dut_res_mems = await dut.run(*dut_args, **dut_mems)

    assert len(dut_res) == 1, f"expect exactly one output from the DUT"
    
    return dut_res[0], [ OutputMemoryState(loc, dut_res_mems[loc]) for loc in array_params ]

async def run_circt_dut(dut, args: list[InputArg]) -> tuple[None | int, list[OutputMemoryState]]:
    """
    Runs the DUT on the input arguments (including initial memory states)
    assuming that it is compiled from Polygeist + CIRCT.
    """
    design_path = os.environ.get("DUT_DESIGN")
    dut = CirctDut(dut, design_path=design_path)
    await dut.init()

    # Build a flat args list matching the DUT input port order:
    # scalars get int values, arrays get MemoryState.
    # The CIRCT pipeline adds one additional zero-width control input at the end.
    dut_args = [
        MemoryState.from_list(arg.value) if arg.is_array() else arg.value
        for arg in args
    ] + [None]

    dut_res, dut_res_mems = await dut.run(dut_args)

    if len(dut_res) == 1:
        dut_res = dut_res[0]
    elif len(dut_res) == 2:
        assert dut_res[1] is None, f"unexpected second output from the DUT: {dut_res}"
        dut_res = dut_res[0]
    else:
        raise RuntimeError(f"expect at most 2 outputs from the DUT, got {len(dut_res)}")

    array_params = [ arg.param for arg in args if arg.is_array() ]
    assert len(dut_res_mems) == len(array_params), \
        f"mismatched number of memory outputs: got {len(dut_res_mems)}, expected {len(array_params)}"

    return dut_res, [
        OutputMemoryState(param, mem)
        for param, mem in zip(array_params, dut_res_mems)
    ]

def parse_input_args(f, tests: list[tuple[None | int | list[int], ...]]) -> list[list[InputArg]]:
    """
    Pairs each test input with the corresponding parameter name.
    """

    assert len(tests) != 0, "at least one test input must be provided"
    assert f.__code__.co_flags & inspect.CO_VARARGS == 0, "variadic arguments are not supported"
    assert f.__code__.co_flags & inspect.CO_VARKEYWORDS == 0, "variadic keyword arguments are not supported"
    assert f.__code__.co_kwonlyargcount == 0, "keyword-only arguments are not supported"

    params = f.__code__.co_varnames[:f.__code__.co_argcount]

    for test in tests:
        assert len(test) == len(params), \
            f"test input has incorrect number of arguments: expected {len(params)}, got {len(test)}"

    return [
        [ InputArg(param, arg) for param, arg in zip(params, test) ]
        for test in tests
    ]

def sim_wavelet(f, tests: list[list[InputArg]]):
    # Compute the path to the Wavelet CLI
    wavelet_cli_path = Path(__file__).parent.parent.parent / "target" / "release" / "wavelet"
    wavelet_cli_path = wavelet_cli_path.resolve()
    assert wavelet_cli_path.exists(), \
        f"Wavelet CLI not found at {wavelet_cli_path}, please build Wavelet first"
    
    design_path = os.environ.get("DUT_DESIGN")
    assert design_path is not None, "DUT_DESIGN environment variable is not set"
    design_path = Path(design_path).resolve()
    assert design_path.exists(), f"DUT design not found at {design_path}"

    total_cycles = 0

    for test in tests:
        scalar_inputs = [ arg.encode_for_wavelet_sim() for arg in test if not arg.is_array() ]
        mem_flags = [
            ["--mem", arg.encode_for_wavelet_sim()]
            for arg in test if arg.is_array()
        ]
        args = [
            "exec",
            "--no-bound",
            "--mod-trivial",
            str(design_path),
            "--args", ",".join(scalar_inputs),
        ] + sum(mem_flags, [])

        # Use subprocess
        print(f"test vector ({', '.join(scalar_inputs)}) ... ", file=sys.stderr, flush=True, end="")
        result = subprocess.run(
            [wavelet_cli_path, *args],
            capture_output=True,
            text=True,
        )
        entire_output = result.stdout + "\n" + result.stderr
        
        # Get number of cycles
        matches = list(re.finditer(r"\[executing\] \d+ ops fired in (\d+) cycles", result.stderr))
        assert len(matches) > 0, f"failed to parse simulation result: {entire_output}"
        cycles = int(matches[-1].group(1))
        total_cycles += cycles
        print(f"finished in {cycles} cycles", file=sys.stderr, flush=True)

        # Parse scalar outputs
        dut_res = []
        match = re.search(r"outputs: (.+)", result.stdout)
        assert match is not None, f"failed to parse simulation output: {entire_output}"
        for output in match.group(1).split(","):
            output = output.strip()
            if output == "()":
                dut_res.append(None)
            else:
                dut_res.append(int(output))

        rest_output = result.stdout[match.end():]

        # Parse final memory states
        dut_mems = {}
        for match in re.finditer(r"(.+): \[(.+)\]", rest_output):
            mem_name = match.group(1).strip()
            mem_values = [ int(x.strip()) for x in match.group(2).split(",") ]
            assert mem_name not in dut_mems, f"duplicate memory output from the simulator for {mem_name}"
            dut_mems[mem_name] = mem_values

        # Finally, compare with reference
        py_res, py_mems = run_python_ref(f, test)

        assert len(dut_res) == 1, "incorrect number of outputs"
        assert dut_res[0] == py_res, f"output mismatch: got {dut_res[0]}, expected {py_res}"

        array_params = [ arg.param for arg in test if arg.is_array() ]
        assert len(py_mems) == len(array_params)
        for py_mem, name in zip(py_mems, array_params):
            dut_mem = dut_mems.get(name, [])
            py_mem_list = py_mem.value.to_list()
            assert dut_mem == py_mem_list, \
                f"memory mismatch for array output {name}: got {dut_mem}, expected {py_mem_list}"

    print(f"total cycles: {total_cycles}", file=sys.stderr, flush=True)

def sim_riptide(f, tests: list[list[InputArg]]):
    design_path = os.environ.get("DUT_DESIGN")
    assert design_path is not None, "DUT_DESIGN environment variable is not set"
    design_path = Path(design_path).resolve()
    assert design_path.exists(), f"DUT design not found at {design_path}"

    with open(design_path) as fp:
        graph_json = json.load(fp)

    # Build a positional mapping from Python param names to JSON arg names,
    # since the two may differ in casing (e.g. Python "M" vs JSON "m").
    json_args = graph_json["function"]["args"]
    assert len(json_args) == len(tests[0]), \
        f"JSON function has {len(json_args)} args but test has {len(tests[0])} params"
    py_to_json = {arg.param: json_args[i]["name"] for i, arg in enumerate(tests[0])}
    total_cycles = 0

    for test in tests:
        scalar_args = {py_to_json[arg.param]: arg.value for arg in test if not arg.is_array()}
        mem_arrays = {py_to_json[arg.param]: arg.value for arg in test if arg.is_array()}

        scalar_desc = ', '.join(f"{k}={v}" for k, v in scalar_args.items())
        print(f"test vector ({scalar_desc}) ... ", file=sys.stderr, flush=True, end="")

        memories, cycles = riptide_run(graph_json, scalar_args, mem_arrays)
        total_cycles += cycles
        print(f"finished in {cycles} cycles", file=sys.stderr, flush=True)

        # Compare with reference
        _, py_mems = run_python_ref(f, test)

        array_params = [arg.param for arg in test if arg.is_array()]
        assert len(py_mems) == len(array_params)
        for py_mem, name in zip(py_mems, array_params):
            json_name = py_to_json[name]
            dut_mem = memories.get(json_name, [])
            py_mem_list = py_mem.value.to_list()
            if dut_mem != py_mem_list:
                print(f"memory mismatch for array output {name}: got {dut_mem}, expected {py_mem_list}", file=sys.stderr, flush=True)

    print(f"total cycles: {total_cycles}", file=sys.stderr, flush=True)

def reference(*tests: tuple[None | int | list[int], ...]):
    """
    A decorator wrapper around `cocotb.test` to test the functional equivalence between
    the DUT and the decorated reference Python function over the given list of test inputs.
    
    For each test (a tuple of numeric or array inputs), the Python function will be
    executed to obtain the expected (numeric) outputs, as well as expected modifications
    to the array inputs.
    
    Then, a suitable DUT wrapper will be used to run the DUT on the same inputs,
    and then check that the DUT outputs and modified arrays (memories) match the expected ones.

    Note that the function should not have any variadic or non-positional arguments.
    """
    def decorator(f):
        nonlocal tests
        tests = parse_input_args(f, tests)

        if os.environ.get("DUT_INTERFACE") == "riptide-sim":
            sim_riptide(f, tests)
            return f

        if os.environ.get("DUT_INTERFACE") == "wavelet-sim":
            # Use high-level Wavelet dataflow simulation instead of using cocotb
            sim_wavelet(f, tests)
            return f

        async def inner(dut, test_idx: int, **_):
            # Start the clock
            clock = cocotb.clock.Clock(dut.clock, 1, unit="ns")
            cocotb.start_soon(clock.start())

            input_args = [ arg.copy() for arg in tests[test_idx] ]
            
            py_res, py_mems = run_python_ref(f, input_args)

            dut_interface = os.environ.get("DUT_INTERFACE", "wavelet")
            if dut_interface == "wavelet":
                dut_res, dut_mems = await run_wavelet_dut(dut, input_args)
            elif dut_interface == "circt":
                dut_res, dut_mems = await run_circt_dut(dut, input_args)
            else:
                raise RuntimeError(f"unsupported DUT interface: {dut_interface}")

            # Compare results and memory states
            assert dut_res == py_res, f"output mismatch: got {dut_res}, expected {py_res}"
            assert len(dut_mems) == len(py_mems), f"mismatched number of arrays: got {len(dut_mems)}, expected {len(py_mems)}"
            for dut_mem, py_mem in zip(dut_mems, py_mems):
                assert dut_mem.param == py_mem.param
                py_mem_list = py_mem.value.to_list()
                dut_mem_list = dut_mem.value.to_list()
                assert dut_mem_list == py_mem_list, \
                    f"memory mismatch for array output {dut_mem.param}: got {dut_mem_list}, expected {py_mem_list}"

        inner.__module__ = "tests"
        inner = cocotb.parametrize(
            (
                # The additional non-array arguments are just for better test names.
                ["test_idx"] + [ arg.param for arg in tests[0] if not arg.is_array() ],
                [
                    [idx] + [ arg.value for arg in inputs if not arg.is_array() ]
                    for idx, inputs in enumerate(tests)
                ],
            ),
        )(inner)
        inner = cocotb.test(name=f.__name__)(inner)

        return inner

    return decorator
