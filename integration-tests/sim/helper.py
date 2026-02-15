"""
Helper functions for the cocotb tests.
"""

from __future__ import annotations
from dataclasses import dataclass
import inspect

import os
import cocotb
import cocotb.clock
from .wavelet import WaveletDut
from .circt import CirctDut
from .common import MemoryState

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

@dataclass    
class OutputMemoryState:
    param: str
    value: MemoryState
    
async def run_python_ref(f, args: list[InputArg]) -> tuple[None | int, list[OutputMemoryState]]:
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

    assert len(dut_res) == 1, f"expect exactly one output from the DUT"
    
    array_params = [ arg.param for arg in args if arg.is_array() ]
    assert len(dut_res_mems) == len(array_params), \
        f"mismatched number of memory outputs: got {len(dut_res_mems)}, expected {len(array_params)}"

    return dut_res[0], [
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

        async def inner(dut, test_idx: int, **_):
            # Start the clock
            clock = cocotb.clock.Clock(dut.clock, 1, unit="ns")
            cocotb.start_soon(clock.start())

            input_args = [ arg.copy() for arg in tests[test_idx] ]
            
            py_res, py_mems = await run_python_ref(f, input_args)

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
                py_mem = py_mem.value.to_list()
                dut_mem = dut_mem.value.to_list()
                assert dut_mem == py_mem, f"memory mismatch for array output {dut_mem.param}: got {dut_mem}, expected {py_mem}"

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
