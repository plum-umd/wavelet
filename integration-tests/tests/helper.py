"""
Helper functions for various cocotb tests in this directory.
Partially adapted from CIRCT's integration tests.
<https://github.com/llvm/circt/blob/75d4a854cb145f6f8a3246f0a44a9e80a95e701c/integration_test/Dialect/Handshake/helper.py>
"""

from typing import Optional, Any
from dataclasses import dataclass

import cocotb
import cocotb.clock
from cocotb.triggers import RisingEdge, ReadOnly

# These names should match the handshake backend
# in `wavelet-core/lean/Wavelet/Backend/Handshake.lean`.
INPUT_PREFIX = "in"
OUTPUT_PREFIX = "out"
MEM_PREFIX = "mem_"
VALID_SUFFIX = "_valid"
READY_SUFFIX = "_ready"

@dataclass
class HandshakeInputPort:
    data: Optional[Any]
    valid: Any
    ready: Any
    clock: Any

    def init(self):
        self.valid.value = 0

    async def wait_handshake(self):
        """
        Wait until the handshake is finished, then reset valid flag.
        """
        await ReadOnly()
        await RisingEdge(self.clock)
        while not self.ready.value:
            await RisingEdge(self.clock)
        self.valid.value = 0

    async def send(self, data=None):
        assert (data is None) == (self.data is None), "unmatched data availability"
        if self.data is not None:
            self.data.value = data
        self.valid.value = 1
        await self.wait_handshake()

@dataclass
class HandshakeOutputPort:
    data: Optional[Any]
    valid: Any
    ready: Any
    clock: Any

    def init(self):
        self.ready.value = 1

    async def read(self):
        """
        Wait until data is valid, then read it and set ready low for one cycle.
        """
        self.ready.value = 1
        while self.valid.value != 1:
            await RisingEdge(self.clock)
        data = self.data.value
        await RisingEdge(self.clock)
        return data

class HandshakeDut:
    """
    Wrapper around a Handshake DUT instance.
    """

    def __init__(self, dut):
        """
        Initializes the given cocotb DUT.
        """
        self.dut = dut
        self.inputs: dict[int, HandshakeInputPort] = {}
        self.outputs: dict[int, HandshakeOutputPort] = {}
        self.find_all_ports()
    
    async def init(self, clock_us=10):
        # Start the clock in the background
        self.clock = cocotb.clock.Clock(self.dut.clock, clock_us, unit="us")
        cocotb.start_soon(self.clock.start())

        for input in self.inputs.values():
            input.init()
        
        for output in self.outputs.values():
            output.init()

        # Reset
        self.dut.reset.value = 1
        await RisingEdge(self.dut.clock)
        self.dut.reset.value = 0
        await RisingEdge(self.dut.clock)

    def find_all_ports(self):
        """
        Find all available input and output ports.
        """
        for name in dir(self.dut):
            if name.startswith(INPUT_PREFIX):
                idx = (name.removeprefix(INPUT_PREFIX)
                    .removesuffix(VALID_SUFFIX)
                    .removesuffix(READY_SUFFIX))
                idx = int(idx)
                if idx not in self.inputs:
                    self.inputs[idx] = HandshakeInputPort(
                        data=getattr(self.dut, f"{INPUT_PREFIX}{idx}", None),
                        valid=getattr(self.dut, f"{INPUT_PREFIX}{idx}{VALID_SUFFIX}"),
                        ready=getattr(self.dut, f"{INPUT_PREFIX}{idx}{READY_SUFFIX}"),
                        clock=self.dut.clock,
                    )
            elif name.startswith(OUTPUT_PREFIX):
                idx = (name.removeprefix(OUTPUT_PREFIX)
                    .removesuffix(VALID_SUFFIX)
                    .removesuffix(READY_SUFFIX))
                idx = int(idx)
                if idx not in self.outputs:
                    self.outputs[idx] = HandshakeOutputPort(
                        data=getattr(self.dut, f"{OUTPUT_PREFIX}{idx}", None),
                        valid=getattr(self.dut, f"{OUTPUT_PREFIX}{idx}{VALID_SUFFIX}"),
                        ready=getattr(self.dut, f"{OUTPUT_PREFIX}{idx}{READY_SUFFIX}"),
                        clock=self.dut.clock,
                    )
    
    async def assert_pure_io(self, inputs: list[Any], expected_outputs: list[Any]):
        """
        Sends the given inputs and then waits and checks the outputs.
        """
        assert len(inputs) == len(self.inputs), "mismatched number of inputs"
        assert len(expected_outputs) == len(self.outputs), "mismatched number of outputs"

        # Push inputs concurrently to avoid blocking on handshakes
        input_steps = [
            cocotb.start_soon(self.inputs[i].send(val)) for i, val in enumerate(inputs)
        ]
        for step in input_steps:
            await step
        
        output_vals = [
            await self.outputs[i].read() for i in range(len(expected_outputs))
        ]
        for i, (got, expected) in enumerate(zip(output_vals, expected_outputs)):
            assert got == expected, f"output {i} mismatch: got {got}, expected {expected}"
