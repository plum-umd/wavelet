"""
Helper functions for various cocotb tests in this directory.
Partially adapted from CIRCT's integration tests.
<https://github.com/llvm/circt/blob/75d4a854cb145f6f8a3246f0a44a9e80a95e701c/integration_test/Dialect/Handshake/helper.py>
"""

from typing import Optional, Any
from dataclasses import dataclass, field

import re
import cocotb
import cocotb.clock
from cocotb.types import LogicArray
from cocotb.triggers import RisingEdge, ReadOnly

# These names should match the handshake backend naming scheme
# in `wavelet-core/lean/Wavelet/Backend/Handshake.lean`.
INPUT_VALID_PATTERN = r"^in(\d+)_valid$"
OUTPUT_VALID_PATTERN = r"^out(\d+)_valid$"
MEM_DATA_VALID_PATTERN = r"^mem_(.*)_(load|store)(\d+)_data_valid$"

@dataclass
class HandshakeInputPort:
    data: Optional[Any]
    valid: Any
    ready: Any
    clock: Any

    def init(self):
        self.valid.value = 0

    def is_ready(self) -> bool:
        return self.ready.value.is_resolvable and self.ready.value == 1

    async def wait_handshake(self):
        """
        Wait until the handshake is finished
        """
        await ReadOnly()
        direct_send = self.is_ready()
        while not self.is_ready():
            await RisingEdge(self.clock)
        if direct_send:
            await RisingEdge(self.clock)

    async def send(self, data=None):
        assert (data is None) == (self.data is None), "unmatched data availability"
        if self.data is not None:
            self.data.value = data
        self.valid.value = 1
        await self.wait_handshake()
        self.valid.value = 0

@dataclass
class HandshakeOutputPort:
    data: Optional[Any]
    valid: Any
    ready: Any
    clock: Any

    def init(self):
        self.ready.value = 0

    def is_valid(self) -> bool:
        return self.valid.value.is_resolvable and self.valid.value == 1

    async def read(self):
        """
        Wait until data is valid, then read it and set ready low for one cycle.
        """
        self.ready.value = 1
        while True:
            await RisingEdge(self.clock)
            if self.is_valid():
                break
        data = None if self.data is None else self.data.value
        self.ready.value = 0
        await RisingEdge(self.clock)
        return data

@dataclass
class MemoryLoadPort:
    addr: HandshakeOutputPort
    data: HandshakeInputPort
    done: HandshakeInputPort

    def init(self):
        self.addr.init()
        self.data.init()
        self.done.init()

    async def simulate(self, memory: dict[int, int]):
        while True:
            addr = await self.addr.read()
            data = memory.get(addr.to_unsigned(), 0)
            # print(f"memory load at {addr}: {data}")
            await self.done.send()
            await self.data.send(data)

@dataclass
class MemoryStorePort:
    addr: HandshakeOutputPort
    data: HandshakeOutputPort
    done: HandshakeInputPort

    def init(self):
        self.addr.init()
        self.data.init()
        self.done.init()

    async def simulate(self, memory: dict[int, int]):
        while True:
            addr = await self.addr.read()
            data = await self.data.read()
            # print(f"memory store at {addr}: {data}")
            memory[addr.to_unsigned()] = data.to_signed()
            await self.done.send()

@dataclass
class Memory:
    """
    Simulated memory with load and store ports.

    We model memory simply as an unbounded map from unsigned integer
    addresses to signed integer values.
    """

    loads: list[MemoryLoadPort]
    stores: list[MemoryStorePort]
    state: dict[int, int] = field(default_factory=dict)

    def init(self):
        for load in self.loads:
            load.init()
        for store in self.stores:
            store.init()

    def simulate(self):
        """Start simulating the memory behavior (in the background)."""
        for load in self.loads:
            cocotb.start_soon(load.simulate(self.state))

        for store in self.stores:
            cocotb.start_soon(store.simulate(self.state))

class HandshakeDut:
    """
    Wrapper around a Handshake DUT instance.
    """

    def __init__(self, dut):
        """
        Initializes the given cocotb DUT.
        """
        self.dut = dut
        self.inputs: list[HandshakeInputPort] = []
        self.outputs: list[HandshakeOutputPort] = []
        self.memories: dict[str, Memory] = {}
        self.find_all_ports()
    
    async def init(self, clock_us=10):
        # Start the clock in the background
        self.clock = cocotb.clock.Clock(self.dut.clock, clock_us, unit="us")
        cocotb.start_soon(self.clock.start())

        for input in self.inputs:
            input.init()
        
        for output in self.outputs:
            output.init()

        for mem in self.memories.values():
            mem.init()

        # Start memory simulations
        for mem in self.memories.values():
            mem.simulate()

        # Reset
        self.dut.reset.value = 1
        await ReadOnly()
        await RisingEdge(self.dut.clock)
        self.dut.reset.value = 0
        await RisingEdge(self.dut.clock)

    def get_input_port(self, name: str) -> HandshakeInputPort:
        return HandshakeInputPort(
            data=getattr(self.dut, name, None),
            valid=getattr(self.dut, f"{name}_valid"),
            ready=getattr(self.dut, f"{name}_ready"),
            clock=self.dut.clock,
        )

    def get_output_port(self, name: str) -> HandshakeOutputPort:
        return HandshakeOutputPort(
            data=getattr(self.dut, name, None),
            valid=getattr(self.dut, f"{name}_valid"),
            ready=getattr(self.dut, f"{name}_ready"),
            clock=self.dut.clock,
        )

    def find_all_ports(self):
        """
        Find all available input and output ports.
        """
        inputs: dict[int, HandshakeInputPort] = {}
        outputs: dict[int, HandshakeOutputPort] = {}
        # loc |-> (loads, stores)
        mem: dict[str, tuple[dict[int, MemoryLoadPort], dict[int, list[MemoryStorePort]]]] = {}

        # Find all inputs/outputs that we recognize
        for name in dir(self.dut):
            if match := re.match(INPUT_VALID_PATTERN, name):
                idx = int(match.group(1))
                assert idx not in inputs
                inputs[idx] = self.get_input_port(f"in{idx}")
            elif match := re.match(OUTPUT_VALID_PATTERN, name):
                idx = int(match.group(1))
                assert idx not in outputs
                outputs[idx] = self.get_output_port(f"out{idx}")
            elif match := re.match(MEM_DATA_VALID_PATTERN, name):
                # Each memory port comes with three channels: `addr`, `data`, and `done`
                loc = match.group(1)
                access = match.group(2)
                idx = int(match.group(3))
                if loc not in mem:
                    mem[loc] = {}, {}

                loads, stores = mem[loc]
                if access == "load":
                    assert idx not in loads
                    loads[idx] = MemoryLoadPort(
                        addr=self.get_output_port(f"mem_{loc}_load{idx}_addr"),
                        data=self.get_input_port(f"mem_{loc}_load{idx}_data"),
                        done=self.get_input_port(f"mem_{loc}_load{idx}_done"),
                    )
                else:
                    assert access == "store"
                    assert idx not in stores
                    stores[idx] = MemoryStorePort(
                        addr=self.get_output_port(f"mem_{loc}_store{idx}_addr"),
                        data=self.get_output_port(f"mem_{loc}_store{idx}_data"),
                        done=self.get_input_port(f"mem_{loc}_store{idx}_done"),
                    )

        # Check that the indices are contiguous
        input_keys = set(inputs.keys())
        output_keys = set(outputs.keys())
        assert input_keys == set(range(len(inputs))), f"non-contiguous input indices: {input_keys}"
        assert output_keys == set(range(len(outputs))), f"non-contiguous output indices: {output_keys}"

        for loc, (loads, stores) in mem.items():
            load_keys = set(loads.keys())
            store_keys = set(stores.keys())
            assert load_keys == set(range(len(loads))), f"non-contiguous load indices for mem {loc}: {load_keys}"
            assert store_keys == set(range(len(stores))), f"non-contiguous store indices for mem {loc}: {store_keys}"

        # Finally store the ports as lists for easier access
        self.inputs = [inputs[i] for i in range(len(inputs))]
        self.outputs = [outputs[i] for i in range(len(outputs))]
        self.memories = {
            loc: Memory(
                [loads[i] for i in range(len(loads))],
                [stores[i] for i in range(len(stores))],
            )
            for loc, (loads, stores) in mem.items()
        }

        mem_summary = ", ".join(list(f"{loc} (ld = {len(mem.loads)}, st = {len(mem.stores)})" for loc, mem in self.memories.items()))
        print(f"found {len(self.inputs)} input(s), {len(self.outputs)} output(s), and memories: {mem_summary}")

    def clear_memory(self):
        for mem in self.memories.values():
            mem.state.clear()

    async def assert_io(self,
        inputs: list[Any],
        expected_outputs: list[Any],
        *,
        init_memory: dict[str, list[int]] = {},
        expected_memory: dict[str, list[int]] = {},
    ):
        """
        Sends the given inputs and then waits and checks the outputs.
        """
        assert len(inputs) == len(self.inputs), "mismatched number of inputs"
        assert len(expected_outputs) == len(self.outputs), "mismatched number of outputs"

        self.clear_memory()

        for loc, mem in init_memory.items():
            assert loc in self.memories, f"unknown memory location {loc}"
            for i, val in enumerate(mem):
                self.memories[loc].state[i] = val

        # Push inputs concurrently to avoid blocking on handshakes
        input_steps = [
            cocotb.start_soon(port.send(val)) for val, port in zip(inputs, self.inputs)
        ]
        for step in input_steps:
            await step

        output_vals = [await port.read() for port in self.outputs]
        for i, (got, expected) in enumerate(zip(output_vals, expected_outputs)):
            assert got == expected, f"output {i} mismatch: got {got}, expected {expected}"

        for loc, expected in expected_memory.items():
            self.assert_memory(loc, expected)

    def assert_memory(self, loc: str, expected: list[int]):
        print(f"{loc}: {self.memories[loc].state}")
        for i, val in enumerate(expected):
            assert i in self.memories[loc].state, f"expecting {loc}[{i}] = {val}, but it is unset"
            mem_val = self.memories[loc].state[i]
            assert mem_val == val, f"expecting {loc}[{i}] = {val}, but got {mem_val}"

        for i, val in self.memories[loc].state.items():
            assert i < len(expected), f"expecting {loc}[{i}] to be unset, but got {val}"
