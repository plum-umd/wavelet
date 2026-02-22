"""
Abstractions for simulating the Wavelet-generated designs.
"""

from __future__ import annotations
from typing import Any
from dataclasses import dataclass, field

import re
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from .common import *

@dataclass
class MemoryLoadPort:
    addr: HandshakeOutputPort
    data: HandshakeInputPort
    done: HandshakeInputPort

    def init(self):
        self.addr.init()
        self.data.init()
        self.done.init()

    async def simulate(self, memory: Memory):
        while True:
            addr = await self.addr.read()
            data = memory.load(addr.to_unsigned())
            assert data is not None, f"loading uninitialized memory at {addr}"
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

    async def simulate(self, memory: Memory):
        while True:
            addr, data = await HandshakeOutputPort.read_all([self.addr, self.data])
            # addr = await self.addr.read()
            # data = await self.data.read()
            # print(f"memory store at {addr}: {data}")
            memory.store(addr.to_unsigned(), data.to_signed())
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
    state: MemoryState = field(default_factory=MemoryState)

    def init(self):
        for load in self.loads:
            load.init()
        for store in self.stores:
            store.init()

    def simulate(self):
        """Start simulating the memory behavior (in the background)."""
        for load in self.loads:
            cocotb.start_soon(load.simulate(self))

        for store in self.stores:
            cocotb.start_soon(store.simulate(self))

    def store(self, addr: int, value: int):
        self.state.state[addr] = value

    def load(self, addr: int) -> Optional[int]:
        return self.state.state.get(addr)

class WaveletDut:
    # These names should match the handshake backend naming scheme
    # in `wavelet-core/lean/Wavelet/Backend/Handshake.lean`.
    INPUT_VALID_PATTERN = r"^in(\d+)_valid$"
    OUTPUT_VALID_PATTERN = r"^out(\d+)_valid$"
    MEM_DATA_VALID_PATTERN = r"^mem_(.*)_(load|store)(\d+)_data_valid$"

    """
    Wrapper around a DUT instance compiled from a Wavelet-generated design.
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
    
    async def init(self):
        """
        Initializes the DUT, assuming that the clock is already running.
        """

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
            if match := re.match(WaveletDut.INPUT_VALID_PATTERN, name):
                idx = int(match.group(1))
                assert idx not in inputs
                inputs[idx] = self.get_input_port(f"in{idx}")
            elif match := re.match(WaveletDut.OUTPUT_VALID_PATTERN, name):
                idx = int(match.group(1))
                assert idx not in outputs
                outputs[idx] = self.get_output_port(f"out{idx}")
            elif match := re.match(WaveletDut.MEM_DATA_VALID_PATTERN, name):
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

    async def run(self, *inputs: Any, **mems: MemoryState) -> tuple[list[Any], dict[str, MemoryState]]:
        """
        Simulates the DUT by sending the given inputs and then waiting for the outputs.
        """
        assert len(inputs) == len(self.inputs), "mismatched number of inputs"
        
        for mem in self.memories.values():
            mem.state = MemoryState()

        for loc, mem in mems.items():
            assert loc in self.memories, f"unknown memory location {loc}"
            self.memories[loc].state = MemoryState(mem)

        # Push inputs concurrently to avoid blocking on handshakes
        input_steps = [
            cocotb.start_soon(port.send(val)) for val, port in zip(inputs, self.inputs)
        ]
        for step in input_steps:
            await step

        outputs = [await port.read() for port in self.outputs]
        final_mems = { loc: MemoryState(mem.state) for loc, mem in self.memories.items() }

        return outputs, final_mems
