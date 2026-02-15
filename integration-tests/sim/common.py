"""
Common abstractions for, e.g., CIRCT/Handshake channels.
"""

from __future__ import annotations
from typing import Optional, Any
from dataclasses import dataclass

from cocotb.triggers import RisingEdge, ReadOnly

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
        return (await HandshakeOutputPort.read_all([self]))[0]
    
    @staticmethod
    async def read_all(ports: list[HandshakeOutputPort]) -> list[Any]:
        """
        Wait until all ports are valid, then read them together and set ready low for one cycle.
        """
        for port in ports:
            port.ready.value = 1
        while True:
            await RisingEdge(ports[0].clock)
            if all(port.is_valid() for port in ports):
                break
        data = [None if port.data is None else port.data.value for port in ports]
        for port in ports:
            port.ready.value = 0
        await RisingEdge(ports[0].clock)
        return data

class MemoryState:
    def __init__(self, state: None | dict[int, int] | MemoryState = None):
        if state is None:
            self.state = {}
        elif isinstance(state, MemoryState):
            self.state = dict(state.state)
        else:
            self.state = dict(state)

    @staticmethod
    def from_list(l: list[int]) -> MemoryState:
        return MemoryState(state={ i: v for i, v in enumerate(l) })
    
    def to_list(self) -> list[int]:
        """
        Checks that the memory state is a contiguous block of values,
        and then returns it as a list.
        """
        max_addr = max(self.state.keys(), default=None)

        if max_addr is None:
            return []
        
        vals = []
        for addr in range(max_addr + 1):
            if addr not in self.state:
                raise Exception(f"memory state is not contiguous: missing address {addr}")
            vals.append(self.state[addr])

        return vals

