"""RipTide dataflow simulator."""

from __future__ import annotations

import json
import sys
import argparse
from collections import deque
from dataclasses import dataclass, field

class Channel:
    def __init__(self, hold=False):
        self.buf = deque()
        self.hold = hold

    def has_data(self):
        return len(self.buf) > 0

    def peek(self):
        return self.buf[0]

    def pop(self):
        val = self.buf[0]
        if self.hold:
            return val
        self.buf.popleft()
        return val

    def push(self, val):
        self.buf.append(val)


OP_REGISTRY: dict[str, type[Op]] = {}

def operator(*op_names):
    def decorator(cls):
        for name in op_names:
            OP_REGISTRY[name] = cls
        return cls
    return decorator

class Op:
    def __init__(self, vid, op_name, name="", pred=None, cmp=None):
        self.id = vid
        self.name = name
        self.op_name = op_name
        self.pred = None if pred is None else ("FALSE" not in pred)
        self.cmp = cmp
        self.inputs: list[Channel] = []
        self.consumers: dict[int, list[Channel]] = {}

    def add_consumer(self, oport, ch):
        self.consumers.setdefault(oport, []).append(ch)

    def all_inputs_ready(self):
        return all(ch.has_data() for ch in self.inputs)

    def push(self, val, oport=0):
        for ch in self.consumers.get(oport, []):
            ch.push(val)

    def pop_all(self):
        for ch in self.inputs:
            ch.pop()

    def is_enabled(self):
        return self.all_inputs_ready()

    def fire(self, mem):
        raise NotImplementedError

def s32(v):
    v = v & 0xFFFFFFFF
    return v - 0x100000000 if v >= 0x80000000 else v

class BinOp(Op):
    fn = staticmethod(lambda a, b: 0)
    def fire(self, mem):
        self.push(self.fn(self.inputs[0].pop(), self.inputs[1].pop()))

@operator("ARITH_CFG_OP_ADD", "ARITH_CFG_OP_GEP", "ARITH_CFG_OP_GEP2", "ARITH_CFG_OP_GEP4")
class Add(BinOp):
    fn = staticmethod(lambda a, b: s32(a + b))

@operator("ARITH_CFG_OP_SUB")
class Sub(BinOp):
    fn = staticmethod(lambda a, b: s32(a - b))

@operator("MUL_CFG_OP_MUL", "MUL_CFG_OP_CLIP")
class Mul(BinOp):
    fn = staticmethod(lambda a, b: s32(a * b))

@operator("ARITH_CFG_OP_SHL")
class Shl(BinOp):
    fn = staticmethod(lambda a, b: s32(a << b))

@operator("ARITH_CFG_OP_ASHR")
class Ashr(BinOp):
    fn = staticmethod(lambda a, b: a >> b)

@operator("ARITH_CFG_OP_LSHR")
class Lshr(BinOp):
    fn = staticmethod(lambda a, b: (a & 0xFFFFFFFF) >> b)

@operator("ARITH_CFG_OP_AND")
class And(BinOp):
    fn = staticmethod(lambda a, b: a & b)

@operator("ARITH_CFG_OP_OR")
class Or(BinOp):
    fn = staticmethod(lambda a, b: a | b)

@operator("ARITH_CFG_OP_XOR")
class Xor(BinOp):
    fn = staticmethod(lambda a, b: a ^ b)

@operator("ARITH_CFG_OP_EQ")
class Eq(BinOp):
    fn = staticmethod(lambda a, b: a == b)

@operator("ARITH_CFG_OP_NE")
class Ne(BinOp):
    fn = staticmethod(lambda a, b: a != b)

@operator("ARITH_CFG_OP_SGT")
class Sgt(BinOp):
    fn = staticmethod(lambda a, b: a > b)

@operator("ARITH_CFG_OP_UGT")
class Ugt(BinOp):
    fn = staticmethod(lambda a, b: (a & 0xFFFFFFFF) > (b & 0xFFFFFFFF))

@operator("ARITH_CFG_OP_SGE")
class Sge(BinOp):
    fn = staticmethod(lambda a, b: a >= b)

@operator("ARITH_CFG_OP_UGE")
class Uge(BinOp):
    fn = staticmethod(lambda a, b: (a & 0xFFFFFFFF) >= (b & 0xFFFFFFFF))

@operator("ARITH_CFG_OP_SLT")
class Slt(BinOp):
    fn = staticmethod(lambda a, b: a < b)

@operator("ARITH_CFG_OP_ULT")
class Ult(BinOp):
    fn = staticmethod(lambda a, b: (a & 0xFFFFFFFF) < (b & 0xFFFFFFFF))

@operator("ARITH_CFG_OP_SLE")
class Sle(BinOp):
    fn = staticmethod(lambda a, b: a <= b)

@operator("ARITH_CFG_OP_ULE")
class Ule(BinOp):
    fn = staticmethod(lambda a, b: (a & 0xFFFFFFFF) <= (b & 0xFFFFFFFF))

@operator("CF_CFG_OP_SELECT")
class Select(Op):
    def fire(self, mem):
        cond = self.inputs[0].pop()
        val_t, val_f = self.inputs[1].pop(), self.inputs[2].pop()
        self.push(val_t if cond else val_f)

@operator("CF_CFG_OP_STEER")
class Steer(Op):
    def fire(self, mem):
        decider, val = self.inputs[0].pop(), self.inputs[1].pop()
        if bool(decider) == self.pred:
            self.push(val)

@operator("CF_CFG_OP_ORDER")
class Order(Op):
    def fire(self, mem):
        left = self.inputs[0].pop()
        self.inputs[1].pop()
        self.push(left)

@operator("CF_CFG_OP_MERGE")
class Merge(Op):
    def is_enabled(self):
        if not self.inputs[0].has_data():
            return False
        return self.inputs[1 if self.inputs[0].peek() else 2].has_data()

    def fire(self, mem):
        decider = self.inputs[0].pop()
        self.push(self.inputs[1 if decider else 2].pop())

@operator("CF_CFG_OP_CARRY")
class Carry(Op):
    INIT, BLOCKED = 0, 1

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.state = self.INIT

    def is_enabled(self):
        if self.state == self.INIT:
            return self.inputs[1].has_data()
        if not self.inputs[0].has_data():
            return False
        if self.inputs[0].peek() == self.pred and not self.inputs[2].has_data():
            return False
        return True

    def fire(self, mem):
        if self.state == self.INIT:
            self.push(self.inputs[1].pop())
            self.state = self.BLOCKED
        elif self.inputs[0].peek() != self.pred:
            self.inputs[0].pop()
            self.state = self.INIT
        else:
            self.inputs[0].pop()
            self.push(self.inputs[2].pop())

@operator("CF_CFG_OP_INVARIANT")
class Invariant(Op):
    INIT, BLOCKED = 0, 1

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.state = self.INIT

    def is_enabled(self):
        if self.state == self.INIT:
            return self.inputs[1].has_data()
        return self.inputs[0].has_data() and self.inputs[1].has_data()

    def fire(self, mem):
        if self.state == self.INIT:
            self.push(self.inputs[1].peek())
            self.state = self.BLOCKED
        else:
            decider = self.inputs[0].pop()
            if decider != self.pred:
                self.inputs[1].pop()
                self.state = self.INIT
            else:
                self.push(self.inputs[1].peek())

@operator("STREAM_CFG_OP_STREAM")
class Stream(Op):
    CMP = {
        "STREAM_CFG_CMP_ULT": lambda i, b: not (i & 0xFFFFFFFF) < (b & 0xFFFFFFFF),
        "STREAM_CFG_CMP_SLT": lambda i, b: not i < b,
        "STREAM_CFG_CMP_ULE": lambda i, b: not (i & 0xFFFFFFFF) <= (b & 0xFFFFFFFF),
        "STREAM_CFG_CMP_SLE": lambda i, b: not i <= b,
        "STREAM_CFG_CMP_UGT": lambda i, b: (i & 0xFFFFFFFF) > (b & 0xFFFFFFFF),
        "STREAM_CFG_CMP_SGT": lambda i, b: i > b,
        "STREAM_CFG_CMP_UGE": lambda i, b: (i & 0xFFFFFFFF) >= (b & 0xFFFFFFFF),
        "STREAM_CFG_CMP_SGE": lambda i, b: i >= b,
    }

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.stream_idx = None

    def is_enabled(self):
        return self.stream_idx is not None or self.all_inputs_ready()

    def fire(self, mem):
        start, bound = self.inputs[0].peek(), self.inputs[1].peek()
        if self.stream_idx is None:
            self.stream_idx = start
        done = self.CMP[self.cmp](self.stream_idx, bound)
        done_flag = int(done != self.pred)
        if not done:
            self.push(self.stream_idx, 0)
            self.stream_idx += self.inputs[2].peek()
        self.push(done_flag, 1)
        if done:
            self.pop_all()
            self.stream_idx = None

@operator("MEM_CFG_OP_LOAD")
class Load(Op):
    def fire(self, mem):
        base, offset = self.inputs[0].peek(), self.inputs[1].peek()
        self.push(mem.get(base + offset, 0), 0)
        self.push(1, 1)
        self.pop_all()

@operator("MEM_CFG_OP_STORE")
class Store(Op):
    def fire(self, mem):
        base, offset = self.inputs[0].peek(), self.inputs[1].peek()
        mem[base + offset] = self.inputs[2].peek()
        self.push(1, 0)
        self.pop_all()

@dataclass
class Memory:
    data: dict[int, int] = field(default_factory=dict)
    base_addrs: dict[str, int] = field(default_factory=dict)
    sizes: dict[str, int] = field(default_factory=dict)

    @staticmethod
    def from_args(func_args: list[dict], mem_arrays: dict[str, list[int]]) -> Memory:
        mem = Memory()
        addr = 0
        for arg_def in func_args:
            name = arg_def["name"]
            if arg_def["type"].endswith("*"):
                arr = mem_arrays.get(name, [])
                mem.base_addrs[name] = addr
                mem.sizes[name] = len(arr)
                for i, val in enumerate(arr):
                    mem.data[addr + i] = val
                addr += len(arr)
        return mem

    def as_arrays(self) -> dict[str, list[int]]:
        results = {}
        for name, base in self.base_addrs.items():
            size = self.sizes[name]
            results[name] = [self.data.get(base + i, 0) for i in range(size)]
        return results

    def get(self, addr: int, default: int = 0) -> int:
        return self.data.get(addr, default)

    def __setitem__(self, addr: int, val: int):
        self.data[addr] = val

def parse_graph(graph_json, scalar_args, mem_arrays):
    func = graph_json["function"]
    mem = Memory.from_args(func["args"], mem_arrays)

    const_values = {}
    for arg_def in func["args"]:
        name = arg_def["name"]
        if arg_def["type"].endswith("*"):
            const_values[name] = mem.base_addrs[name]
        else:
            const_values[name] = scalar_args.get(name, 0)

    vertices = {}
    for v in graph_json["vertices"]:
        op = v["op"]
        vtx = OP_REGISTRY[op](v["ID"], op, name=v.get("name", ""), pred=v.get("pred"), cmp=v.get("cmp"))
        vertices[v["ID"]] = vtx

    for v in graph_json["vertices"]:
        vtx = vertices[v["ID"]]
        for alternatives in v["inputs"]:
            src = alternatives[0]
            hold = src.get("hold", False)
            if src["type"] == "data":
                ch = Channel(hold=hold)
                vtx.inputs.append(ch)
                vertices[src["ID"]].add_consumer(src["oport"], ch)
            else:
                ch = Channel(hold=hold)
                if src["type"] == "xdata":
                    ch.push(const_values[src["name"]])
                else:
                    value = src["value"] & 0xFFFFFFFF
                    value = value - 0x100000000 if value >= 0x80000000 else value
                    ch.push(value)
                vtx.inputs.append(ch)

    non_hold_channels = set()
    for v in graph_json["vertices"]:
        vtx = vertices[v["ID"]]
        for i, alternatives in enumerate(v["inputs"]):
            src = alternatives[0]
            if src["type"] != "data" or not src["hold"]:
                non_hold_channels.add(id(vtx.inputs[i]))

    return vertices, mem, non_hold_channels

def simulate(vertices, mem, max_cycles=None):
    vlist = list(vertices.values())
    cycle = 0
    while True:
        fired = [v for v in vlist if v.is_enabled()]
        if not fired:
            return cycle
        if max_cycles is not None and cycle >= max_cycles:
            return cycle
        for v in fired:
            v.fire(mem)
        cycle += 1

def run(graph_json, scalar_args, mem_arrays, max_cycles=None):
    vertices, mem, non_hold_channels = parse_graph(graph_json, scalar_args, mem_arrays)
    cycles = simulate(vertices, mem, max_cycles)
    # A sanity check for leftover messages
    for v in vertices.values():
        for i, ch in enumerate(v.inputs):
            if id(ch) not in non_hold_channels:
                assert not ch.has_data(), f"vertex {v.id} ({v.name}) input {i} has leftover data: {ch.buf}"
    return mem.as_arrays(), cycles

def main():
    parser = argparse.ArgumentParser(description="RipTide dataflow simulator")
    parser.add_argument("graph", help="path to RipTide dataflow graph in JSON format")
    parser.add_argument("--args", nargs="*", default=[], help="Scalar args: positional or name=value")
    parser.add_argument("--mem", nargs="*", default=[], help="initial arrays (name=v0,v1,v2)")
    parser.add_argument("--max-cycles", type=int, default=None)
    args = parser.parse_args()

    with open(args.graph) as f:
        graph_json = json.load(f)

    scalar_params = [a["name"] for a in graph_json["function"]["args"] if not a["type"].endswith("*")]
    scalar_args = {name: int(val) for name, val in zip(scalar_params, args.args)}

    mem_arrays = {}
    for m in args.mem:
        k, v = m.split("=", 1)
        mem_arrays[k] = [int(x) for x in v.split(",") if x] if v else []

    memories, cycles = run(graph_json, scalar_args, mem_arrays, args.max_cycles)

    print(f"cycles: {cycles}", file=sys.stderr)
    for name, vals in memories.items():
        print(f"{name}: {vals}")

if __name__ == "__main__":
    main()
