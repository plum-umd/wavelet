"""
RipTide dataflow graph format.
"""

from __future__ import annotations

from typing import List, Tuple, Optional, Any, Dict, Mapping, Callable, Set
from dataclasses import dataclass


Value = int


class Constant: ...


@dataclass
class FunctionArgument(Constant):
    variable_name: str
    typ: str


@dataclass
class ConstantValue(Constant):
    value: Value


@dataclass
class Channel:
    id: int

    source: Optional[int]
    source_port: Optional[int]
    destination: Optional[int]
    destination_port: Optional[int]

    constant: Optional[Constant]
    hold: bool # whether it holds the value and cannot be popped

    bound: Optional[int]


@dataclass
class ProcessingElement:
    id: int
    name: str
    operator: str
    pred: Optional[str]
    inputs: Tuple[Channel, ...]
    outputs: Dict[int, Tuple[Channel, ...]]
    llvm_position: Optional[Tuple[str, int]]


@dataclass
class DataflowGraph:
    vertices: Tuple[ProcessingElement, ...]
    channels: Tuple[Channel, ...]
    function_arguments: Tuple[FunctionArgument, ...]

    @staticmethod
    def load_dataflow_graph(obj: Any, default_channel_bound: Optional[int] = None) -> DataflowGraph:
        """
        Load a dataflow graph from an object parsed from the o2p json file (output of the RipTide compiler)
        """

        input_channels: Dict[int, List[Channel]] = {}
        output_channels: Dict[int, Dict[int, List[Channel]]] = {}
        vertices: List[ProcessingElement] = []
        channels: List[Channel] = []

        function_argument_names: Dict[str, FunctionArgument] = {}
        function_arguments: List[FunctionArgument] = []

        for arg_obj in obj["function"]["args"]:
            name = arg_obj["name"]

            if name.startswith("%"):
                name = name[1:]

            arg = FunctionArgument(name, arg_obj["type"])
            function_argument_names[name] = arg
            function_arguments.append(arg)

        for i, vertex in enumerate(obj["vertices"]):
            assert i == vertex["ID"]

            input_channels[i] = []

            for port, inputs in enumerate(vertex["inputs"]):
                assert len(inputs) == 1, "unsupported"
                input = inputs[0]

                channel_id = len(channels)

                if input["type"] == "data":
                    input_pe_id = input["ID"]
                    input_pe_port = input["oport"]
                    channel = Channel(channel_id, input_pe_id, input_pe_port, i, port, None, input["hold"], default_channel_bound)

                    if input_pe_id not in output_channels:
                        output_channels[input_pe_id] = {}

                    if input_pe_port not in output_channels[input_pe_id]:
                        output_channels[input_pe_id][input_pe_port] = []

                    output_channels[input_pe_id][input_pe_port].append(channel)

                elif input["type"] == "xdata":
                    name = input["name"]
                    if name.startswith("%"):
                        name = name[1:]

                    function_arg = function_argument_names[name]
                    channel = Channel(channel_id, None, None, i, port, function_arg, input["hold"], default_channel_bound)

                elif input["type"] == "const":
                    channel = Channel(channel_id, None, None, i, port, ConstantValue(input["value"]), input["hold"], default_channel_bound)

                else:
                    assert False, f"unsupported input channel type {input['type']}"

                input_channels[i].append(channel)
                channels.append(channel)

        for i, vertex in enumerate(obj["vertices"]):
            if vertex["type"] == "STREAM_FU_CFG_T":
                op = "STREAM_FU_CFG_T"
            else:
                op = vertex["op"]

            position = ((vertex["llvm_block"], vertex["llvm_index"])
                        if "llvm_block" in vertex and "llvm_index" in vertex else None)

            vertices.append(ProcessingElement(
                i, vertex["name"], op, vertex.get("pred"),
                tuple(input_channels[i]),
                { k: tuple(v) for k, v in output_channels.get(i, {}).items() }, # convert lists to tuples
                position,
            ))

        return DataflowGraph(tuple(vertices), tuple(channels), tuple(function_arguments))
