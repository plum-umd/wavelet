import Wavelet.Frontend.RipTide
import Wavelet.Backend.Handshake

/-! Foreign interfaces for using Wavelet as a library. -/

namespace Wavelet.Frontend.RipTide

open Frontend Backend Compile Dataflow

section Prog

/-- Parses the JSON input as `RipTide.Prog`. -/
@[export wavelet_riptide_prog_from_json]
def FFI.progFromJson (input : String) : Except String RipTide.Prog :=
  Lean.Json.decode input >>= RawProg.toProg

-- TODO: Outputs `RipTide.Prog` in JSON.

/-- Validates some static properties. -/
@[export wavelet_riptide_prog_validate]
def FFI.validateProg (prog : RipTide.Prog) : Except String Unit :=
  prog.validate

end Prog

section Proc

/-- Parses the JSON input as `RipTide.Proc`. -/
@[export wavelet_riptide_proc_from_json]
def FFI.procFromJson (input : String) : Except String RipTide.Proc := do
  let rawProc : RipTide.RawProc ← Lean.Json.decode input
  rawProc.toProc

/-- Validates some static properties. -/
@[export wavelet_riptide_proc_validate]
def FFI.validateProc (proc : RipTide.Proc) : Except String Unit :=
  proc.validate

/-- Outputs `RipTide.Proc` in JSON. -/
@[export wavelet_riptide_proc_to_json]
def FFI.procToJson (proc : RipTide.Proc) : String :=
  Lean.Json.encodeCompact (RawProc.fromProc proc)

/-- Outputs `RipTide.Proc` in DOT. -/
@[export wavelet_riptide_proc_to_dot]
def FFI.procToDot (proc : RipTide.Proc) : Except String String :=
  proc.inner.proc.plot.run

/-- Returns the number of atomic processes. -/
@[export wavelet_riptide_proc_num_atoms]
def FFI.procNumAtoms (proc : RipTide.Proc) : USize :=
  USize.ofNat proc.inner.proc.atoms.length

/-- Returns the number of "non-trivial" atoms. -/
@[export wavelet_riptide_proc_num_non_trivial_atoms]
def FFI.procNumNonTrivialAtoms (proc : RipTide.Proc) : USize :=
  USize.ofNat <|
    (proc.inner.proc.atoms
    |>.filter (λ
      | .async (AsyncOp.fork ..) ..
      | .async (AsyncOp.forward ..) ..
      | .async (AsyncOp.forwardc ..) ..
      | .async (AsyncOp.inact ..) ..
      | .async (AsyncOp.const ..) ..
      | .async (AsyncOp.sink ..) .. => false
      | _ => true)
    |>.length)

/-- Returns the number of inputs. -/
@[export wavelet_riptide_proc_num_inputs]
def FFI.procNumInputs (proc : RipTide.Proc) : USize :=
  USize.ofNat proc.inner.numIns

/-- Returns the number of outputs. -/
@[export wavelet_riptide_proc_num_outputs]
def FFI.procNumOutputs (proc : RipTide.Proc) : USize :=
  USize.ofNat proc.inner.numOuts

end Proc

section Passes

/-- Outputs `RipTide.Proc` in CIRCT Handshake IR. -/
@[export wavelet_riptide_proc_to_handshake]
def FFI.procToHandshake (proc : RipTide.Proc) : Except String String :=
  Handshake.RipTide.emitProc proc

/-- Control-flow lowering. -/
@[export wavelet_riptide_prog_lower_control_flow]
def FFI.lowerControlFlow (prog : RipTide.Prog) : Except String RipTide.Proc :=
  prog.lowerControlFlow

/-- Attaches sinks to the last `n` outputs. -/
@[export wavelet_riptide_proc_sink_last_n_outputs]
def FFI.sinkLastNOutputs (n : USize) (proc : RipTide.Proc) : RipTide.Proc :=
  proc.sinkLastNOutputs n.toNat

/-- Trims the inputs/outputs to remove any redundant unit inputs/outputs. -/
@[export wavelet_riptide_proc_trim_unit_io]
def FFI.trimUnitIO (proc : RipTide.Proc) : RipTide.Proc :=
  proc.trimUnitIO

/-- Applies selected legalizations and optimizations. -/
@[export wavelet_riptide_proc_optimize]
def FFI.optimizeProc (proc : RipTide.Proc) (disabledRules : Array String) : RipTide.Proc :=
  let (_, _, proc) := proc.rewriteProc
    (naryLowering <|> deadCodeElim <|> RipTide.operatorSel)
    disabledRules.toList
  proc

end Passes

section Testing

/-- Initializes a dataflow configuration from the given process. -/
@[export wavelet_riptide_config_init]
def FFI.initConfig (proc : RipTide.Proc) : Config := .init proc

/-- Checks if the configuration is in the initial state or not (excluding memory state). -/
@[export wavelet_riptide_config_check_init]
def FFI.checkConfigInit (c : Config) : Except String Unit := c.checkInit

/-- Stores a value to a memory location. -/
@[export wavelet_riptide_config_store_mem]
def FFI.configStoreMem
  (c : Config) (loc : Loc) (addr : Value) (val : Value) : Config :=
  c.storeMem loc addr val

/-- Converts an `Int32` to a `Value`. -/
@[export wavelet_riptide_value_from_int32]
def FFI.valueFromInt32 (n : Int32) : Value := .int 32 n.toBitVec

/-- Converts a `Value` to an `Int32`. -/
@[export wavelet_riptide_value_to_int32]
def FFI.valueToInt32 (v : Value) : Except String Int32 := do
  match v with
  | .int 32 bv => return bv.toInt.toInt32
  | _ => throw "value is not a 32-bit integer"

/-- Loads a value from a memory location. -/
@[export wavelet_riptide_config_load_mem]
def FFI.configLoadMem
  (c : Config) (loc : Loc) (addr : Value) : Option Value :=
  c.loadMem loc addr

/-- Pushes the given array of inputs to the input channels. -/
@[export wavelet_riptide_config_push_inputs]
def FFI.configPushInputs
  (c : Config) (inputs : Array Value) : Except String Config :=
  c.pushInputs inputs.toList

/-- Pops one value from each output channel. -/
@[export wavelet_riptide_config_pop_outputs]
def FFI.configPopOutputs
  (c : Config) : Except String (Array Value × Config) := do
  let (vals, c') ← c.popOutputs
  return (vals.toArray, c')

/-- Steps the configuration until the optional bound
or until no more operator is fireable. -/
@[export wavelet_riptide_config_steps]
def FFI.configSteps
  (c : Config) (bound : Option USize) : Except String (Array Label × Config) := do
  let (trace, c') ← c.steps (bound.map USize.toNat)
  return (trace.toArray, c')

end Testing

end Wavelet.Frontend.RipTide
