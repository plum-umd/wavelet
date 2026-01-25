import Wavelet.Frontend.RipTide
import Wavelet.Backend.Handshake

/-! Foreign interfaces for using Wavelet as a library. -/

namespace Wavelet.Frontend.RipTide

open Frontend Backend Compile Dataflow

/-- Parses the JSON input as `RipTide.Prog`. -/
@[export wavelet_riptide_prog_from_json]
def FFI.progFromJson (input : String) : Except String RipTide.Prog :=
  Lean.Json.decode input >>= RawProg.toProg

-- TODO: Outputs `RipTide.Prog` in JSON.

/-- Validates some static properties. -/
@[export wavelet_riptide_prog_validate]
def FFI.validateProg (prog : RipTide.Prog) : Except String Unit :=
  prog.validate

/-- Parses the JSON input as `RipTide.Proc`. -/
@[export wavelet_riptide_proc_from_json]
def FFI.procFromJson (input : String) : Except String RipTide.Proc := do
  let rawProc : RipTide.RawProc ← Lean.Json.decode input
  rawProc.toProc

/-- Outputs `RipTide.Proc` in JSON. -/
@[export wavelet_riptide_proc_to_json]
def FFI.procToJson (proc : RipTide.Proc) : String :=
  Lean.Json.encodeCompact (RawProc.fromProc proc)

/-- Outputs `RipTide.Proc` in DOT. -/
@[export wavelet_riptide_proc_to_dot]
def FFI.procToDot (proc : RipTide.Proc) : Except String String :=
  proc.inner.proc.plot.run

/-- Outputs `RipTide.Proc` in CIRCT Handshake IR. -/
@[export wavelet_riptide_proc_to_handshake]
def FFI.procToHandshake (proc : RipTide.Proc) : Except String String :=
  Handshake.RipTide.emitHandshake proc

/-- Validates some static properties. -/
@[export wavelet_riptide_proc_validate]
def FFI.validateProc (proc : RipTide.Proc) : Except String Unit :=
  proc.validate

/-- Control-flow lowering. -/
@[export wavelet_riptide_prog_lower_control_flow]
def FFI.lowerControlFlow (prog : RipTide.Prog) : Except String RipTide.Proc :=
  prog.lowerControlFlow

/-- Attaches sinks to the last `n` outputs. -/
@[export wavelet_riptide_proc_sink_last_n_outputs]
def FFI.sinkLastNOutputs (n : USize) (proc : RipTide.Proc) : RipTide.Proc :=
  proc.sinkLastNOutputs n.toNat

/-- Applies selected legalizations and optimizations. -/
@[export wavelet_riptide_proc_optimize]
def FFI.optimizeProc (proc : RipTide.Proc) (disabledRules : Array String) : RipTide.Proc :=
  let (_, _, proc) := proc.rewriteProc
    (naryLowering <|> deadCodeElim <|> RipTide.operatorSel)
    disabledRules.toList
  proc

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

end Wavelet.Frontend.RipTide
