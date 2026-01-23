import Wavelet.Frontend.RipTide

/-! Foreign interfaces for using Wavelet as a library. -/

namespace Wavelet.Frontend.RipTide

open Frontend Compile Dataflow

/-- Parses the JSON input as `RipTide.EncapProg`. -/
@[export wavelet_riptide_prog_from_json]
def FFI.progFromJson (input : String) : Except String RipTide.EncapProg :=
  Lean.Json.decode input >>= RawProg.toProg

-- TODO: Outputs `RipTide.EncapProg` in JSON.

/-- Validates some static properties. -/
@[export wavelet_riptide_prog_validate]
def FFI.validateProg (prog : RipTide.EncapProg) : Except String Unit :=
  prog.validate

/-- Parses the JSON input as `RipTide.EncapProc`. -/
@[export wavelet_riptide_proc_from_json]
def FFI.procFromJson (input : String) : Except String RipTide.EncapProc := do
  let rawProc : RipTide.RawProc ← Lean.Json.decode input
  let proc ← rawProc.toProc
  return .fromProc proc

/-- Outputs `RipTide.EncapProc` in JSON. -/
@[export wavelet_riptide_proc_to_json]
def FFI.procToJson (proc : RipTide.EncapProc) : String :=
  Lean.Json.encodeCompact (RawProc.fromProc proc.proc)

/-- Outputs `RipTide.EncapProc` in DOT. -/
@[export wavelet_riptide_proc_to_dot]
def FFI.procToDot (proc : RipTide.EncapProc) : Except String String :=
  proc.proc.plot.run

/-- Outputs `RipTide.EncapProc` in CIRCT Handshake IR. -/
@[export wavelet_riptide_proc_to_handshake]
def FFI.procToHandshake (proc : RipTide.EncapProc) : Except String String :=
  proc.emitHandshake

/-- Validates some static properties. -/
@[export wavelet_riptide_proc_validate]
def FFI.validateProc (proc : RipTide.EncapProc) : Except String Unit :=
  proc.validate

/-- Control-flow lowering. -/
@[export wavelet_riptide_prog_lower_control_flow]
def FFI.lowerControlFlow (prog : RipTide.EncapProg) : Except String RipTide.EncapProc :=
  prog.lowerControlFlow

/-- Attaches sinks to the last `n` outputs. -/
@[export wavelet_riptide_proc_sink_last_n_outputs]
def FFI.sinkLastNOutputs (n : USize) (proc : RipTide.EncapProc) : RipTide.EncapProc :=
  proc.sinkLastNOutputs n.toNat

/-- Applies selected legalizations and optimizations. -/
@[export wavelet_riptide_proc_optimize]
def FFI.optimizeProc (proc : RipTide.EncapProc) : RipTide.EncapProc :=
  let (_, _, proc) := proc.rewriteProc
    (naryLowering <|> RipTide.operatorSel)
    -- TODO: For debugging only!
    [
      "carry-fork-steer-to-inv-left",
      "carry-fork-steer-to-inv-right",
    ]
  proc

/-- Returns the number of atomic processes. -/
@[export wavelet_riptide_proc_num_atoms]
def FFI.procNumAtoms (proc : RipTide.EncapProc) : USize :=
  USize.ofNat proc.proc.atoms.length

/-- Returns the number of "non-trivial" atoms. -/
@[export wavelet_riptide_proc_num_non_trivial_atoms]
def FFI.procNumNonTrivialAtoms (proc : RipTide.EncapProc) : USize :=
  USize.ofNat <|
    (proc.proc.atoms
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
def FFI.procNumInputs (proc : RipTide.EncapProc) : USize :=
  USize.ofNat proc.numIns

/-- Returns the number of outputs. -/
@[export wavelet_riptide_proc_num_outputs]
def FFI.procNumOutputs (proc : RipTide.EncapProc) : USize :=
  USize.ofNat proc.numOuts

end Wavelet.Frontend.RipTide
