import Wavelet.Frontend.RipTide

/-! Foreign interfaces for using Wavelet as a library. -/

namespace Wavelet.Frontend.RipTide

open Frontend Compile Dataflow

/-- Parses the JSON input as `RipTide.EncapProg`. -/
@[export wavelet_riptide_prog_from_json]
def FFI.progFromJson (input : String) : Except String RipTide.EncapProg :=
  Lean.Json.decode input >>= RawProg.toProg

-- TODO: Outputs `RipTide.EncapProg` in JSON.

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

/-- Control-flow lowering. -/
@[export wavelet_riptide_prog_lower_control_flow]
def FFI.lowerControlFlow (prog : RipTide.EncapProg) : Except String RipTide.EncapProc :=
  RipTide.lowerControlFlow prog

/-- Attaches sinks to the last `n` outputs. -/
@[export wavelet_riptide_proc_sink_last_n_outputs]
def FFI.sinkLastNOutputs (n : USize) (proc : RipTide.EncapProc) : RipTide.EncapProc :=
  RipTide.sinkLastNOutputs n.toNat proc

/-- Applies selected legalizations and optimizations. -/
@[export wavelet_riptide_proc_optimize]
def FFI.optimizeProc (proc : RipTide.EncapProc) : (USize × RipTide.EncapProc) :=
  let (numRws, _, proc) := Frontend.RipTide.rewriteProc
    (naryLowering <|> deadCodeElim <|> RipTide.operatorSel) proc
  (USize.ofNat numRws, proc)

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

end Wavelet.Frontend.RipTide
