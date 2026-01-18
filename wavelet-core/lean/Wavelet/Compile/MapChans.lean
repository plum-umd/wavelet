import Wavelet.Dataflow.Proc

/-! Renaming channels of a `Proc`/`AtomicProc`. -/

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.mapChans [Arity Op] (f : χ → χ') : AtomicProc Op χ V → AtomicProc Op χ' V
  | .op o inputs outputs => .op o (inputs.map f) (outputs.map f)
  | .async aop inputs outputs => .async aop (inputs.map f) (outputs.map f)

def AtomicProcs.mapChans [Arity Op] (f : χ → χ')
  : AtomicProcs Op χ V → AtomicProcs Op χ' V
  := List.map (AtomicProc.mapChans f)

def Proc.mapChans [Arity Op] (f : χ → χ') (p : Proc Op χ V m n) : Proc Op χ' V m n :=
  {
    inputs := p.inputs.map f,
    outputs := p.outputs.map f,
    atoms := p.atoms.mapChans f,
  }

abbrev RenameM χ := StateM (List χ)

/-- Gets the corresponding index of a name, or creates a new index. -/
def RenameM.mapName [DecidableEq χ] (name : χ) : RenameM χ Nat := do
  let names ← get
  match names.findIdx? (· = name) with
  | some idx => return idx
  | none =>
    set (names ++ [name])
    return names.length

def AtomicProc.renameChansM
  [Arity Op] [DecidableEq χ]
  : AtomicProc Op χ V → RenameM χ (AtomicProc Op Nat V)
  | .op o inputs outputs => do
    let inputs ← inputs.mapM RenameM.mapName
    let outputs ← outputs.mapM RenameM.mapName
    return .op o inputs outputs
  | .async aop inputs outputs => do
    let inputs ← inputs.mapM RenameM.mapName
    let outputs ← outputs.mapM RenameM.mapName
    return .async aop inputs outputs

def AtomicProcs.renameChansM
  [Arity Op] [DecidableEq χ]
  : AtomicProcs Op χ V → RenameM χ (AtomicProcs Op Nat V)
  := List.mapM AtomicProc.renameChansM

def Proc.renameChansM
  [Arity Op] [DecidableEq χ]
  (p : Proc Op χ V m n) : RenameM χ (Proc Op Nat V m n) :=
  return {
    inputs := ← p.inputs.mapM RenameM.mapName,
    outputs := ← p.outputs.mapM RenameM.mapName,
    atoms := ← p.atoms.renameChansM,
  }

/-- Rename channels in a `Proc` to unique `Nat`s. -/
def Proc.renameChans
  [Arity Op] [DecidableEq χ]
  (p : Proc Op χ V m n) : Proc Op Nat V m n :=
  (Proc.renameChansM p).run' []

end Wavelet.Dataflow
