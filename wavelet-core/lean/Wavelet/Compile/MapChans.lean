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
def RenameM.mapName [DecidableEq χ]
  (renamer : Nat → χ → χ')
  (name : χ) : RenameM χ χ' := do
  let names ← get
  match names.findIdx? (· = name) with
  | some idx => return renamer idx name
  | none =>
    set (names ++ [name])
    return renamer names.length name

def AtomicProc.renameChansM
  [Arity Op] [DecidableEq χ]
  (renamer : Nat → χ → χ')
  : AtomicProc Op χ V → RenameM χ (AtomicProc Op χ' V)
  | .op o inputs outputs => do
    let inputs ← inputs.mapM (RenameM.mapName renamer)
    let outputs ← outputs.mapM (RenameM.mapName renamer)
    return .op o inputs outputs
  | .async aop inputs outputs => do
    let inputs ← inputs.mapM (RenameM.mapName renamer)
    let outputs ← outputs.mapM (RenameM.mapName renamer)
    return .async aop inputs outputs

def AtomicProcs.renameChansM
  [Arity Op] [DecidableEq χ]
  (renamer : Nat → χ → χ')
  : AtomicProcs Op χ V → RenameM χ (AtomicProcs Op χ' V)
  := List.mapM (AtomicProc.renameChansM renamer)

def Proc.renameChansM
  [Arity Op] [DecidableEq χ]
  (renamer : Nat → χ → χ')
  (p : Proc Op χ V m n) : RenameM χ (Proc Op χ' V m n) :=
  return {
    inputs := ← p.inputs.mapM (RenameM.mapName renamer),
    outputs := ← p.outputs.mapM (RenameM.mapName renamer),
    atoms := ← p.atoms.renameChansM renamer,
  }

/-- Rename channels in a `Proc` to unique `Nat`s. -/
def Proc.renameChans
  [Arity Op] [DecidableEq χ]
  (renamer : Nat → χ → χ')
  (p : Proc Op χ V m n) : Proc Op χ' V m n :=
  (Proc.renameChansM renamer p).run' []

end Wavelet.Dataflow
