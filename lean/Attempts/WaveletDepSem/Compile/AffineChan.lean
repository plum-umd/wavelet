import Wavelet.Dataflow

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.inputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ inputs _ => inputs.toList
  | .async _ inputs _ => inputs

def AtomicProc.outputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ _ outputs => outputs.toList
  | .async _ _ outputs => outputs

/-- Each channel name is used at most once. -/
def AtomicProcs.AffineChan [Arity Op] (aps : AtomicProcs Op χ V) : Prop
  :=
  (∀ (i : Fin aps.length),
    aps[i].inputs.Nodup ∧ aps[i].outputs.Nodup) ∧
  (∀ (i j : Fin aps.length), i ≠ j →
    aps[i].inputs.Disjoint aps[j].inputs ∧
    aps[i].outputs.Disjoint aps[j].outputs)

/-- Each channel name is used at most once. -/
def Proc.AffineChan [Arity Op] (proc : Proc Op χ V m n) : Prop :=
  proc.inputs.toList.Nodup ∧
  proc.outputs.toList.Nodup ∧
  proc.atoms.AffineChan ∧
  (∀ input ∈ proc.inputs, ∀ ap ∈ proc.atoms, input ∉ ap.outputs) ∧
  (∀ output ∈ proc.outputs, ∀ ap ∈ proc.atoms, output ∉ ap.inputs)

theorem Proc.AffineChan.atom_inputs_disjoint
  [Arity Op]
  {proc : Proc Op χ V m n}
  (haff : proc.AffineChan)
  (i j : Fin proc.atoms.length)
  (hne : i ≠ j) :
    proc.atoms[i].inputs.Disjoint proc.atoms[j].inputs
  := by
  have ⟨_, _, hatoms, _, _⟩ := haff
  exact (hatoms.2 i j hne).1

theorem Proc.AffineChan.atom_outputs_disjoint
  [Arity Op]
  {proc : Proc Op χ V m n}
  (haff : proc.AffineChan)
  (i j : Fin proc.atoms.length)
  (hne : i ≠ j) :
    proc.atoms[i].outputs.Disjoint proc.atoms[j].outputs
  := by
  have ⟨_, _, hatoms, _, _⟩ := haff
  exact (hatoms.2 i j hne).2

end Wavelet.Dataflow
