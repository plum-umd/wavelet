import Wavelet.Dataflow

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.inputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ inputs _ => inputs.toList
  | .async _ inputs _ => inputs.toList

def AtomicProc.outputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ _ outputs => outputs.toList
  | .async _ _ outputs => outputs.toList

/-- Each channel name is used at most once. -/
def AtomicProcs.AffineChan [Arity Op] (aps : AtomicProcs Op χ V) : Prop
  :=
  (∀ (i : Fin aps.length),
    aps[i].inputs.Nodup ∧ aps[i].outputs.Nodup) ∧
  (∀ (i j : Fin aps.length), i ≠ j →
    aps[i].inputs.Disjoint aps[j].inputs ∧
    aps[i].outputs.Disjoint aps[j].outputs)

/-- Each channel name is used at most once. -/
def Proc.AffineChan [Arity Op] (proc : Proc Op χ V m n) : Prop
  := proc.atoms.AffineChan

end Wavelet.Dataflow
