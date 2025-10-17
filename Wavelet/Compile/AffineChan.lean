import Wavelet.Dataflow

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.inputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ inputs _ => inputs.toList
  | .async _ inputs _ => inputs.toList
  | .steer _ _ inputs _ => inputs.toList
  | .carry _ _ inputs₁ inputs₂ _ => (inputs₁ ++ inputs₂).toList
  | .merge _ inputs₁ inputs₂ _ => (inputs₁ ++ inputs₂).toList
  | .forward inputs _ => inputs.toList
  | .fork input _ => [input]
  | .const _ act _ => [act]
  | .forwardc inputs _ _ => inputs.toList
  | .sink inputs => inputs.toList

def AtomicProc.outputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ _ outputs => outputs.toList
  | .async _ _ outputs => outputs.toList
  | .steer _ _ _ outputs => outputs.toList
  | .carry _ _ _ _ outputs => outputs.toList
  | .merge _ _ _ outputs => outputs.toList
  | .forward _ outputs => outputs.toList
  | .fork _ outputs => outputs.toList
  | .const _ _ outputs => outputs.toList
  | .forwardc _ _ outputs => outputs.toList
  | .sink _ => []

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
