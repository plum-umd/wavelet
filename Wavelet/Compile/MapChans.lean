import Wavelet.Dataflow.Proc

/-! Renaming channels of a `Proc`/`AtomicProc` -/

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.mapChans [Arity Op] (f : χ → χ') : AtomicProc Op χ V → AtomicProc Op χ' V
  | .op o inputs outputs => .op o (inputs.map f) (outputs.map f)
  | .switch decider inputs outputs₁ outputs₂ =>
    .switch (f decider) (inputs.map f) (outputs₁.map f) (outputs₂.map f)
  | .steer flavor decider inputs outputs =>
    .steer flavor (f decider) (inputs.map f) (outputs.map f)
  | .carry inLoop decider inputs₁ inputs₂ outputs =>
    .carry inLoop (f decider) (inputs₁.map f) (inputs₂.map f) (outputs.map f)
  | .merge decider inputs₁ inputs₂ outputs =>
    .merge (f decider) (inputs₁.map f) (inputs₂.map f) (outputs.map f)
  | .forward inputs outputs => .forward (inputs.map f) (outputs.map f)
  | .fork input outputs => .fork (f input) (outputs.map f)
  | .const c act outputs => .const c (f act) (outputs.map f)
  | .forwardc inputs consts outputs => .forwardc (inputs.map f) consts (outputs.map f)
  | .sink inputs => .sink (inputs.map f)

def AtomicProcs.mapChans [Arity Op] (f : χ → χ')
  : AtomicProcs Op χ V → AtomicProcs Op χ' V
  := List.map (AtomicProc.mapChans f)

def Proc.mapChans [Arity Op] (f : χ → χ') (p : Proc Op χ V m n) : Proc Op χ' V m n :=
  {
    inputs := p.inputs.map f,
    outputs := p.outputs.map f,
    atoms := p.atoms.mapChans f,
  }

section Simulation

theorem sim_map_chans_inj
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f) :
  proc.semantics ≲ᵣ (proc.mapChans f).semantics := sorry

end Simulation

end Wavelet.Dataflow
