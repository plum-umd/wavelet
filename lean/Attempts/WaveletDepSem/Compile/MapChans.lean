import Wavelet.Dataflow.Proc

/-! Renaming channels of a `Proc`/`AtomicProc` -/

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
