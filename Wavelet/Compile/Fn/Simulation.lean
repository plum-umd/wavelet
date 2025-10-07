import Wavelet.Compile.Fn.Defs

import Wavelet.Compile.Fn.Simulation.Invariants
import Wavelet.Compile.Fn.Simulation.Init
import Wavelet.Compile.Fn.Simulation.Ret
import Wavelet.Compile.Fn.Simulation.Tail
import Wavelet.Compile.Fn.Simulation.Op
import Wavelet.Compile.Fn.Simulation.Br

/-! Simulation proofs for `compileFn`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow Fn

private theorem sim_compile_fn_init
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (fn : Fn Op χ V m n)
  (hnz : m > 0 ∧ n > 0)
  (hwf : fn.WellFormed) :
  SimRel hnz fn.semantics.init (compileFn hnz fn).semantics.init
  := by
  simp [semantics, Fn.semantics, Seq.Config.init,
    Proc.semantics, Dataflow.Config.init]
  and_intros
  · simp
    funext name
    simp [ChanMap.empty, varsToChans, VarMap.getVar, VarMap.empty]
    cases name <;> rfl
  · simp
  · simp [VarMap.empty, VarMap.getVar]
  · simp [OrderedPathConds]
  · simp
  · simp [HasMerges]
  · exact hwf.1
  · exact hwf.2
  · simp [compileFn, compileFn.inputs]
  · simp [compileFn, compileFn.outputs]
  · simp [HasCompiledProcs, compileFn]

/-- Main forward simulation result for `compileFn`. -/
theorem sim_compile_fn
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (fn : Fn Op χ V m n)
  (hnz : m > 0 ∧ n > 0)
  (hwf : fn.WellFormed) :
  fn.semantics ≲ᵣ (compileFn hnz fn).semantics
  := by
  apply Lts.Similarity.intro (SimRel hnz)
  constructor
  · exact sim_compile_fn_init fn hnz hwf
  · intros ec pc l ec' hsim hstep
    cases h₁ : ec.cont with
    | init => exact sim_step_init hsim hstep h₁
    | expr expr =>
      cases h₂ : expr <;> simp [h₂] at h₁
      case ret => exact sim_step_ret hsim hstep h₁
      case tail => exact sim_step_tail hsim hstep h₁
      case op => exact sim_step_op hsim hstep h₁
      case br => exact sim_step_br hsim hstep h₁

end Wavelet.Compile
