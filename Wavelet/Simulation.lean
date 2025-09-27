import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

import Wavelet.Simulation.Invariants
import Wavelet.Simulation.Init
import Wavelet.Simulation.Ret
import Wavelet.Simulation.Tail
import Wavelet.Simulation.Op
import Wavelet.Simulation.Br
import Wavelet.Simulation.Call

namespace Wavelet.Simulation

open Wavelet.Op Seq Dataflow Compile
open Invariants

/-- Defines refinement of two transition systems in general. -/
def Refines
  {T : Type v} {S : Type w}
  (c₁ : T) (c₂ : S)
  (R : T → S → Prop)
  (Step₁ : T → T → Prop)
  (Step₂ : S → S → Prop) :=
  R c₁ c₂ ∧
  (∀ c₁ c₂ c₁',
    R c₁ c₂ →
    Step₁ c₁ c₁' →
    ∃ c₂', Step₂ c₂ c₂' ∧ R c₁' c₂')

/-- Specific case for a Seq config to refine a dataflow config. -/
def SeqRefinesDataflow
  [DecidableEq χ₁] [DecidableEq χ₂]
  [Arity Op] [InterpConsts V] [InterpOp Op V S]
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  Refines c₁ c₂ R Config.Step Config.StepPlus

/-- Main simulation theorem from `Fn` to compiled `Proc`. -/
theorem sim_compile_fn
  [Arity Op] [InterpConsts V] [InterpOp Op V S] [DecidableEq χ]
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed) :
  ∃ pc',
    Dataflow.Config.StepStar
      (Dataflow.Config.init (compileFn hnz fn) state args) pc' ∧
    SeqRefinesDataflow
      (Seq.Config.init fn state args) pc'
      (SimRel hnz)
:= by
  have ⟨pc', hsteps, hsim_init⟩ := Init.sim_step_init fn args state hnz hwf_fn
  exists pc'
  constructor
  · exact hsteps
  · constructor
    · exact hsim_init
    · intros ec pc ec' hsim hstep
      cases hcont : ec.expr with
      | ret =>
        -- Not possible to step from a final state
        cases hstep with | _ hexpr => simp [hcont] at hexpr
      | cont expr =>
        cases expr with
        | ret => exact Simulation.Ret.sim_step_ret hsim hstep hcont
        | tail => exact Simulation.Tail.sim_step_tail hsim hstep hcont
        | op => exact Simulation.Op.sim_step_op hsim hstep hcont
        | br => exact Simulation.Br.sim_step_br hsim hstep hcont

/-- Converts a trace of `Seq` to a trace of `Dataflow` with
related final configurations. -/
theorem SeqRefinesDataflow_steps_to_steps
  [DecidableEq χ₁] [DecidableEq χ₂]
  [Arity Op] [InterpConsts V] [InterpOp Op V S]
  {ec ec' : Seq.Config Op χ₁ V S m n}
  {pc : Dataflow.Config Op χ₂ V S m n}
  {R : _ → _ → Prop}
  (href : SeqRefinesDataflow ec pc R)
  (hsteps : Seq.Config.StepStar ec ec') :
  ∃ pc',
    Dataflow.Config.StepStar pc pc' ∧ R ec' pc'
:= by
  induction hsteps with
  | refl =>
    exists pc
    constructor
    · exact .refl
    · exact href.1
  | tail hsteps_ec hstep_ec₁ ih =>
    rename_i ec₁ ec₂
    have ⟨pc₁, hsteps_pc, hr⟩ := ih
    have ⟨pc₂, hsteps_pc₁, hr'⟩ := href.2 ec₁ pc₁ ec₂ hr hstep_ec₁
    exists pc₂
    have hsteps := Relation.ReflTransGen.trans hsteps_pc hsteps_pc₁.to_reflTransGen
    simp [hr']
    exact hsteps

/-- Defines the final channel state with the given return values. -/
def finalChans (retVals : Vector V n) : ChanMap (ChanName χ) V :=
  λ name =>
    match name with
    | .final_dest i => if _ : i < n then [retVals[i]] else []
    | _ => []

/-- Same results at termination. -/
theorem sim_compile_fn_forward_results
  [Arity Op] [InterpConsts V] [InterpOp Op V S] [DecidableEq χ]
  {ec : Seq.Config Op χ V S m n}
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed)
  (hsteps : Seq.Config.StepStar (Seq.Config.init fn state args) ec)
  (hterm : ec.expr = .ret retVals) :
  ∃ pc',
    Dataflow.Config.StepStar
      (Dataflow.Config.init (compileFn hnz fn) state args) pc' ∧
    pc'.state = ec.state ∧
    pc'.chans = finalChans retVals
:= by
  have ⟨pc', hsteps_pc, href⟩ :=
    sim_compile_fn fn args state hnz hwf_fn
  have ⟨pc₂, hsteps_pc', hsim⟩ := SeqRefinesDataflow_steps_to_steps href hsteps
  exists pc₂
  and_intros
  · exact Relation.ReflTransGen.trans hsteps_pc hsteps_pc'
  · simp [hsim.eq_state]
  · funext name
    simp [hsim.vars_to_chans, varsToChans, finalChans]
    cases name with
    | var v pathConds =>
      simp [hsim.final_config_empty_path_conds hterm]
      intros _
      split <;> rename_i h₁
      · have := hsim.get_var_to_defined_vars ⟨_, h₁⟩
        simp [hsim.final_config_empty_defined_vars hterm] at this
      · rfl
    | final_dest i => simp [hterm]
    | _ => simp [hsim.final_config_empty_path_conds hterm]

end Wavelet.Simulation
