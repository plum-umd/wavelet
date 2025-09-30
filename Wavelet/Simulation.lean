import Wavelet.Op
import Wavelet.LTS
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

import Wavelet.Simulation.Defs
import Wavelet.Simulation.Invariants
import Wavelet.Simulation.Init
import Wavelet.Simulation.Ret
import Wavelet.Simulation.Tail
import Wavelet.Simulation.Op
import Wavelet.Simulation.Br

namespace Wavelet.Simulation

open Wavelet.Op LTS Seq Dataflow Compile
open Defs Invariants

/-- Main simulation theorem from `Fn` to compiled `Proc`. -/
theorem sim_compile_fn
  [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed) :
  ∃ pc',
    Dataflow.Config.StepPlus (E := E)
      (Dataflow.Config.init (compileFn hnz fn) state args) .ε pc' ∧
    Seq.RefinesDataflow (E := E)
      (Seq.Config.init fn state args) pc'
      (SimRel hnz)
:= by
  have ⟨pc', hsteps, hsim_init⟩ := Init.sim_step_init (E := E) fn args state hnz hwf_fn
  exists pc'
  constructor
  · exact hsteps
  · constructor
    · exact hsim_init
    · intros ec pc ec' tr hsim hstep
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
theorem refines_steps_to_steps
  [DecidableEq χ₁] [DecidableEq χ₂]
  [Arity Op] [InterpConsts V] [InterpOp Op V E S]
  {ec ec' : Seq.Config Op χ₁ V S m n}
  {pc : Dataflow.Config Op χ₂ V S m n}
  {R : _ → _ → Prop}
  (href : Seq.RefinesDataflow (E := E) ec pc R)
  (hsteps : Seq.Config.StepStar (E := E) ec tr ec') :
  ∃ pc',
    Dataflow.Config.StepStar (E := E) pc tr pc' ∧ R ec' pc'
:= by
  induction hsteps with
  | refl =>
    exists pc
    constructor
    · exact .refl
    · exact href.1
  | tail hsteps_ec hstep_ec₁ ih =>
    rename_i ec₁ tr₁ ec₂ tr₂ ec₃
    have ⟨pc₂, hsteps_pc, hr⟩ := ih href
    have ⟨pc₃, hsteps_pc₁, hr'⟩ := href.2 ec₂ pc₂ ec₃ tr₂ hr hstep_ec₁
    exists pc₃
    have hsteps := LTS.Star.trans hsteps_pc hsteps_pc₁.to_star
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
  [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
  {tr : Trace E}
  {ec : Seq.Config Op χ V S m n}
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed)
  (hsteps : Seq.Config.StepStar (Seq.Config.init fn state args) tr ec)
  (hterm : ec.expr = .ret retVals) :
  ∃ pc',
    Dataflow.Config.StepStar
      (Dataflow.Config.init (compileFn hnz fn) state args) tr pc' ∧
    pc'.state = ec.state ∧
    pc'.chans = finalChans retVals
:= by
  have ⟨pc', hsteps_pc, href⟩ :=
    sim_compile_fn (E := E) fn args state hnz hwf_fn
  have ⟨pc₂, hsteps_pc', hsim⟩ := refines_steps_to_steps href hsteps
  exists pc₂
  and_intros
  · exact .trans hsteps_pc.to_star hsteps_pc'
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

/-- Semantics of `fn` and `compileFn fn` have a state-preserving simulation. -/
theorem sp_sim_compile_fn
  [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed) :
  ∃ pc',
    Dataflow.Config.StepStar (E := E)
      (Dataflow.Config.init (compileFn hnz fn) state args) .ε pc' ∧
    Seq.SPRefinesDataflow (E := E)
      (Seq.Config.init fn state args) pc'
      (SimRel hnz)
:= sorry

end Wavelet.Simulation
