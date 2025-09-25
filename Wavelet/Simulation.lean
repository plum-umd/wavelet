import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

import Wavelet.Simulation.Relation
import Wavelet.Simulation.Init
import Wavelet.Simulation.Ret
import Wavelet.Simulation.Tail
import Wavelet.Simulation.Op
import Wavelet.Simulation.Br

namespace Wavelet.Simulation

open Wavelet.Op Seq Dataflow Compile
open Relation

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

/-- Main simulation theorem from `Fn` to compiled `Proc`. -/
theorem sim_compile_fn
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed) :
  ∃ pc',
    Dataflow.Config.StepStar Op (ChanName χ) V S
      (Dataflow.Config.init _ _ _ _ (compileFn Op χ V S hnz fn) state args) pc' ∧
    SeqRefinesDataflow Op V S
      (Seq.Config.init _ _ _ _ fn state args) pc'
      (SimR _ _ _ _ hnz)
:= by
  have ⟨pc', hsteps, hsim_init⟩ := Init.sim_step_init Op χ V S fn args state hnz hwf_fn
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
        | ret => exact Simulation.Ret.sim_step_ret Op χ V S hnz ec ec' pc hsim hstep hcont
        | tail => exact Simulation.Tail.sim_step_tail Op χ V S hnz ec ec' pc hsim hstep hcont
        | op => exact Simulation.Op.sim_step_op Op χ V S hnz ec ec' pc hsim hstep hcont
        | br => exact Simulation.Br.sim_step_br hnz hsim hstep hcont

/-- Converts a trace of `Seq` to a trace of `Dataflow` with
related final configurations. -/
theorem SeqRefinesDataflow_steps_to_steps
  [DecidableEq χ₁] [DecidableEq χ₂]
  (ec : Seq.Config Op χ₁ V S m n)
  (pc : Dataflow.Config Op χ₂ V S m n)
  (href : SeqRefinesDataflow Op V S ec pc R)
  (hsteps : Seq.Config.StepStar Op χ₁ V S ec ec') :
  ∃ pc',
    Dataflow.Config.StepStar Op χ₂ V S pc pc' ∧
    R ec' pc'
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
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed)
  (hsteps : Seq.Config.StepStar Op χ V S (Seq.Config.init _ _ _ _ fn state args) ec)
  (hterm : ec.expr = .ret retVals) :
  ∃ pc',
    Dataflow.Config.StepStar Op (ChanName χ) V S
      (Dataflow.Config.init _ _ _ _ (compileFn Op χ V S hnz fn) state args) pc' ∧
    pc'.state = ec.state ∧
    pc'.chans = finalChans _ _ retVals
:= by
  have ⟨pc', hsteps_pc, href⟩ :=
    sim_compile_fn Op χ V S fn args state hnz hwf_fn
  have ⟨pc₂, hsteps_pc', hsim⟩ := SeqRefinesDataflow_steps_to_steps _ _ _ _ pc' href hsteps
  have ⟨heq_state, hchans, _, hdefined_vars, _, _, _, _, _, _, _,
    _, _, _, _, _, hret, _⟩ := hsim
  exists pc₂
  and_intros
  · exact Relation.ReflTransGen.trans hsteps_pc hsteps_pc'
  · simp [heq_state]
  · funext name
    simp [hchans, SimR.varsToChans, finalChans]
    have ⟨_, _, _, hdefined_vars_empty, hpath_conds_empty⟩ := hret _ hterm

    cases name with
    | var v pathConds =>
      simp [hpath_conds_empty]
      intros _
      split <;> rename_i h₁
      · have := (hdefined_vars v).mpr ⟨_, h₁⟩
        simp [hdefined_vars_empty] at this
      · rfl
    | final_dest i => simp [hterm]
    | _ => simp [hpath_conds_empty]

end Wavelet.Simulation
