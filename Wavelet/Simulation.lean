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
theorem sim_dataflow
  {fn : Fn Op χ m n} {args : Vector V m} {state : S}
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
        | br => exact Simulation.Br.sim_step_br Op χ V S hnz ec ec' pc hsim hstep hcont

end Wavelet.Simulation
