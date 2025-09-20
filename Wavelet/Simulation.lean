import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Lemmas

open Wavelet.Op

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

namespace Wavelet.Simulation

open Op Seq Dataflow Compile

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
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  Refines c₁ c₂ R (Config.Step Op χ₁ V S) (Config.StepPlus Op χ₂ V S)

def SimR.varsToChans
  (ec : Seq.Config Op χ V S m n) : ChanMap (ChanName χ) V :=
  λ name =>
    match name with
    | .var v pathConds =>
      if pathConds = ec.pathConds then
        if let some val := ec.vars.getVar _ _ v then
          [val]
        else []
      else []
    | .merge_cond v =>
      if (true, v) ∈ ec.pathConds ∨ (false, v) ∈ ec.pathConds then
        [instInterp.trueVal]
      else []
    | _ => []

def SimR
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.state = pc.state ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    -- Some invariants about the "shape" of the processes
    pc.proc.atoms = compileFn.initCarry _ _ _ ec.fn carryInLoop :: rest ∧
    (compileFn Op χ V S hnz ec.fn).atoms = compileFn.initCarry _ _ _ ec.fn false :: rest ∧
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    (∀ i, (h : i < ec.pathConds.length) →
      compileExpr.brMerge _ _ _ m n (ec.pathConds[i]'h).2 (ec.pathConds.drop i) ∈ pc.proc.atoms) ∧
    -- (∀ vals, ec.expr = .ret vals → ¬ carryInLoop ∧ ctxCurrent = [] ∧ ctxRight = []) ∧
    (∀ expr, ec.expr = .cont expr → carryInLoop ∧
      expr.WellFormed _ _ ec.definedVars ∧
      compileExpr Op χ V S hnz ec.definedVars ec.pathConds expr = ctxCurrent) ∧
    -- Some invariants about the correspondence between variables and channels
    pc.chans = SimR.varsToChans _ _ _ _ ec ∧
    (∀ var, var ∈ ec.definedVars ↔ ∃ val, ec.vars.getVar _ _ var = some val)

theorem pop_singleton {chans : ChanMap χ V}
  (hsingleton : chans.IsSingleton _ _ name val) :
  ∃ chans',
    chans.popVal _ _ name = some (val, chans') ∧
    chans'.getBuf _ _ name = [] ∧
    ∀ name', name' ≠ name → chans'.getBuf _ _ name' = chans.getBuf _ _ name'
:= sorry

theorem pop_singletons
  {chans : ChanMap χ V}
  {names : Vector χ n}
  (prop : χ → V → Prop)
  (hsingletons : ∀ name ∈ names, ∃ val, chans.IsSingleton _ _ name val ∧ prop name val)
  (hdisj : names.toList.Nodup) :
  ∃ vals chans',
    chans.popVals _ _ names = some (vals, chans') ∧
    List.Forall₂ prop names.toList vals.toList ∧
    (∀ name ∈ names, chans'.IsEmpty _ _ name) ∧
    (∀ name, name ∉ names → chans'.getBuf _ _ name = chans.getBuf _ _ name)
:= sorry

theorem sim_step_br
  {cond}
  (hnz : m > 0 ∧ n > 0)
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hbr : ec.expr = .cont (.br cond left right)) :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ hnz ec' pc' := by
  have ⟨
    heq_state,
    ⟨
      rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
      hatoms,
      hcomp_fn,
      hrest,
      hmerges,
      hcont,
      hlive_vars,
      hdefined_vars,
    ⟩,
  ⟩ := hsim
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont (.br cond left right) hbr
  simp [compileExpr] at hcurrent
  -- Deduce some facts from `hstep`
  cases hstep with
  | step_ret hexpr => simp [hbr] at hexpr
  | step_tail hexpr => simp [hbr] at hexpr
  | step_op hexpr => simp [hbr] at hexpr
  | step_br hexpr hcond =>
    rename_i condVal _ _ cond'
    simp [hbr] at hexpr
    have heq_cond' := hexpr.1
    subst heq_cond'
    -- Some abbreviations
    generalize hcondName :
      compileExpr.varName χ ec.pathConds cond = condName
    simp only [hcondName] at hcurrent
    simp only [compileExpr.varName] at hcondName
    generalize hleftConds : (true, condName) :: ec.pathConds = leftConds
    generalize hrightConds : (false, condName) :: ec.pathConds = rightConds
    simp only [hleftConds, hrightConds] at hcurrent
    generalize hcondValBool :
      Interp.asBool Op S condVal = condValBool
    generalize hleftComp :
      compileExpr Op χ V S hnz (ec.definedVars.erase cond) leftConds left = leftComp
    generalize hrightComp :
      compileExpr Op χ V S hnz (ec.definedVars.erase cond) rightConds right = rightComp
    simp only [hleftComp, hrightComp] at hcurrent
    -- Step 1: Pop `cond` and run the first `fork`.
    have hcondVal : pc.chans condName = [condVal]
    := by simp [hlive_vars, SimR.varsToChans, hcond, ← hcondName]
    have ⟨chans₁, hpop_condVal⟩ :
      ∃ chans₁, pc.chans.popVal _ _ condName = some (condVal, chans₁)
    := by simp [ChanMap.popVal, hlive_vars, SimR.varsToChans, hcond, ← hcondName]
    have hmem_fork :
      .fork condName #v[.switch_cond condName, .merge_cond condName] ∈ pc.proc.atoms
    := by grind
    generalize hpc₁ :
      { pc with
        chans := .pushVals _ _
          #v[.switch_cond condName, .merge_cond condName]
          (Vector.replicate 2 condVal)
          chans₁,
        : Dataflow.Config _ _ _ _ _ _ } = pc₁
    have hstep₁ :
      Dataflow.Config.Step _ _ _ _ pc pc₁
    := by
      apply step_eq
      apply Dataflow.Config.Step.step_fork hmem_fork hpop_condVal
      simp [← hpc₁]
    -- Step 2: Run the switch
    have hmem_switch :
      .switch (.switch_cond condName)
        (compileExpr.allVars χ ec.definedVars ec.pathConds)
        (compileExpr.allVars χ ec.definedVars leftConds)
        (compileExpr.allVars χ ec.definedVars rightConds)
      ∈ pc₁.proc.atoms
    := by grind
    have ⟨chans₂, hchans₂⟩ :
      ∃ chans₂, pc₁.chans.popVal _ _ (.switch_cond condName) = some (condVal, chans₂)
    := sorry
    have ⟨inputVals, chans₃, hchans₃⟩ :
      ∃ inputVals chans₃,
        chans₂.popVals _ _
          (compileExpr.allVars χ ec.definedVars ec.pathConds) =
          some (inputVals, chans₃)
    := sorry
    generalize hpc₂ :
      { pc with
        chans :=
          if condValBool then
            ChanMap.pushVals (ChanName χ) V
              (compileExpr.allVars χ ec.definedVars leftConds)
              inputVals chans₃
          else
            ChanMap.pushVals (ChanName χ) V
              (compileExpr.allVars χ ec.definedVars rightConds)
              inputVals chans₃
      } = pc₂
    have hstep₂ :
      Dataflow.Config.Step _ _ _ _ pc₁ pc₂
    := by
      apply step_eq
      apply Dataflow.Config.Step.step_switch hmem_switch hchans₂ hchans₃
      simp [← hpc₁, ← hpc₂, ← hcondValBool]
    -- Prove the preservation of invariants
    have hsteps : Dataflow.Config.StepPlus _ _ _ _ pc pc₂
    := by
      apply Relation.TransGen.trans
      apply Relation.TransGen.single hstep₁
      apply Relation.TransGen.single hstep₂
    exists pc₂
    simp only [hsteps, true_and]
    and_intros
    · simp [← hpc₂, heq_state]
    · exists rest, carryInLoop
      exists -- ctxLeft
        if condValBool then
          ctxLeft ++ [
            .fork condName #v[.switch_cond condName, .merge_cond condName],
            .switch (.switch_cond condName)
              (compileExpr.allVars χ ec.definedVars ec.pathConds)
              (compileExpr.allVars χ ec.definedVars leftConds)
              (compileExpr.allVars χ ec.definedVars rightConds)
          ]
        else
          ctxLeft ++ [
            .fork condName #v[.switch_cond condName, .merge_cond condName],
            .switch (.switch_cond condName)
              (compileExpr.allVars χ ec.definedVars ec.pathConds)
              (compileExpr.allVars χ ec.definedVars leftConds)
              (compileExpr.allVars χ ec.definedVars rightConds)
          ] ++ compileExpr Op χ V S hnz (ec.definedVars.erase cond) leftConds left
      exists -- ctxCurrent
        if condValBool then leftComp else rightComp
      exists -- ctxRight
        if condValBool then
          rightComp ++ [compileExpr.brMerge Op χ V m n condName ec.pathConds] ++ ctxRight
        else
          [compileExpr.brMerge Op χ V m n condName ec.pathConds] ++ ctxRight
      and_intros
      · grind
      · grind
      · grind
      · sorry
      · sorry
      · sorry
      · sorry

end Wavelet.Simulation
