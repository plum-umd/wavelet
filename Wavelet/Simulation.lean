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

def SimR
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.state = pc.state ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    -- Some invariants about the form of the processes
    pc.proc.atoms = compileFn.initCarry _ _ _ ec.fn carryInLoop :: rest ∧
    (compileFn Op χ V S hnz ec.fn).atoms = compileFn.initCarry _ _ _ ec.fn false :: rest ∧
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    -- TODO: include this
    -- (∀ vals, ec.expr = .ret vals → ¬ carryInLoop ∧ ctxCurrent = [] ∧ ctxRight = []) ∧
    (∀ expr, ec.expr = .cont expr → carryInLoop ∧
      expr.WellFormed _ _ ec.definedVars ∧
      compileExpr Op χ V S hnz ec.definedVars ec.pathConds expr = ctxCurrent) ∧
    (∀ var val, ec.vars.getVar _ _ var = some val →
      pc.chans.IsSingleton _ _ (.var var ec.pathConds) val) ∧
    (∀ cond ∈ ec.pathConds, pc.chans.IsSingleton _ _ (.merge_cond cond.2) instInterp.trueVal) ∧
    (∀ i, (h : i < ec.pathConds.length) →
      compileExpr.brMerge _ _ _ m n (ec.pathConds[i]'h).2 (ec.pathConds.drop i) ∈ pc.proc.atoms) ∧
    (∀ var ∈ ec.definedVars, ∃ val, ec.vars.getVar _ _ var = some val) ∧
    (∀ name : ChanName χ, match name with
      | .var _ pathConds => pathConds ≠ ec.pathConds → pc.chans.IsEmpty _ _ name
      | .merge_cond v => (∀ cond ∈ ec.pathConds, v ≠ cond.2) → pc.chans.IsEmpty _ _ name
      | _ => pc.chans.IsEmpty _ _ name)

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
      hcont,
      hlive_vars,
      hpath_conds,
      hmerges,
      hdefined_vars,
      hempty_names,
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

    -- Pop `cond` and run the first `fork`
    have hcondVal : pc.chans.IsSingleton _ _ (.var cond ec.pathConds) condVal
      := hlive_vars cond condVal hcond
    have ⟨chans', hpop_condVal, hchans'⟩ := pop_singleton _ _ hcondVal
    have hmem_fork :
      .fork (compileExpr.varName χ ec.pathConds cond)
        #v[
          .switch_cond (compileExpr.varName χ ec.pathConds cond),
          .merge_cond (compileExpr.varName χ ec.pathConds cond),
        ]
      ∈ pc.proc.atoms
    := by grind
    generalize hpc₁ :
      { pc with
        chans :=
          .pushVals _ _
            #v[
              .switch_cond (compileExpr.varName χ ec.pathConds cond),
              (compileExpr.varName χ ec.pathConds cond).merge_cond,
            ]
            (Vector.replicate 2 condVal)
            chans',
        : Dataflow.Config _ _ _ _ _ _ } = pc₁
    have hstep₁ :
      Dataflow.Config.Step _ _ _ _ pc pc₁
    := by
      apply step_eq
      apply Dataflow.Config.Step.step_fork hmem_fork hpop_condVal
      simp [← hpc₁]

    -- Run the switch
    have hmem_switch :
      .switch
        (.switch_cond (compileExpr.varName χ ec.pathConds cond))
        (compileExpr.allVars χ ec.definedVars ec.pathConds)
        (compileExpr.allVars χ ec.definedVars
          ((true, compileExpr.varName χ ec.pathConds cond) :: ec.pathConds))
        (compileExpr.allVars χ ec.definedVars
          ((false, compileExpr.varName χ ec.pathConds cond) :: ec.pathConds))
      ∈ pc₁.proc.atoms
    := by grind
    have hcondVal₁ :
      pc₁.chans.IsSingleton _ _ (.switch_cond (compileExpr.varName χ ec.pathConds cond)) condVal
    := sorry
    have ⟨chans'', hpop_condVal₁, hchans''⟩ := pop_singleton _ _ hcondVal₁

    have hallVars_lookup :
      ∀ name ∈ compileExpr.allVars χ ec.definedVars ec.pathConds,
        ∃ val, chans''.IsSingleton _ _ name val ∧
          (∃ var, name = .var var ec.pathConds ∧ ec.vars var = some val)
    := sorry
    have hallVars_disj :
      (compileExpr.allVars χ ec.definedVars ec.pathConds).toList.Nodup
    := sorry -- from well-formedness

    have ⟨inputVals, chans''', hpop_inputVals, _⟩ := pop_singletons _ _ _ hallVars_lookup hallVars_disj

    generalize hpc₂ :
      { pc with
        chans :=
          if Interp.asBool Op S condVal = true then
            ChanMap.pushVals (ChanName χ) V
              (compileExpr.allVars χ ec.definedVars ((true, compileExpr.varName χ ec.pathConds cond) :: ec.pathConds))
              inputVals chans'''
          else
            ChanMap.pushVals (ChanName χ) V
              (compileExpr.allVars χ ec.definedVars ((false, compileExpr.varName χ ec.pathConds cond) :: ec.pathConds))
              inputVals chans'''
      } = pc₂
    have hstep₂ :
      Dataflow.Config.Step _ _ _ _ pc₁ pc₂
    := by
      apply step_eq
      apply Dataflow.Config.Step.step_switch hmem_switch hpop_condVal₁ hpop_inputVals
      simp [← hpc₁, ← hpc₂]

    -- have pc₁.IsSingleton _ _ (.var cond ec.pathConds) condVal
    -- := by
    --   simp [hpc₁]
    --   exact hchans' _ rfl

    -- have hmem_steer₂ :
    --   AtomicProc.steer false
    --     (compileExpr.varName χ ec.pathConds cond)
    --     (compileExpr.allVars χ ec.definedVars ec.pathConds)
    --     (compileExpr.allVars χ ec.definedVars ((false, compileExpr.varName χ ec.pathConds cond) :: ec.pathConds))
    --   ∈ pc.proc.atoms
    -- := by grind

    -- have :
    --   Dataflow.Config.Step _ _ _ _ pc
    --     { pc with

    --     }
    -- := sorry
    sorry

end Wavelet.Simulation
