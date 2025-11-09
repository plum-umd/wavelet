import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Batteries.Data.Vector.Lemmas

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Fn.Simulation.Invariants
import Wavelet.Compile.Fn.Lemmas

/-! Simulation in the case of branching. -/

namespace Wavelet.Compile.Fn

open Semantics Seq Dataflow Compile Fn

/-- Helper lemma to run relevant dataflow operators. -/
private theorem sim_step_br_exec_dataflow
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {cond left right}
  {ec : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hbr : ec.cont = .expr (.br cond left right))
  (hcond : ec.vars.getVar cond = some condVal)
  (hcondBool : InterpConsts.toBool condVal = some condBool) :
  Dataflow.Config.Step.WeakStep .τ pc .τ {
    proc := pc.proc,
    chans := varsToChans (gs.useThenBranch cond condBool) { ec with
      cont := .expr (if condBool then left else right),
      vars := ec.vars.removeVar cond
    },
  } := by
  -- Unpack compiled processes
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hbr
  simp only [compileExpr] at hcurrent
  cases hwf_expr with | wf_br hwf_left hwf_right =>
  -- Some abbreviations
  generalize hleft_conds : (true, .var cond gs.pathConds) :: gs.pathConds = leftConds
  generalize hright_conds : (false, .var cond gs.pathConds) :: gs.pathConds = rightConds
  simp only [hleft_conds, hright_conds] at hcurrent
  -- Step 1: Pop `cond` and fire the first `fork`.
  have ⟨chans₁, hpop_cond, hchans₁⟩ := pop_val_singleton
    (map := pc.chans)
    (name := .var cond gs.pathConds)
    (val := condVal)
    (by simp [hsim.vars_to_chans, varsToChans, hcond])
  have hmem_fork :
    .fork
      (.var cond gs.pathConds)
      #v[
        .switch_cond (.var cond gs.pathConds),
        .merge_cond (.var cond gs.pathConds),
      ] ∈ pc.proc.atoms
    := by simp [hatoms, hrest, ← hcurrent]
  have hsteps₁ : Dataflow.Config.Step.WeakStep .τ pc .τ _
    := .single (Dataflow.Config.Step.step_fork hmem_fork hpop_cond)
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₁
  rotate_left
  · simp
  · simp [hchans₁, hsim.vars_to_chans, varsToChans, hsim.path_conds_acyclic]
  replace ⟨pc₁, hpc₁, hsteps₁⟩ := exists_eq_left.mpr hsteps₁
  -- Step 2: Pop `switch_cond` and all live variable, and fire the `switch` operator
  have ⟨chans₂, hpop_switch_cond, hchans₂⟩ := pop_val_singleton
    (map := pc₁.chans)
    (val := condVal)
    (name := .switch_cond (.var cond gs.pathConds))
    (by simp [hpc₁, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have ⟨chans₃, allVals, hpop_all_vals, hchans₃, hall_vals⟩ :=
    pop_vals_singleton
    (map := chans₂)
    (names := compileExpr.allVarsExcept gs.definedVars [cond] gs.pathConds)
    (λ name val =>
      ∃ var,
        name = .var var gs.pathConds ∧
        ec.vars.getVar var = some val)
    (allVarsExcept_nodup hsim.defined_vars_nodup)
    (by
      intros name hname
      have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept hname
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnot_mem_var
      simp only [List.removeAll, compileExpr.allVarsExcept, Vector.mem_map] at hname
      have ⟨_, h⟩ := hsim.defined_vars_to_get_var hmem_var
      simp [h, hchans₁, hchans₂, hpc₁, hvar, hnot_mem_var, hsim.vars_to_chans,
        varsToChans, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have hchans₃_no_var {var pathConds} : chans₃ (.var var pathConds) = []
  := by
    simp [hchans₃, hchans₂, hchans₁, hpc₁, hsim.vars_to_chans,
      varsToChans, VarMap.getVar, compileExpr.allVarsExcept, List.toVector,
      List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
    intros h₁ h₂ h₃
    split
    · rename_i h₄
      have := hsim.get_var_to_defined_vars ⟨_, h₄⟩
      if h₅ : var = cond then
        simp [h₂ h₅ h₃]
      else
        simp [h₁ (List.mem_filter.mpr ⟨this, by simp [h₅]⟩) h₃.symm]
    · rfl
  have hmem_switch :
    AtomicProc.switch (.switch_cond (.var cond gs.pathConds))
      (compileExpr.allVarsExcept gs.definedVars [cond] gs.pathConds)
      (compileExpr.allVarsExcept gs.definedVars [cond] leftConds)
      (compileExpr.allVarsExcept gs.definedVars [cond] rightConds)
    ∈ pc₁.proc.atoms
  := by simp [hpc₁, hatoms, hrest, ← hcurrent, compileExpr.allVarsExcept]
  have hsteps₂ : Dataflow.Config.Step.WeakStep .τ pc .τ _
    := .tail_tau hsteps₁
        (Dataflow.Config.Step.step_switch
          hmem_switch
          hpop_switch_cond
          hpop_all_vals
          hcondBool
          (decider := .switch_cond (.var cond gs.pathConds))
          (inputs := compileExpr.allVarsExcept gs.definedVars [cond] gs.pathConds)
          (outputs₁ := compileExpr.allVarsExcept gs.definedVars [cond] leftConds)
          (outputs₂ := compileExpr.allVarsExcept gs.definedVars [cond] rightConds))
  simp only at hsteps₂
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₂
  rotate_left
  · split <;> apply allVarsExcept_nodup hsim.defined_vars_nodup
  · split
    all_goals
      intros name hname
      simp only [compileExpr.allVarsExcept, Vector.mem_map] at hname
      replace ⟨var, hvar, hname⟩ := hname
      simp only [List.toVector, Vector.mem_mk, List.mem_toArray] at hvar
      simp [hchans₁, hchans₂, hchans₃, hpc₁, ← hname,
        compileExpr.allVarsExcept, List.toVector,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        hsim.vars_to_chans, varsToChans]
      intros h₁ _ h₂
      exact False.elim (h₁ hvar h₂.symm)
  have :
    (if condBool = true then
      compileExpr.allVarsExcept gs.definedVars [cond] leftConds
    else
      compileExpr.allVarsExcept gs.definedVars [cond] rightConds)
    = compileExpr.allVarsExcept gs.definedVars [cond]
      ((condBool, ChanName.var cond gs.pathConds) :: gs.pathConds)
  := by
    simp only [← hleft_conds, ← hright_conds, compileExpr.allVarsExcept]
    cases condBool <;> simp
  rw [this] at hsteps₂; clear this
  apply hsteps₂.eq_rhs
  simp [hpc₁]
  funext name
  simp only [varsToChans]
  cases name with
  | var v pathConds =>
    simp
    if h₁ : v = cond then
      rw [allVarsExcept_finIdxOf?_none_if_removed (by simp [h₁])]
      simp [h₁, VarMap.getVar, VarMap.removeVar, hchans₃, hchans₂, hpc₁, hchans₁,
        hsim.vars_to_chans, varsToChans,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
      intros _ h₂ h₃
      exact False.elim (h₂ h₃)
    else
      if h₂ : v ∈ gs.definedVars then
        if h₃ : pathConds = (condBool, ChanName.var cond gs.pathConds) :: gs.pathConds then
          have ⟨i, h₄⟩ := allVarsExcept_finIdxOf?_some (removedVars := [cond])
            h₂ (by simp [h₁]) h₃
          simp [h₄]
          simp [compileExpr.allVarsExcept] at h₄
          simp [List.toVector] at h₄
          simp [h₄.1.2, Ne.symm h₁, VarMap.getVar, VarMap.removeVar]
          have ⟨_, h₅⟩ := hsim.defined_vars_to_get_var h₂
          simp only [VarMap.getVar] at h₅
          have := List.forall₂_iff_get.mp hall_vals
          have := this.2 i (by simp) (by simp)
          simp [List.toVector, VarMap.getVar, compileExpr.allVarsExcept, h₄.1.1] at this
          simp [this]
        else
          rw [allVarsExcept_finIdxOf?_none_if_diff_path_conds (by simp [Ne.symm h₃])]
          simp [hchans₃_no_var, h₃]
      else
        rw [allVarsExcept_finIdxOf?_none_if_not_defined (by simp [h₂])]
        simp [hchans₃_no_var]
        split
        · rename_i h₃
          simp [VarMap.getVar, VarMap.removeVar] at h₃
          have := hsim.get_var_to_defined_vars ⟨_, h₃.2⟩
          simp [h₂ this]
        · simp
  | merge_cond name =>
    simp [hchans₃, hchans₂, hpc₁, hchans₁,
      compileExpr.allVarsExcept, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
    if h₁ : .var cond gs.pathConds = name then
      simp [h₁]
      simp [Eq.symm h₁]
      have := InterpConsts.unique_toBool_fromBool _ _ hcondBool
      simp [this, hsim.path_conds_acyclic]
      split <;> (rename_i h₂; simp [h₂])
    else
      cases condBool
      all_goals
      simp [h₁]
      simp [Ne.symm h₁, hsim.vars_to_chans, varsToChans]
  | switch_cond name =>
    cases condBool
    all_goals
      simp [compileExpr.allVarsExcept, hchans₃, hchans₂, hpc₁, hchans₁]
      intro h
      simp [Ne.symm h, hsim.vars_to_chans, varsToChans,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
  | _ =>
    cases condBool
    all_goals
      simp [compileExpr.allVarsExcept, hchans₃, hchans₂, hchans₁, hpc₁]
      try rw [(Vector.finIdxOf?_eq_none_iff).mpr _]
      simp [hsim.vars_to_chans, varsToChans,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]

theorem sim_step_br
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {cond left right}
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hbr : ec.cont = .expr (.br cond left right)) :
  ∃ pc',
    Config.Step.IORestrictedStep pc l pc' ∧
    ∃ gs', SimRel gs' ec' pc' := by
  -- Deduce some facts from `hstep`
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hbr
  cases hstep with
  | step_init hexpr | step_ret hexpr | step_tail hexpr
  | step_op hexpr => simp [hbr] at hexpr
  | step_br hexpr hcond hcondBool =>
    rename_i condVal condBool _ _ cond'
    simp only [hbr, Cont.expr.injEq, Expr.br.injEq] at hexpr
    have h := hexpr.1; subst h
    have h := hexpr.2.1; subst h
    have h := hexpr.2.2; subst h
    clear hexpr
    cases hwf_expr with | wf_br hwf_left hwf_right =>
    have hsteps := sim_step_br_exec_dataflow hsim hbr hcond hcondBool
    exact ⟨_, .step_tau hsteps.to_tau_star,
      gs.useThenBranch cond condBool,
      by
        and_intros
        · simp
        · exact List.Nodup.filter _ hsim.defined_vars_nodup
        · simp; grind [VarMap.removeVar, VarMap.getVar]
        · simp; grind
        · simp; grind
        · simp
          grind [compileExpr]
        · simp only [hsim.has_merges]
        · exact hsim.wf_fn.1
        · exact hsim.wf_fn.2
        · exact hsim.inputs
        · exact hsim.outputs
        · simp [HasCompiledProcs]
          grind [compileExpr]
    ⟩

end Wavelet.Compile.Fn
