import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Batteries.Data.Vector.Lemmas

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Lemmas

import Wavelet.Simulation.Relation
import Wavelet.Simulation.Lemmas

namespace Wavelet.Simulation.Br

open Wavelet.Op Wavelet.Seq Wavelet.Dataflow Wavelet.Compile
open Relation Lemmas

theorem sim_step_br
  [Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]
  {cond left right}
  {ec ec' : Seq.Config Op χ V S m n}
  {pc : Dataflow.Config Op (ChanName χ) V S m n}
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hbr : ec.expr = .cont (.br cond left right)) :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ hnz ec' pc' := by
  have ⟨
    heq_state,
    hlive_vars,
    hdefined_vars_no_dup,
    hdefined_vars,
    hpath_conds_order,
    hpath_conds_nodup,
    hmerges,
    hwf_fn,
    ⟨
      rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
      hatoms,
      hcomp_fn,
      hrest,
      hret,
      hcont,
    ⟩,
  ⟩ := hsim
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hbr
  simp only [compileExpr] at hcurrent
  -- Deduce some facts from `hstep`
  cases hstep with
  | step_ret hexpr | step_tail hexpr | step_op hexpr =>
    simp [hbr] at hexpr
  | step_br hexpr hcond hcondBool =>
    rename_i condVal condBool _ _ cond'
    simp only [hbr, ExprResult.cont.injEq, Expr.br.injEq] at hexpr
    have heq_cond' := hexpr.1; subst heq_cond'
    have heq_left' := hexpr.2.1; subst heq_left'
    have heq_right' := hexpr.2.2; subst heq_right'
    clear hexpr
    cases hwf_expr with | wf_br hwf_left hwf_right =>
    -- Some abbreviations
    generalize hcondName :
      compileExpr.varName χ ec.pathConds cond = condName
    simp only [hcondName] at hcurrent
    simp only [compileExpr.varName] at hcondName
    generalize hleftConds : (true, condName) :: ec.pathConds = leftConds
    generalize hrightConds : (false, condName) :: ec.pathConds = rightConds
    simp only [hleftConds, hrightConds] at hcurrent
    generalize hleftComp :
      compileExpr Op χ V S hnz (ec.definedVars.removeAll [cond]) leftConds left = leftComp
    generalize hrightComp :
      compileExpr Op χ V S hnz (ec.definedVars.removeAll [cond]) rightConds right = rightComp
    simp only [hleftComp, hrightComp] at hcurrent
    -- Step 1: Pop `cond` and fire the first `fork`.
    have hcondVal : pc.chans condName = [condVal]
      := by simp [hlive_vars, SimR.varsToChans, hcond, ← hcondName]
    have ⟨chans₁, hpop_cond, hchans₁⟩ := pop_val_singleton _ _
      (map := pc.chans)
      (name := condName)
      (val := condVal)
      (by simp [hlive_vars, SimR.varsToChans, hcond, ← hcondName])
    have hmem_fork :
      .fork condName #v[.switch_cond condName, .merge_cond condName] ∈ pc.proc.atoms
      := by simp [hatoms, hrest, ← hcurrent]
    have hsteps₁ : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.single (Dataflow.Config.Step.step_fork hmem_fork hpop_cond)
    -- Simplify pushes
    rw [push_vals_empty] at hsteps₁
    rotate_left
    · simp
    · simp [hchans₁, ← hcondName, hlive_vars, SimR.varsToChans,
        path_conds_acyclic hpath_conds_order]
    replace ⟨pc₁, hpc₁, hsteps₁⟩ := exists_eq_left.mpr hsteps₁
    -- Step 2: Pop `switch_cond` and all live variable, and fire the `switch` operator
    have ⟨chans₂, hpop_switch_cond, hchans₂⟩ := pop_val_singleton _ _
      (map := pc₁.chans)
      (val := condVal)
      (name := .switch_cond condName)
      (by simp [hpc₁, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
    have ⟨chans₃, allVals, hpop_all_vals, hchans₃, hall_vals⟩ :=
      pop_vals_singleton _ _
      (map := chans₂)
      (names := compileExpr.allVarsExcept χ ec.definedVars [cond] ec.pathConds)
      (λ name val =>
        ∃ var,
          name = .var var ec.pathConds ∧
          ec.vars.getVar _ _ var = some val)
      (allVarsExcept_nodup hdefined_vars_no_dup)
      (by
        intros name hname
        have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept hname
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hnot_mem_var
        simp only [List.removeAll, compileExpr.allVarsExcept, Vector.mem_map] at hname
        have ⟨_, h⟩ := (hdefined_vars var).mp hmem_var
        simp [h, hchans₁, hchans₂, hpc₁, hvar, hnot_mem_var, ← hcondName, hlive_vars,
          SimR.varsToChans, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
    have hchans₃_no_var {var pathConds} : chans₃ (.var var pathConds) = []
    := by
      simp [hchans₃, hchans₂, hchans₁, hpc₁, hlive_vars, ← hcondName,
        SimR.varsToChans, VarMap.getVar, compileExpr.allVarsExcept, List.toVector,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
      intros h₁ h₂ h₃
      split
      · rename_i h₄
        have := (hdefined_vars var).mpr ⟨_, h₄⟩
        if h₅ : var = cond then
          simp [h₂ h₅ h₃]
        else
          simp [h₁ (List.mem_filter.mpr ⟨this, by simp [h₅]⟩) h₃.symm]
      · rfl
    have hsteps₂ : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.tail hsteps₁
          (Dataflow.Config.Step.step_switch
            (by simp [hpc₁, hatoms, hrest, ← hcurrent])
            hpop_switch_cond
            hpop_all_vals
            hcondBool
            (decider := .switch_cond condName)
            (inputs := compileExpr.allVarsExcept χ ec.definedVars [cond] ec.pathConds)
            (outputs₁ := compileExpr.allVarsExcept χ ec.definedVars [cond] leftConds)
            (outputs₂ := compileExpr.allVarsExcept χ ec.definedVars [cond] rightConds))
    simp only at hsteps₂
    -- Simplify pushes
    rw [push_vals_empty] at hsteps₂
    rotate_left
    · split <;> apply allVarsExcept_nodup hdefined_vars_no_dup
    · split
      all_goals
        intros name hname
        simp only [compileExpr.allVarsExcept, Vector.mem_map] at hname
        replace ⟨var, hvar, hname⟩ := hname
        simp only [List.toVector, Vector.mem_mk, Array.mem_toArray] at hvar
        simp [hchans₁, hchans₂, hchans₃, hpc₁, ← hname,
          compileExpr.allVarsExcept, List.toVector,
          List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
          hlive_vars, SimR.varsToChans]
        intros h₁ _ h₂
        exact False.elim (h₁ hvar h₂.symm)
    have :
      (if condBool = true then
        compileExpr.allVarsExcept χ ec.definedVars [cond] leftConds
      else
        compileExpr.allVarsExcept χ ec.definedVars [cond] rightConds)
      = compileExpr.allVarsExcept χ ec.definedVars [cond]
        ((condBool, ChanName.var cond ec.pathConds) :: ec.pathConds)
    := by
      simp only [← hleftConds, ← hrightConds, ← hcondName]
      cases condBool <;> simp
    rw [this] at hsteps₂; clear this
    replace ⟨pc', hpc', hsteps₂⟩ := exists_eq_left.mpr hsteps₂
    -- Prove simulation
    exists pc'
    constructor
    · exact hsteps₂
    · simp only [hpc', hpc₁]
      and_intros
      · simp [heq_state]
      · funext name
        simp only [SimR.varsToChans]
        cases name with
        | var v pathConds =>
          simp
          if h₁ : v = cond then
            rw [allVarsExcept_finIdxOf?_none_if_removed (by simp [h₁])]
            simp [h₁, VarMap.getVar, VarMap.removeVar, hchans₃, hchans₂, hpc₁, hchans₁,
              hlive_vars, SimR.varsToChans, ← hcondName,
              List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
            intros _ h₂ h₃
            exact False.elim (h₂ h₃)
          else
            if h₂ : v ∈ ec.definedVars then
              if h₃ : pathConds = (condBool, ChanName.var cond ec.pathConds) :: ec.pathConds then
                have ⟨i, h₄⟩ := allVarsExcept_finIdxOf?_some (removedVars := [cond])
                  h₂ (by simp [h₁]) h₃
                simp [h₄]
                simp [compileExpr.allVarsExcept] at h₄
                simp [List.toVector] at h₄
                simp [h₄.1.2, Ne.symm h₁, VarMap.getVar, VarMap.removeVar]
                have ⟨_, h₅⟩ := (hdefined_vars v).mp h₂
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
                have := (hdefined_vars v).mpr ⟨_, h₃.2⟩
                simp [h₂ this]
              · simp
        | merge_cond name =>
          simp [hchans₃, hchans₂, hpc₁, hchans₁,
            compileExpr.allVarsExcept, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
          if h₁ : condName = name then
            simp [h₁]
            simp [hcondName, Eq.symm h₁]
            have := instInterp.unique_toBool_fromBool _ _ hcondBool
            if h₂ : condBool then
              simp [h₂] at this ⊢
              exact this
            else
              simp [h₂] at this ⊢
              split
              · rename_i h
                simp only [← hcondName] at h
                have := hpath_conds_order _ _ _ h
                omega
              · simp [this]
          else
            cases condBool
            all_goals
            simp [h₁]
            simp [hcondName, Ne.symm h₁]
            simp [← hcondName, hlive_vars, SimR.varsToChans]
        | switch_cond name =>
          cases condBool
          all_goals
            simp [compileExpr.allVarsExcept, hchans₃, hchans₂, hpc₁, hchans₁]
            intro h
            simp [Ne.symm h, hlive_vars, SimR.varsToChans,
              List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
        | _ =>
          cases condBool
          all_goals
            simp [compileExpr.allVarsExcept, hchans₃, hchans₂, hchans₁, hpc₁]
            try rw [(Vector.finIdxOf?_eq_none_iff).mpr _]
            simp [← hcondName, hlive_vars, hbr, SimR.varsToChans,
              List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go]
      · exact List.Nodup.filter _ hdefined_vars_no_dup
      · simp; grind [VarMap.getVar, VarMap.removeVar]
      · simp; grind [SimR.OrderedPathConds]
      · simp; grind [SimR.OrderedPathConds]
      · simp; grind
      · simp only [hmerges]
      · exact hwf_fn.1
      · exact hwf_fn.2
      · simp
        exists rest
        simp only [hatoms, hcarryInLoop, hrest, List.append_assoc, hcomp_fn, true_and]
        constructor
        · exists -- ctxLeft
            ctxLeft ++ if condBool then
              [
                .fork condName #v[.switch_cond condName, .merge_cond condName],
                .switch (.switch_cond condName)
                  (compileExpr.allVarsExcept χ ec.definedVars [cond] ec.pathConds)
                  (compileExpr.allVarsExcept χ ec.definedVars [cond] leftConds)
                  (compileExpr.allVarsExcept χ ec.definedVars [cond] rightConds)
              ]
            else
              [
                .fork condName #v[.switch_cond condName, .merge_cond condName],
                .switch (.switch_cond condName)
                  (compileExpr.allVarsExcept χ ec.definedVars [cond] ec.pathConds)
                  (compileExpr.allVarsExcept χ ec.definedVars [cond] leftConds)
                  (compileExpr.allVarsExcept χ ec.definedVars [cond] rightConds)
              ] ++ leftComp
          exists -- ctxRight
            if condBool then
              rightComp ++ [compileExpr.brMerge Op χ V m n condName ec.pathConds] ++ ctxRight
            else
              [compileExpr.brMerge Op χ V m n condName ec.pathConds] ++ ctxRight
          split <;> rename_i h
          · simp [h, ← hleftComp, ← hrightComp, ← hcurrent, ← hleftConds, ← hcondName]
          · simp [h, ← hleftComp, ← hrightComp, ← hcurrent, ← hrightConds, ← hcondName]
        · split
          · exact hwf_left
          · exact hwf_right

end Wavelet.Simulation.Br
