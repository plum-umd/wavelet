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

namespace Wavelet.Simulation.Op

open Wavelet.Op Wavelet.Seq Wavelet.Dataflow Wavelet.Compile
open Relation Lemmas

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

/-- Proves that the correspondence between `definedVars` and `ec.vars`
is preserved after execution of an operator. -/
theorem sim_step_op_defined_vars
  {definedVars args : List χ}
  {map : VarMap χ V}
  (hrets_disj : definedVars.Disjoint rets.toList)
  (hdefined_vars : ∀ var, var ∈ definedVars ↔ ∃ val, map.getVar χ V var = some val) :
  var ∈ definedVars.removeAll args ∨ var ∈ rets ↔
  ∃ val,
    ((map.removeVars χ V args).insertVars χ V rets outputVals).getVar χ V var =
      some val
:= by
  constructor
  · intros h₁
    rcases h₁ with h₂ | h₂
    · have ⟨h₃, h₄⟩ := List.mem_filter.mp h₂
      simp at h₄
      have ⟨val, hval⟩ := (hdefined_vars var).mp h₃
      exists val
      simp [VarMap.getVar, VarMap.removeVars, VarMap.insertVars] at hval ⊢
      right
      and_intros
      · intros v _ h₅ h₆
        simp only [Vector.zip_eq_zipWith] at h₅
        have := Vector.mem_toList_iff.mpr h₅
        simp only [Vector.toList_zipWith] at this
        have := List.of_mem_zip this
        subst h₆
        simp [hrets_disj h₃ this.1]
      · exact h₄
      · exact hval
    · simp [VarMap.getVar, VarMap.removeVars, VarMap.insertVars]
      suffices h : (List.find?
        (λ x => decide (x.fst = var))
        (rets.zip outputVals).toList).isSome by
        replace ⟨v, h⟩ := Option.isSome_iff_exists.mp h
        exists v.2
        left
        exists v.1
      simp
      exact Vector.mem_implies_mem_zip_left h₂
  · intros h₁
    replace ⟨val, h₁⟩ := h₁
    simp [VarMap.getVar, VarMap.removeVars, VarMap.insertVars] at h₁
    rcases h₁ with h₂ | h₂
    · have ⟨_, h₃⟩ := h₂
      have := List.mem_of_find?_eq_some h₃
      simp [Vector.zip_eq_zipWith, Vector.toList_zipWith] at this
      have h₄ := List.of_mem_zip this
      have h₅ := List.find?_some h₃
      simp at h₅
      replace h₅ := h₅.symm
      subst h₅
      simp at h₄
      simp [h₄.1]
    · left
      have ⟨_, h₃, h₄⟩ := h₂
      have := (hdefined_vars var).mpr ⟨_, h₄⟩
      apply List.mem_filter.mpr
      simp [this, h₃]

theorem var_map_insert_vars_disj
  {map : VarMap χ V}
  (hnot_mem : var ∉ vars) :
  (map.insertVars χ V vars vals).getVar χ V var
  = map.getVar χ V var
:= by
  simp [VarMap.getVar, VarMap.insertVars]
  suffices h :
    List.find? (fun x => decide (x.fst = var)) (vars.zip vals).toList = none
    by simp [h]
  simp
  intros a b h h'
  have := Vector.of_mem_zip h
  simp [h'] at this
  simp [hnot_mem this.1]

theorem var_map_remove_vars_disj
  {map : VarMap χ V}
  (hnot_mem : var ∉ vars) :
  (map.removeVars χ V vars).getVar χ V var
  = map.getVar χ V var
:= by
  simp [VarMap.getVar, VarMap.removeVars]
  intros h
  exfalso
  exact hnot_mem h

theorem sim_step_op
  (hnz : m > 0 ∧ n > 0)
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hop : ec.expr = .cont (.op o args rets cont)) :
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
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hop
  simp [compileExpr] at hcurrent
  -- Deduce some facts from `hstep` and `hwf_expr`
  cases hstep with
  | step_ret hexpr | step_tail hexpr | step_br hexpr =>
    simp [hop] at hexpr
  | step_op hexpr hargs hinterp =>
    rename_i o' inputVals outputVals state' args' rets' cont'
    simp [hop] at hexpr
    have ⟨h₁, h₂, h₃, h₄⟩ := hexpr
    subst h₁; subst h₂; subst h₃; subst h₄
    clear hexpr
    cases hwf_expr with
    | wf_op hargs_nodup hrets_nodup hrets_disj hargs_subset hwf_cont =>
    -- Step 1: Pop inputs of `o` and run `o`
    have ⟨chans₁, inputVals', hpop_input_vals, hchans₁, hinput_vals⟩ :=
      pop_vals_singleton _ _
      (map := pc.chans)
      (names := compileExpr.varNames χ ec.pathConds args)
      (λ name val =>
        match name with
        | .var v _ => ec.vars.getVar _ _ v = some val
        | _ => False)
      (vars_nodup_to_var_names_nodup hargs_nodup)
      (by
        intros name hname
        simp [compileExpr.varNames, compileExpr.varName] at hname
        replace ⟨var, hmem_var, hname⟩ := hname
        replace hmem_var := Vector.mem_toList_iff.mpr hmem_var
        have := hargs_subset hmem_var
        have ⟨_, h⟩ := (hdefined_vars var).mp this
        simp [hlive_vars, SimR.varsToChans, ← hname, h])
    have : inputVals = inputVals' := by
      symm
      apply Vector.toList_inj.mp
      apply List.right_unique_forall₂' _ hinput_vals
      · simp [compileExpr.varNames, Vector.toList_map, compileExpr.varName]
        exact List.mapM_some_iff_forall₂.mp (Vector.mapM_toList hargs)
      · simp [Relator.RightUnique]
        intros a b c hb hc
        split at hb <;> rename_i h
        · simp [hb] at hc
          simp [hc]
        · contradiction
    subst this; clear hinput_vals
    have hmem_op :
      .op o
        (compileExpr.varNames χ ec.pathConds args)
        (compileExpr.varNames χ ec.pathConds rets)
      ∈ pc.proc.atoms
    := by grind
    simp [heq_state] at hinterp
    have hsteps : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.single
        (Dataflow.Config.Step.step_op hmem_op hpop_input_vals hinterp)
    -- Simplify pushes
    rw [push_vals_empty] at hsteps
    rotate_left
    · exact vars_nodup_to_var_names_nodup hrets_nodup
    · intros name hname
      simp [hchans₁]
      intros hname₂
      simp [compileExpr.varNames, compileExpr.varName] at hname
      replace ⟨var, hvar, hname⟩ := hname
      simp [← hname, hlive_vars, SimR.varsToChans]
      have : var ∉ ec.definedVars := List.disjoint_right.mp hrets_disj
        (Vector.mem_toList_iff.mpr hvar)
      split <;> rename_i h
      · have h' := (hdefined_vars var).mpr ⟨_, h⟩
        simp [this h']
      · rfl
    replace ⟨pc', hpc', hsteps⟩ := exists_eq_left.mpr hsteps
    -- Prove simulation invariants
    exists pc'
    constructor
    · exact hsteps
    · and_intros
      · simp [hpc']
      · funext name
        simp [hpc', SimR.varsToChans, hchans₁]
        cases name with
        | var var pathConds =>
          simp
          split <;> rename_i h₁
          · rename_i i
            simp [compileExpr.varNames, compileExpr.varName, Vector.get] at h₁
            have ⟨⟨hvar, h₂⟩, h₃⟩ := h₁
            simp [h₂, VarMap.getVar, VarMap.removeVars, VarMap.insertVars]
            have :
              (List.find? (fun x => decide (x.fst = var)) (rets.zip outputVals).toList)
              = some (var, outputVals[i])
              := by
              apply List.find?_eq_some_iff_append.mpr
              and_intros
              · simp
              · exists
                  (rets.zip outputVals).toList.take i,
                  (rets.zip outputVals).toList.drop (i + 1)
                and_intros
                · have : (var, outputVals[i]) = (rets.zip outputVals)[i] := by simp [hvar]
                  simp only [this]
                  apply List.to_append_cons
                · intros x hmem_x
                  simp
                  have ⟨j, hj, hmem_x'⟩ := List.mem_iff_getElem.mp hmem_x
                  simp at hmem_x' hj
                  simp [← hmem_x']
                  intros h
                  simp only [← h] at hvar
                  have := (List.Nodup.getElem_inj_iff hrets_nodup).mp hvar
                  simp at this
                  omega
            simp [this]
          · have := Option.eq_none_iff_forall_ne_some.mpr h₁
            simp at this
            simp [compileExpr.varNames, compileExpr.varName] at this
            split <;> rename_i h₂
            · simp [compileExpr.varNames, compileExpr.varName] at h₂
              simp [h₂.2]
              simp [h₂.1, VarMap.getVar, VarMap.removeVars, VarMap.insertVars]
              split <;> rename_i h₃
              · simp at h₃
                replace ⟨_, h₃⟩ := h₃
                -- replace h₃ := Option.isSome_iff_exists.mpr ⟨_, h₃⟩
                have h₄ := List.find?_some h₃
                have h₅ := List.mem_of_find?_eq_some h₃
                simp at h₄ h₅
                replace h₅ := Vector.of_mem_zip h₅
                simp only [h₄] at h₅
                simp [this h₅.1 h₂.2]
              · rfl
            · simp [compileExpr.varNames, compileExpr.varName] at h₂
              split <;> rename_i h₃
              · simp [hlive_vars, SimR.varsToChans, h₃]
                have : var ∉ rets := by
                  intros h
                  exact this h h₃.symm
                simp [var_map_insert_vars_disj _ _ this]
                have : var ∉ args.toList := by
                  intros h
                  replace h := Vector.mem_toList_iff.mp h
                  exact h₂ h h₃.symm
                simp [var_map_remove_vars_disj _ _ this]
              · simp [hlive_vars, SimR.varsToChans, h₃]
        | _ =>
          simp [compileExpr.varNames, compileExpr.varName, hlive_vars, SimR.varsToChans, hop]
      · simp
        apply List.Nodup.append
        · apply List.Nodup.filter
          exact hdefined_vars_no_dup
        · exact hrets_nodup
        · apply List.disjoint_implies_filter_disjoint_left hrets_disj
      · simp
        intros var
        apply sim_step_op_defined_vars
        · exact hrets_disj
        · exact hdefined_vars
      · grind
      · exact hpath_conds_nodup
      · simp [hpc', hmerges]
      · exact hwf_fn.1
      · exact hwf_fn.2
      · exists rest, carryInLoop
        -- ctxLeft
        exists
          ctxLeft ++ [
            .op o
              (compileExpr.varNames χ ec.pathConds args)
              (compileExpr.varNames χ ec.pathConds rets)
          ]
        -- ctxCurrent
        exists
          compileExpr Op χ V S hnz (ec.definedVars.removeAll args.toList ++ rets.toList) ec.pathConds cont
        -- ctxRight
        exists ctxRight
        grind

end Wavelet.Simulation.Op
