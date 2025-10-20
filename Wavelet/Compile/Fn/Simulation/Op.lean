import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Batteries.Data.Vector.Lemmas

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Fn.Simulation.Invariants
import Wavelet.Compile.Fn.Lemmas

/-! Simulation in the case of operator yielding. -/

namespace Wavelet.Compile.Fn

open Semantics Seq Dataflow Compile Fn

/-- Proves that the correspondence between `definedVars` and `ec.vars`
is preserved after execution of an operator. -/
private theorem sim_step_op_defined_vars
  [DecidableEq χ]
  {definedVars args : List χ}
  {map : VarMap χ V}
  (hrets_disj : definedVars.Disjoint rets.toList)
  (hdefined_vars : ∀ var, var ∈ definedVars ↔ ∃ val, map.getVar var = some val) :
  var ∈ definedVars.removeAll args ∨ var ∈ rets ↔
  ∃ val,
    ((map.removeVars args).insertVars rets outputVals).getVar var =
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

theorem sim_step_op
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {args rets cont}
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hop : ec.cont = .expr (.op o args rets cont)) :
  ∃ pc',
    Config.Step.IORestrictedStep pc l pc' ∧
    ∃ gs', SimRel gs' ec' pc' := by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hop
  simp [compileExpr] at hcurrent
  -- Deduce some facts from `hstep` and `hwf_expr`
  cases hstep with
  | step_init hexpr | step_ret hexpr | step_tail hexpr | step_br hexpr =>
    simp [hop] at hexpr
  | step_op hexpr hargs =>
    rename_i o' inputVals outputVals args' rets' cont'
    simp [hop] at hexpr
    have ⟨h₁, h₂, h₃, h₄⟩ := hexpr
    subst h₁; subst h₂; subst h₃; subst h₄
    clear hexpr
    cases hwf_expr with
    | wf_op hargs_nodup hrets_nodup hrets_disj hargs_subset hwf_cont =>
    -- Step 1: Pop inputs of `o` and run `o`
    have ⟨chans₁, inputVals', hpop_input_vals, hchans₁, hinput_vals⟩ :=
      pop_vals_singleton
      (map := pc.chans)
      (names := args.map (.var · gs.pathConds))
      (λ name val =>
        match name with
        | .var v _ => ec.vars.getVar v = some val
        | _ => False)
      (vars_nodup_to_var_names_nodup hargs_nodup)
      (by
        intros name hname
        simp at hname
        replace ⟨var, hmem_var, hname⟩ := hname
        replace hmem_var := Vector.mem_toList_iff.mpr hmem_var
        have := hargs_subset hmem_var
        have ⟨_, h⟩ := hsim.defined_vars_to_get_var this
        simp [hsim.vars_to_chans, varsToChans, ← hname, h])
    have : inputVals = inputVals' := by
      symm
      apply Vector.toList_inj.mp
      apply List.right_unique_forall₂' _ hinput_vals
      · simp [Vector.toList_map]
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
        (args.map (.var · gs.pathConds))
        (rets.map (.var · gs.pathConds))
      ∈ pc.proc.atoms
    := by grind
    have hstep : Dataflow.Config.Step pc (.yield o inputVals outputVals) _
      := Dataflow.Config.Step.step_op hmem_op hpop_input_vals
    -- Simplify pushes
    rw [push_vals_empty] at hstep
    rotate_left
    · exact vars_nodup_to_var_names_nodup hrets_nodup
    · intros name hname
      simp [hchans₁]
      intros hname₂
      simp at hname
      replace ⟨var, hvar, hname⟩ := hname
      simp [← hname, hsim.vars_to_chans, varsToChans]
      have : var ∉ gs.definedVars := List.disjoint_right.mp hrets_disj
        (Vector.mem_toList_iff.mpr hvar)
      split <;> rename_i h
      · have h' := hsim.get_var_to_defined_vars ⟨_, h⟩
        simp [this h']
      · rfl
    exact ⟨_, .step_yield hstep,
      gs.useThenDefine args.toList rets.toList,
      by
        and_intros
        · funext name
          simp [varsToChans, hchans₁]
          cases name with
          | var var pathConds =>
            simp
            split <;> rename_i h₁
            · rename_i i
              simp [Vector.get] at h₁
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
              split <;> rename_i h₂
              · simp [h₂.2]
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
              · simp at h₂
                split <;> rename_i h₃
                · simp [hsim.vars_to_chans, varsToChans, h₃]
                  have : var ∉ rets := by
                    intros h
                    exact this h h₃.symm
                  rw [var_map_insert_vars_disj this]
                  have : var ∉ args.toList := by
                    intros h
                    replace h := Vector.mem_toList_iff.mp h
                    exact h₂ h h₃.symm
                  rw [var_map_remove_vars_disj this]
                · simp [hsim.vars_to_chans, varsToChans, h₃]
          | _ =>
            simp [hsim.vars_to_chans, varsToChans]
        · simp
          apply List.Nodup.append
          · apply List.Nodup.filter
            exact hsim.defined_vars_nodup
          · exact hrets_nodup
          · apply List.disjoint_implies_filter_disjoint_left hrets_disj
        · simp
          intros var
          apply sim_step_op_defined_vars
          · exact hrets_disj
          · intros v
            apply hsim.defined_vars_iff_get_var
        · grind
        · exact hsim.path_conds_nodup
        · simp [hsim.has_merges]
        · exact hsim.wf_fn.1
        · exact hsim.wf_fn.2
        · simp; exact hsim.inputs
        · simp; exact hsim.outputs
        · exists rest, carryInLoop
          -- ctxLeft
          exists
            ctxLeft ++ [
              .op o
                (args.map (.var · gs.pathConds))
                (rets.map (.var · gs.pathConds))
            ]
          -- ctxCurrent
          exists
            compileExpr (gs.definedVars.removeAll args.toList ++ rets.toList) gs.pathConds cont
          -- ctxRight
          exists ctxRight
          grind
    ⟩

end Wavelet.Compile.Fn
