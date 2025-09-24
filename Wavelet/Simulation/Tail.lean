import Mathlib.Data.Vector.Basic

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Lemmas

import Wavelet.Simulation.Relation
import Wavelet.Simulation.Lemmas
import Wavelet.Simulation.Ret

namespace Wavelet.Simulation.Tail

open Wavelet.Op Wavelet.Seq Wavelet.Dataflow Wavelet.Compile
open Relation Lemmas Ret

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

/-- Values pushed to output channels in the case of a tail call. -/
private def exprOutputVals
  (tailArgs : Vector V m)
  : Vector V (n + (m + 1)) :=
  Vector.replicate n (Interp.junkVal Op S : V) ++
  tailArgs.push
  (Interp.fromBool Op S true)

set_option maxHeartbeats 1000000

/-- Fires `forwardc` and `sink` to get an intermediate state. -/
theorem sim_step_tail_forwardc_sink
  (hnz : m > 0 ∧ n > 0)
  {ec : Seq.Config Op χ V S m n}
  {pc : Dataflow.Config Op (ChanName χ) V S m n}
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hexpr : ec.expr = .cont (.tail vars))
  (hvars : VarMap.getVars χ V vars ec.vars = some tailArgs)
  (hvars_nodup : vars.toList.Nodup) :
  Dataflow.Config.StepPlus Op (ChanName χ) V S pc
  { proc := pc.proc,
    chans := intermChans _ _ _ _ ec pc vars
      (exprOutputVals Op V S tailArgs)
      ec.pathConds
    state := pc.state }
:= by
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
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hexpr
  simp [compileExpr] at hcurrent
  -- Some abbreviations
  generalize hvar_names :
    compileExpr.varNames χ ec.pathConds vars = varNames
  generalize hjunk :
    Interp.junkVal (self := instInterp) Op S = junk
  generalize htrue :
    Interp.fromBool (self := instInterp) Op S true = trueVal
  simp only [hvar_names, hjunk, htrue] at hcurrent
  -- Step 1: Fire `forwardc`.
  have ⟨chans₁, tailArgs', hpop_tail_args, hchans₁, htail_args⟩ :=
    pop_vals_singleton _ _
    (map := pc.chans)
    (names := varNames)
    (λ name val =>
      ∃ var,
        name = .var var ec.pathConds ∧
        ec.vars.getVar _ _ var = some val)
    (by
      simp only [← hvar_names, compileExpr.varNames, Vector.toList_map]
      apply List.Nodup.map _ hvars_nodup
      simp [Function.Injective, compileExpr.varName])
    (by
      simp [← hvar_names, hlive_vars, compileExpr.varNames,
        compileExpr.varName, SimR.varsToChans]
      have := Vector.mapM_some_implies_all_some hvars
      intros v hmem_v
      have ⟨val, _, hval⟩ := this v hmem_v
      exists val
      simp [VarMap.getVar, hval])
  have heq_ret_vals :
    tailArgs' = tailArgs
  := by
    apply Vector.toList_inj.mp
    apply List.right_unique_forall₂' _ htail_args
    · simp [← hvar_names, compileExpr.varNames, compileExpr.varName,
        Vector.toList_map, VarMap.getVar]
      apply List.mapM_some_iff_forall₂.mp (Vector.mapM_toList hvars)
    · simp [Relator.RightUnique, VarMap.getVar]
      grind
  replace heq_ret_vals := heq_ret_vals.symm
  subst heq_ret_vals
  have hmem_forwardc :
    AtomicProc.forwardc
      varNames ((Vector.replicate n junk).push trueVal)
      (compileExpr.exprOutputs' χ m n ec.pathConds)
      ∈ pc.proc.atoms
  := by grind
  have hsteps₁ : Dataflow.Config.StepPlus _ _ _ _ pc _
    := Relation.TransGen.single (Dataflow.Config.Step.step_forwardc hmem_forwardc hpop_tail_args)
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₁
  rotate_left
  · apply exprOutputs'_nodup
  · intros name hmem_name
    simp at hmem_name
    simp [hchans₁, ← hvar_names, compileExpr.varNames,
      compileExpr.varName, hlive_vars, SimR.varsToChans]
    simp [compileExpr.exprOutputs'] at hmem_name
    rcases hmem_name with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h
    · simp [← h]
    · simp [← h]
    · simp [h]
  simp only [hchans₁] at hsteps₁
  replace ⟨pc₁, hpc₁, hsteps₁⟩ := exists_eq_left.mpr hsteps₁
  -- Step 2: Fire `sink` to consume all unused channels in the current context.
  have ⟨chans₂, otherVals, hpop_other_vals, hchans₂, hother_vals⟩ :=
    pop_vals_singleton _ _
    (map := pc₁.chans)
    (names := compileExpr.allVarsExcept χ ec.definedVars vars.toList ec.pathConds)
    (λ name val => True)
    (allVarsExcept_nodup hdefined_vars_no_dup)
    (by
      simp
      intros name hname
      have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept hname
      simp [hvar, hpc₁]
      simp [hlive_vars, SimR.varsToChans]
      have ⟨val, h⟩ := (hdefined_vars var).mp hmem_var
      exists val
      simp at hnot_mem_var
      simp [h, ← hvar_names, compileExpr.varNames, compileExpr.varName, hnot_mem_var])
  have hmem_sink :
    .sink (compileExpr.allVarsExcept χ ec.definedVars vars.toList ec.pathConds)
    ∈ pc₁.proc.atoms
  := by grind
  have hsteps₂ : Dataflow.Config.StepPlus _ _ _ _ pc _
    := Relation.TransGen.tail hsteps₁
      (Dataflow.Config.Step.step_sink hmem_sink hpop_other_vals)
  apply step_plus_eq
  apply hsteps₂
  simp [hpc₁]
  funext name
  simp [intermChans, hchans₂, hpc₁]
  split <;> rename_i h₁
  · have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept h₁
    simp [hvar]
  · split <;> rename_i h₂
    · simp [exprOutputs'_finIdxOf?_some_to_exprOutputs h₂, ← hjunk, ← htrue, exprOutputVals]
      -- Rearrange positions of tail arguments and return values
      rename_i i
      split_ifs <;> rename_i h₃
      · simp [h₃]
      · rename_i h₄
        have : ↑i - m < n := by omega
        simp [Vector.getElem_push, Vector.getElem_append]
        simp [h₄, this]
      · rename_i h₄
        simp at h₃
        simp [Vector.getElem_push, Vector.getElem_append]
        have h₅ : ↑i ≥ m := by omega
        have h₆ : ↑i - m ≥ n := by omega
        simp [h₄, h₆]
    · have := Option.eq_none_iff_forall_ne_some.mpr h₂
      have := exprOutputs'_finIdxOf?_none_to_exprOutputs this
      simp [this, ← hvar_names]
      split <;> rename_i h₃
      · rfl
      · simp [hlive_vars, SimR.varsToChans]
        cases name with
        | var var' pathConds' =>
          simp
          intros h
          simp [h, compileExpr.varNames, compileExpr.varName] at h₃
          simp [compileExpr.allVarsExcept, List.toVector] at h₁
          split <;> rename_i h₄
          · replace h₄ := (hdefined_vars var').mpr ⟨_, h₄⟩
            have := h₁ (List.mem_to_mem_removeAll h₄ (by simp [h₃]))
            simp [h] at this
          · rfl
        | merge_cond condName => rfl
        | _ => simp [hexpr]

/-- TODO: these theorems are similar to `sim_step_ret`,
figure out a way to share these proofs. -/
theorem sim_step_tail
  (hnz : m > 0 ∧ n > 0)
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hexpr : ec.expr = .cont (.tail vars)) :
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
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hexpr
  cases hstep with
  | step_br hexpr' | step_ret hexpr' | step_op hexpr' =>
    simp [hexpr] at hexpr'
  | step_tail hexpr' hvars =>
    rename_i tailArgs vars'
    simp [hexpr] at hexpr'
    subst hexpr'
    cases hwf_expr with | wf_tail hvars_nodup =>
    have hsteps₁ :=
      sim_step_tail_forwardc_sink _ _ _ _ hnz hsim hexpr hvars hvars_nodup
    have hsteps₂ := sim_step_merges _ _ _ _ ec pc
      hmerges (by simp)
      hpath_conds_nodup hsteps₁
    -- Step 4: Fire the `fork` in `compileFn`.
    simp only [compileFn, compileFn.resultSteers] at hcomp_fn
    have ⟨chans₁, hpop_tail_cond, hchans₁⟩ := pop_val_singleton _ _
      (map := intermChans _ _ _ _ ec pc vars
        (exprOutputVals Op V S tailArgs)
        [])
      (name := .tail_cond [])
      (val := instInterp.fromBool true)
      (by simp [intermChans, exprOutputs_finIdxOf?_tail_cond, exprOutputVals])
    have hmem_fork :
      .fork (ChanName.tail_cond [])
        #v[.tail_cond_carry, .tail_cond_steer_dests, .tail_cond_steer_tail_args]
      ∈ pc.proc.atoms
    := by grind
    have hsteps₃ : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.tail hsteps₂
        (Dataflow.Config.Step.step_fork hmem_fork hpop_tail_cond)
    -- Simplify pushes
    rw [push_vals_empty] at hsteps₃
    rotate_left
    · simp
    · simp [hchans₁, intermChans]
    simp at hsteps₃
    replace ⟨pc₁, hpc₁, hsteps₃⟩ := exists_eq_left.mpr hsteps₃
    -- Step 5: Fire the first `steer` in `compileFn` for return values.
    have ⟨chans₂, hpop_tail_cond_steer_dests, hchans₂⟩ := pop_val_singleton _ _
      (map := pc₁.chans)
      (name := .tail_cond_steer_dests)
      (val := instInterp.fromBool true)
      (by simp [hpc₁, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
    have ⟨chans₃, retVals, hpop_ret_vals, hchans₃, hret_vals⟩ :=
      pop_vals_singleton _ _
      (map := chans₂)
      (names := (Vector.range n).map (.dest · []))
      (λ name val => True)
      (by
        simp [Vector.toList_map, Vector.toList_range]
        apply List.Nodup.map _ List.nodup_range
        simp [Function.Injective])
      (by
        intros name hname
        simp at hname
        replace ⟨i, h₂, hname⟩ := hname
        simp [← hname, hchans₂, hpc₁, hchans₁, intermChans,
          List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
          exprOutputs_finIdxOf?_dest h₂, h₂, exprOutputVals])
    have hmem_steer_dests :
      .steer false
        .tail_cond_steer_dests
        ((Vector.range n).map (.dest · []))
        ((Vector.range n).map .final_dest)
      ∈ pc₁.proc.atoms
    := by grind
    have hsteps₄ : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.tail hsteps₃
        (Dataflow.Config.Step.step_steer
          hmem_steer_dests
          hpop_tail_cond_steer_dests
          hpop_ret_vals
          (instInterp.unique_fromBool_toBool _))
    -- Simplify pushes
    rw [push_vals_empty] at hsteps₄
    rotate_left
    · simp [Vector.toList_map, Vector.toList_range]
      apply List.Nodup.map _ List.nodup_range
      simp [Function.Injective]
    · simp [hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        hchans₁, intermChans]
    simp at hsteps₄
    replace ⟨pc₂, hpc₂, hsteps₄⟩ := exists_eq_left.mpr hsteps₄
    -- Step 6: Fire the second `steer` in `compileFn` for tail call args.
    have ⟨chans₄, hpop_tail_cond_steer_tail_args, hchans₄⟩ := pop_val_singleton _ _
      (map := pc₂.chans)
      (name := .tail_cond_steer_tail_args)
      (val := instInterp.fromBool true)
      (by
        simp [hpc₂, hchans₃, hchans₂, hpc₁,
          List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
    have ⟨chans₅, tailArgVals, hpop_tail_arg_vals, hchans₅, htail_arg_vals⟩ :=
      pop_vals_singleton _ _
      (map := chans₄)
      (names := (Vector.range m).map (.tail_arg · []))
      (λ name val =>
        match name with
        | .tail_arg i _ => ∃ (h : i < m), val = tailArgs[i]
        | _ => False)
      (by
        simp [Vector.toList_map, Vector.toList_range]
        apply List.Nodup.map _ List.nodup_range
        simp [Function.Injective])
      (by
        simp
        intros i hi
        simp [hchans₄, hpc₂, hchans₃, hchans₂, hpc₁,
          List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
          hchans₁, intermChans, exprOutputVals,
          exprOutputs_finIdxOf?_tail_args hi, hi])
    have : tailArgs = tailArgVals := by
      symm
      apply Vector.toList_inj.mp
      apply List.right_unique_forall₂' _ htail_arg_vals
      · apply List.forall₂_iff_get.mpr
        simp [Vector.toList_map, Vector.toList_range]
      · simp [Relator.RightUnique]
        intros a b c hb hc
        split at hb <;> simp at hc
        replace ⟨_, hb⟩ := hb
        replace ⟨_, hc⟩ := hc
        simp [hc, hb]
    subst this
    have hmem_steer_tail_args :
      .steer true
        .tail_cond_steer_tail_args
        ((Vector.range m).map (.tail_arg · []))
        ((Vector.range m).map .final_tail_arg)
      ∈ pc₂.proc.atoms
    := by grind
    have hsteps₅ : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.tail hsteps₄
        (Dataflow.Config.Step.step_steer
          hmem_steer_tail_args
          hpop_tail_cond_steer_tail_args
          hpop_tail_arg_vals
          (instInterp.unique_fromBool_toBool _))
    rw [push_vals_empty] at hsteps₅
    rotate_left
    · simp [Vector.toList_map, Vector.toList_range]
      apply List.Nodup.map _ List.nodup_range
      simp [Function.Injective]
    · simp [hchans₅, hchans₄, hpc₂, hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        hchans₁, intermChans]
    simp at hsteps₅
    replace ⟨pc₃, hpc₃, hsteps₅⟩ := exists_eq_left.mpr hsteps₅
    -- Step 7: Fire the first `carry` in `compileFn`.
    have ⟨chans₆, hpop_tail_cond_steer_tail_args, hchans₆⟩ := pop_val_singleton _ _
      (map := pc₃.chans)
      (name := .tail_cond_carry)
      (val := instInterp.fromBool true)
      (by simp [hpc₃, hchans₅, hchans₄, hpc₂, hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
    have ⟨chans₇, tailArgs', hpop_final_tail_args, hchans₇, hfinal_tail_args⟩ :=
      pop_vals_singleton _ _
      (map := chans₆)
      (names := (Vector.range m).map .final_tail_arg)
      (λ name val =>
        match name with
        | .final_tail_arg i => ∃ (h : i < m), val = tailArgs[i]
        | _ => False)
      (by
        simp [Vector.toList_map, Vector.toList_range]
        apply List.Nodup.map _ List.nodup_range
        simp [Function.Injective])
      (by
        simp
        intros i hi
        simp [hchans₆, hpc₃]
        split <;> rename_i h₁
        · simp at h₁
          simp
          exists hi
          congr 1
          omega
        · have := Option.eq_none_iff_forall_ne_some.mpr h₁
          simp at this
          omega)
    have : tailArgs = tailArgs' := by
      symm
      apply Vector.toList_inj.mp
      apply List.right_unique_forall₂' _ hfinal_tail_args
      · simp [Vector.toList_map, Vector.toList_range]
        apply List.forall₂_iff_get.mpr
        simp
      · simp [Relator.RightUnique]
        intros a b c hb hc
        split at hb <;> simp at hc
        replace ⟨_, hb⟩ := hb
        replace ⟨_, hc⟩ := hc
        simp [hc, hb]
    subst this
    have hmem_carry :
      pc₃.proc.atoms = [] ++ [compileFn.initCarry _ _ _ ec.fn carryInLoop] ++ rest
    := by simp [hpc₃, hpc₂, hpc₁, hatoms]
    simp only [compileFn.initCarry, hcarryInLoop] at hmem_carry
    have hsteps₆ : Dataflow.Config.StepPlus _ _ _ _ pc _
      := Relation.TransGen.tail hsteps₅
        (Dataflow.Config.Step.step_carry_true
          hmem_carry
          hpop_tail_cond_steer_tail_args
          (instInterp.unique_fromBool_toBool _)
          hpop_final_tail_args)
    -- Simplify pushes
    rw [push_vals_empty] at hsteps₆
    rotate_left
    · simp [Vector.toList_map]
      apply List.Nodup.map _ hwf_fn.1
      simp [Function.Injective]
    · intros name hname
      simp at hname
      have ⟨var, hmem_var, hname⟩ := hname
      simp [← hname, hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
        hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        hchans₁, intermChans]
    simp at hsteps₆
    replace ⟨pc', hpc', hsteps₆⟩ := exists_eq_left.mpr hsteps₆
    -- Step 8: Prove preservation of invariants.
    exists pc'
    constructor
    · exact hsteps₆
    · and_intros
      · simp only [Seq.Config.init, heq_state, hpc', hpc₃, hpc₂, hpc₁]
      · -- varsToChans
        funext name
        simp [SimR.varsToChans, Seq.Config.init]
        cases name with
        | var v pathConds =>
          simp [hpc', hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
            hchans₃, hchans₂, hpc₁]
          if h₁ : pathConds = [] then
            simp [h₁]
            split <;> rename_i h₂
            · rename_i i
              simp at h₂
              simp [Vector.get] at h₂
              simp [← h₂.1]
              simp [var_map_fromList_get_vars_index hwf_fn.1]
            · have := Option.eq_none_iff_forall_ne_some.mpr h₂
              simp at this
              simp [List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
                hchans₁, intermChans]
              split <;> rename_i h₃
              · have h₄ := var_map_fromList_get_vars.mpr ⟨_, h₃⟩
                exact False.elim (this h₄)
              · rfl
          else
            simp [h₁, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
              hchans₁, intermChans]
        | dest =>
          simp [hpc', hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
            hchans₃, hchans₂, hpc₁,
            List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
            hchans₁, intermChans]
          intros h₁
          simp [exprOutputs_finIdxOf?_no_match_dest h₁]
        | tail_arg =>
          simp [hpc', hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
            hchans₃, hchans₂, hpc₁,
            List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
            hchans₁, intermChans]
          intros h₁
          simp [exprOutputs_finIdxOf?_no_match_tail_args h₁]
        | tail_cond =>
          simp [hpc', hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
            hchans₃, hchans₂, hpc₁,
            List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
            hchans₁, intermChans]
          intros h₁
          simp [exprOutputs_finIdxOf?_no_match_tail_cond h₁]
        | input | switch_cond | merge_cond
        | tail_cond_carry | tail_cond_steer_dests | tail_cond_steer_tail_args
        | final_dest =>
          simp [hpc', hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
            hchans₃, hchans₂, hpc₁,
            List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
            hchans₁, intermChans]
        | final_tail_arg =>
          simp [hpc', hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
            hchans₃, hchans₂, hpc₁,
            List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
            hchans₁, intermChans]
          split <;> rename_i h₁
          · simp at h₁
            omega
          · simp
      · simp [Seq.Config.init, hwf_fn.1]
      · simp [Seq.Config.init]
        intros var
        apply var_map_fromList_get_vars
      · simp [Seq.Config.init]
      · simp [Seq.Config.init]
      · simp [Seq.Config.init, SimR.HasMerges]
      · exact hwf_fn.1
      · exact hwf_fn.2
      · exists rest, true
        -- ctxLeft
        exists []
        -- ctxCurrent
        exists compileExpr Op χ V S hnz ec.fn.params.toList [] ec.fn.body
        -- ctxRight
        exists compileFn.resultSteers Op χ V m n
        simp [hrest] at hcomp_fn
        simp [Seq.Config.init, hpc', hpc₃, hpc₂, hpc₁,
          compileFn.initCarry, compileFn, hatoms,
          compileFn.initCarry, hcarryInLoop, hrest,
          hwf_fn.2, compileFn.bodyComp, compileFn.resultSteers,
          ← hcomp_fn]

end Wavelet.Simulation.Tail
