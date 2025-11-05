import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Batteries.Data.Vector.Lemmas

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Fn.Simulation.Invariants
import Wavelet.Compile.Fn.Simulation.BrMerges
import Wavelet.Compile.Fn.Lemmas

/-! Simulation in the case of tail call. -/

namespace Wavelet.Compile.Fn

open Semantics Seq Dataflow Compile Fn

/-- Values pushed to output channels in the case of a tail call. -/
private def tailArgsToExprOutputs
  [InterpConsts V]
  (tailArgs : Vector V m) : Vector V (n + (m + 1)) :=
  Vector.replicate n (InterpConsts.junkVal : V) ++
  tailArgs.push (InterpConsts.fromBool true)

/-- Fires `forwardc` and `sink` to get an intermediate state. -/
private theorem sim_step_tail_forwardc_sink
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {ec : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hexpr : ec.cont = .expr (.tail vars))
  (hvars : VarMap.getVars vars ec.vars = some tailArgs)
  (hvars_nodup : vars.toList.Nodup) :
  Dataflow.Config.Step.WeakStep .τ pc .τ
  { proc := pc.proc,
    chans := intermChans m n gs vars
      (tailArgsToExprOutputs tailArgs)
      gs.pathConds }
:= by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hexpr
  simp [compileExpr] at hcurrent
  -- Step 1: Fire `forwardc`.
  have ⟨chans₁, tailArgs', hpop_tail_args, hchans₁, htail_args⟩ :=
    pop_vals_singleton
    (map := pc.chans)
    (names := vars.map (.var · gs.pathConds))
    (λ name val =>
      ∃ var,
        name = .var var gs.pathConds ∧
        ec.vars.getVar var = some val)
    (by
      simp only [Vector.toList_map]
      apply List.Nodup.map _ hvars_nodup
      simp [Function.Injective])
    (by
      simp [hsim.vars_to_chans, varsToChans]
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
    · simp [Vector.toList_map, VarMap.getVar]
      apply List.mapM_some_iff_forall₂.mp (Vector.mapM_toList hvars)
    · simp only [Relator.RightUnique]
      intros a b c hb hc
      have ⟨_, hb₁, hb₂⟩ := hb
      have ⟨_, hc₁, hc₂⟩ := hc
      simp [hb₁] at hc₁
      subst hc₁
      simp [hb₂] at hc₂
      exact hc₂
  replace heq_ret_vals := heq_ret_vals.symm
  subst heq_ret_vals
  have hmem_forwardc :
    AtomicProc.forwardc
      (vars.map (.var · gs.pathConds))
      ((Vector.replicate n InterpConsts.junkVal).push (InterpConsts.fromBool true))
      (compileExpr.tailExprOutputs m n gs.pathConds)
      ∈ pc.proc.atoms
  := by grind
  have hsteps₁ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .single (Dataflow.Config.Step.step_forwardc hmem_forwardc hpop_tail_args)
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₁
  rotate_left
  · apply tailExprOutputs_nodup
  · intros name hmem_name
    simp at hmem_name
    simp [hchans₁, hsim.vars_to_chans, varsToChans]
    simp [compileExpr.tailExprOutputs] at hmem_name
    rcases hmem_name with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h
    · simp [← h]
    · simp [← h]
    · simp [h]
  simp only [hchans₁] at hsteps₁
  replace ⟨pc₁, hpc₁, hsteps₁⟩ := exists_eq_left.mpr hsteps₁
  -- Step 2: Fire `sink` to consume all unused channels in the current context.
  have ⟨chans₂, otherVals, hpop_other_vals, hchans₂, hother_vals⟩ :=
    pop_vals_singleton
    (map := pc₁.chans)
    (names := compileExpr.allVarsExcept gs.definedVars vars.toList gs.pathConds)
    (λ name val => True)
    (allVarsExcept_nodup hsim.defined_vars_nodup)
    (by
      simp
      intros name hname
      have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept hname
      simp [hvar, hpc₁]
      simp [hsim.vars_to_chans, varsToChans]
      have ⟨val, h⟩ := hsim.defined_vars_to_get_var hmem_var
      exists val
      simp at hnot_mem_var
      simp [h, hnot_mem_var])
  have hmem_sink :
    .sink (compileExpr.allVarsExcept gs.definedVars vars.toList gs.pathConds)
    ∈ pc₁.proc.atoms
  := by grind
  have hsteps₂ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .tail_tau_star hsteps₁
      (Dataflow.Config.Step.step_sink hmem_sink hpop_other_vals)
  apply hsteps₂.eq_rhs
  simp [hpc₁]
  funext name
  simp [intermChans, hchans₂, hpc₁]
  split <;> rename_i h₁
  · have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept h₁
    simp [hvar]
  · split <;> rename_i h₂
    · simp [tailExprOutputs_finIdxOf?_some_to_exprOutputs h₂, tailArgsToExprOutputs]
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
      have := tailExprOutputs_finIdxOf?_none_to_exprOutputs this
      simp [this]
      split <;> rename_i h₃
      · rfl
      · simp [hsim.vars_to_chans, varsToChans]
        cases name with
        | var var' pathConds' =>
          simp
          intros h
          simp [h] at h₃
          simp [compileExpr.allVarsExcept, List.toVector] at h₁
          split <;> rename_i h₄
          · replace h₄ := hsim.get_var_to_defined_vars ⟨_, h₄⟩
            have := h₁ (List.mem_to_mem_removeAll h₄ (by simp [h₃]))
            simp [h] at this
          · rfl
        | _ => rfl

/- TODO: Fix proof performance -/
set_option maxHeartbeats 300000

/-- Fires relevant operators on the dataflow side. -/
private theorem sim_step_tail_exec_dataflow
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hexpr : ec.cont = .expr (.tail vars)) :
  Dataflow.Config.Step.WeakStep .τ pc l {
    proc := pc.proc,
    chans := varsToChans (.init ec.fn.params.toList) ec',
  }
:= by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, ⟨_, hwf_expr⟩, hcurrent⟩ := hcont _ hexpr
  cases hstep with
  | step_init hexpr' | step_br hexpr' | step_ret hexpr' | step_op hexpr' =>
    simp [hexpr] at hexpr'
  | step_tail hexpr' hvars =>
  rename_i tailArgs vars'
  simp [hexpr] at hexpr'
  subst hexpr'
  cases hwf_expr with | wf_tail hvars_nodup =>
  -- Step 1: Fire `forwardc` and `sink`
  have hsteps₁ := sim_step_tail_forwardc_sink hsim hexpr hvars hvars_nodup
  -- Step 2: Fire final merges
  have hsteps₂ := sim_step_merges pc gs
    hsim.has_merges (by simp)
    hsim.path_conds_nodup hsteps₁
  -- Step 3: Fire the `fork` in `compileFn`.
  simp [compileFn, compileFn.resultSteers] at hcomp_fn
  have ⟨chans₁, hpop_tail_cond, hchans₁⟩ := pop_val_singleton
    (map := intermChans m n gs vars
      (tailArgsToExprOutputs tailArgs)
      [])
    (name := .tail_cond [])
    (val := InterpConsts.fromBool true)
    (by simp [intermChans, exprOutputs_finIdxOf?_tail_cond, tailArgsToExprOutputs])
  have hmem_fork :
    .fork (ChanName.tail_cond [])
      #v[.tail_cond_carry, .tail_cond_steer_dests, .tail_cond_steer_tail_args]
    ∈ pc.proc.atoms
  := by simp [hatoms, ← hcomp_fn]
  have hsteps₃ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .tail_tau hsteps₂
      (Dataflow.Config.Step.step_fork hmem_fork hpop_tail_cond
        (by apply InterpConsts.bool_clonable))
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₃
  rotate_left
  · simp
  · simp [hchans₁, intermChans]
  simp at hsteps₃
  replace ⟨pc₁, hpc₁, hsteps₃⟩ := exists_eq_left.mpr hsteps₃
  -- Step 4: Fire the first `steer` in `compileFn` for return values.
  have ⟨chans₂, hpop_tail_cond_steer_dests, hchans₂⟩ := pop_val_singleton
    (map := pc₁.chans)
    (name := .tail_cond_steer_dests)
    (val := InterpConsts.fromBool true)
    (by simp [hpc₁, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have ⟨chans₃, retVals, hpop_ret_vals, hchans₃, hret_vals⟩ :=
    pop_vals_singleton
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
        exprOutputs_finIdxOf?_dest h₂, h₂, tailArgsToExprOutputs])
  have hmem_steer_dests :
    .steer false
      .tail_cond_steer_dests
      ((Vector.range n).map (.dest · []))
      ((Vector.range n).map .final_dest)
    ∈ pc₁.proc.atoms
  := by simp [hpc₁, hatoms, ← hcomp_fn]
  have hsteps₄ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .tail_tau hsteps₃
      (Dataflow.Config.Step.step_steer
        hmem_steer_dests
        hpop_tail_cond_steer_dests
        hpop_ret_vals
        (InterpConsts.unique_fromBool_toBool _))
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
  -- Step 5: Fire the second `steer` in `compileFn` for tail call args.
  have ⟨chans₄, hpop_tail_cond_steer_tail_args, hchans₄⟩ := pop_val_singleton
    (map := pc₂.chans)
    (name := .tail_cond_steer_tail_args)
    (val := InterpConsts.fromBool true)
    (by
      simp [hpc₂, hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have ⟨chans₅, tailArgVals, hpop_tail_arg_vals, hchans₅, htail_arg_vals⟩ :=
    pop_vals_singleton
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
        hchans₁, intermChans, tailArgsToExprOutputs,
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
  := by simp [hpc₂, hpc₁, hatoms, ← hcomp_fn]
  have hsteps₅ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .tail_tau hsteps₄
      (Dataflow.Config.Step.step_steer
        hmem_steer_tail_args
        hpop_tail_cond_steer_tail_args
        hpop_tail_arg_vals
        (InterpConsts.unique_fromBool_toBool _))
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
  -- Step 6: Fire the first `carry` in `compileFn`.
  have ⟨chans₆, hpop_tail_cond_steer_tail_args, hchans₆⟩ := pop_val_singleton
    (map := pc₃.chans)
    (name := .tail_cond_carry)
    (val := InterpConsts.fromBool true)
    (by simp [hpc₃, hchans₅, hchans₄, hpc₂, hchans₃, hchans₂, hpc₁,
      List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have hmem_carry :
    pc₃.proc.atoms = [] ++ [compileFn.initCarry ec.fn carryInLoop] ++ rest
  := by simp [hpc₃, hpc₂, hpc₁, hatoms]
  simp only [compileFn.initCarry, hcarryInLoop] at hmem_carry
  have hsteps₆ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .tail_tau hsteps₅
      (Dataflow.Config.Step.step_carry_decider
        hmem_carry
        hpop_tail_cond_steer_tail_args
        (InterpConsts.unique_fromBool_toBool _))
  replace ⟨pc₄, hpc₄, hsteps₆⟩ := exists_eq_left.mpr hsteps₆
  -- Step 6: Final step at the carry
  have ⟨chans₇, tailArgs', hpop_final_tail_args, hchans₇, hfinal_tail_args⟩ :=
    pop_vals_singleton
    (map := pc₄.chans)
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
      simp [hpc₄, hchans₆, hpc₃]
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
    pc₄.proc.atoms = [] ++ [compileFn.initCarry ec.fn .popRight] ++ rest
  := by simp [hpc₄, hpc₃, hpc₂, hpc₁, compileFn.initCarry]
  have hsteps₇ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .tail_tau hsteps₆
      (Dataflow.Config.Step.step_carry_right
        hmem_carry
        hpop_final_tail_args)
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₇
  rotate_left
  · simp [Vector.toList_map]
    apply List.Nodup.map _ hsim.wf_fn.1
    simp [Function.Injective]
  · intros name hname
    simp at hname
    have ⟨var, hmem_var, hname⟩ := hname
    simp [← hname, hpc₄, hchans₇, hchans₆, hpc₃, hchans₅, hchans₄, hpc₂,
      hchans₃, hchans₂, hpc₁,
      List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
      hchans₁, intermChans]
  simp at hsteps₇
  replace ⟨pc', hpc', hsteps₇⟩ := exists_eq_left.mpr hsteps₇
  apply hsteps₇.eq_rhs
  simp [hpc', hpc₄, hpc₃, hpc₂, hpc₁,
    hchans₇, hchans₆, hchans₅, hchans₄, hchans₃, hchans₂, hchans₁,
    List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go, intermChans]
  -- Prove that the final channel maps match
  constructor
  · congr 1
    simp [hatoms, compileFn.initCarry, hcarryInLoop]
  · funext name
    simp [varsToChans]
    cases name with
    | var v pathConds =>
      simp
      if h₁ : pathConds = [] then
        simp [h₁]
        split <;> rename_i h₂
        · rename_i i
          simp at h₂
          simp [Vector.get] at h₂
          simp [← h₂.1]
          simp [var_map_fromList_get_vars_index hsim.wf_fn.1]
        · have := Option.eq_none_iff_forall_ne_some.mpr h₂
          simp at this
          simp
          split <;> rename_i h₃
          · have h₄ := var_map_fromList_get_vars.mpr ⟨_, h₃⟩
            exact False.elim (this h₄)
          · rfl
      else
        simp [h₁]
    | dest =>
      simp
      intros h₁
      simp [exprOutputs_finIdxOf?_no_match_dest h₁]
    | tail_arg =>
      simp
      intros h₁
      simp [exprOutputs_finIdxOf?_no_match_tail_args h₁]
    | tail_cond =>
      simp
      intros h₁
      simp [exprOutputs_finIdxOf?_no_match_tail_cond h₁]
    | final_tail_arg =>
      simp
      split <;> rename_i h₁
      · simp at h₁
        omega
      · simp
    | input | switch_cond | merge_cond
    | tail_cond_carry | tail_cond_steer_dests | tail_cond_steer_tail_args
    | final_dest =>
      simp

/-- TODO: these theorems are similar to `sim_step_ret`,
figure out a way to share these proofs. -/
theorem sim_step_tail
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hexpr : ec.cont = .expr (.tail vars)) :
  ∃ pc',
    Config.Step.IORestrictedStep pc l pc' ∧
    ∃ gs', SimRel gs' ec' pc' := by
  have hsteps := sim_step_tail_exec_dataflow hsim hstep hexpr
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, ⟨_, hwf_expr⟩, hcurrent⟩ := hcont _ hexpr
  cases hstep with
  | step_init hexpr' | step_br hexpr' | step_ret hexpr' | step_op hexpr' =>
    simp [hexpr] at hexpr'
  | step_tail hexpr' hvars =>
    rename_i tailArgs vars'
    simp [hexpr] at hexpr'
    subst hexpr'
    cases hwf_expr with | wf_tail hvars_nodup =>
    exact ⟨_, .step_tau hsteps.to_tau_star,
      .init ec.fn.params.toList,
      by
        and_intros
        · simp
        · simp [hsim.wf_fn.1]
        · simp []
          intros var
          apply var_map_fromList_get_vars
        · simp [OrderedPathConds]
        · simp
        · simp [HasMerges]
        · exact hsim.wf_fn.1
        · exact hsim.wf_fn.2
        · exact hsim.inputs
        · exact hsim.outputs
        · simp only [HasCompiledProcs, ↓existsAndEq, compileFn.initCarry,
            List.append_assoc, reduceCtorEq, GhostState.init, Vector.toList_eq_nil_iff,
            and_true, IsEmpty.forall_iff, Cont.expr.injEq, forall_eq', true_and]
          exists [], compileFn.resultSteers m n
          simp only [hatoms, compileFn, compileFn.initCarry, hcarryInLoop]
          simp only [compileFn, List.cons.injEq, true_and] at hcomp_fn
          simp only [← hcomp_fn, compileFn.bodyComp, List.nil_append, true_and]
          exact ⟨_, hsim.wf_fn.2⟩
    ⟩

end Wavelet.Compile.Fn
