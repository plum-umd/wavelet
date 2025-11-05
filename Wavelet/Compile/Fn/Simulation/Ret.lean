import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Batteries.Data.Vector.Lemmas

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Fn.Simulation.Invariants
import Wavelet.Compile.Fn.Simulation.BrMerges
import Wavelet.Compile.Fn.Lemmas

/-! Simulation in the case of returning. -/

namespace Wavelet.Compile.Fn

open Semantics Seq Dataflow Compile Fn

/-- Values pushed to output channels in the case of a return. -/
private def retValsToExprOutputs
  [InterpConsts V]
  (retVals : Vector V n) : Vector V (n + (m + 1)) :=
  retVals ++
  (Vector.replicate m (InterpConsts.junkVal : V)).push
  (InterpConsts.fromBool false)

/-- Fires `forwardc` and `sink` to get an intermediate state. -/
private theorem sim_step_ret_forwardc_sink
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {ec : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hexpr : ec.cont = .expr (.ret vars))
  (hvars : VarMap.getVars vars ec.vars = some retVals)
  (hvars_nodup : vars.toList.Nodup) :
  Dataflow.Config.Step.WeakStep .τ pc .τ
  { proc := pc.proc,
    chans := intermChans m n gs vars
      (retValsToExprOutputs retVals)
      gs.pathConds }
:= by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont _ hexpr
  simp [compileExpr] at hcurrent
  -- Step 1: Fire `forwardc`.
  have ⟨chans₁, retVals', hpop_ret_vals, hchans₁, hret_vals⟩ :=
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
    retVals' = retVals
  := by
    apply Vector.toList_inj.mp
    apply List.right_unique_forall₂' _ hret_vals
    · simp [Vector.toList_map, VarMap.getVar]
      apply List.mapM_some_iff_forall₂.mp (Vector.mapM_toList hvars)
    · simp [Relator.RightUnique, VarMap.getVar]
      grind
  replace heq_ret_vals := heq_ret_vals.symm
  subst heq_ret_vals
  have hmem_forwardc :
    AtomicProc.forwardc
      (vars.map (.var · gs.pathConds))
      ((Vector.replicate m InterpConsts.junkVal).push
        (InterpConsts.fromBool false))
      (compileExpr.exprOutputs m n gs.pathConds)
      ∈ pc.proc.atoms
  := by grind
  have hsteps₁ : Dataflow.Config.Step.WeakStep .τ pc _ _
    := .single (Dataflow.Config.Step.step_forwardc hmem_forwardc hpop_ret_vals)
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₁
  rotate_left
  · apply exprOutputs_nodup
  · intros name hmem_name
    simp at hmem_name
    simp [hchans₁, hsim.vars_to_chans, varsToChans]
    simp [compileExpr.exprOutputs] at hmem_name
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
  -- Prove that the final chan maps match
  funext name
  simp [intermChans, hchans₂, hpc₁]
  split <;> rename_i h₁
  · have ⟨var, hvar, hmem_var, hnot_mem_var⟩ := mem_allVarsExcept h₁
    simp [hvar]
  · split <;> rename_i h₂
    · simp [h₂, retValsToExprOutputs]
    · have := Option.eq_none_iff_forall_ne_some.mpr h₂
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
private theorem sim_step_ret_exec_dataflow
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {rest}
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hexpr : ec.cont = .expr (.ret vars))
  (hpc_atoms : pc.proc.atoms = compileFn.initCarry ec.fn .decider :: rest) :
  Dataflow.Config.Step.IORestrictedStep pc l {
    proc := {
      inputs := pc.proc.inputs,
      outputs := pc.proc.outputs,
      atoms := compileFn.initCarry ec.fn .popLeft :: rest
    },
    chans := varsToChans .empty ec',
  }
:= by
  have ⟨
    rest', carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, ⟨_, hwf_expr⟩, hcurrent⟩ := hcont _ hexpr
  have : rest = rest' := by
    simp [hatoms] at hpc_atoms
    exact hpc_atoms.2.symm
  subst this
  cases hstep with
  | step_init hexpr' | step_br hexpr' | step_tail hexpr'
  | step_op hexpr' =>
    simp [hexpr] at hexpr'
  | step_ret hexpr' hvars =>
  rename_i retVals vars'
  simp [hexpr] at hexpr'
  subst hexpr'
  cases hwf_expr with | wf_ret hvars_nodup =>
  have hsteps₁ :=
    sim_step_ret_forwardc_sink hsim hexpr hvars hvars_nodup
  have hsteps₂ := sim_step_merges pc gs
    hsim.has_merges (by simp)
    hsim.path_conds_nodup hsteps₁
  replace hsteps₂ :
    Dataflow.Config.Step.IORestrictedStep pc _ _
    := .step_tau hsteps₂.to_tau_star
  -- Step 4: Fire the `fork` in `compileFn`.
  simp only [compileFn, compileFn.resultSteers] at hcomp_fn
  have ⟨chans₁, hpop_tail_cond, hchans₁⟩ := pop_val_singleton
    (map := intermChans m n gs vars
      (retValsToExprOutputs retVals)
      [])
    (name := .tail_cond [])
    (val := InterpConsts.fromBool false)
    (by simp [intermChans, exprOutputs_finIdxOf?_tail_cond, retValsToExprOutputs])
  have hmem_fork :
    .fork (ChanName.tail_cond [])
      #v[.tail_cond_carry, .tail_cond_steer_dests, .tail_cond_steer_tail_args]
    ∈ pc.proc.atoms
  := by grind
  have hsteps₃ : Dataflow.Config.Step.IORestrictedStep pc _ _
    := .tail_tau (by simp) hsteps₂
      (Dataflow.Config.Step.step_fork
        hmem_fork hpop_tail_cond
        (by apply InterpConsts.bool_clonable))
  -- Simplify pushes
  rw [push_vals_empty] at hsteps₃
  rotate_left
  · simp
  · simp [hchans₁, intermChans]
  simp at hsteps₃
  replace ⟨pc₁, hpc₁, hsteps₃⟩ := exists_eq_left.mpr hsteps₃
  -- Step 5: Fire the first `steer` in `compileFn` for return values.
  have ⟨chans₂, hpop_tail_cond_steer_dests, hchans₂⟩ := pop_val_singleton
    (map := pc₁.chans)
    (name := .tail_cond_steer_dests)
    (val := InterpConsts.fromBool false)
    (by simp [hpc₁, List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have ⟨chans₃, destVals, hpop_dest_vals, hchans₃, hdest_vals⟩ :=
    pop_vals_singleton
    (map := chans₂)
    (names := (Vector.range n).map (.dest · []))
    (λ name val =>
      match name with
      | .dest i _ => ∃ (h : i < n), val = retVals[i]
      | _ => False)
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
        exprOutputs_finIdxOf?_dest h₂, h₂, retValsToExprOutputs])
  replace hdest_vals : destVals = retVals := by
    apply Vector.toList_inj.mp
    apply List.right_unique_forall₂' _ hdest_vals
    · apply List.forall₂_iff_get.mpr
      simp [Vector.toList_map, Vector.toList_range]
    · simp [Relator.RightUnique]
      intros a b c hb hc
      split at hb <;> simp at hc
      replace ⟨_, hb⟩ := hb
      replace ⟨_, hc⟩ := hc
      simp [hc, hb]
  subst hdest_vals
  have hmem_steer_dests :
    .steer false
      .tail_cond_steer_dests
      ((Vector.range n).map (.dest · []))
      ((Vector.range n).map .final_dest)
    ∈ pc₁.proc.atoms
  := by grind
  have hsteps₄ : Dataflow.Config.Step.IORestrictedStep pc _ _
    := .tail_tau (by simp) hsteps₃
      (Dataflow.Config.Step.step_steer
        hmem_steer_dests
        hpop_tail_cond_steer_dests
        hpop_dest_vals
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
  -- Step 6: Fire the second `steer` in `compileFn` for tail call args.
  have ⟨chans₄, hpop_tail_cond_steer_tail_args, hchans₄⟩ := pop_val_singleton
    (map := pc₂.chans)
    (name := .tail_cond_steer_tail_args)
    (val := InterpConsts.fromBool false)
    (by
      simp [hpc₂, hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have ⟨chans₅, tailArgVals, hpop_tail_arg_vals, hchans₅, htail_arg_vals⟩ :=
    pop_vals_singleton
    (map := chans₄)
    (names := (Vector.range m).map (.tail_arg · []))
    (λ name val => True)
    (by
      simp [Vector.toList_map, Vector.toList_range]
      apply List.Nodup.map _ List.nodup_range
      simp [Function.Injective])
    (by
      simp
      intros i hi
      simp [hchans₄, hpc₂, hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        hchans₁, intermChans,
        exprOutputs_finIdxOf?_tail_args hi])
  have hmem_steer_tail_args :
    .steer true
      .tail_cond_steer_tail_args
      ((Vector.range m).map (.tail_arg · []))
      ((Vector.range m).map .final_tail_arg)
    ∈ pc₂.proc.atoms
  := by grind
  have hsteps₅ : Dataflow.Config.Step.IORestrictedStep pc _ _
    := .tail_tau (by simp) hsteps₄
      (Dataflow.Config.Step.step_steer
        hmem_steer_tail_args
        hpop_tail_cond_steer_tail_args
        hpop_tail_arg_vals
        (InterpConsts.unique_fromBool_toBool _))
  simp at hsteps₅
  replace ⟨pc₃, hpc₃, hsteps₅⟩ := exists_eq_left.mpr hsteps₅
  -- Step 7: Fire the first `carry` in `compileFn`.
  have ⟨chans₆, hpop_tail_cond_steer_tail_args, hchans₆⟩ := pop_val_singleton
    (map := pc₃.chans)
    (name := .tail_cond_carry)
    (val := InterpConsts.fromBool false)
    (by
      simp [hpc₃, hchans₅, hchans₄, hpc₂, hchans₃, hchans₂, hpc₁,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go])
  have hmem_carry :
    pc₃.proc.atoms = [] ++ [compileFn.initCarry ec.fn carryInLoop] ++ rest
  := by simp [hpc₃, hpc₂, hpc₁, hatoms]
  simp only [compileFn.initCarry, hcarryInLoop] at hmem_carry
  have hsteps₆ : Dataflow.Config.Step.IORestrictedStep pc _ _
    := .tail_tau (by simp) hsteps₅
      (Dataflow.Config.Step.step_carry_decider
        hmem_carry
        hpop_tail_cond_steer_tail_args
        (InterpConsts.unique_fromBool_toBool _))
  simp at hsteps₆
  -- Step 8: Make the final transition to emit `.output` label
  have ⟨chans₇, destVals', hpop_final_dest_vals, hchans₇, hdest_vals⟩ :=
    pop_vals_singleton
    (map := chans₆)
    (names := (Vector.range n).map .final_dest)
    (λ name val =>
      match name with
      | .final_dest i => ∃ (h : i < n), val = destVals[i]
      | _ => False)
    (by
      simp [Vector.toList_map, Vector.toList_range]
      apply List.Nodup.map _ List.nodup_range
      simp [Function.Injective])
    (by
      intros name hname
      simp at hname
      replace ⟨i, h₂, hname⟩ := hname
      simp [← hname, hchans₆, hpc₃, hchans₅, hchans₄,
        hpc₂, hchans₃, hchans₂, hpc₁, hchans₁, intermChans,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        final_dest_finIdxOf?_index h₂, h₂, retValsToExprOutputs])
  replace hdest_vals : destVals = destVals' := by
    symm
    apply Vector.toList_inj.mp
    apply List.right_unique_forall₂' _ hdest_vals
    · apply List.forall₂_iff_get.mpr
      simp [Vector.toList_map, Vector.toList_range]
    · simp [Relator.RightUnique]
      intros a b c hb hc
      split at hb <;> simp at hc
      replace ⟨_, hb⟩ := hb
      replace ⟨_, hc⟩ := hc
      simp [hc, hb]
  subst hdest_vals
  have hsteps₇ : Dataflow.Config.Step.IORestrictedStep pc _ _
    := .tail_non_tau (by simp) hsteps₆
      (Dataflow.Config.Step.step_output
        (by
          simp [hpc₃, hpc₂, hpc₁, hsim.outputs]
          apply hpop_final_dest_vals))
  replace ⟨pc', hpc', hsteps₇⟩ := exists_eq_left.mpr hsteps₇
  apply hsteps₇.eq_rhs
  simp [hpc', hpc₃, hpc₂, hpc₁]
  constructor
  · simp [compileFn.initCarry]
  -- Prove that the final channel maps match
  · funext name
    simp [hpc₃, hchans₇, hchans₆, hchans₅, hchans₄, hpc₂, hchans₃,
      hchans₂, hpc₁, hchans₁,
      varsToChans, VarMap.empty, VarMap.getVar]
    cases name with
    | input | var | switch_cond | merge_cond | final_tail_arg =>
      simp [List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go,
        intermChans, compileExpr.exprOutputs]
      rw [Vector.finIdxOf?_eq_none_iff.mpr (by simp)]
    | dest | tail_arg =>
      simp [List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go, intermChans]
      intros h₁
      simp [
        exprOutputs_finIdxOf?_no_match_dest h₁,
        exprOutputs_finIdxOf?_no_match_tail_args h₁,
      ]
    | tail_cond =>
      simp [List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go, intermChans]
      intros h₁
      simp [exprOutputs_finIdxOf?_no_match_tail_cond h₁]
    | tail_cond_carry | tail_cond_steer_dests | tail_cond_steer_tail_args => simp
    | final_dest =>
      simp
      intros hlt
      simp [final_dest_finIdxOf?_none hlt,
        List.finIdxOf?, List.findFinIdx?, List.findFinIdx?.go, intermChans]

theorem sim_step_ret
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hexpr : ec.cont = .expr (.ret vars)) :
  ∃ pc',
    Config.Step.IORestrictedStep pc l pc' ∧
    ∃ gs', SimRel gs' ec' pc' := by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, ⟨_, hwf_expr⟩, hcurrent⟩ := hcont _ hexpr
  simp [hcarryInLoop] at hatoms
  have hsteps := sim_step_ret_exec_dataflow hsim hstep hexpr hatoms
  cases hstep with
  | step_init hexpr' | step_br hexpr' | step_tail hexpr' | step_op hexpr' =>
    simp [hexpr] at hexpr'
  | step_ret hexpr' hvars =>
    rename_i retVals vars'
    simp [hexpr] at hexpr'
    subst hexpr'
    cases hwf_expr with | wf_ret hvars_nodup =>
    exact ⟨_, hsteps,
      .empty,
      by
        and_intros
        · simp
        · simp
        · simp [VarMap.empty, VarMap.getVar]
        · simp [OrderedPathConds]
        · simp
        · simp [HasMerges]
        · exact hsim.wf_fn.1
        · exact hsim.wf_fn.2
        · exact hsim.inputs
        · exact hsim.outputs
        · simp [compileFn.initCarry, HasCompiledProcs]
          exact hcomp_fn
    ⟩

end Wavelet.Compile.Fn
