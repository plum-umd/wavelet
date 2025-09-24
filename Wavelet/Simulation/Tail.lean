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

set_option maxHeartbeats 300000

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

end Wavelet.Simulation.Tail
