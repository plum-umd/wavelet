import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Batteries.Data.Vector.Lemmas

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Fn.Simulation.Invariants
import Wavelet.Compile.Fn.Lemmas

/-! Simulation in the case of initialization. -/

namespace Wavelet.Compile.Fn

open Semantics Seq Dataflow Compile Fn

private theorem init_chans_empty
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {ec : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hinit : ec.cont = .init) :
  pc.chans = ChanMap.empty := by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, _, _, hdefined_vars, hpath_conds⟩ := hret hinit
  simp [hsim.vars_to_chans]
  funext name
  simp [ChanMap.empty, varsToChans, hpath_conds]
  cases name with
  | var v pathConds =>
    simp
    intros h₁
    split <;> rename_i h₂
    · have := hsim.get_var_to_defined_vars ⟨_, h₂⟩
      simp [hdefined_vars] at this
    · rfl
  | _ => rfl

/--
Initial `Seq` and `Dataflow` configurations satisfy
the simulation relation (modulo some setup steps).
-/
theorem sim_step_init
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {l : Label Op V m n}
  {ec ec' : Seq.Config Op χ V m n}
  {pc : Dataflow.Config Op (ChanName χ) V m n}
  {gs : GhostState χ}
  (hsim : SimRel gs ec pc)
  (hstep : Config.Step ec l ec')
  (hinit : ec.cont = .init) :
  ∃ pc',
    Dataflow.Config.Step.IORestrictedStep pc l pc' ∧
    ∃ gs', SimRel gs' ec' pc' := by
  have ⟨
    rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
    hatoms, hcomp_fn, hrest, hret, hcont,
  ⟩ := hsim.has_compiled_procs
  have ⟨hcarryInLoop, _, _, hdefined_vars, hpath_conds⟩ := hret hinit
  cases hstep with
  | step_ret hexpr | step_tail hexpr | step_op hexpr | step_br hexpr =>
    simp [hinit] at hexpr
  | step_init hexpr =>
  rename_i args
  have hsteps₁ : Dataflow.Config.Step.IORestrictedStep pc _ _
    := .single (Dataflow.Config.Step.step_init (args := args))
  -- Simplify initial pushes to the carry gate
  rw [push_vals_empty] at hsteps₁
  rotate_left
  · simp [hsim.inputs, Vector.toList_map]
    apply List.Nodup.map
    · simp [Function.Injective]
    · exact hsim.wf_fn.1
  · simp [init_chans_empty hsim hinit, ChanMap.empty]
  replace ⟨pc₁, hpc₁, hsteps₁⟩ := exists_eq_left.mpr hsteps₁
  -- Step 1: run the first carry gate to initialize variables
  have ⟨chans₁, args', hpop_args, hchans₁, hargs⟩ :=
    pop_vals_singleton
    (map := pc₁.chans)
    (names := compileFn.inputs ec.fn)
    (λ name val => pc₁.chans name = [val])
    (by
      simp [compileFn.inputs, Vector.toList_map]
      apply List.Nodup.map
      · simp [Function.Injective]
      · exact hsim.wf_fn.1)
    (by
      intros name hname
      simp [compileFn.inputs] at hname
      replace ⟨var, hmem_var, hname⟩ := hname
      simp [← hname, hpc₁, hsim.inputs]
      split <;> rename_i h₁
      · simp
      · have := Option.eq_none_iff_forall_ne_some.mpr h₁
        simp at this
        exact False.elim (this hmem_var))
  have : args = args' := by
    symm
    apply Vector.toList_inj.mp
    apply List.right_unique_forall₂' _ hargs
    · simp [compileFn.inputs, hpc₁, hsim.inputs]
      apply List.forall₂_iff_get.mpr
      simp
      intros i hi₁ hi₂
      simp [input_finIdxOf?_index (hlt := hi₂) hsim.wf_fn.1]
    · simp [Relator.RightUnique]
      intros a b c hb hc
      simp [hb] at hc
      exact hc
  subst this
  have hmem_carry :
    pc₁.proc.atoms =
      [] ++ [compileFn.initCarry ec.fn .popLeft]
      ++ (compileFn.bodyComp ec.fn ++ compileFn.resultSteers m n)
  := by
    simp only [hpc₁, hatoms, hcarryInLoop, ← hcomp_fn]
    simp [compileFn]
  simp only [compileFn.initCarry] at hmem_carry
  have hsteps₂ :
    Dataflow.Config.Step.IORestrictedStep pc _ _
  := .tail_tau (by simp) hsteps₁
    (Dataflow.Config.Step.step_carry_left
      hmem_carry
      hpop_args)
  rw [push_vals_empty] at hsteps₂
  rotate_left
  · simp [Vector.toList_map]
    apply List.Nodup.map
    · simp [Function.Injective]
    · exact hsim.wf_fn.1
  · intros name hname
    simp at hname
    have ⟨var, hmem_var, hname⟩ := hname
    simp [← hname, hchans₁, hpc₁, compileFn.inputs, hsim.inputs]
    simp [init_chans_empty hsim hinit, ChanMap.empty]
  simp at hsteps₂
  exact ⟨_, hsteps₂,
    GhostState.init ec.fn.params.toList,
    by
      simp only [hpc₁]
      and_intros
      · simp
        funext name
        simp [varsToChans]
        cases name with
        | var v pathConds =>
          simp
          if h₁ : pathConds = [] then
            simp [h₁]
            split <;> rename_i h₂
            · simp [Vector.get] at h₂
              simp [← h₂.1, var_map_fromList_get_vars_index hsim.wf_fn.1]
            · have := Option.eq_none_iff_forall_ne_some.mpr h₂
              simp at this
              split <;> rename_i h₃
              · have h₄ := var_map_fromList_get_vars.mpr ⟨_, h₃⟩
                exact False.elim (this h₄)
              · simp [hchans₁, hpc₁, compileFn.inputs, hsim.inputs,
                  init_chans_empty hsim hinit, ChanMap.empty]
          else
            simp [h₁, hchans₁, hpc₁, hsim.inputs, compileFn.inputs,
              init_chans_empty hsim hinit, ChanMap.empty]
        | input =>
          simp [hchans₁, hpc₁, compileFn.inputs, hsim.inputs,
            init_chans_empty hsim hinit, ChanMap.empty]
          intros h
          simp [input_finIdxOf?_none h]
        | _ =>
          simp [hchans₁, hpc₁, compileFn.inputs, hsim.inputs,
            init_chans_empty hsim hinit, ChanMap.empty]
      · simp [hsim.wf_fn.1]
      · simp
        intros var
        apply var_map_fromList_get_vars
      · simp [OrderedPathConds]
      · simp
      · simp [HasMerges]
      · exact hsim.wf_fn.1
      · exact hsim.wf_fn.2
      · exact hsim.inputs
      · exact hsim.outputs
      · simp [HasCompiledProcs, compileFn.initCarry, hcomp_fn, hrest]
        simp [hrest, compileFn] at hcomp_fn
        simp [hcomp_fn]
        constructor
        · exists [], compileFn.resultSteers m n
          simp [← hcomp_fn, compileFn.bodyComp]
        · exact hsim.wf_fn.2
  ⟩

end Wavelet.Compile.Fn
