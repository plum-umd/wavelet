import Mathlib.Data.Vector.Basic

import Wavelet.Op
import Wavelet.LTS
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Lemmas

import Wavelet.Simulation.Invariants
import Wavelet.Simulation.Lemmas

namespace Wavelet.Simulation.Init

open Wavelet.Op Wavelet.LTS Wavelet.Seq Wavelet.Dataflow Wavelet.Compile
open Invariants Lemmas

/--
Initial `Seq` and `Dataflow` configurations satisfy
the simulation relation (modulo some setup steps).
-/
theorem sim_step_init
  [Arity Op] [DecidableEq χ] [InterpConsts V] [InterpOp Op V E S]
  (fn : Fn Op χ m n)
  (args : Vector V m)
  (state : S)
  (hnz : m > 0 ∧ n > 0)
  (hwf_fn : fn.WellFormed) :
  ∃ pc',
    Dataflow.Config.StepPlus (E := E)
      (Dataflow.Config.init (compileFn hnz fn) state args) .ε pc' ∧
    SimRel hnz
      (Seq.Config.init fn state args)
      pc'
:= by
  -- Abbreviations
  generalize hpc₀ :
    Dataflow.Config.init (compileFn hnz fn) state args = pc₀
  simp [Dataflow.Config.init] at hpc₀
  generalize hchans₀ :
    ChanMap.pushVals (compileFn.inputs fn) args ChanMap.empty
    = chans₀
  replace hpc₀ := hpc₀.symm
  replace hchans₀ := hchans₀.symm
  simp [compileFn] at hpc₀
  rw [← hchans₀] at hpc₀
  -- Simplify initial pushes to the carry gate
  rw [push_vals_empty] at hchans₀
  rotate_left
  · simp [compileFn.inputs, Vector.toList_map]
    apply List.Nodup.map
    · simp [Function.Injective]
    · exact hwf_fn.1
  · simp [ChanMap.empty]
  -- Step 1: run the first carry gate to initialize variables
  have ⟨chans₁, args', hpop_args, hchans₁, hargs⟩ :=
    pop_vals_singleton _ _
    (map := pc₀.chans)
    (names := compileFn.inputs fn)
    (λ name val => chans₀ name = [val])
    (by
      simp [compileFn.inputs, Vector.toList_map]
      apply List.Nodup.map
      · simp [Function.Injective]
      · exact hwf_fn.1)
    (by
      intros name hname
      simp [compileFn.inputs] at hname
      replace ⟨var, hmem_var, hname⟩ := hname
      simp [← hname, hpc₀, hchans₀, compileFn.inputs]
      split <;> rename_i h₁
      · simp
      · have := Option.eq_none_iff_forall_ne_some.mpr h₁
        simp at this
        exact False.elim (this hmem_var))
  have : args = args' := by
    symm
    apply Vector.toList_inj.mp
    apply List.right_unique_forall₂' _ hargs
    · simp [compileFn.inputs, hchans₀]
      apply List.forall₂_iff_get.mpr
      simp
      intros i hi₁ hi₂
      simp [input_finIdxOf?_index hwf_fn.1]
    · simp [Relator.RightUnique]
      intros a b c hb hc
      simp [hb] at hc
      exact hc
  subst this
  have hmem_carry :
    pc₀.proc.atoms =
      [] ++ [compileFn.initCarry fn false]
      ++ (compileFn.bodyComp hnz fn ++ compileFn.resultSteers m n)
  := by simp [hpc₀]
  simp only [compileFn.initCarry] at hmem_carry
  have hsteps :
    Dataflow.Config.StepPlus (E := E) pc₀ _ _
  := .single
    (Dataflow.Config.Step.step_carry_init
      hmem_carry
      hpop_args)
  rw [push_vals_empty] at hsteps
  rotate_left
  · simp [Vector.toList_map]
    apply List.Nodup.map
    · simp [Function.Injective]
    · exact hwf_fn.1
  · intros name hname
    simp at hname
    have ⟨var, hmem_var, hname⟩ := hname
    simp [← hname, hchans₁, hpc₀, hchans₀, compileFn.inputs, ChanMap.empty]
  simp at hsteps
  replace ⟨pc', hpc', hsteps⟩ := exists_eq_left.mpr hsteps
  -- Prove the simulation relation
  exists pc'
  constructor
  · exact hsteps
  · simp [Seq.Config.init, hpc', hpc₀]
    and_intros
    · simp
    · funext name
      simp [varsToChans]
      cases name with
      | var v pathConds =>
        simp
        if h₁ : pathConds = [] then
          simp [h₁]
          split <;> rename_i h₂
          · simp [Vector.get] at h₂
            simp [← h₂.1, var_map_fromList_get_vars_index hwf_fn.1]
          · have := Option.eq_none_iff_forall_ne_some.mpr h₂
            simp at this
            split <;> rename_i h₃
            · have h₄ := var_map_fromList_get_vars.mpr ⟨_, h₃⟩
              exact False.elim (this h₄)
            · simp [hchans₁, hpc₀, hchans₀, compileFn.inputs, ChanMap.empty]
        else
          simp [h₁, hchans₁, hpc₀, hchans₀, compileFn.inputs, ChanMap.empty]
      | input v =>
        simp [hchans₁, compileFn.inputs, hpc₀, hchans₀]
        intros hv
        split <;> rename_i h₁
        · simp [Vector.get] at h₁
          simp [← h₁.1] at hv
        · simp [ChanMap.empty]
      | _ => simp [hchans₁, compileFn.inputs, hpc₀, hchans₀, ChanMap.empty]
    · simp [hwf_fn.1]
    · simp
      intros var
      apply var_map_fromList_get_vars
    · simp [OrderedPathConds]
    · simp
    · simp [HasMerges]
    · exact hwf_fn.1
    · exact hwf_fn.2
    · simp [HasCompiledProcs, compileFn, compileFn.initCarry, compileFn.bodyComp]
      constructor
      · exists []
        simp
      · exact hwf_fn.2

end Wavelet.Simulation.Init
