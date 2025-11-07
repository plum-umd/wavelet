import Mathlib.Data.List.Lattice

import Wavelet.Determinacy.Defs
import Wavelet.Determinacy.Congr
import Wavelet.Determinacy.DisjointTokens
import Wavelet.Determinacy.Determinism

/-! Confluence properties of various transition systems. -/

namespace Wavelet.Determinacy

open Semantics Dataflow

/--
Without considering shared operator states, and when restricted
to silent/yield labels, a well-formed `Proc` has a strongly
confluent (and thus confluent) semantics, modulo a given
equivalence relation on values to capture certain non-determinism
in the operator semantics.
-/
theorem proc_indexed_strong_confl_at_mod
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (EqV : V → V → Prop) [IsRefl V EqV]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.IndexedStep.StronglyConfluentAtMod
      (λ (i, l) (i', l') =>
        i = i' → Label.IsYieldOrSilentAndDetMod EqV l l')
      (Config.EqMod EqV)
      (λ (i, l) (i', l') => i = i' ∧ Label.EqMod EqV l l')
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases l₁ with ⟨i, l₁⟩
  rcases l₂ with ⟨j, l₂⟩
  -- have ⟨hlabel₁, hlabel₂, hyield_det⟩ := hcompat
  have ⟨_, _, ⟨haff_nodup, haff_disj⟩, _⟩ := haff
  by_cases hij : i = j
  · left
    subst hij
    simp at hcompat
    have := Config.IndexedStep.unique_index_mod (EqV := EqV) hstep₁ hstep₂ hcompat
    simp
    exact this
  · -- Keep some acronyms so that they don't get expanded
    generalize hs₁' : s₁' = s₁''
    generalize hs₂' : s₂' = s₂''
    cases hstep₁ <;> cases hstep₂
    -- Commute two `step_op`s
    case neg.step_op.step_op =>
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hpop₁ hi hget_i
        op₂ inputs₂ outputs₂ inputVals₂ outputVals₂ chans₂' hpop₂ hj hget_j
      right
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj ⟨i, hi⟩ ⟨j, hj⟩ (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_op
          (outputVals := outputVals₂)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁']; exact hget_j)
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by simp [← hs₂']; exact hi)
          (by simp [← hs₂']; exact hget_i)
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute `step_op` and `step_async`
    case neg.step_op.step_async =>
      right
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hpop₁ hi hget_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' hinterp₂ hpop₂ hj hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        hinterp₂.input_sublist.subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        hinterp₂.output_sublist.subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁']; exact hget_j)
          hinterp₂
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by simp [← hs₂']; exact hi)
          (by simp [← hs₂', Ne.symm hij]; exact hget_i)
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute `step_async` and `step_op`
    case neg.step_async.step_op =>
      right
      rename_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' hinterp₂ hpop₂ hi hget_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hpop₁ hj hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        hinterp₂.input_sublist.subset hdisj_inputs.symm
      replace hdisj_outputs := List.disjoint_of_subset_right
        hinterp₂.output_sublist.subset hdisj_outputs.symm
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_async (i := i)
          (by simp [← hs₂']; exact hi)
          (by simp [← hs₂']; exact hget_i)
          hinterp₂
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁', hij]; exact hget_j)
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₂'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute two `step_async`s
    case neg.step_async.step_async =>
      right
      rename_i
        _ _ aop₁ aop₁' allInputs₁ allOutputs₁
        inputs₁ inputVals₁ outputs₁ outputVals₁ chans₁' hinterp₁ hpop₁ hi hget_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' hinterp₂ hpop₂ hj hget_j
      -- Firing two different async ops
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_left
        hinterp₁.input_sublist.subset hdisj_inputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        hinterp₂.input_sublist.subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_left
        hinterp₁.output_sublist.subset hdisj_outputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        hinterp₂.output_sublist.subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₁', hj])
          (by simp [← hs₁', hij]; exact hget_j)
          hinterp₂
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_async (i := i)
          (by simp [← hs₂', hi])
          (by simp [← hs₂', Ne.symm hij]; exact hget_i)
          hinterp₁
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁',
        (by
          apply Lts.Step.eq_rhs hstep₂'
          rfl),
        (by
          rw [List.set_comm]
          · simp [IsRefl.refl]
          · exact hij)
      ⟩

theorem proc_indexed_strong_confl_at
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.IndexedStep.StronglyConfluentAt
      (λ (i, l) (i', l') => i = i' → Label.IsYieldOrSilentAndDet l l')
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have := proc_indexed_strong_confl_at_mod Eq haff hstep₁ hstep₂
    (by simp at hcompat ⊢; exact hcompat)
  simp at this
  cases this with
  | inl h =>
    left
    cases l₁; cases l₂
    simp at h
    simp [h]
  | inr h =>
    right
    exact h

/--
Similar to `proc_indexed_strong_confl_at_mod` but on the
main stepping relation.
-/
theorem proc_strong_confl_at_mod
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (EqV : V → V → Prop)
  [hrefl : IsRefl V EqV]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.Step.StronglyConfluentAtMod
      (Label.IsYieldOrSilentAndDetMod EqV)
      (Config.EqMod EqV)
      (Label.EqMod EqV)
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨i, hstep₁'⟩ := Config.IndexedStep.from_step_yield_or_tau
    hcompat.1 hstep₁
  have ⟨j, hstep₂'⟩ := Config.IndexedStep.from_step_yield_or_tau
    hcompat.2.1 hstep₂
  have := proc_indexed_strong_confl_at_mod
    EqV haff hstep₁' hstep₂'
    (by simp [hcompat])
  cases this with
  | inl h => simp [h]
  | inr h =>
    right
    have ⟨_, _, hstep₁'', hstep₂'', heq⟩ := h
    exact ⟨_, _,
      Config.IndexedStep.to_step_yield_or_tau hstep₁'',
      Config.IndexedStep.to_step_yield_or_tau hstep₂'',
      heq,
    ⟩

theorem proc_strong_confl_at
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.Step.StronglyConfluentAt
      Label.IsYieldOrSilentAndDet
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨hcompat₁, hcompat₂, hcompat₃⟩ := hcompat
  have := proc_strong_confl_at_mod Eq haff hstep₁ hstep₂
    (by simp [hcompat])
  simp at this
  exact this

/-- If the label pair generated by a guarded semantics
satisfies `Label.IsYieldOrSilentAndDet`, then the original
unchecked label must satisfy `Label.IsYieldOrSilentAndDet EqModGhost` -/
private theorem invert_compat_spec_guard
  [Arity Op] [PCM T] [PCM.Cancellative T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁' l₂' : Label Op V m n}
  {l₁ l₂ : LabelWithSpec opSpec ioSpec}
  (hguard₁ : opSpec.Guard ioSpec l₁ l₁')
  (hguard₂ : opSpec.Guard ioSpec l₂ l₂')
  (hcompat : Label.IsYieldOrSilentAndDet l₁' l₂') :
    Label.IsYieldOrSilentAndDet l₁ l₂
  := by
  simp [Label.IsYieldOrSilentAndDet, Label.Deterministic]
  cases hguard₁ <;> cases hguard₂ <;> simp
  any_goals
    simp [Label.IsYieldOrSilentAndDet] at hcompat
  case spec_join.spec_join =>
    rename_i
      k₁ l₁ req₁ rem₁ _ toks₁ vals₁ outputs₁ houtputs₁₀ houtputs₁₁ hsum₁
      k₂ l₂ req₂ rem₂ _ toks₂ vals₂ outputs₂ houtputs₂₀ houtputs₂₁ hsum₂
    intros op inputs outputs₁' outputs₂' hop₁ hinputs₁' houtputs₁' hop₂ hinputs₂' houtputs₂'
    cases op <;> simp at hop₁
    have ⟨h₁, h₂, h₃⟩ := hop₁
    subst h₁; subst h₂; subst h₃
    simp at hop₂
    have ⟨h₁, h₂, h₃⟩ := hop₂
    subst h₁; subst h₂; subst h₃
    simp at hinputs₁'
    simp [← hinputs₁'] at hinputs₂'
    have ⟨h₁, h₂⟩ := Vector.append_inj hinputs₂'
    replace h₁ := Vector.inj_map (by simp [Function.Injective]) h₁
    replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂
    subst h₁; subst h₂
    have heq_rem : rem₁ = rem₂ := by
      simp [← hsum₂] at hsum₁
      exact PCM.Cancellative.cancel_left hsum₁
    subst heq_rem
    simp at houtputs₁' houtputs₂'
    simp [← houtputs₁', ← houtputs₂']
    apply Vector.ext
    intros i hi
    match h : i with
    | 0 => simp [houtputs₁₀, houtputs₂₀]
    | 1 => simp [houtputs₁₁, houtputs₂₁]
  case spec_yield.spec_yield =>
    rename_i
      op₁ ghost₁ inputs₁ outputs₁ hpre₁
      op₂ ghost₂ inputs₂ outputs₂ hpre₂
    intros op inputs outputs₁' outputs₂'
      hop₁ hinputs₁' houtputs₁'
      hop₂ hinputs₂' houtputs₂'
    cases op <;> simp at hop₁
    have ⟨h₁, h₂⟩ := hop₁
    subst h₁ h₂
    simp at hop₂
    have ⟨h₁, h₂⟩ := hop₂
    subst h₁ h₂
    simp only [heq_eq_eq] at *
    simp [← hinputs₁'] at hinputs₂'
    replace ⟨heq_inputs, hinputs₂'⟩ := hinputs₂'
    subst heq_inputs
    simp [← houtputs₁', ← houtputs₂', Vector.push_eq_push]
    simp [Label.Deterministic] at hcompat
    have heq_outputs : outputs₁ = outputs₂ := by
      apply hcompat
      any_goals rfl
    simp [heq_outputs]
  all_goals
    intros op
    cases op <;> simp

/-- Similar to `invert_compat_triv_guard` but for `OpSpec.TrivGuard`. -/
private theorem invert_compat_triv_guard
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {l₁' l₂' : Label Op V m n}
  {l₁ l₂ : LabelWithSpec opSpec ioSpec}
  (hguard₁ : opSpec.TrivGuard ioSpec l₁ l₁')
  (hguard₂ : opSpec.TrivGuard ioSpec l₂ l₂')
  (hcompat : Label.IsYieldOrSilentAndDet l₁' l₂') :
    Label.IsYieldOrSilentAndDetMod EqModGhost l₁ l₂
  := by
  cases l₁ <;> cases l₂
    <;> cases hguard₁
    <;> cases hguard₂
    <;> simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at hcompat
    <;> simp [Label.IsYieldOrSilentAndDetMod, Label.DeterministicMod]
  any_goals
    intros op
    cases op <;> simp
  case yield.yield.triv_yield.triv_yield.op =>
    rename_i
      op₁ ghost₁ inputs₁ outputs₁ tok₁₁ tok₁₂
      op₂ ghost₂ inputs₂ outputs₂ tok₂₁ tok₂₂ _ _
    intros inputs' outputs₁' outputs₂'
      hghost₁ hop₁ hinputs₁' houtputs₁'
      hghost₂ hop₂ hinputs₂' houtputs₂'
    subst hop₁ hop₂ hghost₁ hghost₂
    have heq_inputs : inputs₁ = inputs₂ := by
      simp at hinputs₁' hinputs₂'
      simp [← hinputs₁'] at hinputs₂'
      simp [hinputs₂']
    subst heq_inputs
    have heq_outputs : outputs₁ = outputs₂ := by
      apply hcompat
      any_goals rfl
    subst heq_outputs
    simp at houtputs₁' houtputs₂'
    simp [← houtputs₁', ← houtputs₂']
    apply Vector.forall₂_to_forall₂_push_toList
    · simp [EqModGhost]
    · simp [EqModGhost]
  case yield.yield.triv_join.triv_join.join =>
    intros
    rename_i houtputs₁ _ _ _ _ houtputs₂
    simp [← houtputs₁, ← houtputs₂, Vector.toList_map, EqModGhost]
    apply List.forall₂_iff_get.mpr
    simp

theorem proc_indexed_guarded_spec_strong_confl_at
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec ioSpec χ}
  (haff : s.proc.AffineChan) :
    (Config.IdxGuardStep opSpec ioSpec).StronglyConfluentAt
      (λ (i₁, l₁) (i₂, l₂) => i₁ = i₂ → Label.IsYieldOrSilentAndDet l₁ l₂)
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAt _ _ _ :=
    proc_indexed_strong_confl_at haff
  have hconfl_guard : Lts.StronglyConfluentAt _ _ _ :=
    Lts.guarded_strong_confl_at
      (Guard := IndexedGuard (opSpec.Guard ioSpec))
      _ _ (λ hguard₁ hguard₂ heq => by
        have ⟨hguard₁⟩ := hguard₁
        have ⟨hguard₂⟩ := hguard₂
        have := congr_eq_spec_guard hguard₁ hguard₂
        simp [heq] at this
        simp [heq, this]) hconfl_base
  apply Lts.strong_confl_at_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      IndexedGuard (opSpec.Guard ioSpec) l₁ l₁' →
      IndexedGuard (opSpec.Guard ioSpec) l₂ l₂' →
      l₁.1 = l₂.1 → Label.IsYieldOrSilentAndDet l₁.2 l₂.2)
  · intros
    rename_i hguard₁ hguard₂ heq
    have ⟨hguard₁⟩ := hguard₁
    have ⟨hguard₂⟩ := hguard₂
    apply invert_compat_spec_guard hguard₁ hguard₂
    rename_i hcompat
    simp at hcompat
    exact hcompat heq
  · exact hconfl_guard

theorem proc_guarded_spec_strong_confl_at
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec ioSpec χ}
  (haff : s.proc.AffineChan) :
    (Config.GuardStep opSpec ioSpec).StronglyConfluentAt
      Label.IsYieldOrSilentAndDet
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAt _ _ _ :=
    proc_strong_confl_at haff
  have hconfl_guard : Lts.StronglyConfluentAt _ _ _ :=
    Lts.guarded_strong_confl_at
      (Guard := opSpec.Guard ioSpec)
      _ _ congr_eq_spec_guard hconfl_base
  apply Lts.strong_confl_at_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      opSpec.Guard ioSpec l₁ l₁' →
      opSpec.Guard ioSpec l₂ l₂' →
      Label.IsYieldOrSilentAndDet l₁ l₂)
  · intros
    apply invert_compat_spec_guard
    all_goals assumption
  · exact hconfl_guard

theorem proc_indexed_unguarded_strong_confl_at_mod
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (s : ConfigWithSpec opSpec ioSpec χ)
  (haff : s.proc.AffineChan) :
    (Config.IdxTrivStep opSpec ioSpec).StronglyConfluentAtMod
      (λ (i, l) (i', l') =>
        i = i' → Label.IsYieldOrSilentAndDet l l')
      (Config.EqMod EqModGhost)
      Eq s
  := by
  have hconfl_base : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    proc_indexed_strong_confl_at_mod EqModGhost haff
  simp at hconfl_base
  have hconfl_guard : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    Lts.guarded_strong_confl_at_mod
      (Guard := IndexedGuard (opSpec.TrivGuard ioSpec))
      (EqS := Config.EqMod EqModGhost)
      (EqL := λ (i, l) (i', l') => i = i' ∧ Label.EqMod EqModGhost l l')
      (EqL' := Eq)
      (Compat := λ (i, l) (i', l') => i = i' → Label.IsYieldOrSilentAndDetMod EqModGhost l l')
      (lts := Config.IndexedStep)
      (c := s)
      (by
        intros
        rename_i hguard₁ hguard₂ heq
        rcases hguard₁ with ⟨hguard₁⟩
        rcases hguard₂ with ⟨hguard₂⟩
        simp at heq
        simp [heq]
        apply congr_eq_mod_ghost_triv_guard hguard₁ hguard₂ heq.2)
      hconfl_base
  apply Lts.strong_confl_at_mod_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      (IndexedGuard (opSpec.TrivGuard ioSpec)) l₁ l₁' →
      (IndexedGuard (opSpec.TrivGuard ioSpec)) l₂ l₂' →
      l₁.1 = l₂.1 → Label.IsYieldOrSilentAndDetMod EqModGhost l₁.2 l₂.2)
  · intros l₁' l₂' hcompat
    cases l₁'
    cases l₂'
    intros _ _ hguard₁ hguard₂ heq
    rcases hguard₁ with ⟨hguard₁⟩
    rcases hguard₂ with ⟨hguard₂⟩
    simp at heq hcompat ⊢
    apply invert_compat_triv_guard hguard₁ hguard₂ (hcompat heq)
  · exact hconfl_guard

theorem proc_unguarded_strong_confl_at_mod
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (s : ConfigWithSpec opSpec ioSpec χ)
  (haff : s.proc.AffineChan) :
    (Config.TrivStep opSpec ioSpec).StronglyConfluentAtMod
      Label.IsYieldOrSilentAndDet
      (Config.EqMod EqModGhost)
      Eq
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    proc_strong_confl_at_mod EqModGhost haff
  have hconfl_guard : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    Lts.guarded_strong_confl_at_mod
      (Guard := opSpec.TrivGuard ioSpec)
      (EqS := Config.EqMod EqModGhost)
      (EqL := Label.EqMod EqModGhost)
      (EqL' := Eq)
      (Compat := Label.IsYieldOrSilentAndDetMod EqModGhost)
      Config.Step s
      congr_eq_mod_ghost_triv_guard
      hconfl_base
  apply Lts.strong_confl_at_mod_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      opSpec.TrivGuard ioSpec l₁ l₁' →
      opSpec.TrivGuard ioSpec l₂ l₂' →
      Label.IsYieldOrSilentAndDetMod EqModGhost l₁ l₂)
  · intros
    apply invert_compat_triv_guard
    all_goals assumption
  · exact hconfl_guard

theorem proc_indexed_interp_guarded_strong_confl_at
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  -- Confluent and deterministic operator interpretation
  (hconfl : opSpec.Confluent opInterp)
  (hvalid : opSpec.Valid)
  (hdet : opInterp.Deterministic)
  -- Some required state invariants
  (haff : s.1.proc.AffineChan)
  (hdisj : s.1.DisjointTokens) :
    (Config.IdxInterpGuardStep opSpec ioSpec).StronglyConfluentAt
      (λ (_, l₁) (_, l₂) => l₁.isSilent ∧ l₂.isSilent)
      s
  := by
  rcases s with ⟨s, t⟩
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases s₁' with ⟨s₁', t₁'⟩
  rcases s₂' with ⟨s₂', t₂'⟩
  rcases l₁ with ⟨i₁, l₁⟩
  rcases l₂ with ⟨i₂, l₂⟩
  cases hstep₁ <;> cases hstep₂ <;> simp at hcompat
  case step_tau.step_tau hstep₁ hstep₂ =>
    have := proc_indexed_guarded_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq =>
      left
      simp at heq
      simp [heq]
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t)
      exact ⟨
        .step_tau hstep₁',
        .step_tau hstep₂'
      ⟩
  case step_tau.step_yield hstep₁ _ _ _ hstep₂ hstep_op₂ =>
    have := proc_indexed_guarded_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₂')
      exact ⟨
        .step_yield hstep₁' hstep_op₂,
        .step_tau hstep₂',
      ⟩
  case step_yield.step_tau _ _ _ _ hstep₁ hstep_op₁ hstep₂ =>
    have := proc_indexed_guarded_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₁')
      exact ⟨
        .step_tau hstep₁',
        .step_yield hstep₂' hstep_op₁,
      ⟩
  case step_yield.step_yield
    op₁ inputVals₁ _ hstep₁ hstep_op₁
    op₂ inputVals₂ _ hstep₂ hstep_op₂ =>
    have hconfl_sem := proc_indexed_guarded_spec_strong_confl_at haff hstep₁ hstep₂
      (by
        -- By `hdet`
        intros heq
        simp only [Label.IsYieldOrSilentAndDet, Label.Deterministic]
        and_intros
        · simp
        · simp
        · intros op inputVals outputVals₁ outputVals₂ heq_yield₁ heq_yield₂
          simp at heq_yield₁ heq_yield₂
          have ⟨heq_op₁, heq_inputs₁, heq_outputs₁⟩ := heq_yield₁
          have ⟨heq_op₂, heq_inputs₂, heq_outputs₂⟩ := heq_yield₂
          subst heq_op₁; subst heq_inputs₁; subst heq_outputs₁
          subst heq_op₂; subst heq_inputs₂; subst heq_outputs₂
          simp [hdet hstep_op₁ hstep_op₂])
    cases hconfl_sem with
    | inl heq =>
      left
      simp at heq
      have ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := heq
      subst h₁; subst h₂; subst h₃; subst h₄; subst h₅
      simp [hdet hstep_op₁ hstep_op₂]
    | inr h =>
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rename_i l₁ l₂
      cases l₁ <;> cases l₂
      case yield.yield =>
        rename_i
          op₁ inputVals₁ outputVals₁
          op₂ inputVals₂ outputVals₂
        cases hstep₁ with | step_op _ hget₁ hpop₁ =>
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        by_cases heq_ij : i₁ = i₂
        · -- Firing the same atom, so the result must be the same by `hdet`
          left
          subst heq_ij
          simp [hget₁] at hget₂
          have ⟨h₁, h₂, h₃⟩ := hget₂
          subst h₁ h₂ h₃
          cases hguard₁; cases hguard₂
          simp [hpop₁] at hpop₂
          have ⟨⟨h₄, h₅⟩, h₆⟩ := hpop₂
          subst h₄ h₆
          simp
          have ⟨h₇, h₈⟩ := hdet hstep_op₁ hstep_op₂
          subst h₈
          constructor
          · rfl
          · simp [h₇]
        · right
          have ⟨t', hstep_op₁', hstep_op₂'⟩ := hconfl hstep_op₁ hstep_op₂
            (by
              -- Firing different atoms, so the tokens must be disjoint by `DisjointTokens`.
              simp [OpSpec.CompatLabels]
              cases hguard₁ with | spec_yield hpre₁ =>
              rename Bool => ghost₁
              cases hguard₂ with | spec_yield hpre₂ =>
              rename Bool => ghost₂
              cases ghost₁ <;> cases ghost₂
              case true.true =>
                have := haff.atom_inputs_disjoint
                  ⟨i₁, by assumption⟩ ⟨i₂, by assumption⟩ (by simp [heq_ij])
                simp [hget₁, hget₂, AtomicProc.inputs] at this
                have := pop_vals_pop_vals_disj_preserves_pairwise hdisj.2.to_pairwise this hpop₁ hpop₂
                apply this (.inr (opSpec.pre op₁ inputVals₁)) (.inr (opSpec.pre op₂ inputVals₂))
                all_goals simp [WithSpec.opInputs]
              all_goals
                simp [hpre₁, hpre₂, PCM.disjoint,
                  PCM.Lawful.valid_zero,
                  hvalid.1]
            )
          replace ⟨s', hstep₁', hstep₂'⟩ := h
          exists (s', t')
          exact ⟨
            .step_yield hstep₁' hstep_op₁',
            .step_yield hstep₂' hstep_op₂',
          ⟩
      all_goals cases hguard₁ <;> cases hguard₂

-- TODO: reuse the theorem above to prove this
-- /--
-- Strong confluence of a `ProcWithSpec` when interpreted with
-- a sound and deterministic interpretation.

-- TODO: this is probably generalizable to a general confluent `Semantics`.
-- TODO: use `proc_indexed_interp_strong_confl_at` to prove this.
-- -/
-- theorem proc_interp_guarded_strong_confl_at
--   [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
--   [DecidableEq χ]
--   [InterpConsts V]
--   [opInterp : OpInterp Op V]
--   {opSpec : OpSpec Op V T}
--   {ioSpec : IOSpec V T m n}
--   {s : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
--   -- Confluent and deterministic op interpretation
--   (hconfl : OpSpec.Confluent opSpec opInterp)
--   (hdet : opInterp.Deterministic)
--   -- Some required state invariants
--   (haff : s.1.proc.AffineChan)
--   (hdisj : s.1.DisjointTokens) :
--     (Config.InterpGuardStep opSpec ioSpec).StronglyConfluentAt
--       (λ l₁ l₂ => l₁.isSilent ∧ l₂.isSilent)
--       s
--   := by
--   rcases s with ⟨s, t⟩
--   intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
--   rcases s₁' with ⟨s₁', t₁'⟩
--   rcases s₂' with ⟨s₂', t₂'⟩
--   cases hstep₁ <;> cases hstep₂ <;> simp at hcompat
--   case step_tau.step_tau hstep₁ hstep₂ =>
--     have := proc_guarded_spec_strong_confl_at haff hstep₁ hstep₂
--       (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
--     cases this with
--     | inl heq => simp [heq]
--     | inr h =>
--       right
--       replace ⟨s', hstep₁', hstep₂'⟩ := h
--       exists (s', t)
--       exact ⟨
--         .step_tau hstep₁',
--         .step_tau hstep₂'
--       ⟩
--   case step_tau.step_yield hstep₁ _ _ _ hstep₂ hstep_op₂ =>
--     have := proc_guarded_spec_strong_confl_at haff hstep₁ hstep₂
--       (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
--     cases this with
--     | inl heq => simp at heq
--     | inr h =>
--       right
--       replace ⟨s', hstep₁', hstep₂'⟩ := h
--       exists (s', t₂')
--       exact ⟨
--         .step_yield hstep₁' hstep_op₂,
--         .step_tau hstep₂',
--       ⟩
--   case step_yield.step_tau _ _ _ _ hstep₁ hstep_op₁ hstep₂ =>
--     have := proc_guarded_spec_strong_confl_at haff hstep₁ hstep₂
--       (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
--     cases this with
--     | inl heq => simp at heq
--     | inr h =>
--       right
--       replace ⟨s', hstep₁', hstep₂'⟩ := h
--       exists (s', t₁')
--       exact ⟨
--         .step_tau hstep₁',
--         .step_yield hstep₂' hstep_op₁,
--       ⟩
--   case step_yield.step_yield
--     op₁ inputVals₁ _ hstep₁ hstep_op₁
--     op₂ inputVals₂ _ hstep₂ hstep_op₂ =>
--     have hconfl_sem := proc_guarded_spec_strong_confl_at haff hstep₁ hstep₂
--       (by
--         -- By `hdet`
--         simp only [Label.IsYieldOrSilentAndDet, Label.Deterministic]
--         and_intros
--         · simp
--         · simp
--         · intros op inputVals outputVals₁ outputVals₂ heq_yield₁ heq_yield₂
--           simp at heq_yield₁ heq_yield₂
--           have ⟨heq_op₁, heq_inputs₁, heq_outputs₁⟩ := heq_yield₁
--           have ⟨heq_op₂, heq_inputs₂, heq_outputs₂⟩ := heq_yield₂
--           subst heq_op₁; subst heq_inputs₁; subst heq_outputs₁
--           subst heq_op₂; subst heq_inputs₂; subst heq_outputs₂
--           simp [hdet hstep_op₁ hstep_op₂])
--     cases hconfl_sem with
--     | inl heq =>
--       left
--       simp at heq
--       have ⟨⟨h₁, h₂, h₃⟩, h₄⟩ := heq
--       subst h₁; subst h₂; subst h₃
--       simp [h₄, hdet hstep_op₁ hstep_op₂]
--     | inr h =>
--       cases hstep₁ with | step hguard₁ hstep₁ =>
--       cases hstep₂ with | step hguard₂ hstep₂ =>
--       cases hguard₁ with | spec_yield =>
--       -- rename_i tok₁ tok₁'
--       cases hguard₂ with | spec_yield =>
--       -- rename_i tok₂ tok₂'
--       cases hstep₁ with | step_op hmem₁ hpop₁ =>
--       cases hstep₂ with | step_op hmem₂ hpop₂ =>
--       have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
--       have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem₂
--       by_cases heq_ij : i = j
--       · -- Firing the same atom, so the result must be the same by `hdet`
--         left
--         subst heq_ij
--         simp [hget_i] at hget_j
--         have ⟨h₁, h₂, h₃⟩ := hget_j
--         subst h₁; subst h₂; subst h₃
--         simp [hpop₁, Vector.push_eq_push] at hpop₂
--         have ⟨⟨h₄, h₅⟩, h₆⟩ := hpop₂
--         replace h₅ := Vector.inj_map (by simp [Function.Injective]) h₅
--         subst h₅; subst h₆
--         -- simp [h₄, htok₁', htok₂']
--         have ⟨h₇, h₈⟩ := hdet hstep_op₁ hstep_op₂
--         subst h₈
--         constructor
--         · rfl
--         · simp [h₇]
--       · right
--         have ⟨t', hstep_op₁', hstep_op₂'⟩ := hconfl hstep_op₁ hstep_op₂
--           (by
--             -- Firing different atoms, so the tokens must be disjoint by `DisjointTokens`.
--             simp [OpSpec.CompatLabels]
--             -- apply PCM.eq_congr_disj htok₁ htok₂
--             have := haff.atom_inputs_disjoint ⟨i, hi⟩ ⟨j, hj⟩ (by simp [heq_ij])
--             simp [hget_i, hget_j, AtomicProc.inputs] at this
--             have := pop_vals_pop_vals_disj_preserves_pairwise hdisj.2.to_pairwise this hpop₁ hpop₂
--             -- have := this (.inr _) (.inr _)
--             apply this (.inr (opSpec.pre op₁ inputVals₁)) (.inr (opSpec.pre op₂ inputVals₂))
--             all_goals simp)
--         replace ⟨s', hstep₁', hstep₂'⟩ := h
--         exists (s', t')
--         exact ⟨
--           .step_yield hstep₁' hstep_op₁',
--           .step_yield hstep₂' hstep_op₂',
--         ⟩

/-- If a terminating trace can be demonstrated in the indexed and guarded semantics,
then any step from the same initial state will converge to the same final state. -/
theorem proc_indexed_interp_guarded_terminal_confl
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hconfl : opSpec.Confluent opInterp)
  (hvalid : opSpec.Valid)
  (hdet : opInterp.Deterministic)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (hdisj : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.DisjointTokens) s)
  (htrace : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (_, l) => l.isYield ∨ l.isSilent) s₁.1)
  (hstep₂ : (Config.IdxInterpGuardStep opSpec ioSpec).Step s l s₂) :
    ∃ tr',
      (Config.IdxInterpGuardStep opSpec ioSpec).Star s₂ tr' s₁ ∧
      tr.length = tr'.length + 1
  := by
  have hl := proc_indexed_interp_guarded_step_label hstep₂
  induction htrace
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl =>
    match hstep₂ with
    | .step_tau hstep₂
    | .step_yield hstep₂ _ =>
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      cases hguard₂ <;> exact False.elim (hterm (by simp) hstep₂)
  | head hstep htail ih =>
    rename_i s s' l' tr'
    have hl' := proc_indexed_interp_guarded_step_label hstep
    have := proc_indexed_interp_guarded_strong_confl_at hconfl hvalid hdet
      haff.base hdisj.base hstep hstep₂ (by simp [hl, hl'])
    cases this with
    | inl h =>
      have ⟨h₁, h₂⟩ := h
      subst h₁
      subst h₂
      exact ⟨_, htail, by simp⟩
    | inr h =>
      have ⟨_, hstep₁₂, hstep₂₁⟩ := h
      have ⟨_, htail', hlen⟩ := ih (haff.unfold hstep).2
        (hdisj.unfold hstep).2 hstep₁₂
      exact ⟨_, htail'.prepend hstep₂₁, by simp [hlen]⟩

theorem async_op_interp_ne_zero_inputs
  [InterpConsts V]
  {aop aop' : AsyncOp (V ⊕ T)}
  (hinterp : aop.Interp (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    inputs.length ≠ 0
  := by
  cases hinterp
  any_goals simp [NeZero.ne]
  any_goals rename NeZero _ => inst
  case interp_merge_left | interp_inv_init =>
    intros h
    subst h
    rename_i h
    simp [NeZero.ne'] at h
  case interp_merge_right =>
    have := inst.ne
    omega
  case interp_forward | interp_forwardc | interp_sink | interp_order =>
    intros h
    subst h
    rename_i h
    simp [inst.ne'] at h

theorem proc_output_init_invert
  [Arity Op] [NeZeroArity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  (hstep : Config.Step.Step s (.output vals) s')
  (haff : s.proc.AffineChan)
  (hinit : s'.chans = ChanMap.empty) :
    Config.Step.IsFinalFor (λ l => l.isYield ∨ l.isSilent) s
  := by
  cases hstep with | step_output hpop =>
  simp at hinit
  subst hinit
  intros s'' l hl hstep'
  cases hstep' with
  | step_op hmem hpop' =>
    rename_i op inputs outputs inputVals outputVals chans'
    have ⟨_, _, _, haff_inputs, haff_outputs⟩ := haff
    specialize haff_inputs _ hmem
    specialize haff_outputs _ hmem
    have ⟨_, hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute haff_outputs hpop' hpop
    simp at hpop₂₁
  | step_async hi hget hinterp hpop' =>
    rename_i k₁ k₂ aop aop' allInputs allOutputs inputs inputVals outputs outputVals chans' i
    have hnz := async_op_interp_ne_zero_inputs hinterp
    simp at hnz
    have ⟨_, _, _, haff_inputs, haff_outputs⟩ := haff
    specialize haff_inputs _ (List.mem_of_getElem hget)
    specialize haff_outputs _ (List.mem_of_getElem hget)
    simp [AtomicProc.inputs, AtomicProc.outputs] at haff_inputs haff_outputs
    have ⟨_, hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
      (List.disjoint_of_subset_left hinterp.input_sublist.subset haff_outputs) hpop' hpop
    have _ : NeZero k₁ := .mk hnz
    simp at hpop₂₁
  | _ => simp at hl

theorem proc_guarded_output_init_invert
  [Arity Op] [NeZeroArity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  (hstep : (Config.GuardStep opSpec ioSpec).Step s (.output vals) s')
  (haff : s.proc.AffineChan)
  (hinit : s'.chans = ChanMap.empty) :
    Config.Step.IsFinalFor (λ l => l.isYield ∨ l.isSilent) s
  := by
  rcases hstep with ⟨hguard, hstep⟩
  cases hguard
  exact proc_output_init_invert hstep haff hinit

/--
If a state transitions to an initial state after one output step,
then the previous state should be final wrt yield/τ.

TODO: This needs some additional assumptions that there is no
empty input operator that can fire indefinitely.
-/
theorem proc_interp_guarded_output_init_invert
  [Arity Op] [NeZeroArity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep : (Config.InterpGuardStep opSpec ioSpec).Step s (.output vals) s')
  (haff : s.1.proc.AffineChan)
  (hinit : s'.1.chans = ChanMap.empty) :
    Config.Step.IsFinalFor (λ l => l.isYield ∨ l.isSilent) s.1
  := by
  cases hstep with | step_output hstep =>
  exact proc_guarded_output_init_invert hstep haff hinit

end Wavelet.Determinacy
