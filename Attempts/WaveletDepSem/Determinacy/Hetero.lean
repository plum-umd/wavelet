import Wavelet.Determinacy.Confluence
import Wavelet.Determinacy.Convert
import Wavelet.Determinacy.Congr

/-! "Heterogeneous" confluence theorems between guarded and unguarded semantics. -/

namespace Wavelet.Determinacy

open Semantics Dataflow

/--
If we can make two guarded steps, where the second operator can be already
run in the first step (even in a unguarded way), then we can turn that
unguarded step to a guarded step.
-/
theorem proc_indexed_guarded_hetero_confl_single
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ : Label Op V m n}
  (haff : s.proc.AffineChan)
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s₁ (j, l₂) s₂)
  (hstep₂' : (Config.IdxTrivStep opSpec).Step s (j, l₂) s₁') :
    ∃ s₁'',
      (Config.IdxGuardStep opSpec ioSpec).Step s (j, l₂) s₁''
  := by
  have hl₁ := proc_indexed_guarded_step_label hstep₁
  have hl₂ := proc_indexed_guarded_step_label hstep₂
  by_cases hij : i = j
  · subst hij
    by_cases heq_label : l₁ = l₂
    · subst heq_label
      exact ⟨_, hstep₁⟩
    · cases hstep₁ with | step hguard₁ hstep₁
      cases hstep₂' with | step hguard₂ hstep₂'
      case neg.step.step =>
      cases hguard₁ with | _ hguard₁ =>
      cases hguard₂ with | _ hguard₂ =>
      cases hguard₁ <;> cases hguard₂ <;> simp at heq_label
      case idx_guard.idx_guard.spec_yield.triv_yield =>
        -- NOTE: allowing yield to be non-deterministic here
        rename_i op inputVals₂ outputVals₂ _
        cases hstep₁ with | step_op _ hget₁ hpop₁ =>
        rename_i inputs₁ outputs₁
        cases hstep₂' with | step_op hi hget₂ hpop₂ =>
        rename_i inputs₂ outputs₂
        simp [hget₂] at hget₁
        have ⟨h₁, h₂, h₃⟩ := hget₁
        subst h₁; subst h₂; subst h₃
        simp [hpop₁] at hpop₂
        have ⟨h₁, _⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁
        replace h₁ := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst h₁
        exact ⟨_,
          by
            apply Lts.GuardStep.step
            · apply IndexedGuard.idx_guard
              apply OpSpec.Guard.spec_yield
            · exact .step_op hi hget₂ hpop₁
        ⟩
      any_goals
        simp at hl₁ hl₂
      any_goals
        have := Config.IndexedStep.unique_index hstep₁ hstep₂'
        simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at this
  · case neg =>
    cases hstep₁ with | step hguard₁ hstep₁
    cases hstep₂ with | step hguard₂ hstep₂
    cases hstep₂' with | step hguard₂' hstep₂'
    rename_i l₁' l₂' l₃'
    rcases l₁' with ⟨i₁, l₁'⟩
    rcases l₂' with ⟨i₂, l₂'⟩
    rcases l₃' with ⟨i₃, l₃'⟩
    have : i = i₁ := by cases hguard₁; simp
    subst this
    have : j = i₂ := by cases hguard₂; simp
    subst this
    have : j = i₃ := by cases hguard₂'; simp
    subst this
    have hl := Config.IndexedStep.same_label_kind hstep₁ hstep₂ hstep₂'
    cases hstep₁ with
    | step_op _ hget₁ hpop₁ =>
      cases hstep₂ with
      | step_op _ hget₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
            <;> rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          all_goals
            simp at hl
            simp [hget₂'] at hget₂
          case spec_yield.triv_yield =>
            have ⟨h₁, h₂⟩ := hget₂
            subst h₁; subst h₂
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [Vector.push_eq_push] at h₁ h₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard .spec_yield)
              (.step_op (by assumption) hget₂' hpop₂')⟩
          case spec_join.triv_join =>
            have ⟨⟨h₁, h₂, h₃⟩, h₄, h₅⟩ := hget₂
            subst h₁; subst h₂; subst h₃; subst h₄; subst h₅
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard (.spec_join (by assumption) (by assumption) (by assumption)))
              (.step_op (by assumption) hget₂' hpop₂')⟩
        | step_async => simp at hl
      | step_async _ hget₂ hinterp₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂ hpop₂ => simp at hl
        | step_async _ hget₂' hinterp₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
          rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          simp [hget₂'] at hget₂
          have ⟨h₁, h₂, h₃⟩ := hget₂
          subst h₁; subst h₂; subst h₃
          simp at hpop₂
          have := hinterp₂'.det_inputs hinterp₂
          have ⟨h₁, h₂⟩ := Vector.toList_inj_heq this
          subst h₁; subst h₂
          have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (List.disjoint_of_subset_right
              hinterp₂.input_sublist.subset hdisj_inputs) hpop₁ hpop₂'
          rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
          simp at hpop₂
          have ⟨h₁, h₂⟩ := hpop₂
          subst h₁
          exact ⟨_, .step
            (.idx_guard .spec_tau)
            (.step_async (by assumption) hget₂' hinterp₂' hpop₂')⟩
    | step_async _ hget₁ hinterp₁ hpop₁ =>
      cases hstep₂ with
      | step_op _ hget₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
            <;> rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          all_goals
            simp at hl
            simp [hget₂', hij] at hget₂
          case spec_yield.triv_yield =>
            have ⟨h₁, h₂⟩ := hget₂
            subst h₁; subst h₂
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
              (List.disjoint_of_subset_right
                hinterp₁.input_sublist.subset hdisj_inputs.symm).symm
              hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [Vector.push_eq_push] at h₁ h₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard .spec_yield)
              (.step_op (by assumption) hget₂' hpop₂')⟩
          case spec_join.triv_join =>
            have ⟨⟨h₁, h₂, h₃⟩, h₄, h₅⟩ := hget₂
            subst h₁; subst h₂; subst h₃; subst h₄; subst h₅
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
              (List.disjoint_of_subset_right
                hinterp₁.input_sublist.subset hdisj_inputs.symm).symm
              hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard (.spec_join (by assumption) (by assumption) (by assumption)))
              (.step_op (by assumption) hget₂' hpop₂')⟩
        | step_async => simp at hl
      | step_async _ hget₂ hinterp₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂ hpop₂ => simp at hl
        | step_async _ hget₂' hinterp₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
          rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          simp [hget₂', hij] at hget₂
          have ⟨h₁, h₂, h₃⟩ := hget₂
          subst h₁; subst h₂; subst h₃
          simp at hpop₂
          have := hinterp₂'.det_inputs hinterp₂
          have ⟨h₁, h₂⟩ := Vector.toList_inj_heq this
          subst h₁; subst h₂
          have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (by
              have := (List.disjoint_of_subset_right
                hinterp₁.input_sublist.subset hdisj_inputs.symm).symm
              have := (List.disjoint_of_subset_right
                hinterp₂'.input_sublist.subset this)
              exact this) hpop₁ hpop₂'
          rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
          simp at hpop₂
          have ⟨h₁, h₂⟩ := hpop₂
          subst h₁
          exact ⟨_, .step
            (.idx_guard .spec_tau)
            (.step_async (by assumption) hget₂' hinterp₂' hpop₂')⟩

/-- Similar to `proc_indexed_guarded_hetero_confl_single`, but for interpreted steps. -/
theorem proc_indexed_interp_guarded_hetero_confl_single
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hdet : opInterp.Deterministic)
  (haff : s.1.proc.AffineChan)
  (hstep₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpGuardStep opSpec ioSpec).Step s₁ (j, .τ) s₂)
  (hstep₂' : (Config.IdxInterpTrivStep opSpec).Step s (j, .τ) s₁') :
    ∃ s₁'',
      (Config.IdxInterpGuardStep opSpec ioSpec).Step s (j, .τ) s₁'' ∧
      s₁'.1 ≈ s₁''.1 ∧
      s₁'.2 = s₁''.2
  := by
  have hdet_mod {s₂} hstep := proc_indexed_interp_unguarded_step_det_mod
    (s₂ := s₂) hdet hstep₂' hstep
  by_cases hij : i = j
  · subst hij
    have := hdet_mod (Config.IdxInterpGuardStep.to_indexed_interp_unguarded hstep₁)
    exact ⟨_, hstep₁, this⟩
  · cases hstep₁ with | _ hstep₁
      <;> cases hstep₂ with | _ hstep₂
      <;> cases hstep₂' with | _ hstep₂'
    -- Rule out some cases where `hstep₂` and `hstep₂'` don't have the same label
    any_goals
      have := proc_indexed_unguarded_step_same_label_kind hstep₁ hstep₂ hstep₂'
      simp at this
    -- Some τ cases can be delegated
    case neg.step_tau.step_tau.step_tau
      | neg.step_yield.step_tau.step_tau =>
      have ⟨s', hstep'⟩ := proc_indexed_guarded_hetero_confl_single haff hstep₁ hstep₂ hstep₂'
      simp at hstep'
      exact ⟨_, Lts.IndexedInterpStep.step_tau hstep',
        by
          have := hdet_mod (Config.IdxInterpGuardStep.to_indexed_interp_unguarded (.step_tau hstep'))
          simp at this
          simp [this]⟩
    -- Other cases need a bit more work as they involve
    -- some interaction with `opInterp`'s determinism
    case neg.step_tau.step_yield.step_yield =>
      rename_i hinterp₂ _ _ _ _ _ hinterp₂'
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      cases hguard₂
      cases hguard₂'
      cases hstep₂ with | step_op _ hget₂ hpop₂
      cases hstep₂' with | step_op _ hget₂' hpop₂'
      cases hstep₁ with
      | step_op _ hget₁ hpop₁ =>
        simp [hget₂'] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp at hpop₂
        have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
        rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
        simp at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁ h₂
        simp [h₁] at hpop₂'
        have := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst this
        have ⟨h₁, h₂⟩ := hdet hinterp₂' hinterp₂
        subst h₁; subst h₂
        have : (Config.IdxInterpGuardStep opSpec ioSpec).Step _ _ _ :=
          Lts.IndexedInterpStep.step_yield (.step
            (.idx_guard .spec_yield)
            (.step_op (by assumption) hget₂' hpop₂')) hinterp₂'
        exact ⟨_, this,
          by
            have := hdet_mod (Config.IdxInterpGuardStep.to_indexed_interp_unguarded this)
            simp at this
            simp [this],
        ⟩
      | step_async _ hget₁ hinterp₁ hpop₁ =>
        simp [hij, hget₂'] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp at hpop₂
        have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (List.disjoint_of_subset_right
            hinterp₁.input_sublist.subset hdisj_inputs.symm).symm
          hpop₁ hpop₂'
        rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
        simp at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁ h₂
        simp [h₁] at hpop₂'
        have := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst this
        have ⟨h₁, h₂⟩ := hdet hinterp₂' hinterp₂
        subst h₁; subst h₂
        have : (Config.IdxInterpGuardStep opSpec ioSpec).Step _ _ _ :=
          .step_yield (.step
            (.idx_guard .spec_yield)
            (.step_op (by assumption) hget₂' hpop₂')) hinterp₂'
        exact ⟨_, this,
          by
            have := hdet_mod (Config.IdxInterpGuardStep.to_indexed_interp_unguarded this)
            simp at this
            simp [this],
        ⟩
    case neg.step_yield.step_yield.step_yield =>
      rename_i hinterp₁ _ _ _ _ _ hinterp₂ _ _ _ _ _ hinterp₂'
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      cases hguard₁
      cases hguard₂
      cases hguard₂'
      cases hstep₂ with | step_op _ hget₂ hpop₂
      cases hstep₂' with | step_op _ hget₂' hpop₂'
      cases hstep₁ with
      | step_op _ hget₁ hpop₁ =>
        simp [hget₂'] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp at hpop₂
        have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
        rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
        simp at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁ h₂
        simp [h₁] at hpop₂'
        have := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst this
        have : (Config.IdxInterpGuardStep opSpec ioSpec).Step _ _ _ :=
          .step_yield (.step
            (.idx_guard .spec_yield)
            (.step_op (by assumption) hget₂' hpop₂')) hinterp₂'
        exact ⟨_, this,
          by
            have := hdet_mod (Config.IdxInterpGuardStep.to_indexed_interp_unguarded this)
            simp at this
            simp [this],
        ⟩

/--
If there is a guarded τ trace from `s` to a final state `s₁`,
then we can turn any *unguarded* τ step from `s` to `s₂`,
into a guarded τ step, modulo potentially different ghost tokens.
-/
theorem proc_indexed_guarded_hetero_confl
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {tr : Trace (Nat × Label Op V m n)}
  {l : Label Op V m n}
  (haff : (Config.IdxGuardStep opSpec ioSpec).IsInvariantAt
    (λ s => s.proc.AffineChan) s)
  (htrace₁ : (Config.IdxGuardStep opSpec ioSpec).Star s tr s₁)
  -- The first label in the trace that matches the index should emit the same event
  (hdom : tr.find? (·.1 = i) = .some (i, l))
  (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l) s₂) :
    ∃ s₂',
      (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s₂' ∧
      s₂' ≈ s₂
  := by
  induction htrace₁
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl => simp at hdom
  | head hstep₁ htail₁ ih =>
    rename_i s s₂' l' tr'
    rcases l' with ⟨i', l'⟩
    by_cases hk : (i, l) = (i', l')
    · simp at hk
      have ⟨h₁, h₂⟩ := hk
      subst h₁; subst h₂
      exists s₂'
      simp [hstep₁]
      exact proc_indexed_unguarded_step_det_mod
        (Config.IdxGuardStep.to_indexed_unguarded hstep₁) hstep₂
    · simp at hdom hk
      cases hdom
      · rename_i h
        simp [h] at hk
      rename_i hdom
      have hstep₁' := Config.IdxGuardStep.to_indexed_unguarded hstep₁
      have := proc_indexed_unguarded_strong_confl_at_mod
        s haff.base hstep₁' hstep₂
        (by
          intros h
          exact False.elim (hdom.1 h))
      cases this with
      | inl h =>
        simp at h
        exact False.elim (hk h.1.1.symm h.1.2.symm)
      | inr h =>
        have ⟨s₃', s₃, hstep₃', hstep₃, heq₃⟩ := h
        replace ⟨s₃', hstep₃', heq₃⟩ := ih
          (haff.unfold hstep₁).2
          hdom.2
          hstep₃'
        have ⟨s₂', hstep₂'⟩ := proc_indexed_guarded_hetero_confl_single
          haff.base
          hstep₁ hstep₃' hstep₂
        exact ⟨
          _, hstep₂',
          proc_indexed_unguarded_step_det_mod
            (Config.IdxGuardStep.to_indexed_unguarded hstep₂') hstep₂,
        ⟩

/-- If two operators can fire at the same state, then one can fire after another.
(although no guarantee about the final state). -/
theorem proc_commute_indexed_unguarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hnb : opInterp.NonBlocking)
  (haff : s.1.proc.AffineChan)
  (hstep₁ : (Config.IdxInterpTrivStep opSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (j, .τ) s₂)
  (hne : i ≠ j) :
    ∃ s₂', (Config.IdxInterpTrivStep opSpec).Step s₁ (j, .τ) s₂'
  := by
  cases hstep₁ with
  | step_yield hstep₁ hinterp₁ =>
    rcases hstep₁ with ⟨⟨⟨hguard₁⟩⟩, hstep₁⟩
    cases hstep₁ with | step_op _ hget₁ hpop₁ =>
    cases hstep₂ with
    | step_yield hstep₂ hinterp₂ =>
      rcases hstep₂ with ⟨⟨⟨hguard₂⟩⟩, hstep₂⟩
      cases hstep₂ with | step_op _ hget₂ hpop₂ =>
      have ⟨_, _, hinterp₂'⟩ := hnb hinterp₁ hinterp₂
      have hdisj_inputs := haff.atom_inputs_disjoint
        ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
      have hdisj_outputs := haff.atom_outputs_disjoint
        ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
      simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      exact ⟨_,
        .step_yield (.step
          (.idx_guard (.triv_yield (tok₂ := PCM.zero)))
          (.step_op
            (by assumption)
            hget₂
            (pop_vals_push_vals_commute hpop₁₂)))
            hinterp₂'
      ⟩
    | step_tau hstep₂ =>
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      cases hguard₂ with
      | triv_join =>
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        exact ⟨_,
          .step_tau (.step
            (.idx_guard (.triv_join (outputs := #v[PCM.zero, PCM.zero])))
            (.step_op
              (by assumption)
              hget₂
              (pop_vals_push_vals_commute hpop₁₂)))
        ⟩
      | triv_tau =>
        cases hstep₂ with | step_async _ hget₂ hinterp₂ hpop₂ =>
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (List.disjoint_of_subset_right
            hinterp₂.input_sublist.subset hdisj_inputs) hpop₁ hpop₂
        exact ⟨_,
          .step_tau (.step
            (.idx_guard .triv_tau)
            (.step_async
              (by assumption)
              hget₂
              hinterp₂
              (pop_vals_push_vals_commute hpop₁₂)))
        ⟩
  | step_tau hstep₁ =>
    rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
    cases hguard₁ with
    | triv_join =>
      cases hstep₁ with | step_op _ hget₁ hpop₁ =>
      cases hstep₂ with
      | step_yield hstep₂ hinterp₂ =>
        rcases hstep₂ with ⟨⟨⟨hguard₂⟩⟩, hstep₂⟩
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        -- have ⟨_, _, hinterp₂'⟩ := hnb hinterp₁ hinterp₂
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        exact ⟨_,
          .step_yield (.step
            (.idx_guard (.triv_yield (tok₂ := PCM.zero)))
            (.step_op
              (by assumption)
              hget₂
              (pop_vals_push_vals_commute hpop₁₂)))
              hinterp₂
        ⟩
      | step_tau hstep₂ =>
        rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
        cases hguard₂ with
        | triv_join =>
          cases hstep₂ with | step_op _ hget₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard (.triv_join (outputs := #v[PCM.zero, PCM.zero])))
              (.step_op
                (by assumption)
                hget₂
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩
        | triv_tau =>
          cases hstep₂ with | step_async _ hget₂ hinterp₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (List.disjoint_of_subset_right
              hinterp₂.input_sublist.subset hdisj_inputs) hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard .triv_tau)
              (.step_async
                (by assumption)
                hget₂
                hinterp₂
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩
    | triv_tau =>
      cases hstep₁ with | step_async _ hget₁ hinterp₁ hpop₁ =>
      cases hstep₂ with
      | step_yield hstep₂ hinterp₂ =>
        rcases hstep₂ with ⟨⟨⟨hguard₂⟩⟩, hstep₂⟩
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        -- have ⟨_, _, hinterp₂'⟩ := hnb hinterp₁ hinterp₂
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (List.disjoint_of_subset_right
            hinterp₁.input_sublist.subset hdisj_inputs.symm).symm hpop₁ hpop₂
        exact ⟨_,
          .step_yield (.step
            (.idx_guard (.triv_yield (tok₂ := PCM.zero)))
            (.step_op
              (by simp; assumption)
              (by simp [hne]; exact hget₂)
              (pop_vals_push_vals_commute hpop₁₂)))
              hinterp₂
        ⟩
      | step_tau hstep₂ =>
        rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
        cases hguard₂ with
        | triv_join =>
          cases hstep₂ with | step_op _ hget₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (List.disjoint_of_subset_right
              hinterp₁.input_sublist.subset hdisj_inputs.symm).symm hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard (.triv_join (outputs := #v[PCM.zero, PCM.zero])))
              (.step_op
                (by simp; assumption)
                (by simp [hne]; exact hget₂)
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩
        | triv_tau =>
          cases hstep₂ with | step_async _ hget₂ hinterp₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (by
              have := (List.disjoint_of_subset_right
                hinterp₁.input_sublist.subset hdisj_inputs.symm).symm
              have := (List.disjoint_of_subset_right
                hinterp₂.input_sublist.subset this)
              exact this) hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard .triv_tau)
              (.step_async
                (by simp; assumption)
                (by simp [hne]; exact hget₂)
                hinterp₂
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩

/-- If a guarded trace terminates, then any unguarded step from the same state
must fire one of the operators fired in the guarded trace. -/
theorem proc_indexed_interp_unguarded_term_to_dom
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr : Trace (Nat × Label Semantics.Empty V m n)}
  {l : Label Semantics.Empty V m n}
  (hnb : opInterp.NonBlocking)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (_, l) => l.isYield ∨ l.isSilent) s₁.1)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (i, l) s₂) :
    ∃ l', (i, l') ∈ tr
  := by
  have hl := proc_indexed_interp_unguarded_step_label hstep₂
  subst hl
  induction htrace₁
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl =>
    match hstep₂ with
    | .step_tau hstep₂
    | .step_yield hstep₂ _ =>
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      cases hguard₂ <;> exact False.elim (hterm (by simp) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i s s' l' tr'
    rcases l' with ⟨i', l'⟩
    have this := proc_indexed_interp_guarded_step_label hstep₁
    subst this
    by_cases hii' : i = i'
    · simp [hii']
    · simp [hii']
      have hstep₁' := Config.IdxInterpGuardStep.to_indexed_interp_unguarded hstep₁
      have ⟨s₂'', hstep₂''⟩ := proc_commute_indexed_unguarded hnb haff.base hstep₁' hstep₂ (Ne.symm hii')
      exact ih (haff.unfold hstep₁).2 hstep₂''

/-- If the "good-behaving" semantics of `Config.IdxInterpGuardStep`
has a terminating trace, then any unguarded step can be turned
into a guarded step. -/
theorem proc_indexed_interp_guarded_hetero_confl
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr : Trace (Nat × Label Semantics.Empty V m n)}
  {l : Label Semantics.Empty V m n}
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hdom : ∃ l', (i, l') ∈ tr)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (i, l) s₂) :
    ∃ s₂',
      (Config.IdxInterpGuardStep opSpec ioSpec).Step s (i, l) s₂' ∧
      s₂.1 ≈ s₂'.1 ∧
      s₂.2 = s₂'.2
  := by
  have hl := proc_indexed_interp_unguarded_step_label hstep₂
  subst hl
  induction htrace₁
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl => simp at hdom
  | head hstep₁ htail₁ ih =>
    rename_i s s' l' tr'
    rcases l' with ⟨i', l'⟩
    have this := proc_indexed_interp_guarded_step_label hstep₁
    subst this
    by_cases hii' : i = i'
    · subst hii'
      have := proc_indexed_interp_unguarded_step_det_mod hdet
        hstep₂ (Config.IdxInterpGuardStep.to_indexed_interp_unguarded hstep₁)
      exists s'
    · have hstep₁' := Config.IdxInterpGuardStep.to_indexed_interp_unguarded hstep₁
      have ⟨s₂'', hstep₂''⟩ := proc_commute_indexed_unguarded hnb haff.base hstep₁' hstep₂ (Ne.symm hii')
      have ⟨s₁'', hstep₁'', heq⟩ := ih (haff.unfold hstep₁).2
        (by
          have ⟨l', hl'⟩ := hdom
          exists l'
          simp [hii'] at hl'
          simp [hl'])
        hstep₂''
      exact proc_indexed_interp_guarded_hetero_confl_single
        hdet haff.base hstep₁ hstep₁'' hstep₂

/--
If there exists a terminating and guarded trace, then any unguarded trace
  1. Is bounded by the length of the guarded trace, and
  2. Converges to the same final state as the guarded trace.

This can also be thought of as converting the weak normalization
of `s` in the guarded semantics into its strong normalization
in the unguarded semantics.
-/
theorem proc_indexed_interp_guarded_hetero_terminal_confl
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr₁ tr₂ : Trace (Nat × Label Semantics.Empty V m n)}
  (hconfl : opSpec.Confluent opInterp)
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (hdisj : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.DisjointTokens) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr₁ s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (_, l) => l.isYield ∨ l.isSilent) s₁.1)
  (htrace₂ : (Config.IdxInterpTrivStep opSpec).Star s tr₂ s₂) :
    ∃ s₁' tr₃,
      (Config.IdxInterpTrivStep opSpec).Star s₂ tr₃ s₁' ∧
      tr₁.length = tr₂.length + tr₃.length ∧
      s₁.1 ≈ s₁'.1 ∧
      s₁.2 = s₁'.2
  := by
  cases htrace₂
    using Lts.Star.reverse_induction with
  | refl =>
    exact ⟨_, _, Config.IdxInterpGuardStep.to_indexed_interp_unguarded_star htrace₁,
      by simp [IsRefl.refl]⟩
  | head hstep₂ htail₂ ih =>
    rename_i s s' l' tr₂'
    have := proc_indexed_interp_unguarded_term_to_dom
      hnb haff htrace₁ hterm hstep₂
    have ⟨s'', hstep₂', heq⟩ := proc_indexed_interp_guarded_hetero_confl
      hdet hnb haff htrace₁ this hstep₂
    have ⟨_, htail₂', heq'⟩ := congr_eq_mod_ghost_proc_indexed_interp_unguarded_star htail₂ heq
    have ⟨_, htrace₁', hlen⟩ := proc_indexed_interp_guarded_terminal_confl
      hconfl hdet haff hdisj
      htrace₁ hterm hstep₂'
    have ⟨_, _, htrace₂', hlen₂', heq₂'⟩ := proc_indexed_interp_guarded_hetero_terminal_confl
      hconfl hdet hnb
      (haff.unfold hstep₂').2
      (hdisj.unfold hstep₂').2
      htrace₁' hterm htail₂'
    have := congr_eq_mod_ghost_proc_indexed_interp_unguarded_star htrace₂'
      (by
        constructor
        · exact IsSymm.symm _ _ heq'.1
        · simp [heq'.2])
    have ⟨_, htrace₂'', heq₂''⟩ := this
    exact ⟨
      _, _, htrace₂'',
      by
        constructor
        · simp [hlen, hlen₂']
          omega
        · constructor
          · exact IsTrans.trans _ _ _ heq₂'.1 heq₂''.1
          · simp [← heq₂''.2, heq₂'.2]
    ⟩

/--
Same as `proc_indexed_interp_guarded_hetero_terminal_confl`,
but for the unindexed normal semantics:

If s →* s₁ in the guarded semantics, with s₁ final (wrt. yields and τ's)
and s →* s₂ in the unguarded semantics, then s₂ →* s₁' in the unguarded semantics,
for some s₁' ≈ s₁ (modulo ghost tokens).

In particular, the length of s →* s₂ is also bounded by the length of s →* s₁.
-/
theorem proc_interp_guarded_hetero_terminal_confl
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hconfl : opSpec.Confluent opInterp)
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  (haff : (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (hdisj : (Config.InterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.DisjointTokens) s)
  (htrace₁ : (Config.InterpGuardStep opSpec ioSpec).TauStarN .τ k₁ s s₁)
  (hterm : Config.Step.IsFinalFor (λ l => l.isYield ∨ l.isSilent) s₁.1)
  (htrace₂ : (Config.InterpTrivStep opSpec).TauStarN .τ k₂ s s₂) :
    ∃ s₁' k₃,
      (Config.InterpTrivStep opSpec).TauStarN .τ k₃ s₂ s₁' ∧
      k₁ = k₂ + k₃ ∧
      s₁.1 ≈ s₁'.1 ∧
      s₁.2 = s₁'.2
  := by
  have ⟨_, hlen₁, htrace₁'⟩ := Config.InterpGuardStep.to_indexed_interp_guarded_tau_star htrace₁
  have ⟨_, hlen₂, htrace₂'⟩ := Config.InterpTrivStep.to_indexed_interp_unuarded_tau_star htrace₂
  have ⟨_, _, htrace₃', hlen₃, heq⟩ := proc_indexed_interp_guarded_hetero_terminal_confl
    hconfl hdet hnb
    (haff.map_step (λ hstep => by
      simp [Lts.Step] at hstep
      exact ⟨_, hstep.to_interp_guarded⟩))
    (hdisj.map_step (λ hstep => by
      simp [Lts.Step] at hstep
      exact ⟨_, hstep.to_interp_guarded⟩))
    htrace₁'
    (hterm.map_step
      (lts₁ := Config.Step)
      (lts₂ := Config.IndexedStep)
      (Labels₂ := (λ (_, l) => l.isYield ∨ l.isSilent))
      (λ hl hstep => by
        rename_i l
        simp [Lts.Step] at hstep
        have := hstep.to_step_yield_or_tau
        exact ⟨_, by rcases l with ⟨_, ⟨_⟩⟩ <;> simp at hl ⊢, this⟩))
    htrace₂'
  have htrace₃ := Config.IdxInterpTrivStep.to_interp_unguarded_tau_star htrace₃'
  exact ⟨_, _, htrace₃,
    by
      simp [hlen₁, hlen₂] at hlen₃
      simp [hlen₃], heq⟩

end Wavelet.Determinacy
