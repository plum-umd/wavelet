import Wavelet.Determinacy.Defs

/-! Lemmas about determinism of some indexed step relations. -/

namespace Wavelet.Determinacy

open Semantics Dataflow

variable
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}

theorem proc_indexed_guarded_step_unique_label
  [PCM T]
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₂) s₂)
  (hdet : Label.IsYieldOrSilentAndDet l₁ l₂) :
    l₁ = l₂
  := by
    cases hstep₁ with | step hguard₁ hstep₁
    cases hstep₂ with | step hguard₂ hstep₂
    cases hguard₁ with | _ hguard₁
    cases hguard₂ with | _ hguard₂
    case step.step.idx_guard.idx_guard =>
    cases hguard₁ <;> cases hguard₂
      <;> simp [Label.IsYieldOrSilentAndDet] at hdet
    case spec_yield.spec_yield =>
      have := Config.IndexedStep.unique_index hstep₁ hstep₂
        (by
          constructor; simp
          constructor; simp
          intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
          simp at hyield₁ hyield₂
          have ⟨h₁, h₂, h₃⟩ := hyield₁
          have ⟨h₁', h₂', h₃'⟩ := hyield₂
          simp [← h₁] at h₁'
          have ⟨h₁₁', h₁₂'⟩ := h₁'
          subst h₁₁' h₁₂'
          have := HEq.trans h₂ h₂'.symm
          simp at this
          have ⟨h₁, h₂⟩ := this
          subst h₁
          rename_i outputVals₁' _ outputVals₂' _ _ _
          have : outputVals₁' = outputVals₂' := by
            symm
            apply hdet
            all_goals rfl
          subst this
          rw [← heq_eq_eq _ _]
          apply HEq.trans h₃.symm h₃')
      simp at this
      have ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, _⟩ := this
      subst h₁ h₂
      simp at h₃
      have ⟨h₃₁, h₃₂⟩ := h₃
      subst h₃₁
      simp [Vector.push_eq_push] at h₄
      simp [h₄]
    any_goals rfl
    any_goals
      have := Config.IndexedStep.unique_index hstep₁ hstep₂
      simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at this

theorem proc_indexed_guarded_step_label
  [PCM T]
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hstep : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s') :
    l.isYield ∨ l.isSilent
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> cases hstep <;> simp

theorem proc_indexed_unguarded_step_label
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hstep : (Config.IdxTrivStep opSpec ioSpec).Step s (i, l) s') :
    l.isYield ∨ l.isSilent
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> cases hstep <;> simp

theorem proc_indexed_unguarded_step_same_label_kind
  [PCM T]
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec ioSpec χ}
  {l₁ l₂ l₃ : Label Op V m n}
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s₁ (j, l₂) s₂)
  (hstep₂' : (Config.IdxTrivStep opSpec ioSpec).Step s (j, l₃) s₁') :
    l₂.isYield ↔ l₃.isYield
  := by
    by_cases hij : i = j
    · subst hij
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      have hl := Config.IndexedStep.same_label_kind hstep₁ hstep₂ hstep₂'
      cases hstep₁ with | _ _ hget₁
        <;> cases hstep₂ with | _ _ hget₂
        <;> cases hstep₂' with | _ _ hget₂'
        <;> (simp at hget₂; try simp [hget₂] at hget₂')
        <;> cases hguard₁ <;> try cases hguard₂ <;> try cases hguard₂'
      any_goals simp at hl
      any_goals simp
      any_goals simp at hget₂'
    · rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      have hl := Config.IndexedStep.same_label_kind hstep₁ hstep₂ hstep₂'
      cases hstep₁ with | _ _ hget₁
        <;> cases hstep₂ with | _ _ hget₂
        <;> cases hstep₂' with | _ _ hget₂'
        <;> (simp [hij] at hget₂; simp [hget₂] at hget₂')
        <;> cases hguard₁ <;> try cases hguard₂ <;> try cases hguard₂'
      any_goals simp at hl
      any_goals simp
      any_goals simp at hget₂'

theorem proc_indexed_unguarded_step_det_label_mod
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : (Config.IdxTrivStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxTrivStep opSpec ioSpec).Step s (i, l₂) s₂) :
    Label.EqModYieldOutputs l₁ l₂
  := by
  have hl₁ := proc_indexed_unguarded_step_label hstep₁
  have hl₂ := proc_indexed_unguarded_step_label hstep₂
  rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
  rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
  have heq := Config.IndexedStep.unique_label_mod_outputs hstep₁ hstep₂
  rename_i l₁' l₂'
  cases l₁ <;> cases l₂ <;> simp at hl₁ hl₂
  case yield.yield =>
    cases hguard₁
    cases hguard₂
    case triv_yield.triv_yield =>
      simp [Label.EqModYieldOutputs] at heq ⊢
      have ⟨⟨h₁, h₂⟩, h₃⟩ := heq
      subst h₁ h₂
      simp at h₃
      replace h₃ := h₃.1
      subst h₃
      simp
  any_goals cases hguard₁ <;> cases hguard₂
  any_goals simp [Label.EqModYieldOutputs] at heq ⊢

theorem proc_indexed_unguarded_step_det_mod
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hstep₁ : (Config.IdxTrivStep opSpec ioSpec).Step s (i, l) s₁)
  (hstep₂ : (Config.IdxTrivStep opSpec ioSpec).Step s (i, l) s₂) :
    s₁ ≈ s₂
  := by
  rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
  rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
  apply (Config.IndexedStep.unique_index_mod hstep₁ hstep₂ _).2
  constructor
  · cases hstep₁ <;> simp
  · constructor
    · cases hstep₂ <;> simp
    · cases hguard₁ <;> cases hguard₂
      case triv_yield.triv_yield =>
        intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
        simp at hyield₁ hyield₂
        have ⟨h₁, h₂, h₃⟩ := hyield₁
        have ⟨h₁', h₂', h₃'⟩ := hyield₂
        subst h₁
        simp at h₂ h₃ h₂' h₃'
        simp [← h₃, ← h₃']
        apply Vector.forall₂_to_forall₂_push_toList
        · simp [EqModGhost]
        · simp [EqModGhost]
      case triv_join.triv_join =>
        intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
        simp at hyield₁ hyield₂
        have ⟨h₁, h₂, h₃⟩ := hyield₁
        have ⟨h₁', h₂', h₃'⟩ := hyield₂
        subst h₁
        simp at h₂ h₃ h₂' h₃'
        simp [← h₃, ← h₃', Vector.toList_map, EqModGhost]
        apply List.forall₂_of_length_eq_of_get
        all_goals simp
      all_goals simp [Label.DeterministicMod]

theorem proc_indexed_interp_unguarded_step_det_mod
  [opInterp : OpInterp Op V]
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hdet : opInterp.Deterministic)
  (hstep₁ : (Config.IdxInterpTrivStep opSpec ioSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec ioSpec).Step s (i, .τ) s₂) :
    s₁.1 ≈ s₂.1 ∧ s₁.2 = s₂.2
  := by
  cases hstep₁ <;> cases hstep₂
  case step_yield.step_yield =>
    rename_i hinterp₁ hstep₁ _ _ _ _ _ hinterp₂ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this
    have ⟨h₁, h₂⟩ := this
    subst h₁; subst h₂
    have ⟨h₁, h₂⟩ := hdet hinterp₁ hinterp₂
    subst h₁; subst h₂
    have := proc_indexed_unguarded_step_det_mod hstep₁ hstep₂
    simp [this]
  case step_tau.step_tau =>
    rename_i hstep₁ _ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this
    have := proc_indexed_unguarded_step_det_mod hstep₁ hstep₂
    simp [this]
  case step_tau.step_yield =>
    rename_i hstep₁ _ _ _ _ _ _ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this
  case step_yield.step_tau =>
    rename_i hstep₁ _ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this

theorem proc_indexed_interp_unguarded_step_label
  {interp : Lts S' (RespLabel Op V)}
  {s s' : ConfigWithSpec opSpec ioSpec χ × S'}
  {l : Label Semantics.Empty V m n}
  (hstep : ((Config.IdxTrivStep opSpec ioSpec).IndexedInterpStep interp).Step
    s (i, l) s') :
    l = .τ
  := by
  cases hstep with
  | step_yield hstep
  | step_tau hstep =>
    rcases hstep with ⟨⟨hguard⟩, hstep⟩
    cases hguard <;> cases hstep <;> simp
  | _ hstep =>
    have hl := proc_indexed_unguarded_step_label hstep
    simp at hl

theorem proc_indexed_interp_guarded_step_label
  [PCM T]
  {interp : Lts S' (RespLabel Op V)}
  {s s' : ConfigWithSpec opSpec ioSpec χ × S'}
  {l : Label Semantics.Empty V m n}
  (hstep : ((Config.IdxGuardStep opSpec ioSpec).IndexedInterpStep interp).Step
    s (i, l) s') :
    l = .τ
  := by
  cases hstep with
  | step_yield hstep
  | step_tau hstep =>
    rcases hstep with ⟨⟨hguard⟩, hstep⟩
    cases hguard <;> cases hstep <;> simp
  | _ hstep =>
    have hl := proc_indexed_guarded_step_label hstep
    simp at hl

theorem proc_interp_guarded_det_input
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep₁ : (Config.InterpGuardStep opSpec ioSpec).Step s (.input vals) s₁)
  (hstep₂ : (Config.InterpGuardStep opSpec ioSpec).Step s (.input vals) s₂) :
    s₁ = s₂
  := by
  cases hstep₁ with | step_input hstep₁ =>
  cases hstep₂ with | step_input hstep₂ =>
  rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
  rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
  cases hstep₁ with | step_init =>
  cases hstep₂ with | step_init =>
  rfl

theorem proc_interp_guarded_unguarded_det_input_mod
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s₁ s₂ : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep₁ : (Config.InterpGuardStep opSpec ioSpec).Step s (.input vals) s₁)
  (hstep₂ : (Config.InterpTrivStep opSpec ioSpec).Step s (.input vals) s₂) :
    s₁.1 ≈ s₂.1 ∧ s₁.2 = s₂.2
  := by
  cases hstep₁ with | step_input hstep₁ =>
  cases hstep₂ with | step_input hstep₂ =>
  rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
  rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
  cases hstep₁ with | step_init =>
  cases hstep₂ with | step_init =>
  constructor
  · constructor
    · apply IsRefl.refl
    · simp
      apply congr_eq_mod_push_vals
      · apply IsRefl.refl
      · simp [Vector.toList_append, Vector.toList_map]
        apply List.forall₂_append
        · simp [EqModGhost]
        · simp [EqModGhost]
          apply List.forall₂_true
          simp
  · rfl

end Wavelet.Determinacy
