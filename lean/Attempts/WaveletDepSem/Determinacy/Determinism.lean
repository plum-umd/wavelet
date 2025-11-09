import Wavelet.Determinacy.Defs

/-! Lemmas about determinism of some indexed step relations. -/

namespace Wavelet.Determinacy

open Semantics Dataflow

theorem proc_indexed_guarded_step_unique_label
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
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
          subst h₁'
          have := HEq.trans h₂ h₂'.symm
          simp [Vector.push_eq_push] at this
          replace this := Vector.inj_map (by simp [Function.Injective]) this.2
          subst this
          rename_i outputVals₁' _ outputVals₂'
          have : outputVals₁' = outputVals₂' := by
            symm
            apply hdet
            all_goals rfl
          subst this
          rw [← heq_eq_eq _ _]
          apply HEq.trans h₃.symm h₃')
      simp at this
      have ⟨⟨h₁, h₂, h₃⟩, _⟩ := this
      subst h₁
      simp [Vector.push_eq_push] at h₂
      replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂.2
      subst h₂
      simp [Vector.push_eq_push] at h₃
      replace h₃ := Vector.inj_map (by simp [Function.Injective]) h₃.2
      subst h₃
      rfl
    any_goals rfl
    any_goals
      have := Config.IndexedStep.unique_index hstep₁ hstep₂
      simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at this

theorem proc_indexed_guarded_step_label
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hstep : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s') :
    l.isYield ∨ l.isSilent
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> cases hstep <;> simp

theorem proc_indexed_unguarded_step_label
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hstep : (Config.IdxTrivStep opSpec).Step s (i, l) s') :
    l.isYield ∨ l.isSilent
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> cases hstep <;> simp

theorem proc_indexed_unguarded_step_same_label_kind
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ l₃ : Label Op V m n}
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s₁ (j, l₂) s₂)
  (hstep₂' : (Config.IdxTrivStep opSpec).Step s (j, l₃) s₁') :
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
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : (Config.IdxTrivStep opSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l₂) s₂) :
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
    simp [Label.EqModYieldOutputs] at heq ⊢
    have ⟨h₁, h₂⟩ := heq
    subst h₁
    simp [Vector.push_eq_push] at h₂
    replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂.2
    subst h₂
    simp
  any_goals cases hguard₁ <;> cases hguard₂
  any_goals simp [Label.EqModYieldOutputs] at heq ⊢

theorem proc_indexed_unguarded_step_det_mod
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hstep₁ : (Config.IdxTrivStep opSpec).Step s (i, l) s₁)
  (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l) s₂) :
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
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hdet : opInterp.Deterministic)
  (hstep₁ : (Config.IdxInterpTrivStep opSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (i, .τ) s₂) :
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
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {interp : Lts S' (RespLabel Op V)}
  {s s' : ConfigWithSpec opSpec χ m n × S'}
  {l : Label Semantics.Empty V m n}
  (hstep : ((Config.IdxTrivStep opSpec).IndexedInterpStep interp).Step
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
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {interp : Lts S' (RespLabel Op V)}
  {s s' : ConfigWithSpec opSpec χ m n × S'}
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

end Wavelet.Determinacy
