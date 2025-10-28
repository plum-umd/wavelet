import Wavelet.Determinacy.Defs
import Wavelet.Determinacy.Determinism

/-! Lemmas about converting steps through `EqMod`. -/

namespace Wavelet.Dataflow

open Semantics Determinacy

theorem congr_eq_mod_ghost_async_op_interp
  [InterpConsts V]
  {aop aop' aop₁ aop₁' : AsyncOp (V ⊕ T)}
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop₁)
  (heq_aop : aop ≈ aop')
  (heq_inputs : List.Forall₂ EqModGhost inputVals inputVals') :
    ∃ outputVals',
      AsyncOp.Interp aop'
        (.mk allInputs allOutputs inputs inputVals' outputs outputVals') aop₁' ∧
      aop₁ ≈ aop₁' ∧
      List.Forall₂ EqModGhost outputVals outputVals'
  := sorry

theorem congr_eq_mod_ghost_proc_indexed_unguarded
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n}
  {l : Nat × Label Op V m n}
  (hstep : (Config.IdxTrivStep opSpec).Step s₁ l s₂)
  (heq : s₁ ≈ s₁') :
    ∃ s₂',
      (Config.IdxTrivStep opSpec).Step s₁' l s₂' ∧
      s₂ ≈ s₂'
  := by
  have hl := proc_indexed_unguarded_step_label hstep
  have ⟨⟨_, _, heq_aps⟩, heq_chans⟩ := heq
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hstep with
  | step_op => sorry
  | step_async hi hget hinterp hpop =>
    have := heq_aps.get hi (by simp [heq_aps.length_eq] at hi; exact hi)
    simp [hget, AtomicProc.EqMod] at this
    sorry
    -- split at this
    -- · rename_i hget'
    --   replace ⟨_, _, hpop, heq_outputs, heq_chans'⟩ := chan_map_pop_vals_equiv heq_chans hpop
    --   sorry
    -- · sorry
    -- -- simp at hpop
    -- exact ⟨
    --   _,
    --   .step
    --     (.idx_guard hguard)
    --     (.step_async
    --       hi
    --       hget
    --       hinterp
    --       hpop),
    --   sorry
    -- ⟩

theorem congr_eq_mod_ghost_proc_indexed_interp_unguarded
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hstep : (Config.IdxInterpTrivStep opSpec).Step s₁ l s₂)
  (heq : s₁.1 ≈ s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      (Config.IdxInterpTrivStep opSpec).Step s₁' l s₂' ∧
      s₂.1 ≈ s₂'.1 ∧ s₂.2 = s₂'.2
  := by
  have hl := proc_indexed_interp_unguarded_step_label hstep
  cases hstep with
  | step_yield hstep hinterp =>
    have ⟨_, hstep', heq'⟩ := congr_eq_mod_ghost_proc_indexed_unguarded hstep heq.1
    simp at heq
    simp [heq.2] at hinterp
    exact ⟨
      _, .step_yield hstep' hinterp,
      by
        simp at heq ⊢
        simp [heq']
    ⟩
  | step_tau hstep =>
    have ⟨_, hstep', heq'⟩ := congr_eq_mod_ghost_proc_indexed_unguarded hstep heq.1
    exact ⟨
      _, .step_tau hstep',
      by
        simp at heq ⊢
        simp [heq, heq']
    ⟩
  | _ hstep => simp at hl

theorem congr_eq_mod_ghost_proc_indexed_interp_unguarded_star
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (htrace : (Config.IdxInterpTrivStep opSpec).Star s₁ tr s₂)
  (heq : s₁.1 ≈ s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      (Config.IdxInterpTrivStep opSpec).Star s₁' tr s₂' ∧
      s₂.1 ≈ s₂'.1 ∧ s₂.2 = s₂'.2
  := by
  induction htrace
    using Lts.Star.reverse_induction
    generalizing s₁' with
  | refl => exact ⟨s₁', .refl, heq⟩
  | head hstep htail ih =>
    have ⟨_, hstep', heq₁⟩ := congr_eq_mod_ghost_proc_indexed_interp_unguarded hstep heq
    have ⟨_, htail', heq₂⟩ := ih heq₁
    exact ⟨_, htail'.prepend hstep', heq₂⟩

/-- Equal labels translate to equal labels through `OpSpec.Guard`. -/
theorem congr_eq_spec_guard
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  {l₁' l₂' : Label Op V m n}
  (hguard₁ : opSpec.Guard ioSpec l₁ l₁')
  (hguard₂ : opSpec.Guard ioSpec l₂ l₂')
  (heq : l₁ = l₂) : l₁' = l₂' := by
  subst heq
  cases l₁ with
  | yield op inputs outputs =>
    cases op with
    | op op =>
      cases hguard₁
      rename_i inputs₁ outputs₁
      generalize hinputs₁' :
        (Vector.map Sum.inl inputs₁).push (Sum.inr (opSpec.pre op inputs₁)) = inputs₁'
      generalize houtputs₁' :
        (Vector.map Sum.inl outputs₁).push (Sum.inr (opSpec.post op inputs₁ outputs₁)) = outputs₁'
      rw [hinputs₁', houtputs₁'] at hguard₂
      cases hguard₂
      rename_i inputs₂ outputs₂
      simp [Vector.push_eq_push] at hinputs₁' houtputs₁'
      have heq₁ := Vector.inj_map (by simp [Function.Injective]) hinputs₁'.2
      have heq₂ := Vector.inj_map (by simp [Function.Injective]) houtputs₁'.2
      simp [heq₁, heq₂]
    | join k l req =>
      cases hguard₁ with | spec_join h₁ h₂ =>
      rename_i rem₁ toks₁ vals₁
      generalize h :
        (Vector.map Sum.inr rem₁ : Vector (V ⊕ T) _) ++
          (Vector.map Sum.inl toks₁ : Vector (V ⊕ T) _) = x
      rw [h] at hguard₂
      cases hguard₂
      rfl
  | input vals =>
    cases hguard₁ with | spec_input =>
    rename_i vals₁
    generalize h :
      (Vector.map Sum.inl vals₁).push (Sum.inr (ioSpec.pre vals₁)) = x
    rw [h] at hguard₂
    cases hguard₂
    simp [Vector.push_eq_push] at h
    have heq := Vector.inj_map (by simp [Function.Injective]) h.2
    simp [heq]
  | output vals =>
    cases hguard₁ with | spec_output =>
    rename_i vals₁
    generalize h :
      (Vector.map Sum.inl vals₁).push (Sum.inr (ioSpec.post vals₁)) = x
    rw [h] at hguard₂
    cases hguard₂
    simp [Vector.push_eq_push] at h
    have heq := Vector.inj_map (by simp [Function.Injective]) h.2
    simp [heq]
  | τ =>
    cases hguard₁
    cases hguard₂
    rfl

/-- Similar to `congr_spec_guard` but for `OpSpec.TrivGuard`. -/
theorem congr_eq_mod_ghost_triv_guard
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  {l₁' l₂' : Label Op V m n}
  (hguard₁ : opSpec.TrivGuard l₁ l₁')
  (hguard₂ : opSpec.TrivGuard l₂ l₂')
  (heq : Label.EqMod EqModGhost l₁ l₂) : l₁' = l₂' := by
  cases l₁ <;> cases l₂
    <;> cases hguard₁
    <;> cases hguard₂
    <;> simp [Label.EqMod] at heq
  any_goals rfl
  case yield.yield.triv_yield.triv_yield =>
    have ⟨h₁, heq₂, heq₃⟩ := heq
    subst h₁
    replace ⟨heq₂, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq₂
    replace ⟨heq₃, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq₃
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq₂
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq₃
    simp [heq₂, heq₃]
  case input.input.triv_input.triv_input =>
    replace ⟨heq, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq
    simp [heq]
  case output.output.triv_output.triv_output =>
    replace ⟨heq, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq
    simp [heq]

end Wavelet.Dataflow
