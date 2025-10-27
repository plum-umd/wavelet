import Wavelet.Determinacy.Defs
import Wavelet.Determinacy.Determinism

/-! Lemmas about converting steps through `EqMod`. -/

namespace Wavelet.Dataflow

open Semantics Determinacy

theorem async_op_interp_congr
  [InterpConsts V]
  {aop aop' aop₁ aop₁' : AsyncOp (V ⊕ T)}
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop₁)
  (heq_aop : AsyncOp.EqMod EqModGhost aop aop')
  (heq_inputs : List.Forall₂ EqModGhost inputVals inputVals') :
    ∃ outputVals',
      AsyncOp.Interp aop'
        (.mk allInputs allOutputs inputs inputVals' outputs outputVals') aop₁' ∧
      AsyncOp.EqMod EqModGhost aop₁ aop₁' ∧
      List.Forall₂ EqModGhost outputVals outputVals'
  := sorry

theorem proc_indexed_unguarded_congr
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n}
  {l : Nat × Label Op V m n}
  (hstep : (Config.IdxTrivStep opSpec).Step s₁ l s₂)
  (heq : Config.EqMod EqModGhost s₁ s₁') :
    ∃ s₂',
      (Config.IdxTrivStep opSpec).Step s₁' l s₂' ∧
      Config.EqMod EqModGhost s₂ s₂'
  := by
  have hl := proc_indexed_unguarded_step_label hstep
  have ⟨heq_aps, heq_chans⟩ := heq
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hstep with
  | step_op => sorry
  | step_async hi hget hinterp hpop => sorry
    -- replace ⟨_, _, hpop, heq_outputs, heq_chans'⟩ := chan_map_pop_vals_equiv heq_chans hpop
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

theorem proc_indexed_interp_unguarded_congr
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hstep : (Config.IdxInterpTrivStep opSpec).Step s₁ l s₂)
  (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      (Config.IdxInterpTrivStep opSpec).Step s₁' l s₂' ∧
      Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
      s₂.2 = s₂'.2
  := by
  have hl := proc_indexed_interp_unguarded_step_label hstep
  cases hstep with
  | step_yield hstep hinterp =>
    have ⟨_, hstep', heq'⟩ := proc_indexed_unguarded_congr hstep heq.1
    simp at heq
    simp [heq.2] at hinterp
    exact ⟨
      _, .step_yield hstep' hinterp,
      by
        simp at heq ⊢
        simp [heq']
    ⟩
  | step_tau hstep =>
    have ⟨_, hstep', heq'⟩ := proc_indexed_unguarded_congr hstep heq.1
    exact ⟨
      _, .step_tau hstep',
      by
        simp at heq ⊢
        simp [heq, heq']
    ⟩
  | _ hstep => simp at hl

theorem proc_indexed_interp_unguarded_steps_congr
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (htrace : (Config.IdxInterpTrivStep opSpec).Star s₁ tr s₂)
  (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      (Config.IdxInterpTrivStep opSpec).Star s₁' tr s₂' ∧
      Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
      s₂.2 = s₂'.2
  := by
  induction htrace
    using Lts.Star.reverse_induction
    generalizing s₁' with
  | refl => exact ⟨s₁', .refl, heq⟩
  | head hstep htail ih =>
    have ⟨_, hstep', heq₁⟩ := proc_indexed_interp_unguarded_congr hstep heq
    have ⟨_, htail', heq₂⟩ := ih heq₁
    exact ⟨_, htail'.prepend hstep', heq₂⟩

end Wavelet.Dataflow
