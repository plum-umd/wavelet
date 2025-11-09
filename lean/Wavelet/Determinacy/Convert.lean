import Wavelet.Determinacy.Defs
import Wavelet.Determinacy.Determinism

/-! Conversion between various stepping relations. -/

namespace Wavelet.Dataflow

open Semantics Determinacy

variable
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}

/-- Converts an indexed guarded step to a guarded step. -/
theorem Config.IdxGuardStep.to_guarded
  [PCM T]
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hstep : Config.IdxGuardStep opSpec ioSpec s (i, l) s') :
    (Config.GuardStep opSpec ioSpec) s l s'
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard
  case spec_yield h₁ =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step (.spec_yield h₁) this
  case spec_join h₁ h₂ h₃ =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step (.spec_join h₁ h₂ h₃) this
  case spec_tau =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .spec_tau this
  any_goals cases hstep

/-- Converts a guarded step to an indexed guarded step. -/
theorem Config.GuardStep.to_indexed_guarded
  [PCM T]
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.GuardStep opSpec ioSpec s l s') :
    ∃ i, Config.IdxGuardStep opSpec ioSpec s (i, l) s'
  := by
  cases hstep with | step hguard hstep
  cases hguard <;> simp at hl
  case step.spec_yield h₁ =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard (.spec_yield h₁)) hstep'⟩
  case step.spec_join h₁ h₂ h₃ =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard (.spec_join h₁ h₂ h₃)) hstep'⟩
  case step.spec_tau =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, .step (.idx_guard .spec_tau) hstep'⟩

/-- Converts an indexed unguarded step to an unguarded step. -/
theorem Config.IdxTrivStep.to_unguarded
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hstep : Config.IdxTrivStep opSpec ioSpec s (i, l) s') :
    Config.TrivStep opSpec ioSpec s l s'
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard
  case triv_yield =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_yield this
  case triv_join =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_join this
  case triv_tau =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_tau this
  any_goals cases hstep

/-- Converts an unguarded step to an indexed unguarded step. -/
theorem Config.TrivStep.to_indexed_unguarded
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.TrivStep opSpec ioSpec s l s') :
    ∃ i, Config.IdxTrivStep opSpec ioSpec s (i, l) s'
  := by
  cases hstep with | step hguard hstep
  cases hguard <;> simp at hl
  case step.triv_yield =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard .triv_yield) hstep'⟩
  case step.triv_join =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard .triv_join) hstep'⟩
  case step.triv_tau =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, .step (.idx_guard .triv_tau) hstep'⟩

theorem Config.IdxGuardStep.to_indexed_unguarded
  [PCM T]
  {s s' : ConfigWithSpec opSpec ioSpec χ}
  {l : Label Op V m n} :
    Config.IdxGuardStep opSpec ioSpec s (i, l) s' →
    Config.IdxTrivStep opSpec ioSpec s (i, l) s'
  := .map_guard (λ ⟨hguard⟩ => ⟨OpSpec.spec_guard_implies_triv_guard hguard⟩)

theorem Config.IdxInterpGuardStep.to_indexed_interp_unguarded
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S} :
    Config.IdxInterpGuardStep opSpec ioSpec s (i, l) s' →
    Config.IdxInterpTrivStep opSpec ioSpec s (i, l) s'
  := Lts.IndexedInterpStep.map_step Config.IdxGuardStep.to_indexed_unguarded

theorem Config.IdxInterpGuardStep.to_indexed_interp_unguarded_star
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (htrace : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s') :
    (Config.IdxInterpTrivStep opSpec ioSpec).Star s tr s'
  := htrace.map_step Config.IdxInterpGuardStep.to_indexed_interp_unguarded

theorem Config.IdxInterpGuardStep.to_interp_guarded
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep : Config.IdxInterpGuardStep opSpec ioSpec s (i, l) s') :
    Config.InterpGuardStep opSpec ioSpec s l s'
  := hstep.to_interp Config.IdxGuardStep.to_guarded

theorem Config.IdxInterpGuardStep.to_interp_guarded_tau_star
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (htrace : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s') :
    (Config.InterpGuardStep opSpec ioSpec).TauStarN .τ tr.length s s'
  := by
  induction htrace with
  | refl => exact .refl
  | tail pref tail ih =>
    have := tail.to_interp_guarded
    have hl := proc_indexed_interp_guarded_step_label tail
    simp [hl] at this
    simp
    exact .tail ih this

theorem Config.InterpGuardStep.to_indexed_interp_guarded_tau
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep : Config.InterpGuardStep opSpec ioSpec s .τ s') :
    ∃ i, Config.IdxInterpGuardStep opSpec ioSpec s (i, .τ) s'
  := hstep.to_indexed_interp_tau Config.GuardStep.to_indexed_guarded

theorem Config.InterpGuardStep.to_interp_unguarded
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep : Config.InterpGuardStep opSpec ioSpec s l s') :
    Config.InterpTrivStep opSpec ioSpec s l s'
  := Lts.InterpStep.map_step (.map_guard opSpec.spec_guard_implies_triv_guard) hstep

theorem Config.InterpGuardStep.to_indexed_interp_guarded_tau_star
  [PCM T]
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (htrace : (Config.InterpGuardStep opSpec ioSpec).TauStarN .τ k s s') :
    ∃ tr,
      tr.length = k ∧
      (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s'
  := by
  induction htrace with
  | refl => exact ⟨_, by simp, .refl⟩
  | tail pref tail ih =>
    have ⟨_, h, pref'⟩ := ih
    have ⟨_, hstep'⟩ := tail.to_indexed_interp_guarded_tau
    exact ⟨_, by simp [h], .tail pref' hstep'⟩

theorem Config.IdxInterpTrivStep.to_interp_unguarded
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep : Config.IdxInterpTrivStep opSpec ioSpec s (i, l) s') :
    Config.InterpTrivStep opSpec ioSpec s l s'
  := hstep.to_interp Config.IdxTrivStep.to_unguarded

theorem Config.IdxInterpTrivStep.to_interp_unguarded_tau_star
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (htrace : (Config.IdxInterpTrivStep opSpec ioSpec).Star s tr s') :
    (Config.InterpTrivStep opSpec ioSpec).TauStarN .τ tr.length s s'
  := by
  induction htrace with
  | refl => exact .refl
  | tail pref tail ih =>
    have := tail.to_interp_unguarded
    have hl := proc_indexed_interp_unguarded_step_label tail
    simp [hl] at this
    simp
    exact .tail ih this

theorem Config.InterpTrivStep.to_indexed_interp_unguarded_tau
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (hstep : Config.InterpTrivStep opSpec ioSpec s .τ s') :
    ∃ i, Config.IdxInterpTrivStep opSpec ioSpec s (i, .τ) s'
  := hstep.to_indexed_interp_tau Config.TrivStep.to_indexed_unguarded

theorem Config.InterpTrivStep.to_indexed_interp_unuarded_tau_star
  [opInterp : OpInterp Op V]
  {s s' : ConfigWithSpec opSpec ioSpec χ × opInterp.S}
  (htrace : (Config.InterpTrivStep opSpec ioSpec).TauStarN .τ k s s') :
    ∃ tr,
      tr.length = k ∧
      (Config.IdxInterpTrivStep opSpec ioSpec).Star s tr s'
  := by
  induction htrace with
  | refl => exact ⟨_, by simp, .refl⟩
  | tail pref tail ih =>
    have ⟨_, h, pref'⟩ := ih
    have ⟨_, hstep'⟩ := tail.to_indexed_interp_unguarded_tau
    exact ⟨_, by simp [h], .tail pref' hstep'⟩

end Wavelet.Dataflow
