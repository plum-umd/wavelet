import Wavelet.Determinacy.Defs

/-! Conversion between various stepping relations. -/

namespace Wavelet.Dataflow

open Semantics Determinacy

/-- Converts an indexed guarded step to a guarded step. -/
theorem Config.IdxGuardStep.to_guarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.IdxGuardStep opSpec ioSpec s (i, l) s') :
    (Config.GuardStep opSpec ioSpec) s l s'
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> simp at hl
  case spec_yield =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .spec_yield this
  case spec_join h₁ h₂ h₃ =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step (.spec_join h₁ h₂ h₃) this
  case spec_tau =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .spec_tau this

/-- Converts a guarded step to an indexed guarded step. -/
theorem Config.GuardStep.to_indexed_guarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.GuardStep opSpec ioSpec s l s') :
    ∃ i, Config.IdxGuardStep opSpec ioSpec s (i, l) s'
  := by
  cases hstep with | step hguard hstep
  cases hguard <;> simp at hl
  case step.spec_yield =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard .spec_yield) hstep'⟩
  case step.spec_join h₁ h₂ h₃ =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard (.spec_join h₁ h₂ h₃)) hstep'⟩
  case step.spec_tau =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, .step (.idx_guard .spec_tau) hstep'⟩

/-- Converts an indexed unguarded step to an unguarded step. -/
theorem Config.IdxTrivStep.to_unguarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.IdxTrivStep opSpec s (i, l) s') :
    Config.TrivStep opSpec s l s'
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> simp at hl
  case triv_yield =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_yield this
  case triv_join =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_join this
  case triv_tau =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_tau this

/-- Converts an unguarded step to an indexed unguarded step. -/
theorem Config.TrivStep.to_indexed_unguarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : Config.TrivStep opSpec s l s') :
    ∃ i, Config.IdxTrivStep opSpec s (i, l) s'
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
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n} :
    Config.IdxGuardStep opSpec ioSpec s (i, l) s' →
    Config.IdxTrivStep opSpec s (i, l) s'
  := Guard.map_guard (λ ⟨hguard⟩ => ⟨OpSpec.spec_guard_implies_triv_guard hguard⟩)

theorem Config.IdxInterpGuardStep.to_indexed_interp_unguarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n × opInterp.S} :
    Config.IdxInterpGuardStep opSpec ioSpec s (i, l) s' →
    Config.IdxInterpTrivStep opSpec s (i, l) s'
  := Lts.IndexedInterpStep.map_step Config.IdxGuardStep.to_indexed_unguarded

theorem Config.IdxInterpGuardStep.to_indexed_interp_unguarded_star
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n × opInterp.S}
  (htrace : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s') :
    (Config.IdxInterpTrivStep opSpec).Star s tr s'
  := htrace.map_step Config.IdxInterpGuardStep.to_indexed_interp_unguarded

end Wavelet.Dataflow
