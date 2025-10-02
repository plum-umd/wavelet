/-! Definitions and utilities for labelled transition systems. -/

namespace Wavelet.Lts

abbrev Lts (C : Type u) (E : Type v) := C → E → C → Prop

abbrev Lts.Step (lts : Lts C E) := lts

/-- Zero or more steps with the given label -/
inductive Lts.TauStar (lts : Lts C E) (τ : E) : C → C → Prop
  | refl : lts.TauStar τ c c
  | tail (c₁ c₂ c₃ : C) :
      lts.TauStar τ c₁ c₂ → lts c₂ τ c₃ → lts.TauStar τ c₁ c₃

/-- A non-tau step preceded and followed by zero or more tau steps. -/
inductive Lts.StepModTau (lts : Lts C E) (τ : E) : Lts C E where
  | mk :
      lts.TauStar τ c₁ c₂ →
      lts c₂ e c₃ →
      e ≠ τ →
      lts.TauStar τ c₃ c₄ →
      lts.StepModTau τ c₁ e c₄

/-- Introduces a single step without any τ events -/
def Lts.StepModTau.single
  {lts : Lts C E} {τ : E}
  (hstep : lts.Step c₁ l c₂) (hne : l ≠ τ)
  : lts.StepModTau τ c₁ l c₂ := ⟨.refl, hstep, hne, .refl⟩

abbrev Trace := List

abbrev Trace.ε : Trace E := []

abbrev Trace.single (e : E) : Trace E := [e]

abbrev Trace.cons (tr : Trace E) (e : E) : Trace E := tr ++ [e]

inductive LTS.Plus (R : Lts C E) : Lts C (Trace E) where
  | single : R c tr c' → Plus R c (.single tr) c'
  | tail : Plus R c tr c' → R c' tr' c'' → Plus R c (.cons tr tr') c''

inductive LTS.Star (R : Lts C E) : Lts C (Trace E) where
  | refl : Star R c .ε c
  | tail : Star R c tr c' → R c' tr' c'' → Star R c (.cons tr tr') c''

structure Lts.Simulates
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (R : C₁ → C₂ → Prop)
  (c₁ : C₁) (c₂ : C₂) : Prop where
  init : R c₁ c₂
  coind : ∀ c₁ l c₁',
    R c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      R c₁' c₂'

end Wavelet.Lts
