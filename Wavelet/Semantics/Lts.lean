/-! Definitions and utilities for labelled transition systems. -/

namespace Wavelet.Semantics

abbrev Lts (C : Type u) (E : Type v) := C → E → C → Prop

abbrev Lts.Step (lts : Lts C E) := lts

/-- Zero or more steps with the given label -/
inductive Lts.TauStar (lts : Lts C E) (τ : E) : C → C → Prop
  | refl : lts.TauStar τ c c
  | tail {c₁ c₂ c₃ : C} :
      lts.TauStar τ c₁ c₂ → lts c₂ τ c₃ → lts.TauStar τ c₁ c₃

theorem Lts.TauStar.prepend
  {lts : Lts C E}
  (hhead : lts c₁ τ c₂)
  (htail : lts.TauStar τ c₂ c₃)
  : lts.TauStar τ c₁ c₃ := by
  induction htail with
  | refl => exact Lts.TauStar.tail .refl hhead
  | tail _ h ih => exact Lts.TauStar.tail ih h

theorem Lts.TauStar.trans
  {lts : Lts C E}
  (h₁ : lts.TauStar τ c₁ c₂)
  (h₂ : lts.TauStar τ c₂ c₃) :
  lts.TauStar τ c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | tail h₁' hstep ih =>
    have := Lts.TauStar.prepend hstep h₂
    exact ih this

/-- A non-tau step preceded and followed by zero or more tau steps. -/
inductive Lts.StepModTau (lts : Lts C E) (τ : E) : Lts C E where
  | mk :
      lts.TauStar τ c₁ c₂ →
      lts c₂ e c₃ →
      lts.TauStar τ c₃ c₄ →
      lts.StepModTau τ c₁ e c₄

/-- Introduces a single step without any τ events -/
def Lts.StepModTau.single
  {lts : Lts C E} {τ : E}
  (hstep : lts.Step c₁ l c₂)
  : lts.StepModTau τ c₁ l c₂ := ⟨.refl, hstep, .refl⟩

/-- Append a τ step at the end of `StepModTau`. -/
theorem Lts.StepModTau.tail_tau
  {lts : Lts C E} {τ : E}
  (hstep : lts.StepModTau τ c₁ l c₂)
  (htau : lts.Step c₂ τ c₃)
  : lts.StepModTau τ c₁ l c₃ := by
  have ⟨h₁, h₂, h₃⟩ := hstep
  exact ⟨h₁, h₂, Lts.TauStar.tail h₃ htau⟩

theorem Lts.StepModTau.to_tau_star
  {lts : Lts C E} {τ : E}
  (hstep : lts.StepModTau τ c₁ τ c₂)
  : lts.TauStar τ c₁ c₂ := by
  have ⟨h₁, h₂, h₃⟩ := hstep
  exact .trans h₁ (.prepend h₂ h₃)

theorem Lts.StepModTau.tail_non_tau
  {lts : Lts C E} {τ : E}
  (htau_steps : lts.StepModTau τ c₁ τ c₂)
  (hstep : lts.Step c₂ l c₃)
  : lts.StepModTau τ c₁ l c₃ :=
  ⟨htau_steps.to_tau_star, hstep, .refl⟩

theorem Lts.StepModTau.eq_rhs
  {lts : Lts C E} {τ : E}
  (hstep : lts.StepModTau τ c₁ l c₂)
  (heq : c₂ = c₂') :
  lts.StepModTau τ c₁ l c₂' := by
  simp [heq] at hstep
  exact hstep

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

structure Lts.SimulatedBy
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (R : C₁ → C₂ → Prop)
  (c₁ : C₁) (c₂ : C₂) : Prop where
  init : R c₁ c₂
  coind : ∀ c₁ c₂ l c₁',
    R c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      R c₁' c₂'

inductive Lts.SimilarBy
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (c₁ : C₁) (c₂ : C₂) : Prop where
  | mk (Sim : C₁ → C₂ → Prop) :
      lts₁.SimulatedBy lts₂ Sim c₁ c₂ →
      SimilarBy lts₁ lts₂ c₁ c₂

theorem Lts.SimilarBy.refl
  {lts : Lts C E} {c : C} :
  Lts.SimilarBy lts lts c c := ⟨
    λ c₁ c₂ => c₁ = c₂,
    by simp,
    by
      intros c₁ c₂ l c₁' hc₁ hstep
      subst hc₁
      exists c₁'
  ⟩

theorem Lts.SimilarBy.trans
  {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {E : Type u₄}
  {lts₁ : Lts C₁ E} {lts₂ : Lts C₂ E} {lts₃ : Lts C₃ E}
  {c₁ : C₁} {c₂ : C₂} {c₃ : C₃} :
  Lts.SimilarBy lts₁ lts₂ c₁ c₂ →
  Lts.SimilarBy lts₂ lts₃ c₂ c₃ →
  Lts.SimilarBy lts₁ lts₃ c₁ c₃ := by
  rintro ⟨R₁₂, hsim₁₂_init, hsim₁₂_coind⟩
  rintro ⟨R₂₃, hsim₂₃_init, hsim₂₃_coind⟩
  apply Lts.SimilarBy.mk λ c₁ c₃ => ∃ c₂, R₁₂ c₁ c₂ ∧ R₂₃ c₂ c₃
  constructor
  · exists c₂
  · intros c₁ c₃ l c₁' hR hstep_c₁
    have ⟨c₂, hR₁₂, hR₂₃⟩ := hR
    have ⟨c₂', hstep_c₂, hR₁₂'⟩ := hsim₁₂_coind c₁ c₂ l c₁' hR₁₂ hstep_c₁
    have ⟨c₃', hstep_c₃, hR₂₃'⟩ := hsim₂₃_coind c₂ c₃ l c₂' hR₂₃ hstep_c₂
    exists c₃'
    constructor
    · exact hstep_c₃
    · exists c₂'

end Wavelet.Semantics
