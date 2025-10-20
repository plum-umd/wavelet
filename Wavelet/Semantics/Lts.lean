/-! Definitions and utilities for labelled transition systems. -/

namespace Wavelet.Semantics

abbrev Lts (C : Type u) (E : Type v) := C → E → C → Prop

abbrev Lts.Step (lts : Lts C E) := lts

theorem Lts.Step.eq_rhs
  {lts : Lts C E}
  (hstep : lts.Step c₁ l c₂)
  (heq : c₂ = c₂') :
  lts.Step c₁ l c₂' := by
  simp [heq] at hstep
  exact hstep

theorem Lts.Step.eq_lhs
  {lts : Lts C E}
  (hstep : lts.Step c₁ l c₂)
  (heq : c₁ = c₁') :
  lts.Step c₁' l c₂ := by
  simp [heq] at hstep
  exact hstep

/-- Zero or more steps with the given label -/
inductive Lts.TauStar (lts : Lts C E) (τ : E) : C → C → Prop
  | refl : lts.TauStar τ c c
  | tail {c₁ c₂ c₃ : C} :
      lts.TauStar τ c₁ c₂ → lts c₂ τ c₃ → lts.TauStar τ c₁ c₃

/-- Map each transition to a different `lts` while keeping the same states. -/
theorem Lts.TauStar.map
  {lts : Lts C E} {τ : E}
  {lts' : Lts C E'} {τ' : E'}
  (hmap : ∀ {c₁ c₂}, lts c₁ τ c₂ → lts' c₁ τ' c₂)
  (htau : lts.TauStar τ c₁ c₂) :
  lts'.TauStar τ' c₁ c₂ := by
  induction htau with
  | refl => exact .refl
  | tail htau hstep ih =>
    exact .tail ih (hmap hstep)

theorem Lts.TauStar.eq_rhs
  {lts : Lts C E}
  (hstep : lts.TauStar τ c₁ c₂)
  (heq : c₂ = c₂') :
  lts.TauStar τ c₁ c₂' := by
  simp [heq] at hstep
  exact hstep

theorem Lts.TauStar.eq_lhs
  {lts : Lts C E}
  (hstep : lts.TauStar τ c₁ c₂)
  (heq : c₁ = c₁') :
  lts.TauStar τ c₁' c₂ := by
  simp [heq] at hstep
  exact hstep

theorem Lts.TauStar.single
  {lts : Lts C E} {τ : E}
  (hstep : lts c₁ τ c₂) :
  lts.TauStar τ c₁ c₂ := Lts.TauStar.tail .refl hstep

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

/-- Induction principal for `TauStar` from the left of the trace. -/
def TauStar.reverseInduction
  {lts : Lts C E} {τ : E}
  {motive : ∀ {c₁ c₂}, lts.TauStar τ c₁ c₂ → Prop}
  (refl : ∀ c, motive (.refl : lts.TauStar τ c c))
  (head : ∀ {c₁ c₂ c₃}
    (hstep : lts c₁ τ c₂)
    (htau : lts.TauStar τ c₂ c₃),
    motive htau → motive (.prepend hstep htau))
  (htau : lts.TauStar τ c₁ c₂) :
    motive htau
  := by
  cases htau with
  | refl => apply refl
  | tail pref tail =>

    sorry

/-- A non-τ step preceded and followed by zero or more tau steps,
or zero or more τ steps. -/
inductive Lts.WeakStep (lts : Lts C E) (τ : E) : Lts C E where
  | refl : lts.WeakStep τ c τ c
  | step :
      lts.TauStar τ c₁ c₂ →
      lts c₂ e c₃ →
      lts.TauStar τ c₃ c₄ →
      lts.WeakStep τ c₁ e c₄

/-- Introduces a single step without any τ events -/
def Lts.WeakStep.single
  {lts : Lts C E} {τ : E}
  (hstep : lts.Step c₁ l c₂) :
  lts.WeakStep τ c₁ l c₂ := .step .refl hstep .refl

/-- Append a τ step at the end of `WeakStep`. -/
theorem Lts.WeakStep.tail_tau
  {lts : Lts C E} {τ : E}
  (hstep : lts.WeakStep τ c₁ l c₂)
  (htau : lts.Step c₂ τ c₃) :
  lts.WeakStep τ c₁ l c₃ := by
  cases hstep with
  | refl => exact .step .refl htau .refl
  | step htau₁ hstep' htau₂ =>
    exact .step htau₁ hstep' (.tail htau₂ htau)

theorem Lts.WeakStep.to_tau_star
  {lts : Lts C E} {τ : E}
  (hstep : lts.WeakStep τ c₁ τ c₂)
  : lts.TauStar τ c₁ c₂ := by
  cases hstep with
  | refl => exact .refl
  | step htau₁ hstep' htau₂ =>
    exact .trans htau₁ (.prepend hstep' htau₂)

theorem Lts.WeakStep.from_tau_star
  {lts : Lts C E} {τ : E}
  (htau : lts.TauStar τ c₁ c₂)
  : lts.WeakStep τ c₁ τ c₂ := by
  induction htau with
  | refl => exact .refl
  | tail htau' hstep ih =>
    exact .tail_tau ih hstep

theorem Lts.WeakStep.tail_non_tau
  {lts : Lts C E} {τ : E}
  (htau_steps : lts.WeakStep τ c₁ τ c₂)
  (hstep : lts.Step c₂ l c₃)
  : lts.WeakStep τ c₁ l c₃ :=
  .step htau_steps.to_tau_star hstep .refl

theorem Lts.WeakStep.eq_rhs
  {lts : Lts C E} {τ : E}
  (hstep : lts.WeakStep τ c₁ l c₂)
  (heq : c₂ = c₂') :
  lts.WeakStep τ c₁ l c₂' := by
  simp [heq] at hstep
  exact hstep

abbrev Trace := List

abbrev Trace.ε : Trace E := []

abbrev Trace.single (e : E) : Trace E := [e]

abbrev Trace.cons (tr : Trace E) (e : E) : Trace E := tr ++ [e]

inductive Lts.Plus (R : Lts C E) : Lts C (Trace E) where
  | single : R c tr c' → Plus R c (.single tr) c'
  | tail : Plus R c tr c' → R c' tr' c'' → Plus R c (.cons tr tr') c''

inductive Lts.Star (R : Lts C E) : Lts C (Trace E) where
  | refl : Star R c .ε c
  | tail : Star R c tr c' → R c' tr' c'' → Star R c (.cons tr tr') c''

structure Lts.Simulation
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

def Lts.Similarity
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (c₁ : C₁) (c₂ : C₂) : Prop :=
  ∃ Sim : C₁ → C₂ → Prop, lts₁.Simulation lts₂ Sim c₁ c₂

theorem Lts.Similarity.intro
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (Sim : C₁ → C₂ → Prop)
  (hsim : lts₁.Simulation lts₂ Sim c₁ c₂)
  : Lts.Similarity lts₁ lts₂ c₁ c₂ := by exists Sim

abbrev Lts.Similarity.Sim
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Similarity lts₁ lts₂ c₁ c₂) :
  C₁ → C₂ → Prop := hsim.choose

theorem Lts.Similarity.sim_init
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Similarity lts₁ lts₂ c₁ c₂) :
  hsim.Sim c₁ c₂ := hsim.choose_spec.init

theorem Lts.Similarity.sim_step
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Similarity lts₁ lts₂ c₁ c₂) :
  ∀ c₁ c₂ l c₁',
    hsim.Sim c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      hsim.Sim c₁' c₂' := hsim.choose_spec.coind

theorem Lts.Similarity.refl_single
  {lts₁ lts₂ : Lts C E} {c : C}
  (single : ∀ {c l c'}, lts₁.Step c l c' → lts₂.Step c l c') :
  Lts.Similarity lts₁ lts₂ c c := ⟨
    λ c₁ c₂ => c₁ = c₂,
    by simp,
    by
      intros c₁ c₂ l c₁' hc₁ hstep
      subst hc₁
      exists c₁'
      simp [single hstep]
  ⟩

theorem Lts.Similarity.refl
  {lts : Lts C E} {c : C} :
  Lts.Similarity lts lts c c := .refl_single (by simp)

theorem Lts.Similarity.trans_single
  {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {E : Type u₄}
  {lts₁ : Lts C₁ E} {lts₂ lts₂' : Lts C₂ E} {lts₃ : Lts C₃ E}
  {c₁ : C₁} {c₂ : C₂} {c₃ : C₃}
  (single₂ : ∀ {c l c'}, lts₂.Step c l c' → lts₂'.Step c l c') :
  Lts.Similarity lts₁ lts₂ c₁ c₂ →
  Lts.Similarity lts₂' lts₃ c₂ c₃ →
  Lts.Similarity lts₁ lts₃ c₁ c₃ := by
  rintro ⟨R₁₂, hsim₁₂_init, hsim₁₂_coind⟩
  rintro ⟨R₂₃, hsim₂₃_init, hsim₂₃_coind⟩
  apply Lts.Similarity.intro λ c₁ c₃ => ∃ c₂, R₁₂ c₁ c₂ ∧ R₂₃ c₂ c₃
  constructor
  · exists c₂
  · intros c₁ c₃ l c₁' hR hstep_c₁
    have ⟨c₂, hR₁₂, hR₂₃⟩ := hR
    have ⟨c₂', hstep_c₂, hR₁₂'⟩ := hsim₁₂_coind c₁ c₂ l c₁' hR₁₂ hstep_c₁
    have ⟨c₃', hstep_c₃, hR₂₃'⟩ := hsim₂₃_coind c₂ c₃ l c₂' hR₂₃ (single₂ hstep_c₂)
    exists c₃'
    constructor
    · exact hstep_c₃
    · exists c₂'

theorem Lts.Similarity.trans
  {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {E : Type u₄}
  {lts₁ : Lts C₁ E} {lts₂ : Lts C₂ E} {lts₃ : Lts C₃ E}
  {c₁ : C₁} {c₂ : C₂} {c₃ : C₃} :
  Lts.Similarity lts₁ lts₂ c₁ c₂ →
  Lts.Similarity lts₂ lts₃ c₂ c₃ →
  Lts.Similarity lts₁ lts₃ c₁ c₃ := .trans_single (by simp)

structure Lts.Bisimulation
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (R : C₁ → C₂ → Prop)
  (c₁ : C₁) (c₂ : C₂) : Prop where
  init : R c₁ c₂
  coind₁ : ∀ c₁ c₂ l c₁',
    R c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      R c₁' c₂'
  coind₂ : ∀ c₁ c₂ l c₂',
    R c₁ c₂ →
    lts₂.Step c₂ l c₂' →
    ∃ c₁',
      lts₁.Step c₁ l c₁' ∧
      R c₁' c₂'

def Lts.Bisimilarity
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (c₁ : C₁) (c₂ : C₂) : Prop :=
  ∃ Sim : C₁ → C₂ → Prop, lts₁.Bisimulation lts₂ Sim c₁ c₂

theorem Lts.Bisimilarity.intro
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (Sim : C₁ → C₂ → Prop)
  (hsim : lts₁.Bisimulation lts₂ Sim c₁ c₂)
  : Lts.Bisimilarity lts₁ lts₂ c₁ c₂ := by exists Sim

abbrev Lts.Bisimilarity.Bisim
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Bisimilarity lts₁ lts₂ c₁ c₂) :
  C₁ → C₂ → Prop := hsim.choose

theorem Lts.Bisimilarity.bisim_init
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Bisimilarity lts₁ lts₂ c₁ c₂) :
  hsim.Bisim c₁ c₂ := hsim.choose_spec.init

theorem Lts.Bisimilarity.sim_step₁
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Bisimilarity lts₁ lts₂ c₁ c₂) :
  ∀ c₁ c₂ l c₁',
    hsim.Bisim c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      hsim.Bisim c₁' c₂' := hsim.choose_spec.coind₁

theorem Lts.Bisimilarity.sim_step₂
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.Bisimilarity lts₁ lts₂ c₁ c₂) :
  ∀ c₁ c₂ l c₂',
    hsim.Bisim c₁ c₂ →
    lts₂.Step c₂ l c₂' →
    ∃ c₁',
      lts₁.Step c₁ l c₁' ∧
      hsim.Bisim c₁' c₂' := hsim.choose_spec.coind₂

theorem Lts.Bisimilarity.refl
  {lts : Lts C E} {c : C} :
  Lts.Bisimilarity lts lts c c :=
  ⟨
    λ c₁ c₂ => c₁ = c₂,
    by simp,
    (by
      intros c₁ c₂ l c₁' hc₁ hstep
      subst hc₁
      exists c₁'),
    (by
      intros c₁ c₂ l c₂' hc₁ hstep
      subst hc₁
      exists c₂'),
  ⟩

end Wavelet.Semantics
