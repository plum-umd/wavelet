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

/-- Similar but with a specific length. -/
inductive Lts.TauStarN (lts : Lts C E) (τ : E) : Nat → C → C → Prop
  | refl : lts.TauStarN τ 0 c c
  | tail {n : Nat} {c₁ c₂ c₃ : C} :
      lts.TauStarN τ n c₁ c₂ → lts c₂ τ c₃ → lts.TauStarN τ (n + 1) c₁ c₃

theorem Lts.TauStar.with_length
  {lts : Lts C E} {τ : E}
  (htau : lts.TauStar τ c₁ c₂) : ∃ n, lts.TauStarN τ n c₁ c₂ := by
  induction htau with
  | refl => exact ⟨0, .refl⟩
  | tail htau' hstep ih =>
    rcases ih with ⟨n, htauN⟩
    exact ⟨n + 1, .tail htauN hstep⟩

theorem Lts.TauStarN.without_length
  {lts : Lts C E} {τ : E}
  {n : Nat}
  (htauN : lts.TauStarN τ n c₁ c₂) : lts.TauStar τ c₁ c₂ := by
  induction htauN with
  | refl => exact .refl
  | tail htauN' hstep ih => exact .tail ih hstep

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

theorem Lts.TauStarN.prepend
  {lts : Lts C E}
  (hhead : lts c₁ τ c₂)
  (htail : lts.TauStarN τ k c₂ c₃)
  : lts.TauStarN τ (1 + k) c₁ c₃ := by
  induction htail with
  | refl => exact Lts.TauStarN.tail .refl hhead
  | tail pref h ih => exact Lts.TauStarN.tail (ih hhead) h

theorem Lts.TauStarN.eq_len
  {lts : Lts C E} {τ : E}
  {n m : Nat}
  (htauN : lts.TauStarN τ n c₁ c₂)
  (heq : n = m) :
    lts.TauStarN τ m c₁ c₂ := by
  simp [heq] at htauN
  exact htauN

theorem Lts.TauStarN.trans
  {lts : Lts C E} {τ : E}
  (h₁ : lts.TauStarN τ k₁ c₁ c₂)
  (h₂ : lts.TauStarN τ k₂ c₂ c₃) :
    lts.TauStarN τ (k₁ + k₂) c₁ c₃
  := by
  induction h₁ generalizing k₂ with
  | refl => simp; exact h₂
  | tail h₁' hstep ih =>
    have := Lts.TauStarN.prepend hstep h₂
    exact .eq_len (ih this) (by omega)

/-- Alternative induction principal for `TauStar`. -/
theorem Lts.TauStar.reverse_induction
  {lts : Lts C E}
  {motive : ∀ c₁, lts.TauStar τ c₁ c₂ → Prop} {c₁ : C}
  (refl : motive c₂ .refl)
  (head : ∀ {c₁ c₁'}
    (hstep : lts.Step c₁ τ c₁')
    (htail : lts.TauStar τ c₁' c₂),
    motive c₁' htail → motive c₁ (htail.prepend hstep))
  (hsteps : lts.TauStar τ c₁ c₂) :
    motive c₁ hsteps
  := by
  induction hsteps with
  | refl => exact refl
  | tail pref tail ih =>
    rename_i c₁' c₂
    apply ih (head tail _ refl)
    intros _ _ hstep htail
    apply head hstep

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

/-- Append multiple τ steps at the end of `WeakStep`. -/
theorem Lts.WeakStep.tail_tau_star
  {lts : Lts C E} {τ : E}
  (hstep : lts.WeakStep τ c₁ l c₂)
  (htau : lts.TauStar τ c₂ c₃) :
  lts.WeakStep τ c₁ l c₃ := by
  cases hstep with
  | refl => exact .from_tau_star htau
  | step htau₁ hstep' htau₂ =>
    exact .step htau₁ hstep' (.trans htau₂ htau)

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

abbrev Trace.prepend (e : E) (tr : Trace E) : Trace E := e :: tr

inductive Lts.Plus (R : Lts C E) : Lts C (Trace E) where
  | single : R c tr c' → Plus R c (.single tr) c'
  | tail : Plus R c tr c' → R c' tr' c'' → Plus R c (.cons tr tr') c''

inductive Lts.Star (R : Lts C E) : Lts C (Trace E) where
  | refl : Star R c .ε c
  | tail : Star R c tr c' → R c' tr' c'' → Star R c (.cons tr tr') c''

theorem Lts.Star.prepend
  {lts : Lts C E} {l : E}
  (hhead : lts.Step c₁ l c₂)
  (htail : lts.Star c₂ tr c₃) :
    lts.Star c₁ (tr.prepend l) c₃ := by
  induction htail with
  | refl => exact .tail (.refl) hhead
  | tail _ h ih => exact .tail (ih hhead) h

/-- Alternative induction principal for `Star`. -/
theorem Lts.Star.reverse_induction
  {lts : Lts C E}
  {motive : ∀ tr c₁, lts.Star c₁ tr c₂ → Prop} {c₁ : C}
  (refl : motive [] c₂ .refl)
  (head : ∀ {c₁ c₁' l tr}
    (hstep : lts.Step c₁ l c₁')
    (htail : lts.Star c₁' tr c₂),
    motive tr c₁' htail → motive (tr.prepend l) c₁ (htail.prepend hstep))
  (hsteps : lts.Star c₁ tr c₂) :
    motive tr c₁ hsteps
  := by
  induction hsteps with
  | refl => exact refl
  | tail pref tail ih =>
    rename_i c₁' c₂
    apply ih (head tail _ refl)
    intros _ _ _ _ hstep htail
    apply head hstep

theorem Lts.Star.map_step
  {lts : Lts C E} {lts' : Lts C E}
  (hmap : ∀ {c₁ c₂ l}, lts.Step c₁ l c₂ → lts'.Step c₁ l c₂)
  (hsteps : lts.Star c₁ tr c₂) : lts'.Star c₁ tr c₂ := by
  induction hsteps with
  | refl => exact .refl
  | tail hpref hstep ih => exact .tail ih (hmap hstep)

theorem Lts.Star.map_hetero_step
  {lts : Lts C E} {lts' : Lts C E'}
  (hmap : ∀ {c₁ c₂ l}, lts.Step c₁ l c₂ → ∃ l', lts'.Step c₁ l' c₂)
  (hsteps : lts.Star c₁ tr c₂) : ∃ tr', lts'.Star c₁ tr' c₂ := by
  induction hsteps with
  | refl => exact ⟨_, .refl⟩
  | tail hpref hstep ih =>
    have ⟨_, hpref'⟩ := ih
    have ⟨_, hstep'⟩ := hmap hstep
    exact ⟨_, .tail hpref' hstep'⟩

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

theorem Lts.Simulation.sim_init
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  {R : C₁ → C₂ → Prop}
  (hsim : Lts.Simulation lts₁ lts₂ R c₁ c₂) :
  R c₁ c₂ := hsim.init

theorem Lts.Simulation.sim_step
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  {R : C₁ → C₂ → Prop}
  (hsim : Lts.Simulation lts₁ lts₂ R c₁ c₂) :
  ∀ c₁ c₂ l c₁',
    R c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      R c₁' c₂' := hsim.coind

/-- Existence of a simulation satisfying a relation `R`. -/
def Lts.SimilaritySt
  (R : C₁ → C₂ → Prop)
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (c₁ : C₁) (c₂ : C₂) : Prop :=
  ∃ Sim : C₁ → C₂ → Prop,
    lts₁.Simulation lts₂ Sim c₁ c₂ ∧
    ∀ c₁ c₂, Sim c₁ c₂ → R c₁ c₂

def Lts.Similarity
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (c₁ : C₁) (c₂ : C₂) : Prop
  := Lts.SimilaritySt (λ _ _ => True) lts₁ lts₂ c₁ c₂

theorem Lts.SimilaritySt.to_sim
  {R : C₁ → C₂ → Prop}
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.SimilaritySt R lts₁ lts₂ c₁ c₂) :
    Lts.Similarity lts₁ lts₂ c₁ c₂
  := by
  rcases hsim with ⟨Sim, hsim, _⟩
  exact ⟨Sim, hsim, by simp⟩

theorem Lts.SimilaritySt.intro
  {R : C₁ → C₂ → Prop}
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (Sim : C₁ → C₂ → Prop)
  (hsim : lts₁.Simulation lts₂ Sim c₁ c₂)
  (hR : ∀ {c₁ c₂}, Sim c₁ c₂ → R c₁ c₂) :
    Lts.SimilaritySt R lts₁ lts₂ c₁ c₂
  := by exists Sim

theorem Lts.Similarity.intro
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (Sim : C₁ → C₂ → Prop)
  (hsim : lts₁.Simulation lts₂ Sim c₁ c₂) :
    Lts.Similarity lts₁ lts₂ c₁ c₂
  := by
  exists Sim
  exact ⟨hsim, by simp⟩

theorem Lts.Simulation.to_sim
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {R : C₁ → C₂ → Prop}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : lts₁.Simulation lts₂ R c₁ c₂)
  : Lts.Similarity lts₁ lts₂ c₁ c₂ := .intro _ hsim

abbrev Lts.SimilaritySt.Sim
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.SimilaritySt R lts₁ lts₂ c₁ c₂) :
    C₁ → C₂ → Prop := hsim.choose

theorem Lts.SimilaritySt.sim_init
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.SimilaritySt R lts₁ lts₂ c₁ c₂) :
    hsim.Sim c₁ c₂ := hsim.choose_spec.1.init

theorem Lts.SimilaritySt.sim_step
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.SimilaritySt R lts₁ lts₂ c₁ c₂) :
  ∀ c₁ c₂ l c₁',
    hsim.Sim c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      hsim.Sim c₁' c₂' := hsim.choose_spec.1.coind

theorem Lts.SimilaritySt.sim_prop
  {lts₁ : Lts C₁ E}
  {lts₂ : Lts C₂ E}
  {c₁ : C₁} {c₂ : C₂}
  (hsim : Lts.SimilaritySt R lts₁ lts₂ c₁ c₂) :
    ∀ c₁ c₂, hsim.Sim c₁ c₂ → R c₁ c₂ := hsim.choose_spec.2

theorem Lts.Similarity.refl_single
  {lts₁ lts₂ : Lts C E} {c : C}
  (single : ∀ {c l c'}, lts₁.Step c l c' → lts₂.Step c l c') :
  Lts.Similarity lts₁ lts₂ c c := ⟨
    λ c₁ c₂ => c₁ = c₂,
    ⟨
      by simp,
      by
        intros c₁ c₂ l c₁' hc₁ hstep
        subst hc₁
        exists c₁'
        simp [single hstep],
    ⟩,
    by simp,
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
  rintro ⟨R₁₂, ⟨hsim₁₂_init, hsim₁₂_coind⟩, _⟩
  rintro ⟨R₂₃, ⟨hsim₂₃_init, hsim₂₃_coind⟩, _⟩
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
