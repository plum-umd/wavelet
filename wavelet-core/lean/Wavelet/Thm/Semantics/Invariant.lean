import Wavelet.Semantics.Defs

/-! Definitions for invariants on semantics and LTSs. -/

namespace Wavelet.Semantics

/-- An invariant holds for all states reachable via the given set of labels. -/
def Lts.IsInvariantForAt
  (lts : Lts C E) (Labels : E → Prop) (P : C → Prop) (c : C) : Prop :=
  ∀ {c' tr}, lts.Star c tr c' → (∀ {l}, l ∈ tr → Labels l) → P c'

/-- An invariant holds for all state reachable from the given state. -/
def Lts.IsInvariantAt
  (lts : Lts C E) (P : C → Prop) (c : C) : Prop :=
  ∀ {c' tr}, lts.Star c tr c' → P c'

/-- A property `P` is an invariant at `s` if it is satisfied
by every reachable state from `s`. -/
def IsInvariantAt
  [Arity Op]
  (sem : Semantics Op V m n)
  (P : sem.S → Prop)
  (s : sem.S) : Prop := sem.lts.IsInvariantAt P s

def IsInvariant
  [Arity Op]
  (sem : Semantics Op V m n)
  (P : sem.S → Prop) : Prop := sem.IsInvariantAt P sem.init

/-- Prove an invariant by induction. -/
theorem Lts.IsInvariantAt.by_induction
  {lts : Lts C E}
  {P : C → Prop}
  {c : C}
  (hbase : P c)
  (hstep : ∀ {c₁ c₂ l},
    P c₁ → lts.Step c₁ l c₂ → P c₂) :
  lts.IsInvariantAt P c := by
  intros c' tr hstar
  induction hstar with
  | refl => exact hbase
  | tail pref tail ih => exact hstep (ih hbase) tail

theorem Lts.IsInvariantForAt.by_induction
  {lts : Lts C E}
  {Labels : E → Prop}
  {P : C → Prop}
  {c : C}
  (hbase : P c)
  (hstep : ∀ {c₁ c₂ l},
    P c₁ → Labels l → lts.Step c₁ l c₂ → P c₂) :
  lts.IsInvariantForAt Labels P c := by
  intros c' tr hstar hlabels
  induction hstar with
  | refl => exact hbase
  | tail pref tail ih =>
    simp at hlabels
    have := ih hbase (λ hl => hlabels (.inl hl))
    exact hstep this (hlabels (.inr rfl)) tail

/-- Prove an invariant by strong induction. -/
theorem Lts.IsInvariantAt.by_strong_induction
  {lts : Lts C E}
  {P : C → Prop}
  {c : C}
  (hbase : P c)
  (hstep : ∀ {c₁ c₂ l tr},
    lts.Star c tr c₁ → P c₁ → lts.Step c₁ l c₂ → P c₂) :
  lts.IsInvariantAt P c := by
  intros c' tr hstar
  induction hstar with
  | refl => exact hbase
  | tail pref tail ih =>
    exact hstep pref (ih hbase hstep) tail

theorem Lts.IsInvariantForAt.by_strong_induction
  {lts : Lts C E}
  {Labels : E → Prop}
  {P : C → Prop}
  {c : C}
  (hbase : P c)
  (hstep : ∀ {c₁ c₂ l tr},
    lts.Star c tr c₁ → (∀ {l}, l ∈ tr → Labels l) →
    P c₁ → Labels l → lts.Step c₁ l c₂ → P c₂) :
  lts.IsInvariantForAt Labels P c := by
  intros c' tr hstar hlabels
  induction hstar with
  | refl => exact hbase
  | tail pref tail ih =>
    simp at hlabels
    grind only [cases Or]

theorem Lts.IsInvariantAt.base
  {lts : Lts C E}
  {P : C → Prop} {c : C}
  (hinv : lts.IsInvariantAt P c) : P c := hinv .refl

theorem Lts.IsInvariantForAt.base
  {lts : Lts C E}
  {Labels : E → Prop}
  {P : C → Prop} {c : C}
  (hinv : lts.IsInvariantForAt Labels P c) : P c := hinv .refl (by simp)

theorem Lts.IsInvariantAt.unfold
  {lts : Lts C E}
  {P : C → Prop} {c c' : C} {l : E}
  (hinv : lts.IsInvariantAt P c)
  (hstep : lts.Step c l c') :
    P c' ∧ lts.IsInvariantAt P c'
  := ⟨
    hinv (Lts.Star.tail .refl hstep),
    by
      intros c'' tr hstar
      exact hinv (hstar.prepend hstep)⟩

theorem Lts.IsInvariantForAt.unfold
  {lts : Lts C E}
  {Labels : E → Prop}
  {P : C → Prop} {c c' : C} {l : E}
  (hinv : lts.IsInvariantForAt Labels P c)
  (hstep : lts.Step c l c')
  (hl : Labels l) :
    P c' ∧ lts.IsInvariantForAt Labels P c'
  := ⟨
    hinv (Lts.Star.tail .refl hstep) (by simp [hl]),
    by
      intros c'' tr hstar htr
      exact hinv (hstar.prepend hstep)
        (by
          intros l' hl'
          simp at hl'
          cases hl' <;> rename_i h
          · subst h; exact hl
          · exact htr h)⟩

theorem Lts.IsInvariantAt.map_step
  {lts₁ : Lts C E₁}
  {lts₂ : Lts C E₂}
  {P : C → Prop}
  (hmap : ∀ {c c' l}, lts₂.Step c l c' → ∃ l', lts₁.Step c l' c')
  (hinv : lts₁.IsInvariantAt P c) : lts₂.IsInvariantAt P c := by
  intros c tr hsteps
  have ⟨_, hsteps'⟩ := hsteps.map_hetero_step hmap
  exact hinv hsteps'

theorem Lts.IsInvariantForAt.map_step
  {lts₁ : Lts C E₁}
  {lts₂ : Lts C E₂}
  {Labels₁ : E₁ → Prop}
  {Labels₂ : E₂ → Prop}
  {P : C → Prop}
  (hmap : ∀ {c c' l₂},
    Labels₂ l₂ → lts₂.Step c l₂ c' → ∃ l₁, Labels₁ l₁ ∧ lts₁.Step c l₁ c')
  (hinv : lts₁.IsInvariantForAt Labels₁ P c) :
    lts₂.IsInvariantForAt Labels₂ P c := by
  intros c₁ tr hsteps htr
  have ⟨tr', htr', hsteps'⟩ := hsteps.map_hetero_step_alt hmap htr
  exact hinv hsteps' htr'

/-- Converts `IsInvariantForAt` to `IsInvariantAt` when the
label restriction always holds in the LTS. -/
theorem Lts.IsInvariantForAt.to_inv_at
  {lts : Lts C E}
  {Labels : E → Prop}
  {P : C → Prop}
  (hl : ∀ {c l c'}, lts.Step c l c' → Labels l)
  (hinv : lts.IsInvariantForAt Labels P c) : lts.IsInvariantAt P c := by
  intros c₁ tr hsteps
  induction hsteps using Lts.Star.reverse_induction with
  | refl => exact hinv .refl (by simp)
  | head head tail ih =>
    apply ih
    exact (hinv.unfold head (hl head)).2

theorem Lts.IsInvariantForAt.imp_labels
  {lts : Lts C E}
  {Labels₁ Labels₂ : E → Prop}
  {P : C → Prop}
  (himp : ∀ l, Labels₂ l → Labels₁ l)
  (hinv : lts.IsInvariantForAt Labels₁ P c) :
    lts.IsInvariantForAt Labels₂ P c := by
  intros c' tr hstar hlabels
  exact hinv hstar (by intros l hl; exact himp l (hlabels hl))

theorem Lts.IsInvariantAt.imp
  {lts : Lts C E}
  {P₁ P₂ : C → Prop}
  (himp : ∀ c, P₁ c → P₂ c)
  (hinv : lts.IsInvariantAt P₁ c) : lts.IsInvariantAt P₂ c := by
  intros c' tr hstar
  exact himp _ (hinv hstar)

def Lts.IsFinal (lts : Lts C E) (c : C) : Prop :=
  ∀ {c' l}, ¬ lts.Step c l c'

def Lts.IsFinalFor (lts : Lts C E) (Labels : E → Prop) (c : C) : Prop :=
  ∀ {c' l}, Labels l → ¬ lts.Step c l c'

@[simp]
def IsFinal
  [Arity Op]
  (sem : Semantics Op V m n)
  (s : sem.S) : Prop := sem.lts.IsFinal s

@[simp]
def IsFinalFor
  [Arity Op]
  (sem : Semantics Op V m n)
  (Labels : Label Op V m n → Prop)
  (s : sem.S) : Prop := sem.lts.IsFinalFor Labels s

theorem Lts.IsFinalFor.map_step
  {lts₁ : Lts C E₁}
  {lts₂ : Lts C E₂}
  {Labels₁ : E₁ → Prop}
  {Labels₂ : E₂ → Prop}
  (hmap : ∀ {c c' l₂},
    Labels₂ l₂ → lts₂.Step c l₂ c' →
    ∃ l₁, Labels₁ l₁ ∧ lts₁.Step c l₁ c')
  (hfinal : lts₁.IsFinalFor Labels₁ c) : lts₂.IsFinalFor Labels₂ c := by
  intros c' l₂ hlabel hstep
  have ⟨l₁, hlabel₁, hstep₁⟩ := hmap hlabel hstep
  exact hfinal hlabel₁ hstep₁

end Wavelet.Semantics
