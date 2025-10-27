import Wavelet.Semantics.Defs

/-! Some definitions for confluence. -/

namespace Wavelet.Semantics

/-- Strong confluence of `c` when the labels are restricted
by the compatibility relation `Compat`. -/
def Lts.StronglyConfluentAt
  {C : Type u} {E : Type v}
  (lts : Lts C E)
  (Compat : E → E → Prop)
  (c : C) : Prop :=
  ∀ {c₁ c₂ : C} {l₁ l₂ : E},
    lts.Step c l₁ c₁ →
    lts.Step c l₂ c₂ →
    Compat l₁ l₂ →
    (l₁ = l₂ ∧ c₁ = c₂) ∨
    ∃ c',
      lts.Step c₁ l₂ c' ∧
      lts.Step c₂ l₁ c'

/-- Similar to `StronglyConfluentAt`, but modulo an equivalence relation on states. -/
def Lts.StronglyConfluentAtMod
  {C : Type u} {E : Type v}
  (lts : Lts C E)
  (Compat : E → E → Prop)
  (EqC : C → C → Prop)
  (EqE : E → E → Prop)
  (c : C) : Prop :=
  ∀ {c₁ c₂ : C} {l₁ l₂ : E},
    lts.Step c l₁ c₁ →
    lts.Step c l₂ c₂ →
    Compat l₁ l₂ →
    (EqE l₁ l₂ ∧ EqC c₁ c₂) ∨
    ∃ c₁' c₂',
      lts.Step c₁ l₂ c₁' ∧
      lts.Step c₂ l₁ c₂' ∧
      EqC c₁' c₂'

/-- Strong confluence of an LTS when restricted to a subset of states. -/
def Lts.StronglyConfluent
  {C : Type u} {E : Type v}
  (lts : Lts C E)
  (States : C → Prop)
  (Compat : E → E → Prop) : Prop :=
  ∀ {c : C}, States c → lts.StronglyConfluentAt Compat c

theorem Lts.strong_confl_at_imp_compat
  {lts : Lts C E}
  {Compat₁ Compat₂ : E → E → Prop}
  {c : C}
  (himp : ∀ {l₁ l₂}, Compat₂ l₁ l₂ → Compat₁ l₁ l₂)
  (hconfl : lts.StronglyConfluentAt Compat₁ c) :
    lts.StronglyConfluentAt Compat₂ c
  := by
  intros c₁ c₂ l₁ l₂ hstep₁ hstep₂ hcompat
  have hcompat' := himp hcompat
  exact hconfl hstep₁ hstep₂ hcompat'

theorem Lts.strong_confl_at_mod_imp_compat
  {lts : Lts C E}
  {Compat₁ Compat₂ : E → E → Prop}
  {EqC : C → C → Prop}
  {EqE : E → E → Prop}
  {c : C}
  (himp : ∀ {l₁ l₂}, Compat₂ l₁ l₂ → Compat₁ l₁ l₂)
  (hconfl : lts.StronglyConfluentAtMod Compat₁ EqC EqE c) :
    lts.StronglyConfluentAtMod Compat₂ EqC EqE c
  := by
  intros c₁ c₂ l₁ l₂ hstep₁ hstep₂ hcompat
  have hcompat' := himp hcompat
  exact hconfl hstep₁ hstep₂ hcompat'

/--
Having a terminating trace in a confluent LTS means that
all other traces can go to the same final state.
-/
theorem strong_confl_final_confl_tau
  {lts : Lts C E} {c : C} {τ : E}
  {Compat : E → E → Prop}
  (hinv : lts.IsInvariantAt (lts.StronglyConfluentAt Compat) c)
  (htau : ∀ {l l'}, Compat l l' ↔ l = τ ∧ l' = τ)
  (hsteps₁ : lts.TauStar τ c c₁)
  (hterm : lts.IsFinalFor (· = τ) c₁)
  (hstep₂ : lts.Step c τ c₂) : lts.TauStar τ c₂ c₁
  := by
  induction hsteps₁
    using Lts.TauStar.reverse_induction
    generalizing c₂ with
  | refl =>
    exact False.elim (hterm (by rfl) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i c c'
    have ⟨hconfl', hinv'⟩ := hinv.unfold hstep₁
    have := hinv.base hstep₁ hstep₂ (by simp [htau])
    cases this with
    | inl heq => simp [← heq, htail₁]
    | inr h =>
      have ⟨c'', hstep₁', hstep₂'⟩ := h
      have := ih hinv' hstep₁'
      exact this.prepend hstep₂'

end Wavelet.Semantics
