import Wavelet.Semantics.Defs

/-! Some definitions for confluence. -/

namespace Wavelet.Semantics

/-- Strong confluence of `c` when the labels are restricted
by the compatibility relation `Compat`. -/
def Lts.StronglyConfluentAt
  {C : Type u} {E : Type v}
  (lts : Lts C E)
  (c : C)
  (Compat : E → E → Prop) : Prop :=
  ∀ {c₁ c₂ : C} {l₁ l₂ : E},
    lts.Step c l₁ c₁ →
    lts.Step c l₂ c₂ →
    Compat l₁ l₂ →
    c₁ = c₂ ∨
    ∃ c',
      lts.Step c₁ l₂ c' ∧
      lts.Step c₂ l₁ c'

/-- Strong confluence of an LTS when restricted to a subset of states. -/
def Lts.StronglyConfluent
  {C : Type u} {E : Type v}
  (lts : Lts C E)
  (States : C → Prop)
  (Compat : E → E → Prop) : Prop :=
  ∀ {c : C}, States c → lts.StronglyConfluentAt c Compat

end Wavelet.Semantics
