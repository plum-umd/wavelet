import Mathlib.Logic.Function.Basic

import Wavelet.Semantics.Lts

/-! A general framework for defining concurrent semantics parametric
in a set of uninterpreted `operators`. -/

namespace Wavelet.Semantics

/-- Assigns arities to each operator. -/
class Arity Op where
  ι : Op → Nat
  ω : Op → Nat

/-- Arities for a sum of operator sets. -/
instance [Arity Op₁] [Arity Op₂] : Arity (Op₁ ⊕ Op₂) where
  ι | .inl o => Arity.ι o
    | .inr o => Arity.ι o
  ω | .inl o => Arity.ω o
    | .inr o => Arity.ω o

/-- Some constants used in compilation. -/
class InterpConsts (V : Type v) where
  -- Placeholder value
  junkVal : V
  -- Booleans
  toBool : V → Option Bool
  fromBool : Bool → V
  unique_fromBool_toBool : ∀ b, toBool (fromBool b) = some b
  unique_toBool_fromBool : ∀ b v, toBool v = some b → v = fromBool b

inductive Label (Op : Type u) V m n [Arity Op] where
  | yield (o : Op) (inputs : Vector V (Arity.ι o)) (outputs : Vector V (Arity.ω o))
  | input (vals : Vector V m)
  | output (vals : Vector V n)
  | τ

@[simp]
def Label.isSilent [Arity Op] : Label Op V m n → Bool
  | .τ => true
  | _ => false

end Wavelet.Semantics

namespace Wavelet

open Semantics

/-- A labelled transition with an initial state that can
interact with uninterpreted operators in `Op` by yielding
and receiving values of type `V`. -/
structure Semantics.{u, v, w} (Op : Type u) (V : Type v) [Arity Op] m n : Type (max u v (w + 1)) where
  S : Type w
  init : S
  lts : Lts S (Label Op V m n)

end Wavelet

namespace Wavelet.Semantics

/-- Whether the given state can potentially yield. -/
def HasYield
  [Arity Op]
  (sem : Semantics Op V m n)
  (s : sem.S) (op : Op) (inputs : Vector V (Arity.ι op)) : Prop :=
  ∃ outputs s', sem.lts.Step s (.yield op inputs outputs) s'

/-- Simulation modulo the silent label. -/
abbrev SimulatedBy
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.SimulatedBy
    (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ)
    R
    sem₁.init sem₂.init

abbrev SimilarBy
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.SimilarBy (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ) sem₁.init sem₂.init

infix:50 " ≲ " => Semantics.SimilarBy

/-- Helper lemma for `SimulatedBy.alt`. -/
private theorem SimulatedBy.alt_tau_star_to_tau_star
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  {s₁ s₁' : sem₁.S}
  {s₂ : sem₂.S}
  (hsim : ∀ s₁ s₂ l s₁',
    R s₁ s₂ →
    sem₁.lts.Step s₁ l s₁' →
    ∃ s₂',
      sem₂.lts.StepModTau .τ s₂ l s₂' ∧
      R s₁' s₂')
  (hR : R s₁ s₂)
  (htau_steps : sem₁.lts.TauStar .τ s₁ s₁') :
  ∃ s₂',
    sem₂.lts.TauStar .τ s₂ s₂' ∧
    R s₁' s₂' := by
  induction htau_steps with
  | refl =>
    exists s₂
    constructor
    · exact .refl
    · exact hR
  | tail pref tail ih =>
    have ⟨s₂₂, hstep_s₂, hR₂⟩ := ih
    have ⟨s₂', htau_step, hR'⟩ := hsim _ _ .τ _ hR₂ tail
    exists s₂'
    constructor
    · exact .trans hstep_s₂ htau_step.to_tau_star
    · exact hR'

/-- A sufficient proof obligation for simulation modulo tau. -/
theorem SimulatedBy.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hinit : R sem₁.init sem₂.init)
  (hsim : ∀ s₁ s₂ l s₁',
    R s₁ s₂ →
    sem₁.lts.Step s₁ l s₁' →
    ∃ s₂',
      sem₂.lts.StepModTau .τ s₂ l s₂' ∧
      R s₁' s₂') :
  Semantics.SimulatedBy sem₁ sem₂ R := by
  apply Lts.SimulatedBy.mk
  · exact hinit
  · intros s₁ s₂ l s₁' hR hstep
    have ⟨hstep₁, hstep₂, hstep₃⟩ := hstep
    have ⟨s₂₁, hstep_s₂, hR₂₁⟩ := SimulatedBy.alt_tau_star_to_tau_star hsim hR hstep₁
    have ⟨s₂₂, ⟨h₁, h₂, h₃⟩, hR₂₂⟩ := hsim _ _ l _ hR₂₁ hstep₂
    have ⟨s₂', hstep_s₂₂, hR'⟩ := SimulatedBy.alt_tau_star_to_tau_star hsim hR₂₂ hstep₃
    exists s₂'
    constructor
    · exact ⟨.trans hstep_s₂ h₁, h₂, .trans h₃ hstep_s₂₂⟩
    · exact hR'

theorem SimilarBy.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ sem := Lts.SimilarBy.refl

theorem SimilarBy.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ sem₂) (h₂ : sem₂ ≲ sem₃) :
  sem₁ ≲ sem₃ :=
  Lts.SimilarBy.trans h₁ h₂

end Wavelet.Semantics
