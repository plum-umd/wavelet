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

@[simp]
def Label.isOutput [Arity Op] : Label Op V m n → Bool
  | .output _ => true
  | _ => false

@[simp]
def Label.isInput [Arity Op] : Label Op V m n → Bool
  | .input _ => true
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
  /-- Shorthand for whether the given state can potentially yield. -/
  HasYield
    (s : S) (op : Op) (inputs : Vector V (Arity.ι op)) : Prop :=
    ∃ outputs s', lts.Step s (.yield op inputs outputs) s'
  /-- Yield transitions behave like a function. -/
  yields_functional {s op inputs outputs s'} :
    lts.Step s (.yield op inputs outputs) s' →
    ∀ outputs', ∃ s', lts.Step s (.yield op inputs outputs') s'

end Wavelet

namespace Wavelet.Semantics

/-- Weak simulation (up to the silent label). -/
abbrev WeakSimulation
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.Simulation
    (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ)
    R
    sem₁.init sem₂.init

/-- Helper lemma for `WeakSimulation.alt`. -/
private theorem WeakSimulation.alt_tau_star_to_tau_star
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
theorem WeakSimulation.alt
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
  WeakSimulation sem₁ sem₂ R := by
  apply Lts.Simulation.mk
  · exact hinit
  · intros s₁ s₂ l s₁' hR hstep
    have ⟨hstep₁, hstep₂, hstep₃⟩ := hstep
    have ⟨s₂₁, hstep_s₂, hR₂₁⟩ := WeakSimulation.alt_tau_star_to_tau_star hsim hR hstep₁
    have ⟨s₂₂, ⟨h₁, h₂, h₃⟩, hR₂₂⟩ := hsim _ _ l _ hR₂₁ hstep₂
    have ⟨s₂', hstep_s₂₂, hR'⟩ := WeakSimulation.alt_tau_star_to_tau_star hsim hR₂₂ hstep₃
    exists s₂'
    constructor
    · exact ⟨.trans hstep_s₂ h₁, h₂, .trans h₃ hstep_s₂₂⟩
    · exact hR'

abbrev WeakSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ) sem₁.init sem₂.init

infix:50 " ≲ " => WeakSimilarity

theorem WeakSimilarity.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ sem := Lts.Similarity.refl

theorem WeakSimilarity.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ sem₂) (h₂ : sem₂ ≲ sem₃) :
  sem₁ ≲ sem₃ :=
  Lts.Similarity.trans h₁ h₂

/-- Slightly stronger than `StepModTau` and does not allow
τ steps before input or after output. -/
inductive Lts.IORestrictedStep
  {S} [Arity Op]
  (lts : Lts S (Label Op V m n)) : Lts S (Label Op V m n) where
  | step_yield :
    lts.StepModTau .τ s (.yield o inputs outputs) s' →
    lts.IORestrictedStep s (.yield o inputs outputs) s'
  | step_input :
    lts.Step s (.input vals) s' →
    lts.TauStar .τ s' s'' →
    lts.IORestrictedStep s (.input vals) s''
  | step_output :
    lts.TauStar .τ s s' →
    lts.Step s' (.output vals) s'' →
    lts.IORestrictedStep s (.output vals) s''
  | step_tau :
    lts.TauStar .τ s s' →
    lts.IORestrictedStep s .τ s'

theorem Lts.IORestrictedStep.single
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' : S} {l : Label Op V m n}
  (hstep : lts.Step s l s')
  : lts.IORestrictedStep s l s' := by
  cases l with
  | yield => exact .step_yield (.single hstep)
  | input => exact .step_input hstep .refl
  | output => exact .step_output .refl hstep
  | τ => exact .step_tau (.single hstep)

/-- Append a τ transition at the end if allowed. -/
theorem Lts.IORestrictedStep.tail_tau
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' s'' : S} {l : Label Op V m n}
  (hl : ¬ l.isOutput)
  (hstep : lts.IORestrictedStep s l s')
  (hstep_tau : lts.Step s' .τ s'') :
  lts.IORestrictedStep s l s'' := by
  cases hstep with
  | step_yield hstep' => exact .step_yield (.tail_tau hstep' hstep_tau)
  | step_input hstep₁ hstep₂ => exact .step_input hstep₁ (.tail hstep₂ hstep_tau)
  | step_output hstep₁ hstep₂ => simp at hl
  | step_tau hstep' => exact .step_tau (.tail hstep' hstep_tau)

/-- Append a non-τ transition at the end if allowed. -/
theorem Lts.IORestrictedStep.tail_non_tau
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' s'' : S} {l : Label Op V m n}
  (hl : ¬ l.isInput)
  (hstep_tau : lts.IORestrictedStep s .τ s')
  (hstep : lts.Step s' l s'') :
  lts.IORestrictedStep s l s'' := by
  cases hstep_tau with | step_tau hstep_tau =>
  cases l with
  | yield => exact .step_yield ⟨hstep_tau, hstep, .refl⟩
  | input => simp at hl
  | output => exact .step_output hstep_tau hstep
  | τ => exact .step_tau (.tail hstep_tau hstep)

theorem Lts.IORestrictedStep.eq_rhs
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s₁ s₂ s₂' : S} {l : Label Op V m n}
  (hstep : lts.IORestrictedStep s₁ l s₂)
  (heq : s₂ = s₂') :
  lts.IORestrictedStep s₁ l s₂' := by
  subst heq
  exact hstep

theorem Lts.IORestrictedStep.eq_lhs
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s₁ s₁' s₂ : S} {l : Label Op V m n}
  (hstep : lts.IORestrictedStep s₁ l s₂)
  (heq : s₁ = s₁') :
  lts.IORestrictedStep s₁' l s₂ := by
  subst heq
  exact hstep

theorem Lts.IORestrictedStep.to_tau_star
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s₁ s₂ : S}
  (hstep : lts.IORestrictedStep s₁ .τ s₂) :
  lts.TauStar .τ s₁ s₂ := by
  cases hstep
  assumption

abbrev IORestrictedSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init

infix:50 " ≲ᵣ " => IORestrictedSimilarity

theorem IORestrictedSimilarity.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ᵣ sem :=
  Lts.Similarity.refl_single .single

private theorem IORestrictedSimilarity.alt_helper
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {s₁ s₁' : sem₁.S} {s₂ : sem₂.S}
  (hsim : Lts.Similarity sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init)
  (hR : hsim.Sim s₁ s₂)
  (hstep_tau : sem₁.lts.TauStar .τ s₁ s₁') :
  ∃ s₂', sem₂.lts.TauStar .τ s₂ s₂' ∧ hsim.Sim s₁' s₂' := by
  induction hstep_tau with
  | refl =>
    exists s₂
    constructor
    · exact .refl
    · exact hR
  | tail pref tail ih =>
    rename_i s₁'' s₁'
    have ⟨s₂'', hstep_s₂, hR₂''⟩ := ih
    have ⟨s₂', hstep_s₂', hR'⟩ := hsim.sim_step _ _ _ _ hR₂'' tail
    exists s₂'
    constructor
    · exact .trans hstep_s₂ hstep_s₂'.to_tau_star
    · exact hR'

theorem IORestrictedSimilarity.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (hsim : Lts.Similarity sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init) :
  Lts.Similarity sem₁.lts.IORestrictedStep sem₂.lts.IORestrictedStep sem₁.init sem₂.init
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    cases hstep with
    | step_yield hstep' =>
      have ⟨h₁, h₂, h₃⟩ := hstep'
      have ⟨s₁₂, hstep_s₂, hsim₂⟩ := alt_helper hsim hR h₁
      have ⟨s₂₂, hstep_s₁₂, hsim₁₂⟩ := hsim.sim_step _ _ _ _ hsim₂ h₂
      have ⟨s₂', hstep_s₂₂, hsim'⟩ := alt_helper hsim hsim₁₂ h₃
      exists s₂'
      constructor
      · rcases hstep_s₁₂ with ⟨h₁', h₂', h₃'⟩
        exact .step_yield ⟨.trans hstep_s₂ h₁', h₂', .trans h₃' hstep_s₂₂⟩
      · exact hsim'
    | step_input hstep₁ hstep₂ =>
      have ⟨s₂₁, hstep_s₂₁, hsim₁⟩ := hsim.sim_step _ _ _ _ hR hstep₁
      have ⟨s₂', hstep_s₂₂, hsim'⟩ := alt_helper hsim hsim₁ hstep₂
      exists s₂'
      constructor
      · cases hstep_s₂₁ with | step_input h₁ h₂ =>
        exact .step_input h₁ (.trans h₂ hstep_s₂₂)
      · exact hsim'
    | step_output hstep₁ hstep₂ =>
      have ⟨s₂₁, hstep_s₂₁, hsim₁⟩ := alt_helper hsim hR hstep₁
      have ⟨s₂', hstep_s₂₂, hsim'⟩ := hsim.sim_step _ _ _ _ hsim₁ hstep₂
      exists s₂'
      constructor
      · cases hstep_s₂₂ with | step_output h₁ h₂ =>
        exact .step_output (.trans hstep_s₂₁ h₁) h₂
      · exact hsim'
    | step_tau hstep' =>
      have ⟨s₂', hstep_s₂, hsim'⟩ := alt_helper hsim hR hstep'
      exists s₂'
      constructor
      · exact .step_tau hstep_s₂
      · exact hsim'

theorem IORestrictedSimilarity.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ᵣ sem₂) (h₂ : sem₂ ≲ᵣ sem₃) :
  sem₁ ≲ᵣ sem₃ := Lts.Similarity.trans h₁ (IORestrictedSimilarity.alt h₂)

end Wavelet.Semantics
