import Mathlib.Logic.Function.Basic
import Batteries.Data.List.Basic

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

@[simp]
def Label.isYield [Arity Op] : Label Op V m n → Bool
  | .yield _ _ _ => true
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

abbrev StrongSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts sem₂.lts sem₁.init sem₂.init

infix:50 " ≲ₛ " => StrongSimilarity

abbrev WeakSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init

infix:50 " ≲ " => WeakSimilarity

private theorem WeakSimilarity.alt_helper
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {s₁ s₁' : sem₁.S} {s₂ : sem₂.S}
  (hsim : Lts.Similarity sem₁.lts (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init)
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

theorem WeakSimilarity.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (hsim : Lts.Similarity sem₁.lts (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init) :
  Lts.Similarity (sem₁.lts.WeakStep .τ) (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    cases hstep with
    | refl =>
      exists s₂
      exact ⟨.refl, hR⟩
    | step htau₁' hstep' htau₁'' =>
      have ⟨s₂₁, hstep_s₂₁, hsim₁⟩ := alt_helper hsim hR htau₁'
      have ⟨s₂', hstep_s₂₂, hsim'⟩ := hsim.sim_step _ _ _ _ hsim₁ hstep'
      have ⟨s₂'', hstep_s₂₃, hsim''⟩ := alt_helper hsim hsim' htau₁''
      exists s₂''
      constructor
      · cases hstep_s₂₂ with
        | refl =>
          exact .from_tau_star (.trans hstep_s₂₁ hstep_s₂₃)
        | step htau₂₁ hstep₂ htau₂₂ =>
          exact .step (.trans hstep_s₂₁ htau₂₁) hstep₂ (.trans htau₂₂ hstep_s₂₃)
      · exact hsim''

theorem WeakSimilarity.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ sem := Lts.Similarity.refl_single .single

theorem WeakSimilarity.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ sem₂) (h₂ : sem₂ ≲ sem₃) :
  sem₁ ≲ sem₃ :=
  Lts.Similarity.trans h₁ (WeakSimilarity.alt h₂)

/-- Stronger than `WeakStep` and does not allow τ steps
before input, after output, or before/after yields. -/
inductive Lts.IORestrictedStep
  {S} [Arity Op]
  (lts : Lts S (Label Op V m n)) : Lts S (Label Op V m n) where
  | step_yield :
    lts.Step s (.yield o inputs outputs) s' →
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
  | yield => exact .step_yield hstep
  | input => exact .step_input hstep .refl
  | output => exact .step_output .refl hstep
  | τ => exact .step_tau (.single hstep)

/-- Append a τ transition at the end if allowed. -/
theorem Lts.IORestrictedStep.tail_tau
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' s'' : S} {l : Label Op V m n}
  (hl : l.isInput ∨ l.isSilent)
  (hstep : lts.IORestrictedStep s l s')
  (hstep_tau : lts.Step s' .τ s'') :
  lts.IORestrictedStep s l s'' := by
  cases hstep with
  | step_yield hstep' => simp at hl
  | step_input hstep₁ hstep₂ => exact .step_input hstep₁ (.tail hstep₂ hstep_tau)
  | step_output hstep₁ hstep₂ => simp at hl
  | step_tau hstep' => exact .step_tau (.tail hstep' hstep_tau)

/-- Append a non-τ transition at the end if allowed. -/
theorem Lts.IORestrictedStep.tail_non_tau
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' s'' : S} {l : Label Op V m n}
  (hl : l.isOutput ∨ l.isSilent)
  (hstep_tau : lts.IORestrictedStep s .τ s')
  (hstep : lts.Step s' l s'') :
  lts.IORestrictedStep s l s'' := by
  cases hstep_tau with | step_tau hstep_tau =>
  cases l with
  | yield => simp at hl
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
      have ⟨s₂', hsim'⟩ := hsim.sim_step _ _ _ _ hR hstep'
      exists s₂'
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

theorem IORestrictedSimilarity.to_weak_sim
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (hsim : sem₁ ≲ᵣ sem₂) : sem₁ ≲ sem₂ := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    have ⟨s₂', hstep', hR'⟩ := hsim.sim_step _ _ _ _ hR hstep
    exists s₂'
    constructor
    · cases hstep' with
      | step_yield hstep' => exact .single hstep'
      | step_input hstep' htau => exact .step .refl hstep' htau
      | step_output htau hstep' => exact .step htau hstep' .refl
      | step_tau htau => exact .from_tau_star htau
    · exact hR'

/-- A property `P` is an invariant at `s` if it is satisfied
by every reachable state from `s`. -/
def IsInvariantAt
  [Arity Op]
  (sem : Semantics Op V m n)
  (P : sem.S → Prop)
  (s : sem.S) : Prop :=
  ∀ s' tr, sem.lts.Star s tr s' → P s'

def IsInvariant
  [Arity Op]
  (sem : Semantics Op V m n)
  (P : sem.S → Prop) : Prop := sem.IsInvariantAt P sem.init

/-- Prove an invariant by induction. -/
theorem IsInvariantAt.by_induction
  [Arity Op]
  {sem : Semantics Op V m n}
  {P : sem.S → Prop}
  {s : sem.S}
  (hbase : P s)
  (hstep : ∀ {s₁ s₂ l},
    P s₁ →
    sem.lts.Step s₁ l s₂ →
    P s₂) :
  sem.IsInvariantAt P s := by
  intros s' tr hstar
  induction hstar with
  | refl => exact hbase
  | tail pref tail ih => exact hstep (ih hbase) tail

end Wavelet.Semantics
