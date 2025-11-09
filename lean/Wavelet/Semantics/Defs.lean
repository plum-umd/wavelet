import Mathlib.Logic.Function.Basic
import Batteries.Data.List.Basic

import Wavelet.Semantics.Lts
import Wavelet.Data.Vector

/-! A general framework for defining concurrent semantics parametric
in a set of uninterpreted `operators`. -/

namespace Wavelet.Semantics

/-- Assigns arities to each operator. -/
class Arity Op where
  ι : Op → Nat
  ω : Op → Nat

/-- Operators with non-zero arities. -/
class NeZeroArity Op [Arity Op] where
  neZeroᵢ : ∀ op : Op, NeZero (Arity.ι op)
  neZeroₒ : ∀ op : Op, NeZero (Arity.ω op)

instance [inst : Arity Op] [NeZeroArity Op] : NeZero (inst.ι op)
  := NeZeroArity.neZeroᵢ op

instance [inst : Arity Op] [NeZeroArity Op] : NeZero (inst.ω op)
  := NeZeroArity.neZeroₒ op

/-- Arities for a sum of operator sets. -/
instance [Arity Op₁] [Arity Op₂] : Arity (Op₁ ⊕ Op₂) where
  ι | .inl o => Arity.ι o
    | .inr o => Arity.ι o
  ω | .inl o => Arity.ω o
    | .inr o => Arity.ω o

instance [Arity Op₁] [Arity Op₂] [NeZeroArity Op₁] [NeZeroArity Op₂] :
  NeZeroArity (Op₁ ⊕ Op₂) where
  neZeroᵢ op := by cases op <;> simp [Arity.ι] <;> apply NeZeroArity.neZeroᵢ
  neZeroₒ op := by cases op <;> simp [Arity.ω] <;> apply NeZeroArity.neZeroₒ

/-- Some required constants in compilation and semantics. -/
class InterpConsts (V : Type v) where
  -- Placeholder value
  junkVal : V
  -- Booleans
  toBool : V → Option Bool
  fromBool : Bool → V
  unique_fromBool_toBool : ∀ b, toBool (fromBool b) = some b
  unique_toBool_fromBool : ∀ b v, toBool v = some b → v = fromBool b
  -- Clonable values
  isClonable : V → Bool
  bool_clonable : ∀ b, isClonable (fromBool b) = true

inductive Label (Op : Type u) V m n [Arity Op] where
  | yield (o : Op) (inputs : Vector V (Arity.ι o)) (outputs : Vector V (Arity.ω o))
  | input (vals : Vector V m)
  | output (vals : Vector V n)
  | τ
  deriving Repr

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

/-- A constraint on two yield labels that if their
operator and inputs match, the outputs should match. -/
def Label.Deterministic
  [Arity Op]
  {V : Type v} {m n}
  (l₁ l₂ : Label Op V m n) : Prop :=
    ∀ {op inputVals outputVals₁ outputVals₂},
      l₁ = .yield op inputVals outputVals₁ →
      l₂ = .yield op inputVals outputVals₂ →
      outputVals₁ = outputVals₂

/-- A constraint on two yield labels that if their
operator and inputs match, the outputs should match. -/
def Label.DeterministicMod
  [Arity Op]
  {V : Type v} {m n}
  (EqV : V → V → Prop)
  (l₁ l₂ : Label Op V m n) : Prop :=
    ∀ {op inputVals outputVals₁ outputVals₂},
      l₁ = .yield op inputVals outputVals₁ →
      l₂ = .yield op inputVals outputVals₂ →
      List.Forall₂ EqV outputVals₁.toList outputVals₂.toList

@[simp]
theorem Label.DeterministicMod.eq_eq
  [Arity Op] {l₁ l₂ : Label Op V m n} :
    Label.DeterministicMod Eq l₁ l₂ ↔ Label.Deterministic l₁ l₂
  := by
  constructor
  · intros h
    simp [Label.Deterministic]
    simp [Label.DeterministicMod] at h
    intros _ _ _ _ h₁ h₂
    apply Vector.toList_inj.mp
    apply h h₁ h₂
  · intros h
    simp [Label.DeterministicMod]
    simp [Label.Deterministic] at h
    intros _ _ _ _ h₁ h₂
    apply Vector.toList_inj.mpr
    apply h h₁ h₂

/-- If two labels are either yield or silent and are deterministic (mod `EqV`). -/
def Label.IsYieldOrSilentAndDetMod
  [Arity Op] (EqV : V → V → Prop)
  (l₁ : Label Op V m n) (l₂ : Label Op V m n) : Prop :=
  (l₁.isYield ∨ l₁.isSilent) ∧
  (l₂.isYield ∨ l₂.isSilent) ∧
  Label.DeterministicMod EqV l₁ l₂

def Label.IsYieldOrSilentAndDet
  [Arity Op]
  (l₁ : Label Op V m n) (l₂ : Label Op V m n) : Prop :=
  (l₁.isYield ∨ l₁.isSilent) ∧
  (l₂.isYield ∨ l₂.isSilent) ∧
  Label.Deterministic l₁ l₂

@[simp]
theorem Label.IsYieldOrSilentAndDetMod.eq_eq
  [Arity Op] {l₁ l₂ : Label Op V m n} :
    Label.IsYieldOrSilentAndDetMod Eq l₁ l₂ ↔ Label.IsYieldOrSilentAndDet l₁ l₂
  := by
  simp only [Label.IsYieldOrSilentAndDetMod, Label.IsYieldOrSilentAndDet]
  simp

def Label.EqMod
  [Arity Op]
  (Eq : V → V → Prop)
  (l₁ l₂ : Label Op V m n) : Prop :=
  match l₁, l₂ with
  | .input vals₁, .input vals₂ =>
      List.Forall₂ Eq vals₁.toList vals₂.toList
  | .output vals₁, .output vals₂ =>
      List.Forall₂ Eq vals₁.toList vals₂.toList
  | .yield op₁ inputs₁ outputs₁, .yield op₂ inputs₂ outputs₂ =>
      op₁ = op₂ ∧
      List.Forall₂ Eq inputs₁.toList inputs₂.toList ∧
      List.Forall₂ Eq outputs₁.toList outputs₂.toList
  | .τ, .τ => True
  | _, _ => False

instance {Eq : V → V → Prop} [Arity Op] [IsRefl V Eq] :
  IsRefl (Label Op V m n) (Label.EqMod Eq) where
  refl l := by cases l <;> simp [Label.EqMod, IsRefl.refl]

@[simp]
def Label.EqMod.eq_eq
  [Arity Op] {l₁ l₂ : Label Op V m n} :
    Label.EqMod Eq l₁ l₂ ↔ l₁ = l₂
  := by
  constructor
  · cases l₁ <;> cases l₂
    any_goals simp [Label.EqMod]
    · intros h₁ h₂ h₃
      subst h₁
      simp [Vector.toList_inj] at h₂
      simp [Vector.toList_inj] at h₃
      simp [h₂, h₃]
    · simp [Vector.toList_inj]
    · simp [Vector.toList_inj]
  · intros h
    simp [h, IsRefl.refl]

def Label.EqModYieldOutputs
  [Arity Op] : Label Op V m n → Label Op V m n → Prop
  | .yield op₁ inputs₁ _, .yield op₂ inputs₂ _ =>
      op₁ = op₂ ∧ inputs₁ ≍ inputs₂
  | l₁, l₂ => l₁ = l₂

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

abbrev StrongSimilaritySt
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.SimilaritySt R sem₁.lts sem₂.lts sem₁.init sem₂.init

abbrev StrongSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts sem₂.lts sem₁.init sem₂.init

notation sem₁ " ≲ₛ" "[" R "] " sem₂ => StrongSimilaritySt sem₁ sem₂ R
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

abbrev IORestrictedSimulation
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.Simulation sem₁.lts sem₂.lts.IORestrictedStep R sem₁.init sem₂.init

abbrev IORestrictedSimilaritySt
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.SimilaritySt R sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init

abbrev IORestrictedSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init

-- notation sem₁ " ≲ᵣ" "[" R "] " sem₂ => IORestrictedSimulation sem₁ sem₂ R
notation sem₁ " ≲ᵣ" "[" R "] " sem₂ => IORestrictedSimilaritySt sem₁ sem₂ R
infix:50 " ≲ᵣ " => IORestrictedSimilarity

@[refl]
theorem IORestrictedSimilarity.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ᵣ sem :=
  Lts.Similarity.refl_single .single

private theorem IORestrictedSimilaritySt.alt_helper
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {s₁ s₁' : sem₁.S} {s₂ : sem₂.S}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : Lts.SimilaritySt R sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init)
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

theorem IORestrictedSimilaritySt.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : Lts.SimilaritySt R sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init) :
  Lts.SimilaritySt R sem₁.lts.IORestrictedStep sem₂.lts.IORestrictedStep sem₁.init sem₂.init
  := by
  apply Lts.SimilaritySt.intro hsim.Sim
  · constructor
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
  · apply hsim.sim_prop

@[trans]
theorem IORestrictedSimilarity.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ᵣ sem₂) (h₂ : sem₂ ≲ᵣ sem₃) :
  sem₁ ≲ᵣ sem₃ := Lts.Similarity.trans h₁ (IORestrictedSimilaritySt.alt h₂)

@[trans]
theorem IORestrictedSimilaritySt.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  {R₁ : sem₁.S → sem₂.S → Prop}
  {R₂ : sem₂.S → sem₃.S → Prop}
  (h₁ : sem₁ ≲ᵣ[R₁] sem₂) (h₂ : sem₂ ≲ᵣ[R₂] sem₃) :
  sem₁ ≲ᵣ[Relation.Comp R₁ R₂] sem₃ :=
    Lts.SimilaritySt.trans h₁ (IORestrictedSimilaritySt.alt h₂)

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

theorem StrongSimilaritySt.to_restricted_sim
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : sem₁ ≲ₛ[R] sem₂) : sem₁ ≲ᵣ[R] sem₂ := by
  apply Lts.SimilaritySt.intro hsim.Sim
  · constructor
    · exact hsim.sim_init
    · intros s₁ s₂ l s₁' hR hstep
      have ⟨s₂', hstep', hR'⟩ := hsim.sim_step _ _ _ _ hR hstep
      exists s₂'
      constructor
      · exact Lts.IORestrictedStep.single hstep'
      · exact hR'
  · apply hsim.sim_prop

theorem IORestrictedSimilaritySt.map_tau_star
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : sem₁ ≲ᵣ[R] sem₂)
  {s₁ s₁' : sem₁.S}
  {s₂ : sem₂.S}
  (h : hsim.Sim s₁ s₂)
  (htau : sem₁.lts.TauStar .τ s₁ s₁') :
    ∃ s₂', sem₂.lts.TauStar .τ s₂ s₂' ∧ hsim.Sim s₁' s₂'
  := by
  induction htau with
  | refl => exact ⟨_, .refl, h⟩
  | tail pref tail ih =>
    have ⟨_, pref', h'⟩ := ih
    have ⟨_, tail', h''⟩ := hsim.sim_step _ _ _ _ h' tail
    cases tail' with | step_tau tail'' =>
    exact ⟨_, pref'.trans tail'', h''⟩

instance [Arity Op] : IsRefl (Semantics Op V m n) IORestrictedSimilarity where
  refl := .refl

instance [Arity Op] : IsTrans (Semantics Op V m n) IORestrictedSimilarity where
  trans _ _ _ := .trans

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

/-- Used for restricting some simulation relations. -/
def PreservesInit
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (s₁ : sem₁.S) (s₂ : sem₂.S) : Prop :=
  s₁ = sem₁.init → s₂ = sem₂.init

@[trans]
theorem IORestrictedSimilaritySt.trans_preserves_init
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ᵣ[PreservesInit] sem₂) (h₂ : sem₂ ≲ᵣ[PreservesInit] sem₃) :
  sem₁ ≲ᵣ[PreservesInit] sem₃ := by
  have := Lts.SimilaritySt.trans h₁ (IORestrictedSimilaritySt.alt h₂)
  apply Lts.SimilaritySt.weaken _ this
  simp [Relation.Comp, PreservesInit]
  grind only

end Wavelet.Semantics
