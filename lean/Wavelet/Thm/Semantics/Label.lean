import Wavelet.Semantics.Defs
import Wavelet.Thm.Data.Vector

/-! More definitions for `Label`. -/

namespace Wavelet.Semantics

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
