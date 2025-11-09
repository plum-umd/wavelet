import Mathlib.Data.List.Basic
import Mathlib.Data.NNRat.Defs

/-! Definitions for PCM. -/

namespace Wavelet.Determinacy

class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop

namespace PCM

infixl:60 " ⊔ " => add
prefix:40 "✓ " => valid

def disjoint [PCM C] (a b : C) : Prop := ✓ a ⊔ b

def framePreserving [PCM C] (a b : C) : Prop :=
  ∀ c, ✓ a ⊔ c → ✓ b ⊔ c

def sum [PCM C] (xs : List C) : C :=
  xs.foldl (· ⊔ ·) zero

infix:50 " ⊥ " => disjoint
infix:50 " ⟹ " => framePreserving

instance [PCM C] : LE C where
  le a b := ∃ c, b = a ⊔ c

noncomputable def sub [PCM C] (a b : C) (hle : b ≤ a) : C :=
  hle.choose

class Lawful (R : Type u) [inst : PCM R] where
  add_comm : ∀ {a b : R}, a ⊔ b = b ⊔ a
  add_assoc : ∀ {a b c : R}, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  add_ident : ∀ {a : R}, a ⊔ inst.zero = a
  valid_add : ∀ {a b : R}, ✓ a ⊔ b → ✓ a
  valid_zero : ✓ inst.zero

instance [inst : PCM R] [Lawful R] : Std.Commutative inst.add where
  comm := by apply Lawful.add_comm

instance [inst : PCM R] [Lawful R] : Std.Associative inst.add where
  assoc := by apply Lawful.add_assoc

instance [inst : PCM R] : Std.LeftIdentity inst.add inst.zero where

instance [inst : PCM R] [Lawful R] : Std.LawfulLeftIdentity inst.add inst.zero where
  left_id a := by rw [Lawful.add_comm]; apply Lawful.add_ident

instance [inst : PCM R] : Std.RightIdentity inst.add inst.zero where

instance [inst : PCM R] [Lawful R] : Std.LawfulRightIdentity inst.add inst.zero where
  right_id a := by apply Lawful.add_ident

class Cancellative (R : Type u) [PCM R] where
  cancel_left : ∀ {a b c : R}, a ⊔ b = a ⊔ c → b = c
  cancel_right : ∀ {a b c : R}, b ⊔ a = c ⊔ a → b = c

/-- PCM homomorphism. -/
class Hom [instR : PCM R] [instS : PCM S] (h : R → S) where
  hom_zero : h PCM.zero = PCM.zero
  hom_add : ∀ {a b : R}, h (a ⊔ b) = h a ⊔ h b
  hom_valid : ∀ {a : R}, ✓ a → ✓ h a

/-- A trivial PCM with only one element. -/
inductive Triv where | zero

instance : PCM Triv where
  add _ _ := Triv.zero
  zero := Triv.zero
  valid _ := True

instance : Lawful Triv := by
  constructor
  all_goals intros; trivial

def Triv.homFrom R [PCM R] : R → Triv := λ _ => Triv.zero

instance [PCM R] : Hom (Triv.homFrom R) := by
  constructor
  all_goals intros; trivial

theorem disjoint.symm [PCM C] [Lawful C] {a b : C} : a ⊥ b → b ⊥ a := by
  intro h; rw [disjoint, Lawful.add_comm]; exact h

theorem valid.add_left [PCM C] [Lawful C] {a b : C} (h : ✓ a ⊔ b) : ✓ a
  := Lawful.valid_add h

theorem valid.add_right [PCM C] [Lawful C] {a b : C} (h : ✓ a ⊔ b) : ✓ b
  := by
  rw [Lawful.add_comm] at h
  exact Lawful.valid_add h

theorem valid.le [PCM C] [Lawful C] {a b : C} (h : ✓ b) (hle : a ≤ b) : ✓ a := by
  have ⟨c, h⟩ := hle
  subst h
  apply valid.add_left h

theorem framePreserving.from_le [PCM C] [Lawful C]
  {a b : C} (hle : a ≤ b) : b ⟹ a := by
  have ⟨c, h⟩ := hle
  subst h
  intros d hd
  rw [Lawful.add_comm, ← Lawful.add_assoc] at hd
  have := hd.add_left
  rw [Lawful.add_comm] at this
  exact this

theorem framePreserving.congr_add_left [PCM C] [Lawful C]
  {a b c : C} (hfp : a ⟹ b) : c ⊔ a ⟹ c ⊔ b := by
  intros d hd
  rw [Lawful.add_assoc, Lawful.add_comm, Lawful.add_assoc] at hd ⊢
  apply hfp _ hd

@[simp]
theorem add.right_zero_id [PCM C] [Lawful C] (a : C) : a ⊔ PCM.zero = a :=
  Lawful.add_ident

@[simp]
theorem add.left_zero_id [PCM C] [Lawful C] (a : C) : PCM.zero ⊔ a = a := by
  rw [Lawful.add_comm]; apply Lawful.add_ident

@[simp]
theorem add.le_add_right [PCM C] {a b : C} : a ≤ a ⊔ b := by exists b

theorem add.le_add_right_alt [PCM C] [PCM.Lawful C] {a b c : C} (h : a ≤ b) : a ≤ c ⊔ b := by
  have ⟨d, hd⟩ := h
  subst hd
  rw [Lawful.add_comm, Lawful.add_assoc]
  simp

@[simp]
theorem add.le_add_left [PCM C] [PCM.Lawful C] {a b : C} : b ≤ a ⊔ b := by
  rw [Lawful.add_comm];
  exists a

theorem add.le_add_left_alt [PCM C] [PCM.Lawful C] {a b c : C} (h : a ≤ b) : a ≤ b ⊔ c := by
  have ⟨d, hd⟩ := h
  subst hd
  rw [Lawful.add_assoc]
  simp

theorem add.le_add_congr [PCM C] [PCM.Lawful C]
  {a₁ a₂ b₁ b₂ : C} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ := by
  have ⟨c₁, hc₁⟩ := ha
  have ⟨c₂, hc₂⟩ := hb
  subst hc₁; subst hc₂
  calc
    a₁ ⊔ b₁ ≤ (a₁ ⊔ b₁) ⊔ (c₁ ⊔ c₂) := by simp
    _ = _  := by
      rw [Lawful.add_assoc, Lawful.add_assoc]
      rw [@Lawful.add_comm _ _ _ b₁ (c₁ ⊔ c₂)]
      rw [@Lawful.add_assoc]
      rw [@Lawful.add_comm _ _ _ b₁ c₂]

@[simp]
theorem le.refl [PCM C] [Lawful C] (a : C) : a ≤ a := by exists PCM.zero; simp

@[trans]
theorem le.trans [PCM C] [Lawful C]
  {a b c : C} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  have ⟨d₁, hd₁⟩ := hab
  have ⟨d₂, hd₂⟩ := hbc
  subst hd₁; subst hd₂
  exists (d₁ ⊔ d₂)
  rw [Lawful.add_assoc]

@[simp]
theorem le.zero [PCM C] [Lawful C] (a : C) : PCM.zero ≤ a := by
  exists a
  rw [add.left_zero_id]

@[simp]
theorem sum.nil [inst : PCM C] : sum [] = inst.zero := by simp [sum]

@[simp]
theorem sum.singleton [PCM C] [Lawful C] (a : C) : sum [a] = a := by
  simp [sum, Lawful.add_comm]

@[simp]
theorem sum.cons [PCM C] [Lawful C] (a : C) (xs : List C) : sum (a :: xs) = a ⊔ sum xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [ih, sum]
    simp [List.foldl_eq_foldr]
    rw [sum]
    simp [List.foldl_eq_foldr]

@[simp]
theorem sum.append [PCM C] [Lawful C] (xs ys : List C) :
  sum (xs ++ ys) = sum xs ⊔ sum ys := by
  induction xs with
  | nil => simp [Lawful.add_comm]
  | cons a xs ih =>
    simp [ih]
    rw [Lawful.add_assoc]

theorem sum.mem_to_le [PCM C] [Lawful C] {xs : List C}
  {a : C} (hmem : a ∈ xs) :
  a ≤ sum xs := by
  induction xs with
  | nil => simp at hmem
  | cons x xs ih =>
    simp at hmem
    cases hmem with
    | inl h₁ => subst h₁; simp
    | inr h₁ =>
      specialize ih h₁
      simp [add.le_add_right_alt ih]

theorem sum.le_disj_get [PCM C] [Lawful C] {xs : List C}
  (hne : i ≠ j)
  (hi : i < xs.length)
  (hj : j < xs.length) :
    xs[i] ⊔ xs[j] ≤ sum xs := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    simp at hi hj
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j' =>
        simp
        apply add.le_add_congr
        · simp
        · apply sum.mem_to_le; simp
    | succ i' =>
      cases j with
      | zero =>
        simp
        rw [Lawful.add_comm]
        apply add.le_add_congr
        · simp
        · apply sum.mem_to_le; simp
      | succ j' =>
        simp at hne ⊢
        apply add.le_add_right_alt
        apply ih hne

@[simp]
theorem sum.replicate_zero
  [inst : PCM C] [Lawful C] (n : Nat) :
    sum (List.replicate n PCM.zero) = inst.zero := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.replicate]


/- Fractional permissions indexed by memory locations form a PCM. -/
section Fractional

variable {Loc : Type u}

abbrev FractionPerm (Loc : Type u) := Loc → NNRat

instance (Loc : Type u) : PCM (FractionPerm Loc) where
  add a b := λ ℓ => a ℓ + b ℓ
  zero := λ _ => 0
  valid a := ∀ ℓ, (a ℓ : ℚ) ≤ 1

namespace FractionPerm

@[simp] lemma add_apply (a b : FractionPerm Loc) (ℓ : Loc) :
  (PCM.add a b) ℓ = a ℓ + b ℓ := rfl

@[simp] lemma zero_apply (ℓ : Loc) : (PCM.zero : FractionPerm Loc) ℓ = 0 := rfl

lemma le_add_right (a b : FractionPerm Loc) (ℓ : Loc) :
  a ℓ ≤ (PCM.add a b) ℓ := by
  change (a ℓ : ℚ) ≤ (a ℓ : ℚ) + (b ℓ : ℚ)
  exact le_add_of_nonneg_right (show (0 : ℚ) ≤ (b ℓ : ℚ) from (b ℓ).property)

end FractionPerm

instance (Loc : Type u) : PCM.Lawful (FractionPerm Loc) := by
  constructor
  · intro a b; funext ℓ; simp [FractionPerm.add_apply, add_comm]
  · intro a b c; funext ℓ; simp [FractionPerm.add_apply, add_assoc]
  · intro a; funext ℓ; simp [FractionPerm.add_apply]
  · intro a b hvalid ℓ
    have hmono : (a ℓ : ℚ) ≤ ((PCM.add a b) ℓ : ℚ) := by
      exact_mod_cast FractionPerm.le_add_right (a := a) (b := b) ℓ
    have hsum := hvalid ℓ
    exact le_trans hmono hsum
  · intro ℓ; simp

end Fractional

end PCM

end Wavelet.Determinacy
