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

end PCM

end Wavelet.Determinacy
