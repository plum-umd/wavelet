/-! Definitions for PCM. -/

namespace Wavelet.Semantics

class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop
  eq : C → C → Prop

infixl:60 " ⊔ " => PCM.add
infix:40 " ≡ " => PCM.eq
prefix:40 "✓ " => PCM.valid

def PCM.disjoint [PCM C] (a b : C) : Prop := ✓ a ⊔ b

def PCM.framePreserving [PCM C] (a b : C) : Prop :=
  ∀ c, ✓ a ⊔ c → ✓ b ⊔ c

def PCM.sum [PCM C] (xs : List C) : C :=
  xs.foldl (· ⊔ ·) PCM.zero

infix:50 " ⊥ " => PCM.disjoint
infix:50 " ⟹ " => PCM.framePreserving

instance [PCM C] : LE C where
  le a b := ∃ c, b ≡ a ⊔ c

noncomputable def PCM.sub [PCM C] (a b : C) (hle : b ≤ a) : C :=
  hle.choose

class LawfulPCM (R : Type u) [inst : PCM R] where
  add_comm : ∀ a b : R, a ⊔ b ≡ b ⊔ a
  add_assoc : ∀ a b c : R, (a ⊔ b) ⊔ c ≡ a ⊔ (b ⊔ c)
  add_ident : ∀ a : R, a ⊔ inst.zero ≡ a
  valid_add : ∀ a b : R, ✓ a ⊔ b → ✓ a
  valid_zero : ✓ inst.zero
  valid_eq : ∀ a b : R, a ≡ b → ✓ a → ✓ b
  eq_refl : ∀ a : R, a ≡ a
  eq_symm : ∀ a b : R, a ≡ b → b ≡ a
  eq_trans : ∀ a b c : R, a ≡ b → b ≡ c → a ≡ c

end Wavelet.Semantics
