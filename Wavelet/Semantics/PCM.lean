/-! Definitions for PCM. -/

namespace Wavelet.Semantics

class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop
  eq : C → C → Prop

namespace PCM

infixl:60 " ⊔ " => add
infix:40 " ≡ " => eq
prefix:40 "✓ " => valid

def disjoint [PCM C] (a b : C) : Prop := ✓ a ⊔ b

def framePreserving [PCM C] (a b : C) : Prop :=
  ∀ c, ✓ a ⊔ c → ✓ b ⊔ c

def sum [PCM C] (xs : List C) : C :=
  xs.foldl (· ⊔ ·) zero

infix:50 " ⊥ " => disjoint
infix:50 " ⟹ " => framePreserving

instance [PCM C] : LE C where
  le a b := ∃ c, b ≡ a ⊔ c

noncomputable def sub [PCM C] (a b : C) (hle : b ≤ a) : C :=
  hle.choose

class Lawful (R : Type u) [inst : PCM R] where
  add_comm : ∀ {a b : R}, a ⊔ b ≡ b ⊔ a
  add_assoc : ∀ {a b c : R}, (a ⊔ b) ⊔ c ≡ a ⊔ (b ⊔ c)
  add_ident : ∀ {a : R}, a ⊔ inst.zero ≡ a
  valid_add : ∀ {a b : R}, ✓ a ⊔ b → ✓ a
  valid_zero : ✓ inst.zero
  eq_refl : ∀ {a : R}, a ≡ a
  eq_symm : ∀ {a b : R}, a ≡ b → b ≡ a
  eq_trans : ∀ {a b c : R}, a ≡ b → b ≡ c → a ≡ c
  eq_congr_valid : ∀ {a b : R}, a ≡ b → ✓ a → ✓ b
  eq_congr_add :
    ∀ {a₁ a₂ b₁ b₂ : R},
      a₁ ≡ a₂ →
      b₁ ≡ b₂ →
      a₁ ⊔ b₁ ≡ a₂ ⊔ b₂

theorem eq_congr_disj
  [PCM C] [Lawful C]
  {a₁ a₂ b₁ b₂ : C}
  (ha : a₁ ≡ a₂)
  (hb : b₁ ≡ b₂)
  (hdisj : a₁ ⊥ b₁) :
    a₂ ⊥ b₂
  := by
  simp [disjoint]
  apply Lawful.eq_congr_valid
  apply Lawful.eq_congr_add ha hb
  exact hdisj

/-- PCM homomorphism. -/
class Hom [instR : PCM R] [instS : PCM S] (h : R → S) where
  hom_zero : h PCM.zero = PCM.zero
  hom_add : ∀ {a b : R}, h (a ⊔ b) ≡ h a ⊔ h b
  hom_valid : ∀ {a : R}, ✓ a → ✓ h a
  hom_eq : ∀ {a b : R}, a ≡ b → h a ≡ h b

/-- A trivial PCM with only one element. -/
inductive Triv where | zero

instance : PCM Triv where
  add _ _ := Triv.zero
  zero := Triv.zero
  valid _ := True
  eq _ _ := True

instance : Lawful Triv := by
  constructor
  all_goals intros; trivial

def Triv.homFrom R [PCM R] : R → Triv := λ _ => Triv.zero

instance [PCM R] : Hom (Triv.homFrom R) := by
  constructor
  all_goals intros; trivial

end PCM

end Wavelet.Semantics
