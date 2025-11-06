


-- /-- Similar to `Decidable`, but with additional data on both cases. -/
-- class inductive ExceptD (P : Prop) (A : Type u) (B : Type v) : Type (max u v) where
--   | isTrue (a : A) (h : P) : DecidableSum P A B
--   | isFalse (b : B) (h : ¬ P) : DecidableSum P A B

-- namespace DecidableSum

-- def toDecidable {P : Prop} {A : Type u} {B : Type v}
--   [DecidableSum P A B] : Decidable P :=
--   match ‹DecidableSum P A B› with
--   | isTrue _ h => .isTrue h
--   | isFalse _ h => .isFalse h

-- instance [Decidable P] : DecidableSum P Unit Unit :=
--   match ‹Decidable P› with
--   | .isTrue h => isTrue () h
--   | .isFalse h => isFalse () h

-- def decideSum [d : DecidableSum P A B] : A ⊕ B :=
--   d.casesOn (λ a _ => .inl a) (λ b _ => .inr b)

-- def decideExcept [d : DecidableSum P A B] : Except B A :=
--   d.casesOn (λ a _ => .ok a) (λ b _ => .error b)

-- end DecidableSum
