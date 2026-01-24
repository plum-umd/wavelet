import Wavelet.Semantics.Lts

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
  -- Booleans
  toBool : V → Option Bool
  fromBool : Bool → V
  unique_fromBool_toBool : ∀ b, toBool (fromBool b) = some b
  unique_toBool_fromBool : ∀ b v, toBool v = some b → v = fromBool b
  -- Clonable values
  isClonable : V → Bool
  bool_clonable : ∀ b, isClonable (fromBool b) = true
  /-- This special value is used in compilation
  to denote values that will be immediately discarded
  (e.g., a placeholder for a return value when actually
  a tail call is made). Ideally, we should modify the
  dataflow semantics to generate a non-deterministic value,
  but this encoding makes proofs simpler. -/
  junkVal : V

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
