/-! Simple syntax and semantics of (synchronous) operators. -/

namespace Wavelet.Op

universe u
variable (Op : Type u) (χ : Type u)

/-- Assigns arities to each operator. -/
class Arity where
  ι : Op → Nat
  ω : Op → Nat

variable [Arity Op]

/-- Interpretation of an operator set as concrete values. -/
class Interp (V S : Type u) where
  interp : (op : Op) → Vector V (Arity.ι op) → StateT S Option (Vector V (Arity.ω op))
  toBool : V → Option Bool
  fromBool : Bool → V
  -- Some constants used in compilation
  junkVal : V
  unique_fromBool_toBool : ∀ b, toBool (fromBool b) = some b
  unique_toBool_fromBool : ∀ b v, toBool v = some b → v = fromBool b

end Wavelet.Op
