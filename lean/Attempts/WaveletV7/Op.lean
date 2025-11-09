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
  asBool : V → Bool
  -- Some constants used in compilation
  trueVal : V
  falseVal : V
  junkVal : V

end Wavelet.Op
