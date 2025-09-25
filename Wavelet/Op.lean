/-! Simple syntax and semantics of (synchronous) operators. -/

namespace Wavelet.Op

/-- Assigns arities to each operator. -/
class Arity Op where
  ι : Op → Nat
  ω : Op → Nat

/-- Some constants used in compilation. -/
class InterpConsts (V : Type v) where
  -- Placeholder value
  junkVal : V
  -- Booleans
  toBool : V → Option Bool
  fromBool : Bool → V
  unique_fromBool_toBool : ∀ b, toBool (fromBool b) = some b
  unique_toBool_fromBool : ∀ b v, toBool v = some b → v = fromBool b

/--
Interpretation of operators.
TODO: `V` and `S` are in the same universe due to the type of `StateT`.
-/
class InterpOp Op (V S : Type v) [Arity Op] where
  interp : (op : Op) → Vector V (Arity.ι op) → StateT S Option (Vector V (Arity.ω op))

end Wavelet.Op
