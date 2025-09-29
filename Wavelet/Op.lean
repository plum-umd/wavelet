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

abbrev Trace := List

@[simp, grind]
def Trace.ε : Trace E := []

/--
Operators are interpreted as potentially non-deterministic state machines
that can take multiple transitions, before terminating with some output values.

In the dataflow semantics, these transitions can interleave
with rest of the dataflow graph; but in the sequential semantics,
we are blocked on the state machine until it reaches a final state.
-/
class InterpOp Op (V : Type u) (E : Type v) (S : Type w) [Arity Op] where
  Step (op : Op) (inputs : Vector V (Arity.ι op)) :
    S → Trace E → S × Option (Vector V (Arity.ω op)) → Prop

end Wavelet.Op
