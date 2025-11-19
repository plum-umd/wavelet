import Wavelet.Semantics.Defs

/-! Interpretations for operators. -/

namespace Wavelet.Semantics

/-- The empty operator set -/
inductive Empty : Type

def Empty.elim {α} (e : Empty) : α := by cases e

instance : Arity Empty where
  ι e := e.elim
  ω e := e.elim

instance : NeZeroArity Empty where
  neZeroᵢ e := e.elim
  neZeroₒ e := e.elim

/-- The dual action of `Label.yield`. -/
inductive RespLabel (Op : Type u) (V : Type v) [Arity Op] : Type (max u v) where
  | respond (op : Op) (inputs : Vector V (Arity.ι op)) (outputs : Vector V (Arity.ω op))

def RespLabel.MatchLabel
  [Arity Op]
  {V : Type v} : RespLabel Op V → Label Op V m n → Prop
  | .respond op₁ inputs₁ outputs₁, .yield op₂ inputs₂ outputs₂ =>
    op₁ = op₂ ∧ inputs₁ ≍ inputs₂ ∧ outputs₁ ≍ outputs₂
  | _, _ => False

/-- Parallel composition of `sem` and `interp`. -/
inductive Lts.InterpStep
  [Arity Op]
  (base : Lts S₁ (Label Op V m n))
  (interp : Lts S₂ (RespLabel Op V)) : Lts (S₁ × S₂) (Label Empty V m n) where
  | step_tau :
    base.Step s .τ s' →
    InterpStep base interp (s, t) .τ (s', t)
  | step_input :
    base.Step s (.input inputVals) s' →
    InterpStep base interp (s, t) (.input inputVals) (s', t)
  | step_output :
    base.Step s (.output outputVals) s' →
    InterpStep base interp (s, t) (.output outputVals) (s', t)
  | step_yield :
    base.Step s (.yield op inputs outputs) s' →
    interp.Step t (.respond op inputs outputs) t' →
    InterpStep base interp (s, t) .τ (s', t')

/-- Similar to `Interp`, but allowing additional indices in the base LTS. -/
inductive Lts.IndexedInterpStep
  {Op : Type u} {V : Type v}
  {S₁ : Type w₁} {S₂ : Type w₂}
  [Arity Op] {I : Type}
  (base : Lts S₁ (I × Label Op V m n))
  (interp : Lts S₂ (RespLabel Op V)) : Lts (S₁ × S₂) (I × Label Empty V m n) where
  | step_tau :
    base.Step s (i, .τ) s' →
    IndexedInterpStep base interp (s, t) (i, .τ) (s', t)
  | step_input :
    base.Step s (i, .input inputVals) s' →
    IndexedInterpStep base interp (s, t) (i, .input inputVals) (s', t)
  | step_output :
    base.Step s (i, .output outputVals) s' →
    IndexedInterpStep base interp (s, t) (i, .output outputVals) (s', t)
  | step_yield :
    base.Step s (i, .yield op inputs outputs) s' →
    interp.Step t (.respond op inputs outputs) t' →
    IndexedInterpStep base interp (s, t) (i, .τ) (s', t')

/-- Base semantics interprets all of the operators in the same LTS
with potentially shared states.

TODO: The fact that we need two definitions of semantics (`OpInterp`
and `Semantics`) is a bit unfortunate. Try unify?
-/
class OpInterp.{u, v, w} (Op : Type u) (V : Type v) [Arity Op] : Type (max u v (w + 1)) where
  S : Type w
  init : S
  lts : Lts S (RespLabel Op V)

/-- Fully interpret all operators using a `OpInterp` to get
a transition system with only input/output/silent events. -/
def interpret.{u, v, w₁, w₂}
  {Op : Type u} {V : Type v}
  [Arity Op]
  (sem : Semantics.{_, _, w₁} Op V m n)
  (interp : OpInterp.{_, _, w₂} Op V)
  : Semantics.{_, _, max w₁ w₂} Empty V m n
  := {
    S := sem.S × interp.S,
    init := (sem.init, interp.init),
    lts := Lts.InterpStep sem.lts interp.lts,
  }

/-- A monad interpretation of operators (mostly used in executing dataflow graphs) -/
class OpInterpM.{u, v, w}
  (Op : Type u) (V : Type v) (M : Type v → Type w) [Arity Op] : Type (max u v w) where
  interp : (op : Op) → Vector V (Arity.ι op) → M (Vector V (Arity.ω op))

end Wavelet.Semantics
