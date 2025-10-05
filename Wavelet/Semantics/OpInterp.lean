import Mathlib.Logic.Function.Basic

import Wavelet.Semantics.Defs

/-! Interpretations for operators. -/

namespace Wavelet.Semantics

/-- The empty operator set -/
inductive Empty

def Empty.elim {α} (e : Empty) : α := by cases e

instance : Arity Empty where
  ι e := e.elim
  ω e := e.elim

/-- Base semantics interprets all of the operators in the same LTS
with potentially shared states.

TODO: The fact that we need two definitions of semantics (`OpInterp`
and `Semantics`) is a bit unfortunate. Try unify?
-/
class OpInterp (Op : Type u) (V : Type v) [Arity Op] where
  S : Type w
  init : S
  interp :
    (op : Op) →
    Vector V (Arity.ι op) → S →
    Vector V (Arity.ω op) → S → Prop

inductive InterpStep
  [Arity Op]
  (sem : Semantics Op V m n)
  (interp : OpInterp Op V)
  : Lts (sem.S × interp.S) (Label Empty V m n) where
  | step_tau :
    sem.lts.Step s .τ s' →
    InterpStep sem interp (s, t) .τ (s', t)
  | step_input :
    sem.lts.Step s (.input inputVals) s' →
    InterpStep sem interp (s, t) (.input inputVals) (s', t)
  | step_output :
    sem.lts.Step s (.output outputVals) s' →
    InterpStep sem interp (s, t) (.output outputVals) (s', t)
  | step_yield :
    sem.lts.Step s (.yield op inputs outputs) s' →
    interp.interp op inputs t outputs t' →
    InterpStep sem interp (s, t) .τ (s', t')

/-- Fully interpret all operators using a `OpInterp`
to get a transition system with only input/output/silent events. -/
def interpret
  [Arity Op]
  (sem : Semantics Op V m n)
  (interp : OpInterp Op V)
  : Semantics Empty V m n
  := {
    S := sem.S × interp.S,
    init := (sem.init, interp.init),
    lts := sem.InterpStep interp,
  }

end Wavelet.Semantics
