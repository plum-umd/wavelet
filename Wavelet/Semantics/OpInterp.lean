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

/-- The dual action of `Label.yield`. -/
inductive RespLabel Op V [Arity Op] where
  | respond (op : Op) (inputs : Vector V (Arity.ι op)) (outputs : Vector V (Arity.ω op))

/-- Base semantics interprets all of the operators in the same LTS
with potentially shared states.

TODO: The fact that we need two definitions of semantics (`OpInterp`
and `Semantics`) is a bit unfortunate. Try unify?
-/
class OpInterp (Op : Type u) (V : Type v) [Arity Op] where
  S : Type w
  init : S
  lts : Lts S (RespLabel Op V)

/-- Parallel composition of `sem` and `interp`. -/
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
    interp.lts.Step t (.respond op inputs outputs) t' →
    InterpStep sem interp (s, t) .τ (s', t')

/-- Fully interpret all operators using a `OpInterp` to get
a transition system with only input/output/silent events. -/
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

/-- Deterministic operator set. -/
def OpInterp.Deterministic
  [Arity Op]
  (interp : OpInterp Op V) : Prop :=
  ∀ {s s₁' s₂' op inputs outputs₁ outputs₂},
    interp.lts.Step s (.respond op inputs outputs₁) s₁' →
    interp.lts.Step s (.respond op inputs outputs₂) s₂' →
    s₁' = s₂' ∧ outputs₁ = outputs₂

end Wavelet.Semantics
