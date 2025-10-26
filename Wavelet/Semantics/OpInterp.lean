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
  [Arity Op] {I}
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
class OpInterp (Op : Type u) (V : Type v) [Arity Op] where
  S : Type w
  init : S
  lts : Lts S (RespLabel Op V)

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
    lts := Lts.InterpStep sem.lts interp.lts,
  }

/-- Deterministic operator set. -/
def OpInterp.Deterministic
  [Arity Op]
  (interp : OpInterp Op V) : Prop :=
  ∀ {s s₁' s₂' op inputs outputs₁ outputs₂},
    interp.lts.Step s (.respond op inputs outputs₁) s₁' →
    interp.lts.Step s (.respond op inputs outputs₂) s₂' →
    s₁' = s₂' ∧ outputs₁ = outputs₂

def Lts.Interp.map_step
  [Arity Op] {S S'}
  {lts₁ lts₂ : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hmap : ∀ {s s' l}, lts₁.Step s l s' → lts₂.Step s l s')
  (hstep : (Lts.InterpStep lts₁ lts').Step s l s') :
    (Lts.InterpStep lts₂ lts').Step s l s'
  := by
  cases hstep with
  | step_tau hstep => exact .step_tau (hmap hstep)
  | step_input hstep => exact .step_input (hmap hstep)
  | step_output hstep => exact .step_output (hmap hstep)
  | step_yield hbase hinterp => exact .step_yield (hmap hbase) hinterp

end Wavelet.Semantics
