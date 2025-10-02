import Mathlib.Logic.Function.Basic

import Wavelet.Lts

/-! A general framework for defining concurrent semantics parametric
in a set of uninterpreted `operators`. -/

namespace Wavelet.Op

open Lts

/-- Assigns arities to each operator. -/
class Arity Op where
  ι : Op → Nat
  ω : Op → Nat

/-- Arities for a sum of operator sets. -/
instance [Arity Op₁] [Arity Op₂] : Arity (Op₁ ⊕ Op₂) where
  ι | .inl o => Arity.ι o
    | .inr o => Arity.ι o
  ω | .inl o => Arity.ω o
    | .inr o => Arity.ω o

/-- Some constants used in compilation. -/
class InterpConsts (V : Type v) where
  -- Placeholder value
  junkVal : V
  -- Booleans
  toBool : V → Option Bool
  fromBool : Bool → V
  unique_fromBool_toBool : ∀ b, toBool (fromBool b) = some b
  unique_toBool_fromBool : ∀ b v, toBool v = some b → v = fromBool b

inductive Label (Op : Type u) V m n [Arity Op] where
  | yield (o : Op) (inputs : Vector V (Arity.ι o)) (outputs : Vector V (Arity.ω o))
  | input (vals : Vector V m)
  | output (vals : Vector V n)
  | τ

/-- A labelled transition with an initial state that can
interact with uninterpreted operators in `Op` by yielding
and receiving values of type `V`. -/
structure Semantics.{u, v, w} (Op : Type u) (V : Type v) [Arity Op] m n : Type (max u v (w + 1)) where
  S : Type w
  init : S
  lts : Lts S (Label Op V m n)

/-- Whether the given state can potentially yield. -/
def Semantics.HasYield
  [Arity Op]
  (sem : Semantics Op V m n)
  (s : sem.S) (op : Op) (inputs : Vector V (Arity.ι op)) : Prop :=
  ∃ outputs s', sem.lts.Step s (.yield op inputs outputs) s'

/-- Simulation modulo the silent label. -/
abbrev Semantics.SimulatedBy
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.SimulatedBy
    (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ)
    R
    sem₁.init sem₂.init

abbrev Semantics.SimilarBy
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.SimilarBy sem₁.lts sem₂.lts sem₁.init sem₂.init

infix:50 " ∼ " => Semantics.SimilarBy

theorem Semantics.SimilarBy.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ∼ sem := Lts.SimilarBy.refl

theorem Semantics.SimilarBy.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ∼ sem₂) (h₂ : sem₂ ∼ sem₃) :
  sem₁ ∼ sem₃ :=
  Lts.SimilarBy.trans h₁ h₂

/-- Interprets a set of operators with semantics using another
set of operators, with no shared states between them. -/
abbrev PartInterp Op₀ Op V [Arity Op₀] [Arity Op] :=
  (op : Op) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)

structure Semantics.LinkState
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V) where
  mainState : main.S
  depStates : (op : Op₁) → (deps op).S

def Semantics.LinkState.init
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V) : LinkState main deps := {
    mainState := main.init,
    depStates := λ op => (deps op).init ,
  }

inductive Semantics.LinkStep
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V)
  : Lts (LinkState main deps) (Label Op₀ V m n) where
  | step_main_tau :
    main.lts.Step s.mainState .τ mainState' →
    LinkStep main deps s .τ { s with mainState := mainState' }
  | step_main_yield :
    main.lts.Step s.mainState (.yield (.inl op) inputs outputs) mainState' →
    LinkStep main deps s (.yield op inputs outputs) { s with mainState := mainState' }
  | step_main_input :
    main.lts.Step s.mainState (.input inputVals) mainState' →
    LinkStep main deps s (.input inputVals) { s with mainState := mainState' }
  | step_main_output :
    main.lts.Step s.mainState (.output outputVals) mainState' →
    LinkStep main deps s (.output outputVals) { s with mainState := mainState' }
  | step_dep_tau {depState depState' : (deps depOp).S} :
    (deps depOp).lts.Step (s.depStates depOp) .τ depState' →
    LinkStep main deps s .τ
      { s with depStates := Function.update s.depStates depOp depState' }
  | step_dep_yield {depState depState' : (deps depOp).S} :
    (deps depOp).lts.Step (s.depStates depOp) (.yield op inputs outputs) depState' →
    LinkStep main deps s (.yield op inputs outputs)
      { s with depStates := Function.update s.depStates depOp depState' }
  | step_dep_input :
    main.HasYield s.mainState (.inr depOp) inputVals →
    (deps depOp).lts.Step (s.depStates depOp) (.input inputVals) depState' →
    LinkStep main deps s .τ
      { s with depStates := Function.update s.depStates depOp depState' }
  | step_dep_output :
    (deps depOp).lts.Step (s.depStates depOp) (.output outputVals) depState' →
    main.lts.Step s.mainState (.yield (.inr depOp) inputVals outputVals) mainState' →
    LinkStep main deps s .τ
      { s with
        mainState := mainState',
        depStates := Function.update s.depStates depOp depState' }

/-- Interprets a subset of operators (`Op₁`) in the remaining ones (`Op₀`). -/
def Semantics.link
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V)
  : Semantics Op₀ V m n
  := {
    S := LinkState main deps,
    init := LinkState.init main deps,
    lts := LinkStep main deps,
  }

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

inductive Semantics.InterpStep
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
def Semantics.interpret
  [Arity Op]
  (sem : Semantics Op V m n)
  (interp : OpInterp Op V)
  : Semantics Empty V m n
  := {
    S := sem.S × interp.S,
    init := (sem.init, interp.init),
    lts := sem.InterpStep interp,
  }

end Wavelet.Op
