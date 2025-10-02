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

/-- The empty operator set -/
inductive Empty

def Empty.elim {α} (e : Empty) : α := by cases e

instance : Arity Empty where
  ι e := e.elim
  ω e := e.elim

inductive Label (Op : Type u) V n [Arity Op] where
  | yield (o : Op) (inputs : Vector V (Arity.ι o)) (outputs : Vector V (Arity.ω o))
  | output (vals : Vector V n)
  | τ

/-- A labelled transition with an initial state that can
interact with uninterpreted operators in `Op` by yielding
and receiving values of type `V`. -/
structure Semantics (Op : Type u) (V : Type v) [Arity Op] m n where
  S : Type w
  init : Vector V m → S
  lts : Lts S (Label Op V n)

/-- Whether the given state can potentially yield. -/
def Semantics.HasYield
  [Arity Op]
  (sem : Semantics Op V m n)
  (s : sem.S) (op : Op) (inputs : Vector V (Arity.ι op)) : Prop :=
  ∃ outputs s', sem.lts.Step s (.yield op inputs outputs) s'

/-- Simulation modulo the silent label. -/
abbrev Semantics.Simulates
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := ∀ args, Lts.Simulates
    (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ)
    R
    (sem₁.init args) (sem₂.init args)

/-- Interprets a set of operators with semantics using another set of operators. -/
abbrev PartInterp Op₀ Op V [Arity Op₀] [Arity Op] :=
  (op : Op) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)

structure Semantics.LinkState
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V) where
  mainState : main.S
  depStates : (op : Op₁) → Option (deps op).S

def Semantics.LinkState.init
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V)
  (args : Vector V m) : LinkState main deps := {
    mainState := main.init args,
    depStates := λ _ => none,
  }

inductive Semantics.LinkStep
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V)
  : Lts (LinkState main deps) (Label Op₀ V n) where
  | step_main_tau :
    main.lts.Step s.mainState .τ mainState' →
    LinkStep main deps s .τ { s with mainState := mainState' }
  | step_main_yield :
    main.lts.Step s.mainState (.yield (.inl op) inputs outputs) mainState' →
    LinkStep main deps s (.yield op inputs outputs) { s with mainState := mainState' }
  | step_main_output :
    main.lts.Step s.mainState (.output outputVals) mainState' →
    LinkStep main deps s (.output outputVals) { s with mainState := mainState' }
  | step_dep_tau {depState depState' : (deps depOp).S} :
    s.depStates depOp = some depState →
    (deps depOp).lts.Step depState .τ depState' →
    LinkStep main deps s .τ
      { s with depStates := Function.update s.depStates depOp (some depState') }
  | step_dep_yield {depState depState' : (deps depOp).S} :
    s.depStates depOp = some depState →
    (deps depOp).lts.Step depState (.yield op inputs outputs) depState' →
    LinkStep main deps s (.yield op inputs outputs)
      { s with depStates := Function.update s.depStates depOp (some depState') }
  -- Semantics to yield and return to the partial interpretation
  | step_spawn :
    main.HasYield s.mainState (.inr depOp) inputVals →
    s.depStates depOp = none → -- No parallel yields to the same dependency
    LinkStep main deps s .τ
      { s with depStates :=
        Function.update s.depStates depOp (some ((deps depOp).init inputVals)) }
  | step_join
    {depState : (deps depOp).S} :
    s.depStates depOp = some depState →
    (deps depOp).lts.Step depState (.output outputVals) depState' →
    main.lts.Step s.mainState (.yield (.inr depOp) inputVals outputVals) mainState' →
    LinkStep main deps s .τ
      { s with
        mainState := mainState',
        depStates := Function.update s.depStates depOp none }

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

end Wavelet.Op
