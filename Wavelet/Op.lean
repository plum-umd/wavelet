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

@[simp]
def Label.isSilent [Arity Op] : Label Op V m n → Bool
  | .τ => true
  | _ => false

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
  := Lts.SimilarBy (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ) sem₁.init sem₂.init

infix:50 " ≲ " => Semantics.SimilarBy

private theorem sim_tau_step_to_tau_star
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  {s₁ s₁' : sem₁.S}
  {s₂ : sem₂.S}
  (hR : R s₁ s₂)
  (hsim_tau : ∀ s₁ s₂ s₁',
    R s₁ s₂ →
    sem₁.lts.Step s₁ .τ s₁' →
    ∃ s₂',
      sem₂.lts.TauStar .τ s₂ s₂' ∧
      R s₁' s₂')
  (hstep_tau : sem₁.lts.TauStar .τ s₁ s₁') :
  ∃ s₂',
    sem₂.lts.TauStar .τ s₂ s₂' ∧
    R s₁' s₂' := by
  induction hstep_tau with
  | refl =>
    exists s₂
    constructor
    · exact .refl
    · exact hR
  | tail pref tail ih =>
    have ⟨s₂₂, hstep_s₂, hR₂⟩ := ih
    have ⟨s₂', hstep_s₂₂, hR₂₂⟩ := hsim_tau _ s₂₂ _ hR₂ tail
    have := Lts.TauStar.trans hstep_s₂ hstep_s₂₂
    exists s₂'

/-- A sufficient proof obligation for simulation mod tau. -/
theorem Semantics.SimulatedBy.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hinit : R sem₁.init sem₂.init)
  (hsim : ∀ s₁ s₂ l s₁',
    R s₁ s₂ →
    sem₁.lts.Step s₁ l s₁' →
    ∃ s₂',
      sem₂.lts.StepModTau .τ s₂ l s₂' ∧
      R s₁' s₂') :
  Semantics.SimulatedBy sem₁ sem₂ R := by
  sorry

theorem Semantics.SimilarBy.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ sem := Lts.SimilarBy.refl

theorem Semantics.SimilarBy.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ sem₂) (h₂ : sem₂ ≲ sem₃) :
  sem₁ ≲ sem₃ :=
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
  /-- This field indicates which semantics should be used
  currently: `none` for the `main` semantics, `some op`
  for the `deps op` semantics. This helps sequentializing
  the yields. -/
  curSem : Option Op₁
  mainState : main.S
  depStates : (op : Op₁) → (deps op).S

def Semantics.LinkState.init
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V) : LinkState main deps := {
    curSem := none,
    mainState := main.init,
    depStates := λ op => (deps op).init ,
  }

/-- Labels from the main semantics can be passed through. -/
inductive Semantics.MainLabelPassthrough
  [Arity Op₀] [Arity Op₁] :
  Label (Op₀ ⊕ Op₁) V m n → Label Op₀ V m n → Prop where
  | pass_tau : MainLabelPassthrough .τ .τ
  | pass_input {vals} : MainLabelPassthrough (.input vals) (.input vals)
  | pass_output {vals} : MainLabelPassthrough (.output vals) (.output vals)
  | pass_yield_inl {op : Op₀} {inputs outputs} :
      MainLabelPassthrough (.yield (.inl op) inputs outputs) (.yield op inputs outputs)

/-- Labels from the dependencies that can be passed through -/
inductive Semantics.DepLabelPassthrough
  [Arity Op] :
  Label Op V m' n' → Label Op V m n → Prop where
  | pass_yield :
      DepLabelPassthrough (.yield op inputs outputs) (.yield op inputs outputs)
  | pass_tau : DepLabelPassthrough .τ .τ

/-- Step relation of the linked semantics. -/
inductive Semantics.LinkStep
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V)
  : Lts (LinkState main deps) (Label Op₀ V m n) where
  /-- Pass through some labels from the main semantics. -/
  | step_main :
    s.curSem = none →
    MainLabelPassthrough l l' →
    main.lts.Step s.mainState l mainState' →
    LinkStep main deps s l' { s with mainState := mainState' }
  /-- Pass through some labels from the dependency semantics. -/
  | step_dep :
    s.curSem = some depOp →
    DepLabelPassthrough l l' →
    (deps depOp).lts.Step (s.depStates depOp) l depState' →
    LinkStep main deps s l' { s with depStates := Function.update s.depStates depOp depState' }
  /--
  If the main semantics can yield, send the inputs to the corresponding dependency.

  Note that this rule and the next one are left a bit ambiguous in the case
  when then main semantics can make different yields to the same operator.
  One well-formedness condition we could add is that these restricted relations
  are deterministic:
  - `R₁(outputs, s') := Step s (.yield op inputs outputs) s'` for any `s, op, inputs`
  - `R₂(op, inputs) := HasYield s op inputs` for any `s`
  -/
  | step_dep_spawn :
    s.curSem = none →
    main.HasYield s.mainState (.inr depOp) inputVals →
    (deps depOp).lts.Step (s.depStates depOp) (.input inputVals) depState' →
    LinkStep main deps s .τ
      { s with
        curSem := some depOp, -- Block until the dependency finishes
        depStates := Function.update s.depStates depOp depState' }
  /-- If the dependency outputs, forward the results back to the main semantics. -/
  | step_dep_ret :
    s.curSem = some depOp →
    (deps depOp).lts.Step (s.depStates depOp) (.output outputVals) depState' →
    main.lts.Step s.mainState (.yield (.inr depOp) inputVals outputVals) mainState' →
    LinkStep main deps s .τ
      { s with
        curSem := none, -- Return to the main semantics
        mainState := mainState',
        depStates := Function.update s.depStates depOp depState' }

/-- Interprets a subset of operators (`Op₁`) in the remaining ones (`Op₀`).
Any yields to `Op₁` in `main` is synchronous: `main` will only continue
after `Op₁` outputs. -/
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
