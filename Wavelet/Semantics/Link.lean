import Mathlib.Logic.Function.Basic

import Wavelet.Semantics.Defs

/-! Definitions for "synchronously" linking multiple semantics. -/

namespace Wavelet.Semantics

/-- Interprets a set of operators with semantics using another
set of operators, with no shared states between them. -/
abbrev PartInterp Op₀ Op V [Arity Op₀] [Arity Op] :=
  (op : Op) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)

structure LinkState
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

def LinkState.init
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  (deps : PartInterp Op₀ Op₁ V) : LinkState main deps := {
    curSem := none,
    mainState := main.init,
    depStates := λ op => (deps op).init ,
  }

/-- Labels from the main semantics can be passed through. -/
inductive MainLabelPassthrough
  [Arity Op₀] [Arity Op₁] :
  Label (Op₀ ⊕ Op₁) V m n → Label Op₀ V m n → Prop where
  | pass_tau : MainLabelPassthrough .τ .τ
  | pass_input {vals} : MainLabelPassthrough (.input vals) (.input vals)
  | pass_output {vals} : MainLabelPassthrough (.output vals) (.output vals)
  | pass_yield_inl {op : Op₀} {inputs outputs} :
      MainLabelPassthrough (.yield (.inl op) inputs outputs) (.yield op inputs outputs)

/-- Labels from the dependencies that can be passed through -/
inductive DepLabelPassthrough
  [Arity Op] :
  Label Op V m' n' → Label Op V m n → Prop where
  | pass_yield :
      DepLabelPassthrough (.yield op inputs outputs) (.yield op inputs outputs)
  | pass_tau : DepLabelPassthrough .τ .τ

/-- Step relation of the linked semantics. -/
inductive LinkStep
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
def link
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

section Simulation

/-- Refining components implies refining the linked semantics. -/
theorem sim_congr_link
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main main' : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps deps' : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps i ≲ deps' i)
  (hsim_main : main ≲ main')
  : main.link deps ≲ main'.link deps'
  := sorry

end Simulation

end Wavelet.Semantics
