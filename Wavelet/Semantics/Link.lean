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

/-- Similar to `step_main`, but uses `TauStar`. -/
theorem LinkStep.step_main_tau_star
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : PartInterp Op₀ Op₁ V}
  {s : LinkState main deps}
  {mainState' : main.S}
  (hcur : s.curSem = none)
  (hstep : main.lts.TauStar .τ s.mainState mainState') :
  (LinkStep main deps).TauStar .τ s { s with mainState := mainState' }
  := by
  induction hstep with
  | refl => exact .refl
  | tail pref tail ih =>
    apply Lts.TauStar.trans
    · exact ih
    · apply Lts.TauStar.single
      exact .step_main hcur .pass_tau tail

/-- Similar to `step_main`, but uses `StepModTau`. -/
theorem LinkStep.step_main_mod_tau
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : PartInterp Op₀ Op₁ V}
  {s : LinkState main deps}
  {l : Label (Op₀ ⊕ Op₁) V m n}
  {l' : Label Op₀ V m n}
  {mainState' : main.S}
  (hcur : s.curSem = none)
  (hlabel : MainLabelPassthrough l l')
  (hstep : main.lts.StepModTau .τ s.mainState l mainState') :
  (LinkStep main deps).StepModTau .τ s l' { s with mainState := mainState' }
  := by
  have ⟨h₁, h₂, h₃⟩ := hstep
  constructor
  · exact LinkStep.step_main_tau_star hcur h₁
  · exact .step_main hcur hlabel h₂
  · exact LinkStep.step_main_tau_star hcur h₃

private def SimRel
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main main' : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps deps' : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps i ≲ deps' i)
  (hsim_main : main ≲ main')
  (s : LinkState main deps)
  (s' : LinkState main' deps') : Prop
  :=
    s.curSem = s'.curSem ∧
    hsim_main.Sim s.mainState s'.mainState ∧
    (∀ op, (hsim_deps op).Sim (s.depStates op) (s'.depStates op))

/-- Refining components implies refining the linked semantics. -/
theorem sim_congr_link
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main main' : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps deps' : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps i ≲ deps' i)
  (hsim_main : main ≲ main')
  : main.link deps ≲ main'.link deps'
  := by
  apply Lts.SimilarBy.intro (SimRel hsim_deps hsim_main)
  apply SimulatedBy.alt
  and_intros
  · simp [link, LinkState.init]
  · exact hsim_main.sim_init
  · intros op
    exact (hsim_deps op).sim_init
  · intros s₁ s₂ l s₁' hsim hstep
    have ⟨hcur_sem, hsim_main_states, hsim_dep_states⟩ := hsim
    cases hstep with
    | step_main hcur hlabel hstep_main =>
      have ⟨mainState', hstep', hsim'⟩
        := hsim_main.sim_step _ _ _ _ hsim.2.1 (.single hstep_main)
      exists { s₂ with mainState := mainState' }
      constructor
      · simp [link, hcur_sem] at hcur ⊢
        simp [Lts.Step] at hstep'
        exact LinkStep.step_main_mod_tau hcur hlabel hstep'
      · and_intros
        · simp [hcur_sem]
        · exact hsim'
        · exact hsim_dep_states
    | _ => sorry

end Simulation

end Wavelet.Semantics
