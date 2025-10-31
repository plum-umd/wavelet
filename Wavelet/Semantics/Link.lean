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
    depStates := λ op => (deps op).init,
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

/-- Shorthand for whether the given state can potentially yield. -/
def HasYield
  [Arity Op]
  (sem : Semantics Op V m n)
  (s : sem.S) (op : Op) (inputs : Vector V (Arity.ι op)) : Prop :=
  ∃ outputs s', sem.lts.Step s (.yield op inputs outputs) s'

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
  (deps : (op : Op₁) → Semantics Op₀ V (Arity.ι op) (Arity.ω op))
  : Semantics Op₀ V m n
  := {
    S := LinkState main deps,
    init := LinkState.init main deps,
    lts := LinkStep main deps,
  }

/-- Converts individual state predicates to a single predicate on the linked state. -/
def LinkInv
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : (op : Op₁) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)}
  (mainInv : main.S → Prop)
  (depInvs : (op : Op₁) → (deps op).S → Prop)
  (s : LinkState main deps) : Prop
  := main.IsInvariantAt mainInv s.mainState ∧
    ∀ op, (deps op).IsInvariantAt (depInvs op) (s.depStates op)

/-- `LinkStep` preserves invariants on the main and dependent semantics. -/
theorem link_inv
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : (op : Op₁) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)}
  {mainInv : main.S → Prop}
  {depInvs : (op : Op₁) → (deps op).S → Prop}
  (hinv_main : main.IsInvariant mainInv)
  (hinv_deps : ∀ op, (deps op).IsInvariant (depInvs op)) :
    (link main deps).IsInvariant (LinkInv mainInv depInvs)
  := by
  apply Lts.IsInvariantAt.by_induction
  · simp [link, LinkState.init]
    constructor
    · exact hinv_main
    · intros depOp
      exact hinv_deps depOp
  · intros s₁ s₂ l hinv hstep
    cases hstep with
    | step_main hcur_sem hpass hstep =>
      simp [LinkInv] at hinv ⊢
      have ⟨hinv_main, hinv_deps⟩ := hinv
      constructor
      · have ⟨_, h⟩ := Lts.IsInvariantAt.unfold hinv_main hstep
        assumption
      · exact hinv_deps
    | step_dep hcur_sem hpass hstep
    | step_dep_spawn hcur_sem hpass hstep =>
      rename Op₁ => depOp
      simp [LinkInv] at hinv ⊢
      constructor
      · exact hinv.1
      · intros depOp'
        by_cases heq : depOp = depOp'
        · subst heq
          have ⟨_, h⟩ := Lts.IsInvariantAt.unfold (hinv.2 depOp) hstep
          intros h₁
          simp at h₁
          apply h h₁
        · simp [Ne.symm heq]
          exact hinv.2 depOp'
    | step_dep_ret hcur_sem hstep_dep hstep_main =>
      rename Op₁ => depOp
      simp [LinkInv] at hinv ⊢
      have ⟨hinv_main, hinv_deps⟩ := hinv
      constructor
      · have ⟨_, h⟩ := Lts.IsInvariantAt.unfold hinv_main hstep_main
        assumption
      · intros depOp'
        by_cases heq : depOp = depOp'
        · subst heq
          have ⟨_, h⟩ := Lts.IsInvariantAt.unfold (hinv.2 depOp) hstep_dep
          intros h₁
          simp at h₁
          apply h h₁
        · simp [Ne.symm heq]
          exact hinv.2 depOp'

/-- Any trace in the linked semantics can be converted
into a trace of any specific dependency (i.e., all dependency
states are only changed via their own transition and not
suddenly reset). -/
theorem link_star_to_dep_star
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : (op : Op₁) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)}
  {s s' : LinkState main deps}
  {tr : Trace (Label Op₀ V m n)}
  (hsteps : (link main deps).lts.Star s tr s')
  (depOp : Op₁) :
    ∃ tr',
      (deps depOp).lts.Star (s.depStates depOp) tr' (s'.depStates depOp)
  := sorry

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

/-- Similar to `step_dep`, but uses `TauStar`. -/
theorem LinkStep.step_dep_tau_star
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : PartInterp Op₀ Op₁ V}
  {s : LinkState main deps}
  {depState' : (deps depOp).S}
  (hcur : s.curSem = some depOp)
  (hstep : (deps depOp).lts.TauStar .τ (s.depStates depOp) depState') :
  (LinkStep main deps).TauStar .τ s
    { s with depStates := Function.update s.depStates depOp depState' }
  := by
  induction hstep with
  | refl => simp; exact .refl
  | tail pref tail ih =>
    apply Lts.TauStar.trans
    · exact ih
    · apply Lts.TauStar.single
      apply Lts.Step.eq_rhs
      · exact LinkStep.step_dep hcur .pass_tau
          (Lts.Step.eq_lhs tail (by simp))
      · simp

/-- Similar to `step_main`, but uses `IORestrictedStep`. -/
theorem LinkStep.step_main_io_restricted
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
  (hstep : main.lts.IORestrictedStep s.mainState l mainState') :
  (LinkStep main deps).IORestrictedStep s l' { s with mainState := mainState' }
  := by
  cases hstep with
  | step_yield hstep =>
    cases hlabel
    exact .step_yield (LinkStep.step_main hcur .pass_yield_inl hstep)
  | step_input hstep hstep_tau =>
    cases hlabel
    apply Lts.IORestrictedStep.step_input
    apply LinkStep.step_main hcur .pass_input
    exact hstep
    exact LinkStep.step_main_tau_star hcur hstep_tau
  | step_output hstep_tau hstep =>
    cases hlabel
    apply Lts.IORestrictedStep.step_output
    exact LinkStep.step_main_tau_star hcur hstep_tau
    apply LinkStep.step_main _ .pass_output
    exact hstep
    simp [hcur]
  | step_tau hstep =>
    cases hlabel
    exact .step_tau (LinkStep.step_main_tau_star hcur hstep)

/-- Similar to `step_dep`, but uses `IORestrictedStep`. -/
theorem LinkStep.step_dep_io_restricted
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps : PartInterp Op₀ Op₁ V}
  {depOp : Op₁}
  {s : LinkState main deps}
  {l : Label Op₀ V (Arity.ι depOp) (Arity.ω depOp)}
  {l' : Label Op₀ V m n}
  {depState' : (deps depOp).S}
  (hcur : s.curSem = some depOp)
  (hlabel : DepLabelPassthrough l l')
  (hstep : (deps depOp).lts.IORestrictedStep (s.depStates depOp) l depState') :
  (LinkStep main deps).IORestrictedStep s l'
    { s with depStates := Function.update s.depStates depOp depState' }
  := by
  cases hstep with
  | step_yield hstep =>
    cases hlabel
    exact .step_yield (LinkStep.step_dep hcur .pass_yield hstep)
  | step_input hstep hstep_tau =>
    cases hlabel
  | step_output hstep_tau hstep =>
    cases hlabel
  | step_tau hstep =>
    cases hlabel
    exact .step_tau (LinkStep.step_dep_tau_star hcur hstep)

private def SimRel
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main₁ main₂ : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps₁ deps₂ : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps₁ i ≲ᵣ deps₂ i)
  (hsim_main : main₁ ≲ᵣ main₂)
  (s₁ : LinkState main₁ deps₁)
  (s₂ : LinkState main₂ deps₂) : Prop
  :=
    s₁.curSem = s₂.curSem ∧
    hsim_main.Sim s₁.mainState s₂.mainState ∧
    (∀ op, (hsim_deps op).Sim (s₁.depStates op) (s₂.depStates op))

/-- Refining components implies refining the linked semantics. -/
theorem sim_congr_link
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main₁ main₂ : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps₁ deps₂ : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps₁ i ≲ᵣ deps₂ i)
  (hsim_main : main₁ ≲ᵣ main₂) :
    main₁.link deps₁ ≲ᵣ main₂.link deps₂
  := by
  apply Lts.Similarity.intro (SimRel hsim_deps hsim_main)
  constructor
  and_intros
  · simp [link, LinkState.init]
  · exact hsim_main.sim_init
  · intros op
    exact (hsim_deps op).sim_init
  · intros s₁ s₂ l s₁' hsim hstep_s₁
    have ⟨hcur_sem, hsim_main_states, hsim_dep_states⟩ := hsim
    cases hstep_s₁ with
    | step_main hcur₁ hlabel hstep_main₁ =>
      have ⟨mainState₂', hstep_s₂, hsim'⟩
        := hsim_main.sim_step _ _ _ _ hsim_main_states hstep_main₁
      exists { s₂ with mainState := mainState₂' }
      constructor
      · simp [link, hcur_sem] at hcur₁ ⊢
        simp [Lts.Step] at hstep_s₂
        exact LinkStep.step_main_io_restricted hcur₁ hlabel hstep_s₂
      · and_intros
        · simp [hcur_sem]
        · exact hsim'
        · exact hsim_dep_states
    | step_dep hcur₁ hlabel hstep_dep₁ =>
      rename_i depOp _ _
      have ⟨depState₂', hstep_s₂, hsim'⟩
        := (hsim_deps depOp).sim_step _ _ _ _
          (hsim_dep_states depOp) hstep_dep₁
      exists { s₂ with depStates := Function.update s₂.depStates depOp depState₂' }
      constructor
      · simp [link, hcur_sem] at hcur₁ ⊢
        simp [Lts.Step] at hstep_s₂
        exact LinkStep.step_dep_io_restricted hcur₁ hlabel hstep_s₂
      · and_intros
        · simp [hcur_sem]
        · exact hsim_main_states
        · intros op
          simp
          by_cases h : op = depOp
          · rw [h]
            simp
            exact hsim'
          · simp [h]
            apply hsim_dep_states
    | step_dep_spawn hcur₁ hyield₁ hstep_dep₁ =>
      rename_i depOp inputVals depState₁'
      have hcur₂ : s₂.curSem = none := by simp [hcur_sem] at hcur₁; exact hcur₁
      -- Convert `dep₁` input to `dep₂` input
      have ⟨depState₂', hstep_s₂, hsim₂'⟩
        := (hsim_deps depOp).sim_step _ _ _ _
          (hsim_dep_states depOp) hstep_dep₁
      cases hstep_s₂ with | step_input hstep_input_s₂ hstep_tau_s₂₁ =>
      rename_i s₂₁
      -- Convert `main₁` yield to `main₂` yield
      replace ⟨_, _, hyield₁⟩ := hyield₁
      have ⟨mainState₁', hstep_yield_s₂, hsim'⟩
        := hsim_main.sim_step _ _ _ _ hsim_main_states hyield₁
      cases hstep_yield_s₂ with | step_yield hstep_yield_s₂ =>
      -- Make the spawning step in the overall semantics
      have hstep_spawn₂ := LinkStep.step_dep_spawn hcur₂ ⟨_, _, hstep_yield_s₂⟩ hstep_input_s₂
      -- Finally, there are some leftover τ steps in `dep₂`
      replace hstep_spawn₂ := Lts.TauStar.trans
        (.single hstep_spawn₂)
        (LinkStep.step_dep_tau_star (by rfl) (by
          simp
          exact hstep_tau_s₂₁))
      simp at hstep_spawn₂
      replace ⟨s₂', hs₂', hstep_spawn₂⟩ := exists_eq_left.mpr hstep_spawn₂
      exists s₂'
      constructor
      · exact .step_tau hstep_spawn₂
      · simp [hs₂']
        and_intros
        · simp
        · simp [hsim_main_states]
        · simp
          intros op
          by_cases h : op = depOp
          · rw [h]
            simp [hsim₂']
          · simp [h]
            apply hsim_dep_states
    | step_dep_ret hcur₁ hstep_dep₁ hyield₁ =>
      rename_i depOp outputVals depState₁' inputVals mainState₁'
      have hcur₂ : s₂.curSem = some depOp
        := by simp [hcur_sem] at hcur₁; exact hcur₁
      -- Convert `dep₁` output to `dep₂` output
      have ⟨depState₂', hstep_s₂, hsim₂'⟩
        := (hsim_deps depOp).sim_step _ _ _ _
          (hsim_dep_states depOp) hstep_dep₁
      -- Convert `main₁` yield to `main₂` yield
      have ⟨mainState₂', hstep_yield_s₂, hsim'⟩
        := hsim_main.sim_step _ _ _ _ hsim_main_states hyield₁
      cases hstep_yield_s₂ with | step_yield hstep_yield_s₂ =>
      -- Make leftover τ steps before `hstep_s₂`
      cases hstep_s₂ with | step_output hstep_tau_s₂ hstep_output_s₂ =>
      have := LinkStep.step_dep_tau_star hcur₂ hstep_tau_s₂
      -- Make the returning step
      have := Lts.TauStar.trans
        this
        (.single
          (LinkStep.step_dep_ret hcur₂
            (by simp; exact hstep_output_s₂)
            hstep_yield_s₂))
      simp at this
      replace ⟨s₂', hs₂', hstep_ret₂⟩ := exists_eq_left.mpr this
      exists s₂'
      constructor
      · exact .step_tau hstep_ret₂
      · simp [hs₂']
        and_intros
        · simp
        · simp [hsim']
        · simp
          intros op
          by_cases h : op = depOp
          · rw [h]
            simp [hsim₂']
          · simp [h]
            apply hsim_dep_states

private def SimRelPI
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main₁ main₂ : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps₁ deps₂ : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps₁ i ≲ᵣ[PreservesInit] deps₂ i)
  (hsim_main : main₁ ≲ᵣ[PreservesInit] main₂)
  (s₁ : LinkState main₁ deps₁)
  (s₂ : LinkState main₂ deps₂) : Prop
  :=
    s₁.curSem = s₂.curSem ∧
    hsim_main.Sim s₁.mainState s₂.mainState ∧
    (∀ op, (hsim_deps op).Sim (s₁.depStates op) (s₂.depStates op))

/-- TODO: Merge this proof with `sim_congr_link`. -/
theorem sim_congr_link_preserves_init
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main₁ main₂ : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps₁ deps₂ : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps₁ i ≲ᵣ[PreservesInit] deps₂ i)
  (hsim_main : main₁ ≲ᵣ[PreservesInit] main₂) :
    main₁.link deps₁ ≲ᵣ[PreservesInit] main₂.link deps₂
  := by
  apply Lts.SimilaritySt.intro (SimRelPI hsim_deps hsim_main)
  · constructor
    and_intros
    · simp [link, LinkState.init]
    · exact hsim_main.sim_init
    · intros op
      exact (hsim_deps op).sim_init
    · intros s₁ s₂ l s₁' hsim hstep_s₁
      have ⟨hcur_sem, hsim_main_states, hsim_dep_states⟩ := hsim
      cases hstep_s₁ with
      | step_main hcur₁ hlabel hstep_main₁ =>
        have ⟨mainState₂', hstep_s₂, hsim'⟩
          := hsim_main.sim_step _ _ _ _ hsim_main_states hstep_main₁
        exists { s₂ with mainState := mainState₂' }
        constructor
        · simp [link, hcur_sem] at hcur₁ ⊢
          simp [Lts.Step] at hstep_s₂
          exact LinkStep.step_main_io_restricted hcur₁ hlabel hstep_s₂
        · and_intros
          · simp [hcur_sem]
          · exact hsim'
          · exact hsim_dep_states
      | step_dep hcur₁ hlabel hstep_dep₁ =>
        rename_i depOp _ _
        have ⟨depState₂', hstep_s₂, hsim'⟩
          := (hsim_deps depOp).sim_step _ _ _ _
            (hsim_dep_states depOp) hstep_dep₁
        exists { s₂ with depStates := Function.update s₂.depStates depOp depState₂' }
        constructor
        · simp [link, hcur_sem] at hcur₁ ⊢
          simp [Lts.Step] at hstep_s₂
          exact LinkStep.step_dep_io_restricted hcur₁ hlabel hstep_s₂
        · and_intros
          · simp [hcur_sem]
          · exact hsim_main_states
          · intros op
            simp
            by_cases h : op = depOp
            · rw [h]
              simp
              exact hsim'
            · simp [h]
              apply hsim_dep_states
      | step_dep_spawn hcur₁ hyield₁ hstep_dep₁ =>
        rename_i depOp inputVals depState₁'
        have hcur₂ : s₂.curSem = none := by simp [hcur_sem] at hcur₁; exact hcur₁
        -- Convert `dep₁` input to `dep₂` input
        have ⟨depState₂', hstep_s₂, hsim₂'⟩
          := (hsim_deps depOp).sim_step _ _ _ _
            (hsim_dep_states depOp) hstep_dep₁
        cases hstep_s₂ with | step_input hstep_input_s₂ hstep_tau_s₂₁ =>
        rename_i s₂₁
        -- Convert `main₁` yield to `main₂` yield
        replace ⟨_, _, hyield₁⟩ := hyield₁
        have ⟨mainState₁', hstep_yield_s₂, hsim'⟩
          := hsim_main.sim_step _ _ _ _ hsim_main_states hyield₁
        cases hstep_yield_s₂ with | step_yield hstep_yield_s₂ =>
        -- Make the spawning step in the overall semantics
        have hstep_spawn₂ := LinkStep.step_dep_spawn hcur₂ ⟨_, _, hstep_yield_s₂⟩ hstep_input_s₂
        -- Finally, there are some leftover τ steps in `dep₂`
        replace hstep_spawn₂ := Lts.TauStar.trans
          (.single hstep_spawn₂)
          (LinkStep.step_dep_tau_star (by rfl) (by
            simp
            exact hstep_tau_s₂₁))
        simp at hstep_spawn₂
        replace ⟨s₂', hs₂', hstep_spawn₂⟩ := exists_eq_left.mpr hstep_spawn₂
        exists s₂'
        constructor
        · exact .step_tau hstep_spawn₂
        · simp [hs₂']
          and_intros
          · simp
          · simp [hsim_main_states]
          · simp
            intros op
            by_cases h : op = depOp
            · rw [h]
              simp [hsim₂']
            · simp [h]
              apply hsim_dep_states
      | step_dep_ret hcur₁ hstep_dep₁ hyield₁ =>
        rename_i depOp outputVals depState₁' inputVals mainState₁'
        have hcur₂ : s₂.curSem = some depOp
          := by simp [hcur_sem] at hcur₁; exact hcur₁
        -- Convert `dep₁` output to `dep₂` output
        have ⟨depState₂', hstep_s₂, hsim₂'⟩
          := (hsim_deps depOp).sim_step _ _ _ _
            (hsim_dep_states depOp) hstep_dep₁
        -- Convert `main₁` yield to `main₂` yield
        have ⟨mainState₂', hstep_yield_s₂, hsim'⟩
          := hsim_main.sim_step _ _ _ _ hsim_main_states hyield₁
        cases hstep_yield_s₂ with | step_yield hstep_yield_s₂ =>
        -- Make leftover τ steps before `hstep_s₂`
        cases hstep_s₂ with | step_output hstep_tau_s₂ hstep_output_s₂ =>
        have := LinkStep.step_dep_tau_star hcur₂ hstep_tau_s₂
        -- Make the returning step
        have := Lts.TauStar.trans
          this
          (.single
            (LinkStep.step_dep_ret hcur₂
              (by simp; exact hstep_output_s₂)
              hstep_yield_s₂))
        simp at this
        replace ⟨s₂', hs₂', hstep_ret₂⟩ := exists_eq_left.mpr this
        exists s₂'
        constructor
        · exact .step_tau hstep_ret₂
        · simp [hs₂']
          and_intros
          · simp
          · simp [hsim']
          · simp
            intros op
            by_cases h : op = depOp
            · rw [h]
              simp [hsim₂']
            · simp [h]
              apply hsim_dep_states
  · intros s₁ s₂ hsim hinit
    subst hinit
    rcases s₂ with ⟨curSem, mainState, depStates⟩
    simp [SimRelPI, link, LinkState.init] at hsim
    have ⟨h₁, h₂, h₃⟩ := hsim
    simp [link, LinkState.init, h₁, hsim_main.sim_prop _ _ h₂ (by rfl)]
    funext depOp
    exact (hsim_deps depOp).sim_prop _ _ (h₃ depOp) (by rfl)

end Simulation

end Wavelet.Semantics
