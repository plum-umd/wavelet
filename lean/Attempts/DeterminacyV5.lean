import Mathlib.Control.ULiftable
import Mathlib.Logic.Basic

import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

namespace Wavelet.Semantics

def InrDisjointTokens
  [PCM T]
  (v₁ v₂ : V ⊕ T) : Prop :=
  ∀ {t₁ t₂},
    v₁ = .inr t₁ →
    v₂ = .inr t₂ →
    t₁ ⊥ t₂

end Wavelet.Semantics

namespace Wavelet.Seq

open Semantics

def VarMap.Pairwise
  (P : V → V → Prop)
  (vars : VarMap χ V) : Prop :=
  ∀ {x₁ x₂ v₁ v₂},
    x₁ ≠ x₂ →
    vars.getVar x₁ = some v₁ →
    vars.getVar x₂ = some v₂ →
    P v₁ v₂

def VarMap.DisjointTokens
  [PCM T]
  (vars : VarMap χ (V ⊕ T)) : Prop :=
  vars.Pairwise InrDisjointTokens

@[simp]
theorem VarMap.pairwise_empty
  (P : V → V → Prop) :
  (VarMap.empty (χ := χ)).Pairwise P := by
  intros x₁ x₂ v₁ v₂ hne hget₁ hget₂
  simp [getVar, empty] at hget₁

@[simp]
def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop := c.vars.DisjointTokens

abbrev ExprWithSpec
  [Arity Op] [PCM T]
  (opSpec : Semantics.OpSpec Op V T) χ m n
  := Expr (WithSpec Op opSpec) χ (m + 1) (n + 1)

abbrev FnWithSpec
  [Arity Op] [PCM T]
  (opSpec : Semantics.OpSpec Op V T) χ m n
  := Fn (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics

def ChanMap.Pairwise
  (P : V → V → Prop)
  (map : ChanMap χ V) : Prop :=
  ∀ {x₁ x₂}
    {buf₁ buf₂ : List V}
    {i : Fin buf₁.length}
    {j : Fin buf₂.length},
    x₁ ≠ x₂ ∨ i.val ≠ j.val →
    map x₁ = some buf₁ →
    map x₂ = some buf₂ →
    P buf₁[i] buf₂[j]

@[simp]
theorem ChanMap.pairwise_empty
  (P : V → V → Prop) :
  (ChanMap.empty (χ := χ)).Pairwise P := by
  intros x₁ x₂ buf₁ buf₂ i j hne hget₁ hget₂
  simp [ChanMap.empty] at hget₁
  simp [hget₁] at i
  exact Fin.elim0 i

/-- Defines a config property that imposes a
constraint on every pair of values in the config. -/
def Config.Pairwise
  [Arity Op]
  (P : V → V → Prop)
  (c : Config Op χ V m n) : Prop :=
  c.chans.Pairwise P

@[simp]
def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  c.Pairwise InrDisjointTokens

abbrev ProcWithSpec
  [Arity Op] [PCM T]
  (opSpec : Semantics.OpSpec Op V T) χ m n
  := Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow

/-
Proof sketch (for a single `Fn`):

We show that

```
untyped functions
≤ typed functions + disjoint tokens + dynamic race detector
≤ typed processes + disjoint tokens + dynamic race detector
```

```
fn.semantics
  ≲ᵣ (fn'.semantics.guard ...).interpLabel
  ≲ᵣ ((compileFn ... fn').semantics.guard ...).interpLabel
    -- by (fn'.semantics.guard ...) ≲ᵣ ((compileFn ... fn').semantics.guard ...)
  (... maybe some optimization passes)
  ≲ᵣ proc.semantics.guard ...
  ≲ᵣ (eraseGhost proc).semantics
```
and also
```
(eraseGhost proc).semantics
  ≲ᵣ proc.semantics.guard ...
```

`(eraseGhost proc)` would be the final compiled dataflow program.

And we have:

1. Correctness:
   - For any trace of `fn.semantics`, there exists a
     corresponding trace `T₁` of `proc.semantics.guard ...`
   - For any trace of `(eraseGhost proc).semantics`
     there exists a corresponding trace `T₂` of `proc.semantics.guard ...`
   By `guarded_confluence` below, they should converge to the same state.

2. Liveness: since `fn.semantics ≲ᵣ (eraseGhost proc).semantics`
   `eraseGhost proc` should have at least one trace simulating `fn`.
-/

/-- Erase ghost tokens. -/
def eraseGhost
  [Arity Op] [PCM T]
  {opSpec : Semantics.OpSpec Op V T}
  (proc : ProcWithSpec opSpec χ m n) : Proc Op χ V m n
  := sorry

/-- Backward simulation for `eraseGhost`. -/
theorem sim_erase_ghost
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n) :
  (eraseGhost proc).semantics ≲ᵣ
    proc.semantics.guard (opSpec.Guard ioSpec)
  := sorry

/-- Forward simulation for liveness. -/
theorem sim_erase_ghost_forward
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n) :
  proc.semantics.guard (opSpec.Guard ioSpec)
    ≲ᵣ (eraseGhost proc).semantics
  := sorry

/-- If two labels are either yield or silent and are deterministic. -/
def Label.IsYieldOrSilentAndDet
  [Arity Op]
  (l₁ : Label Op V m n) (l₂ : Label Op V m n) : Prop :=
  (l₁.isYield ∨ l₁.isSilent) ∧
  (l₂.isYield ∨ l₂.isSilent) ∧
  Label.Deterministic l₁ l₂

/-- Without considering shared operator states, and when
restricted to silent/yield labels, a well-formed `Proc` has
a strongly confluent (and thus confluent) semantics. -/
theorem proc_strong_confl_at
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  (proc : Proc Op χ V m n)
  (s : proc.semantics.S)
  (haff : s.proc.AffineChan) :
    proc.semantics.lts.StronglyConfluentAt s Label.IsYieldOrSilentAndDet
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨hlabel₁, hlabel₂, hyield_det⟩ := hcompat
  have ⟨_, _, ⟨haff_nodup, haff_disj⟩, _⟩ := haff
  by_cases heq_state : s₁' = s₂'
  · exact .inl heq_state
  · right
    -- Keep some acronyms so that they don't get expanded
    generalize hs₁' : s₁' = s₁''
    generalize hs₂' : s₂' = s₂''
    cases hstep₁ <;> cases hstep₂
    any_goals
      simp at hlabel₁ hlabel₂
    -- Commute two `step_op`s
    case neg.h.step_op.step_op =>
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hmem₁ hpop₁
        op₂ inputs₂ outputs₂ inputVals₂ outputVals₂ chans₂' hmem₂ hpop₂
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem₂
      by_cases h : i = j
      · subst h
        simp [hget_i] at hget_j
        have ⟨h₁, h₂, h₃⟩ := hget_j
        subst h₁; subst h₂; subst h₃
        simp [hpop₁] at hpop₂
        have ⟨h₄, h₅⟩ := hpop₂
        subst h₄; subst h₅
        have := hyield_det (by rfl) (by rfl)
        subst this
        simp at heq_state
      · have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h])
        simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
          .step_op
            (outputVals := outputVals₂)
            (by simp [← hs₁']; exact hmem₂)
            (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
        have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
          .step_op (outputVals := outputVals₁)
            (by simp [← hs₂']; exact hmem₁)
            (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
        rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
        simp [← hs₁'] at hstep₁' ⊢
        simp [← hs₂'] at hstep₂' ⊢
        exact ⟨_, hstep₁', hstep₂'⟩
    -- Commute `step_op` and `step_async`
    case neg.h.step_op.step_async =>
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hmem₁ hpop₁
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' j hinterp₂ hj hget_j hpop₂
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have hne : i ≠ j := by
        intro heq; subst heq
        simp [hget_i] at hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hne])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      -- simp [happ₂] at hmem₁
      have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁']; exact hget_j)
          hinterp₂
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by
            simp [← hs₂']
            apply List.mem_set_ne
            exact hget_i
            exact hne.symm)
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp [← hs₁'] at hstep₁' ⊢
      simp [← hs₂'] at hstep₂' ⊢
      exact ⟨_, hstep₁', hstep₂'⟩
    -- Commute `step_async` and `step_op`
    case neg.h.step_async.step_op =>
      rename_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' j hinterp₂ hj hget_j hpop₂
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hmem₁ hpop₁
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have hne : i ≠ j := by
        intro heq; subst heq
        simp [hget_i] at hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hne])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      -- simp [happ₂] at hmem₁
      have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₂']; exact hj)
          (by simp [← hs₂']; exact hget_j)
          hinterp₂
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by
            simp [← hs₁']
            apply List.mem_set_ne
            exact hget_i
            exact hne.symm)
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₂'
      simp [← hs₁'] at hstep₁' ⊢
      simp [← hs₂'] at hstep₂' ⊢
      exact ⟨_, hstep₁', hstep₂'⟩
    -- Commute two `step_async`s
    case neg.h.step_async.step_async =>
      rename_i
        _ _ aop₁ aop₁' allInputs₁ allOutputs₁
        inputs₁ inputVals₁ outputs₁ outputVals₁ chans₁' i hinterp₁ hi hget_i hpop₁
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' j hinterp₂ hj hget_j hpop₂
      by_cases h : i = j
      -- Firing the same async op => final state should be the same
      · apply False.elim
        apply heq_state
        subst h
        simp [hget_i] at hget_j
        have ⟨h₁, h₂, h₃⟩ := hget_j
        subst h₁; subst h₂; subst h₃
        simp at hinterp₁ hinterp₂
        simp
        have heq_inputs_len := async_op_interp_det_inputs_len hinterp₁ hinterp₂
        simp at heq_inputs_len
        subst heq_inputs_len
        have heq_inputs : inputs₁ = inputs₂ := by
          -- Generealize so that we can do case analysis
          generalize hinputs₁ : inputs₁.toList = inputs₁
          generalize hinput_vals₁ : inputVals₁.toList = inputVals₁
          generalize houtputs₁ : outputs₁.toList = outputs₁
          generalize houtput_vals₁ : outputVals₁.toList = outputVals₁
          rw [hinputs₁, hinput_vals₁, houtputs₁, houtput_vals₁] at hinterp₁
          generalize hinputs₂ : inputs₂.toList = inputs₂
          generalize hinput_vals₂ : inputVals₂.toList = inputVals₂
          generalize houtputs₂ : outputs₂.toList = outputs₂
          generalize houtput_vals₂ : outputVals₂.toList = outputVals₂
          rw [hinputs₂, hinput_vals₂, houtputs₂, houtput_vals₂] at hinterp₂
          cases hinterp₁ <;> cases hinterp₂
          any_goals
            simp [← hinputs₁, Vector.toList_inj] at hinputs₂
            simp [hinputs₂]
          -- Merges are slightly complicated,
          -- since the inputs can depend on input decider value...
          -- TODO: a better solution would be to add local states
          -- to merge similar to carry.
          case
            interp_merge_true.interp_merge_false |
            interp_merge_false.interp_merge_true =>
            have := pop_vals_eq_head hinputs₁ hinputs₂ hpop₁ hpop₂
            simp [hinput_vals₁, hinput_vals₂] at this
            subst this
            grind only
        have heq_input_vals : inputVals₁ = inputVals₂ := by
          simp [heq_inputs] at hpop₁
          simp [hpop₁] at hpop₂
          simp [hpop₂]
        have heq_outputs := async_op_interp_det_outputs hinterp₁ hinterp₂
          (by simp [heq_inputs])
          (by simp [heq_input_vals])
        have heq_chans : chans₁' = chans₂' := by
          simp [heq_inputs] at hpop₁
          simp [hpop₁] at hpop₂
          simp [hpop₂]
        congr 1
        · congr
          simp [heq_outputs]
        · have ⟨h, _⟩ := Vector.toList_inj_heq heq_outputs.1
          subst h
          simp [Vector.toList_inj] at heq_outputs
          simp [heq_outputs, heq_chans]
      -- Firing two different async ops
      · have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
          ⟨i, hi⟩ ⟨j, hj⟩
          (by simp [h])
        simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        replace hdisj_inputs := List.disjoint_of_subset_left
          (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs
        replace hdisj_inputs := List.disjoint_of_subset_right
          (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
        replace hdisj_outputs := List.disjoint_of_subset_left
          (async_op_interp_output_sublist hinterp₁).subset hdisj_outputs
        replace hdisj_outputs := List.disjoint_of_subset_right
          (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
          .step_async (i := j)
            (by simp [← hs₁', hj])
            (by simp [← hs₁', h]; exact hget_j)
            hinterp₂
            (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
        have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
          .step_async (i := i)
            (by simp [← hs₂', hi])
            (by simp [← hs₂', Ne.symm h]; exact hget_i)
            hinterp₁
            (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
        rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
        simp [← hs₁'] at hstep₁' ⊢
        simp [← hs₂'] at hstep₂' ⊢
        exact ⟨_, hstep₁',
          by
            apply Lts.Step.eq_rhs hstep₂'
            congr 2
            apply List.set_comm
            exact Ne.symm h
        ⟩

-- theorem guard_state_strong_confl_at
--   [Arity Op] [Arity Op']
--   (sem : Semantics Op V m n)
--   (s : sem.S)
--   {Inv : sem.S → Prop}
--   {Compat : Label Op V m n → Label Op V m n → Prop}
--   (hinv : sem.IsInvariantAt Inv s)
--   (hconfl : sem.lts.StronglyConfluentAt s Compat) :
--     (sem.guardState Inv).lts.StronglyConfluentAt s Compat
--   := by
--   -- This requires `Inv` to be an invariant, so maybe
--   -- the guard is not needed in the first place?
--   sorry

/--
Applying `guardState (Config.Pairwise P)` preserves confluence.

NOTE: `guardState` does not preserve confluence in general.
-/
theorem proc_gaurd_pairwise_strong_confl_at
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {P : V → V → Prop}
  {Compat : Label Op V m n → Label Op V m n → Prop}
  (proc : Proc Op χ V m n)
  (s : proc.semantics.S)
  -- (haff : s.proc.AffineChan)
  (hconfl : proc.semantics.lts.StronglyConfluentAt s Compat) :
    (proc.semantics.guardState (Config.Pairwise P)).lts.StronglyConfluentAt s Compat
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases hstep₁ with ⟨hinv₁, hinv₁', hstep₁⟩
  rcases hstep₂ with ⟨hinv₂, hinv₂', hstep₂⟩
  cases hconfl hstep₁ hstep₂ hcompat with
  | inl heq => exact .inl heq
  | inr h =>
    right
    have ⟨s', hstep₁', hstep₂'⟩ := h
    exists s'
    constructor
    · apply Lts.GuardState.step
      · exact hinv₁'
      · -- TODO: actually this probably not true.
        sorry
      · exact hstep₁'
    · sorry

theorem guard_label_strong_confl_at
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (s : sem.S)
  {Guard : Label Op V m n → Label Op' V' m' n' → Prop}
  {Compat : Label Op V m n → Label Op V m n → Prop}
  (hconfl : sem.lts.StronglyConfluentAt s Compat) :
    (sem.guardLabel Guard).lts.StronglyConfluentAt s
      (λ l₁' l₂' => ∀ {l₁ l₂},
        Guard l₁ l₁' →
        Guard l₂ l₂' →
        Compat l₁ l₂)
  := by
  intros s₁' s₂' l₁' l₂' hstep₁ hstep₂ hcompat
  rcases hstep₁ with ⟨hguard₁', hstep₁⟩
  rcases hstep₂ with ⟨hguard₂', hstep₂⟩
  have hcompat' := hcompat hguard₁' hguard₂'
  cases hconfl hstep₁ hstep₂ hcompat' with
  | inl heq => exact .inl heq
  | inr h =>
    right
    have ⟨s', hstep₁', hstep₂'⟩ := h
    exists s'
    constructor
    · exact ⟨hguard₂', hstep₁'⟩
    · exact ⟨hguard₁', hstep₂'⟩

/-- `Config.DisjointTokens` is a state invariant of a guarded `Proc` semantics. -/
theorem proc_guard_label_inv_disj
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n) :
    (proc.semantics.guardLabel (opSpec.Guard ioSpec)).IsInvariant
      Config.DisjointTokens
  := by
  apply IsInvariantAt.by_induction
  · simp [Dataflow.Config.init, Semantics.guardLabel,
      Proc.semantics, Config.Pairwise]
  · intros s s' l hinv hstep
    sorry

/-- Strong confluence of a `ProcWithSpec` when interpreted. -/
theorem proc_interp_strong_confl
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  -- Sound (wrt. opSpec) and deterministic interpretation
  (interp : OpInterp Op V)
  (hsound : OpSpec.Sound opSpec interp)
  (hdet : interp.Deterministic) :
    ((proc.semantics.guardLabel (opSpec.Guard ioSpec)).interpret interp).lts.StronglyConfluent
      (λ (s, _) => s.proc.AffineChan)
      (λ l₁ l₂ => l₁.isSilent ∧ l₂.isSilent)
  := by
  intros s hinv s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases s with ⟨s, t⟩
  rcases s₁' with ⟨s₁', t₁'⟩
  rcases s₂' with ⟨s₂', t₂'⟩
  case mk.mk.mk =>
  simp at hinv
  cases hstep₁ <;> cases hstep₂ <;> simp at hcompat
  case step_tau.step_tau hstep₁ hstep₂ =>
    cases hstep₁ with | step hguard₁ hstep₁ =>
    cases hstep₂ with | step hguard₂ hstep₂ =>
    cases hguard₁ <;> cases hguard₂
    · have := proc_strong_confl_at proc s hinv hstep₁ hstep₂
      -- There is some non-determinism with join...
      sorry
    all_goals sorry
  all_goals sorry

-- TODO: guarding a confluent semantics is confluent

-- TODO: enforcing SpecLabelInterp on a confluent semantics is confluent

end Wavelet.Compile

namespace Wavelet.Seq

open Semantics

/-- Simple non-dependent resource specs. -/
structure SimpleOpSpec Op T [PCM T] where
  pre : Op → T
  post : Op → T
  frame_preserving : ∀ op, pre op ⟹ post op

def SimpleOpSpec.toOpSpec
  V [Arity Op] [PCM T]
  (spec : SimpleOpSpec Op T) :
  Semantics.OpSpec Op V T := {
    pre op _ := spec.pre op,
    post op _ _ := spec.post op,
    frame_preserving := by intros; apply spec.frame_preserving
  }

structure SimpleIOSpec T [PCM T] where
  pre : T
  post : T

def SimpleIOSpec.toIOSpec
  [PCM T]
  (spec : SimpleIOSpec T) m n :
  IOSpec V T m n := {
    pre _ := spec.pre,
    post _ := spec.post,
  }

/-- `.inl` for base vars, `.inr` for token variables. -/
abbrev TypedName χ := χ ⊕ Nat

/-- Tries to find a set of `ts : Fin numToks`
such that `req ≤ sum of (ts.map ctx)`. -/
def tryAcquire
  (ctx : Nat → Option T)
  (numToks : Nat)
  (req : T) : Option (List Nat) :=
  sorry

/-- Helper function for `typeCheck`. -/
noncomputable def typeCheckInternal
  [Arity Op] [PCM T]
  [DecidableLE T]
  (opSpec : SimpleOpSpec Op T)
  (ioSpec : SimpleIOSpec T)
  (ctx : Nat → Option T)
  (numToks : Nat) :
  Expr Op χ m n →
  Option (ExprWithSpec (opSpec.toOpSpec V) (TypedName χ) m n)
  | .ret args => do
    let toks ← tryAcquire ctx numToks ioSpec.post
    return .op (.join toks.length)
      (toks.toVector.map .inr)
      #v[.inr numToks, .inr (numToks + 1)]
      (.ret ((args.map .inl).push (.inr numToks)))
  | .tail args => do
    let toks ← tryAcquire ctx numToks ioSpec.pre
    return .op (.join toks.length)
      (toks.toVector.map .inr)
      #v[.inr numToks, .inr (numToks + 1)]
      (.tail ((args.map .inl).push (.inr numToks)))
  | .op o args bind cont => do
    let toks ← tryAcquire ctx numToks (opSpec.pre o)
    let tok₁ := .inr numToks
    let tok₂ := .inr (numToks + 1)
    let tok₃ := .inr (numToks + 2)
    let newCtx₁ := λ i => if i ∈ toks then none else ctx i
    let newCtx₂ := Function.update newCtx₁ numToks (some (opSpec.pre o))
    let sumToks ← toks.foldlM (λ acc i => return acc ⊔ (← ctx i)) PCM.zero
    if h : opSpec.pre o ≤ sumToks then
      let newCtx₃ := Function.update newCtx₂ (numToks + 1) (some (PCM.sub sumToks (opSpec.pre o) h))
      let newCtx₄ := Function.update newCtx₃ (numToks + 2) (some (opSpec.post o))
      return .op (.join toks.length) (toks.toVector.map .inr) #v[tok₁, tok₂]
        (.op (.op o)
          ((args.map .inl).push tok₁)
          ((bind.map .inl).push tok₃)
          (← typeCheckInternal opSpec ioSpec newCtx₄ (numToks + 3) cont))
    else
      none
  | .br cond left right => do
    let left' ← typeCheckInternal opSpec ioSpec ctx numToks left
    let right' ← typeCheckInternal opSpec ioSpec ctx numToks right
    return .br (.inl cond) left' right'

/-- Type check a function against the given specs,
and insert split/join to concretize the flow of permissions. -/
noncomputable def typeCheck
  [Arity Op] [PCM T]
  [DecidableLE T]
  (opSpec : SimpleOpSpec Op T)
  (ioSpec : SimpleIOSpec T)
  (fn : Fn Op χ V m n) :
  Option (FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n)
  := return {
    params := (fn.params.map .inl).push (.inr 0),
    body := ← typeCheckInternal opSpec ioSpec
      (Function.update (Function.const _ none) 0 (some ioSpec.pre)) 1 fn.body,
  }

/-- Map from ghost variable names to their concrete permission. -/
structure PermCtx T where
  perms : VarMap Nat T
  numVars : Nat

/-- Insert `n` new permission tokens and return the fresh indices -/
def PermCtx.insertVars
  [PCM T]
  (ctx : PermCtx T) (tys : Vector T n) :
  Vector Nat n × PermCtx T :=
  let newIdxs := Vector.range' ctx.numVars n
  (newIdxs, {
    perms := ctx.perms.insertVars newIdxs tys,
    numVars := ctx.numVars + n
  })

def PermCtx.removeVars
  [PCM T]
  (ctx : PermCtx T) (idxs : List Nat) : PermCtx T :=
  { ctx with perms := ctx.perms.removeVars idxs }

/-- Initial context with a single permission variable. -/
def PermCtx.init
  [PCM T] (init : T) : PermCtx T := {
    perms idx := if idx = 0 then some init else none,
    numVars := 1
  }

/-- Defines when a (disjoint) list of variable indices
has a total permission equal to the sum of `req` and `rem`. -/
def PermCtx.Acquire
  [PCM T]
  (ctx : PermCtx T)
  (req rem : T)
  (tokIds : Vector Nat k)
  (toks : Vector T k) : Prop :=
  tokIds.toList.Nodup ∧
  ctx.perms.getVars tokIds = some toks ∧
  req ⊔ rem ≡ PCM.sum toks.toList

/-- Relational definition for a function to be well-typed
as a more elaborated `FnWithSpec` with explicit permissions. -/
inductive Expr.WellPermTyped
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T) :
  PermCtx T → Expr Op χ m n →
  ExprWithSpec (opSpec.toOpSpec V) (TypedName χ) m n → Prop where
  | wpt_ret {joined ctx' ctx vars rem}
    (k : Nat) {tokIds : Vector Nat k} {toks : Vector T k} :
    ctx.Acquire ioSpec.post rem tokIds toks →
    ctx.insertVars #v[ioSpec.post, rem] = (joined, ctx') →
    WellPermTyped ioSpec ctx
      (.ret vars)
      (.op (.join k) (tokIds.map .inr) (joined.map .inr)
        (.ret ((vars.map .inl).push (.inr joined[0]))))
  | wpt_tail {joined ctx' ctx args rem}
    (k : Nat) {tokIds : Vector Nat k} {toks : Vector T k} :
    -- The returned permission should exactly match since the token is non-dependent
    ctx.Acquire ioSpec.pre rem tokIds toks →
    ctx.insertVars #v[ioSpec.pre, rem] = (joined, ctx') →
    WellPermTyped ioSpec ctx
      (.tail args)
      (.op (.join k) (tokIds.map .inr) (joined.map .inr)
        (.tail ((args.map .inl).push (.inr joined[0]))))
  | wpt_op {ctx' joined ctx'' cont cont' ctx o args rem}
    {bind}
    (k : Nat) {tokIds : Vector Nat k} {toks : Vector T k} :
    ctx.Acquire (opSpec.pre o) rem tokIds toks →
    ctx.removeVars tokIds.toList = ctx' →
    ctx'.insertVars #v[opSpec.pre o, rem, opSpec.post o] = (joined, ctx'') →
    WellPermTyped ioSpec (ctx''.removeVars [joined[0]]) cont cont' →
    WellPermTyped ioSpec ctx
      (.op o args bind cont)
      (.op (.join k) -- First call join to collect required permissions
        (tokIds.map .inr)
        #v[.inr joined[0], .inr joined[1]]
        (.op (.op o) -- Then call the actual operator
          ((args.map .inl).push (.inr joined[0]))
          ((bind.map .inl).push (.inr joined[2])) cont'))
  | wpt_br {ctx cond left left' right right'} :
    WellPermTyped ioSpec ctx left left' →
    WellPermTyped ioSpec ctx right right' →
    WellPermTyped ioSpec ctx (.br cond left right) (.br (.inl cond) left' right')

def Fn.WellPermTyped
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T)
  (fn : Fn Op χ V m n)
  (fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n) :
  Prop :=
  fn'.params = (fn.params.map .inl).push (.inr 0) ∧
  Expr.WellPermTyped ioSpec (.init (ioSpec.pre)) fn.body fn'.body

def SimRel
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T)
  (s₁ : Config Op χ V m n)
  (s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)) :
  Prop :=
  s₁.fn.WellPermTyped ioSpec s₂.fn ∧
  s₂.DisjointTokens ∧
  (s₁.cont = .init → s₂.cont = .init) ∧
  (∀ expr,
    s₁.cont = .expr expr →
    ∃ ctx expr₂,
      s₂.cont = .expr expr₂ ∧
      Expr.WellPermTyped ioSpec ctx expr expr₂ ∧
      s₂.vars = VarMap.disjointUnion s₁.vars ctx.perms)

/-! Lemmas. TODO: move to somewhere else -/
section Lemmas

theorem var_map_disjoint_union_get_vars_left
  {m₁ : VarMap χ₁ V₁}
  {m₂ : VarMap χ₂ V₂}
  (hget : m₁.getVars vars = some vals) :
  (VarMap.disjointUnion m₁ m₂).getVars (vars.map .inl) = some (vals.map .inl)
  := sorry

theorem var_map_disjoint_union_get_var_left
  {m₁ : VarMap χ₁ V₁}
  {m₂ : VarMap χ₂ V₂}
  (hget : m₁.getVar var = some val) :
  (VarMap.disjointUnion m₁ m₂).getVar (.inl var) = some (.inl val)
  := sorry

theorem var_map_disjoint_union_get_vars_right
  {m₁ : VarMap χ₁ V₁}
  {m₂ : VarMap χ₂ V₂}
  (hget : m₂.getVars vars = some vals) :
  (VarMap.disjointUnion m₁ m₂).getVars (vars.map .inr) = some (vals.map .inr)
  := sorry

theorem var_map_init_disjoint_tokens
  [DecidableEq χ] [PCM T]
  {vars : Vector χ (n + 1)}
  {args : Vector V n}
  {tok : T} :
  (VarMap.fromList (vars.zip ((args.map .inl).push (.inr tok))).toList).DisjointTokens
:= sorry

end Lemmas

theorem sim_type_check_init
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  (hwt : fn.WellPermTyped ioSpec fn') :
    SimRel ioSpec
      fn.semantics.init
      (fn'.semantics.guard Config.DisjointTokens
          ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).init
  := by
  simp [Fn.semantics, Semantics.guard, Semantics.guardState, Semantics.guardLabel, Config.init]
  simp [Fn.WellPermTyped] at hwt
  and_intros
  · simp [hwt]
  · simp [hwt]
  · simp [VarMap.DisjointTokens]
  · simp
  · simp

theorem sim_type_check_input_vars
  [DecidableEq χ] [PCM T]
  {params : Vector χ n}
  {args : Vector V n}
  {tok : T} :
    VarMap.fromList
      (((params.map .inl).push (.inr 0)).zip
        ((args.map .inl).push (.inr tok))).toList =
    VarMap.disjointUnion (VarMap.fromList (params.zip args).toList) (PermCtx.init tok).perms
  := sorry

theorem sim_type_check_input
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : LawfulPCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  (hsim : SimRel ioSpec s₁ s₂)
  (hcont : s₁.cont = .init)
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard Config.DisjointTokens
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, hinit, _⟩ := hsim
  cases hstep with
  | step_ret hexpr | step_tail hexpr
  | step_op hexpr | step_br hexpr => simp [hcont] at hexpr
  | step_init =>
  rename Vector V m => args
  have hcont₂ := hinit hcont
  simp [Fn.semantics, Semantics.guard, Semantics.guardState, Semantics.guardLabel, Config.init]
  have hstep₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ (.input args) _ :=
    guard_single
      (.step_init
        (args := (args.map .inl).push (.inr ioSpec.pre))
        hcont₂)
      hdisj
      (by exact var_map_init_disjoint_tokens)
      (by
        apply OpSpec.Guard.spec_input (tok := ioSpec.pre)
        simp [SimpleIOSpec.toIOSpec]
        apply pcm.eq_refl)
  exact ⟨_, .single hstep₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · exact var_map_init_disjoint_tokens
      · simp
      · simp
        exists PermCtx.init ioSpec.pre
        and_intros
        · simp [hwt_fn.2]
        · simp [hwt_fn.1]
          apply sim_type_check_input_vars
  ⟩

theorem sim_type_check_ret
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : LawfulPCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  (hsim : SimRel ioSpec s₁ s₂)
  (hret : s₁.cont = .expr (.ret vars))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard Config.DisjointTokens
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_tail hexpr
  | step_op hexpr | step_br hexpr => simp [hret] at hexpr
  | step_ret hexpr hget_vars =>
  rename_i retVals vars
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_ret k hacq hins =>
  rename Vector T k => toks
  rename Vector ℕ k => tokIds
  rename Vector ℕ 2 => joined
  rename T => rem
  have ⟨hacq₁, hacq₂, hacq₃⟩ := hacq
  -- Join required permissions
  have hstep₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ _ _ :=
    guard_single
      (e' := .τ)
      (.step_op (outputVals := #v[.inr ioSpec.post, .inr rem])
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_vars_right hacq₂))
      hdisj
      (by
        -- TODO: remove tokens and add new tokens
        simp
        sorry)
      (.spec_join (by rfl) (by rfl) hacq₃)
  -- Run the actual return expression
  have hsteps₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ (.output retVals) _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_single
      (.step_ret (retVals := (retVals.map .inl).push (.inr ioSpec.post))
        (by rfl)
        (by
          simp
          -- TODO: some var map manipulation
          sorry))
      (by
        simp
        -- TODO: remove tokens and add new tokens
        sorry)
      (by
        simp [VarMap.DisjointTokens])
      (by
        apply OpSpec.Guard.spec_output
        apply pcm.eq_refl))
  simp at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp [VarMap.DisjointTokens]
      · simp
      · simp
  ⟩

theorem sim_type_check_tail
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : LawfulPCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  (hsim : SimRel ioSpec s₁ s₂)
  (htail : s₁.cont = .expr (.tail vars))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard Config.DisjointTokens
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_ret hexpr
  | step_op hexpr | step_br hexpr => simp [htail] at hexpr
  | step_tail hexpr hget_vars =>
  rename_i tailArgs vars
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_tail k hacq hins =>
  rename Vector T k => toks
  rename Vector ℕ k => tokIds
  rename Vector ℕ 2 => joined
  rename T => rem
  have ⟨hacq₁, hacq₂, hacq₃⟩ := hacq
  -- Join required permissions
  have hstep₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ _ _ :=
    guard_single
      (e' := .τ)
      (.step_op (outputVals := #v[.inr ioSpec.pre, .inr rem])
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_vars_right hacq₂))
      hdisj
      (by
        -- TODO: remove tokens and add new tokens
        simp
        sorry)
      (.spec_join (by rfl) (by rfl) hacq₃)
  -- Run the actual return expression
  have hsteps₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ .τ _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_single
      (.step_tail (tailArgs := (tailArgs.map .inl).push (.inr ioSpec.pre))
        (by rfl)
        (by
          simp
          -- TODO: some var map manipulation
          sorry))
      (by
        simp
        -- TODO: remove tokens and add new tokens
        sorry)
      (by
        sorry)
      .spec_tau)
  simp at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp
        sorry
      · simp
      · simp
        exists PermCtx.init ioSpec.pre
        and_intros
        · simp [hwt_fn.2]
        · simp [hwt_fn.1]
          apply sim_type_check_input_vars
  ⟩

theorem sim_type_check_op
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : LawfulPCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  {bind cont' args}
  (hsim : SimRel ioSpec s₁ s₂)
  (hret : s₁.cont = .expr (.op op args bind cont'))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard Config.DisjointTokens
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_tail hexpr
  | step_ret hexpr | step_br hexpr => simp [hret] at hexpr
  | step_op hexpr hget_vars =>
  rename_i op inputVals outputVals args bind cont
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_op k hacq hremove hins hwt' =>
  rename T => rem
  have ⟨hacq₁, hacq₂, hacq₃⟩ := hacq
  -- Join permissions
  have hstep₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ .τ _ :=
    guard_single
      (.step_op (outputVals := #v[.inr (opSpec.pre op), .inr rem])
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_vars_right hacq₂))
      hdisj
      (by
        -- TODO: remove tokens and add new tokens
        simp
        sorry)
      (.spec_join (by rfl) (by rfl) hacq₃)
  replace ⟨s₂', hstep₂, hs₂'⟩ := exists_eq_right.mpr hstep₂
  have hstep₂' :
    fn'.semantics.lts.Step s₂' (.yield (.op _) _ _) _
    := .step_op
        (inputVals := (inputVals.map Sum.inl).push (.inr (opSpec.pre op)))
        (outputVals := (outputVals.map Sum.inl).push (.inr (opSpec.post op)))
        (by simp only [hs₂']; rfl)
        (by
          -- TODO: var map manipulation
          simp [hs₂']
          sorry)
  have hsteps₂ :
    (fn'.semantics.guard _
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ (.yield op inputVals outputVals) _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_single
      hstep₂'
      (by
        simp [hs₂']
        -- TODO: remove tokens and add new tokens
        sorry)
      (by
        simp [hs₂']
        sorry)
      (by
        apply OpSpec.Guard.spec_yield
          (tok₁ := opSpec.pre op)
          (tok₂ := opSpec.post op)
        · apply pcm.eq_refl
        · apply pcm.eq_refl))
  simp [hs₂'] at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp
        sorry
      · simp
      · simp
        constructor
        and_intros;
        -- exact hwt'
        all_goals sorry
  ⟩

theorem sim_type_check_br
  [Arity Op]
  [InterpConsts V]
  [PCM T] [pcm : LawfulPCM T]
  [DecidableEq χ]
  [DecidableLE T]
  {opSpec : SimpleOpSpec Op T}
  {ioSpec : SimpleIOSpec T}
  {fn : Fn Op χ V m n}
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  {s₁ s₁' : Config Op χ V m n}
  {s₂ : Config (WithSpec Op (opSpec.toOpSpec V)) (TypedName χ) (V ⊕ T) (m + 1) (n + 1)}
  {l : Label Op V m n}
  {cond left right}
  (hsim : SimRel ioSpec s₁ s₂)
  (hret : s₁.cont = .expr (.br cond left right))
  (hstep : fn.semantics.lts.Step s₁ l s₁') :
    ∃ s₂',
      (fn'.semantics.guard Config.DisjointTokens
        ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.WeakStep
        .τ s₂ l s₂' ∧
      SimRel ioSpec s₁' s₂'
  := by
  have ⟨hwt_fn, hdisj, _, hcont⟩ := hsim
  cases hstep with
  | step_init hexpr | step_tail hexpr
  | step_ret hexpr | step_op hexpr => simp [hret] at hexpr
  | step_br hexpr hget_cond hcond_bool =>
  have ⟨ctx, expr₂, hcont₂, hwt, hvars⟩ := hcont _ hexpr
  cases hwt with | wpt_br hwt₁ hwt₂ =>
  have hstep₂ :
    (fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))).lts.Step
      s₂ .τ _ :=
    guard_single
      (.step_br
        hcont₂
        (by
          simp [hvars]
          apply var_map_disjoint_union_get_var_left hget_cond)
        hcond_bool)
      hdisj
      (by
        -- TODO: remove a variable
        simp
        sorry)
      .spec_tau
  exact ⟨_, .single hstep₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp
        sorry
      · simp
      · simp
        exists ctx
        constructor
        · split
          · exact hwt₁
          · exact hwt₂
        · sorry
  ⟩

/--
Type soundness theorem formulated as a simulation:
if the untyped `Fn` can execute without error, then
the typed version can also execute with the same trace
while keeping the ghost tokens disjoint, i.e., progress
is simulation and preservation is the `DisjointTokens`
invariant on the states.

Need to use weak simulation here due to `join` being
interpreted as silent steps.
-/
theorem sim_type_check
  {V T : Type u} -- TODO: relax this constraint
  [Arity Op]
  [InterpConsts V]
  [PCM T] [LawfulPCM T]
  [DecidableEq χ]
  [DecidableLE T]
  (opSpec : SimpleOpSpec Op T)
  (ioSpec : SimpleIOSpec T)
  (fn : Fn Op χ V m n)
  {fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n}
  (hwf : fn.AffineVar)
  (hwt : fn.WellPermTyped ioSpec fn') :
  fn.semantics ≲
    fn'.semantics.guard Config.DisjointTokens
      ((opSpec.toOpSpec V).Guard (ioSpec.toIOSpec m n))
  := by
  apply Lts.Similarity.intro (SimRel ioSpec)
  constructor
  · apply sim_type_check_init hwt
  · intros s₁ s₂ l s₁' hsim hstep
    cases h₁ : s₁.cont with
    | init => exact sim_type_check_input hsim h₁ hstep
    | expr expr =>
      cases h₂ : expr <;> simp [h₂] at h₁
      case ret => exact sim_type_check_ret hsim h₁ hstep
      case tail => exact sim_type_check_tail hsim h₁ hstep
      case op => exact sim_type_check_op hsim h₁ hstep
      case br => exact sim_type_check_br hsim h₁ hstep

end Wavelet.Seq
