import Mathlib.Control.ULiftable
import Mathlib.Logic.Basic

import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Dataflow.IndexedStep
import Wavelet.Compile

namespace Wavelet.Semantics

def InrDisjointTokens
  [PCM T]
  (v₁ v₂ : V ⊕ T) : Prop :=
  ∀ {t₁ t₂},
    v₁ = .inr t₁ →
    v₂ = .inr t₂ →
    t₁ ⊥ t₂

def EqModGhost : V ⊕ T → V ⊕ T → Prop
  | .inl v₁, .inl v₂ => v₁ = v₂
  | .inr _, .inr _ => True
  | _, _ => False

instance : IsRefl (V ⊕ T) EqModGhost where
  refl v := by cases v <;> simp [EqModGhost]

instance : IsSymm (V ⊕ T) EqModGhost where
  symm v := by cases v <;> simp [EqModGhost]

instance : IsTrans (V ⊕ T) EqModGhost where
  trans v := by cases v <;> simp [EqModGhost]

/-- Map permission tokens in the spec through a PCM map. -/
def OpSpec.mapTokens
  [Arity Op]
  (opSpec : OpSpec Op V T₁)
  (hom : T₁ → T₂) : OpSpec Op V T₂ := {
    pre op inputs := hom (opSpec.pre op inputs),
    post op inputs outputs := hom (opSpec.post op inputs outputs),
  }

def IOSpec.mapTokens
  (ioSpec : IOSpec V T₁ m n)
  (hom : T₁ → T₂) : IOSpec V T₂ m n := {
    pre vals := hom (ioSpec.pre vals),
    post vals := hom (ioSpec.post vals),
  }

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

def VarMap.DisjointTokens [PCM T]
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
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Expr (WithSpec Op opSpec) χ (m + 1) (n + 1)

abbrev FnWithSpec
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Fn (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics

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
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

abbrev ConfigWithSpec
  [Arity Op] (opSpec : Semantics.OpSpec Op V T) χ m n
  := Config (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

def AsyncOp.mapValues
  (f : V₁ → V₂) : AsyncOp V₁ → AsyncOp V₂
  | .switch n => .switch n
  | .steer flavor n => .steer flavor n
  | .merge state n => .merge state n
  | .forward n => .forward n
  | .fork n => .fork n
  | .const c n => .const (f c) n
  | .forwardc n m consts => .forwardc n m (consts.map f)
  | .sink n => .sink n

def AtomicProc.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂) :
  AtomicProc (WithSpec Op opSpec) χ (V ⊕ T₁) → AtomicProc (WithSpec Op (opSpec.mapTokens hom)) χ (V ⊕ T₂)
  | .op (.op o) inputs outputs => .op (.op o) inputs outputs
  | .op (.join k l req) inputs outputs => .op (.join k l (hom ∘ req)) inputs outputs
  | .async o inputs outputs =>
    .async (o.mapValues mapValue) inputs outputs
  where
    mapValue : V ⊕ T₁ → V ⊕ T₂
      | .inl v => .inl v
      | .inr t => .inr (hom t)

def AtomicProcs.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂)
  (aps : AtomicProcs (WithSpec Op opSpec) χ (V ⊕ T₁)) :
    AtomicProcs (WithSpec Op (opSpec.mapTokens hom)) χ (V ⊕ T₂)
  := aps.map (.mapTokens hom)

/-- Map the tokens through a PCM map. Note that on a well-formed
process, this should not change anything, since we should not have
token constants in the processes. -/
def Proc.mapTokens
  [Arity Op]
  {opSpec : OpSpec Op V T₁}
  (hom : T₁ → T₂)
  (proc : ProcWithSpec opSpec χ m n) :
    ProcWithSpec (OpSpec.mapTokens opSpec hom) χ m n
  := {
    inputs := proc.inputs,
    outputs := proc.outputs,
    atoms := proc.atoms.mapTokens hom,
  }

/-- Converts any guard on normal labels to indexed labels. -/
inductive IndexedGuard (P : E → E' → Prop) : Nat × E → Nat × E' → Prop where
  | idx_guard : P l l' → IndexedGuard P (i, l) (i, l')

/- Some abbreviations for some proc related LTS. -/

abbrev Config.GuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := (Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.Guard ioSpec)

abbrev Config.TrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  := (Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.TrivGuard (m := m) (n := n))

abbrev Config.InterpGuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := ((Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.Guard ioSpec)).InterpStep
    opInterp.lts

abbrev Config.InterpTrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  := ((Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.TrivGuard (m := m) (n := n))).InterpStep
    opInterp.lts

abbrev Config.IdxGuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := (Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.Guard ioSpec))

abbrev Config.IdxTrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  := (Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.TrivGuard (m := m) (n := n)))

abbrev Config.IdxInterpGuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := ((Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.Guard ioSpec))).IndexedInterpStep
    opInterp.lts

abbrev Config.IdxInterpTrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  := ((Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.TrivGuard (m := m) (n := n)))).IndexedInterpStep
    opInterp.lts

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow

/--
`Config.DisjointTokens` is a state invariant of a guarded `Proc` semantics.

TODO: this requires the `opSpec` to be frame preserving.
-/
theorem proc_guard_inv_disj
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n) :
    (proc.semantics.guard (opSpec.Guard ioSpec)).IsInvariant
      Config.DisjointTokens
  := by
  apply Lts.IsInvariantAt.by_induction
  · simp [Dataflow.Config.init, Semantics.guard,
      Proc.semantics, Config.Pairwise]
  · intros s s' l hinv hstep
    sorry

/--
`Config.DisjointTokens` is a state invariant of a guarded `Fn` semantics.

TODO: not quite true. should disallow multiple inputs transitions
-/
theorem fn_guard_inv_disj
  [Arity Op] [PCM T] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (fn : FnWithSpec opSpec χ m n) :
    (fn.semantics.guard (opSpec.Guard ioSpec)).IsInvariant
      Config.DisjointTokens
  := by
  apply Lts.IsInvariantAt.by_induction
  · simp [Seq.Config.init, Semantics.guard,
      Fn.semantics, VarMap.DisjointTokens]
  · intros s s' l hinv hstep
    sorry

/--
Without considering shared operator states, and when restricted
to silent/yield labels, a well-formed `Proc` has a strongly
confluent (and thus confluent) semantics, modulo a given
equivalence relation on values to capture certain non-determinism
in the operator semantics.
-/
theorem proc_indexed_strong_confl_at_mod
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (EqV : V → V → Prop) [IsRefl V EqV]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.IndexedStep.StronglyConfluentAtMod
      (λ (i, l) (i', l') =>
        i = i' → Label.IsYieldOrSilentAndDetMod EqV l l')
      (Config.EqMod EqV)
      (λ (i, l) (i', l') => i = i' ∧ Label.EqMod EqV l l')
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases l₁ with ⟨i, l₁⟩
  rcases l₂ with ⟨j, l₂⟩
  -- have ⟨hlabel₁, hlabel₂, hyield_det⟩ := hcompat
  have ⟨_, _, ⟨haff_nodup, haff_disj⟩, _⟩ := haff
  by_cases hij : i = j
  · left
    subst hij
    simp at hcompat
    have := Config.IndexedStep.unique_index_mod (EqV := EqV) hstep₁ hstep₂ hcompat
    simp
    exact this
  · -- Keep some acronyms so that they don't get expanded
    generalize hs₁' : s₁' = s₁''
    generalize hs₂' : s₂' = s₂''
    cases hstep₁ <;> cases hstep₂
    -- Commute two `step_op`s
    case neg.step_op.step_op =>
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hpop₁ hi hget_i
        op₂ inputs₂ outputs₂ inputVals₂ outputVals₂ chans₂' hpop₂ hj hget_j
      right
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj ⟨i, hi⟩ ⟨j, hj⟩ (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_op
          (outputVals := outputVals₂)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁']; exact hget_j)
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by simp [← hs₂']; exact hi)
          (by simp [← hs₂']; exact hget_i)
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute `step_op` and `step_async`
    case neg.step_op.step_async =>
      right
      rename_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hpop₁ hi hget_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' hinterp₂ hpop₂ hj hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs
      replace hdisj_outputs := List.disjoint_of_subset_right
        (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁']; exact hget_j)
          hinterp₂
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by simp [← hs₂']; exact hi)
          (by simp [← hs₂', Ne.symm hij]; exact hget_i)
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute `step_async` and `step_op`
    case neg.step_async.step_op =>
      right
      rename_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' hinterp₂ hpop₂ hi hget_i
        op₁ inputs₁ outputs₁ inputVals₁ outputVals₁ chans₁' hpop₁ hj hget_j
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hij])
      simp [hget_i, hget_j, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      replace hdisj_inputs := List.disjoint_of_subset_right
        (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs.symm
      replace hdisj_outputs := List.disjoint_of_subset_right
        (async_op_interp_output_sublist hinterp₂).subset hdisj_outputs.symm
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_async (i := i)
          (by simp [← hs₂']; exact hi)
          (by simp [← hs₂']; exact hget_i)
          hinterp₂
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_op (outputVals := outputVals₁)
          (by simp [← hs₁']; exact hj)
          (by simp [← hs₁', hij]; exact hget_j)
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₂'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁', hstep₂', by simp [IsRefl.refl]⟩
    -- Commute two `step_async`s
    case neg.step_async.step_async =>
      right
      rename_i
        _ _ aop₁ aop₁' allInputs₁ allOutputs₁
        inputs₁ inputVals₁ outputs₁ outputVals₁ chans₁' hinterp₁ hpop₁ hi hget_i
        _ _ aop₂ aop₂' allInputs₂ allOutputs₂
        inputs₂ inputVals₂ outputs₂ outputVals₂ chans₂' hinterp₂ hpop₂ hj hget_j
      -- Firing two different async ops
      have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj
        ⟨i, hi⟩ ⟨j, hj⟩
        (by simp [hij])
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
      have hstep₁' : Config.IndexedStep s₁'' _ _ :=
        .step_async (i := j)
          (by simp [← hs₁', hj])
          (by simp [← hs₁', hij]; exact hget_j)
          hinterp₂
          (by simp [← hs₁']; exact pop_vals_push_vals_commute hpop₁₂)
      have hstep₂' : Config.IndexedStep s₂'' _ _ :=
        .step_async (i := i)
          (by simp [← hs₂', hi])
          (by simp [← hs₂', Ne.symm hij]; exact hget_i)
          hinterp₁
          (by simp [← hs₂']; exact pop_vals_push_vals_commute hpop₂₁)
      rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
      simp only [← hs₁'] at hstep₁' ⊢
      simp only [← hs₂'] at hstep₂' ⊢
      exact ⟨_, _, hstep₁',
        (by
          apply Lts.Step.eq_rhs hstep₂'
          rfl),
        (by
          rw [List.set_comm]
          · simp [IsRefl.refl]
          · exact hij)
      ⟩

theorem proc_indexed_strong_confl_at
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.IndexedStep.StronglyConfluentAt
      (λ (i, l) (i', l') => i = i' → Label.IsYieldOrSilentAndDet l l')
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have := proc_indexed_strong_confl_at_mod Eq haff hstep₁ hstep₂
    (by simp at hcompat ⊢; exact hcompat)
  simp at this
  cases this with
  | inl h =>
    left
    cases l₁; cases l₂
    simp at h
    simp [h]
  | inr h =>
    right
    exact h

/--
Similar to `proc_indexed_strong_confl_at_mod` but on the
main stepping relation.
-/
theorem proc_strong_confl_at_mod
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (EqV : V → V → Prop)
  [hrefl : IsRefl V EqV]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.Step.StronglyConfluentAtMod
      (Label.IsYieldOrSilentAndDetMod EqV)
      (Config.EqMod EqV)
      (Label.EqMod EqV)
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨i, hstep₁'⟩ := Config.IndexedStep.from_step_yield_or_tau
    hcompat.1 hstep₁
  have ⟨j, hstep₂'⟩ := Config.IndexedStep.from_step_yield_or_tau
    hcompat.2.1 hstep₂
  have := proc_indexed_strong_confl_at_mod
    EqV haff hstep₁' hstep₂'
    (by simp [hcompat])
  cases this with
  | inl h => simp [h]
  | inr h =>
    right
    have ⟨_, _, hstep₁'', hstep₂'', heq⟩ := h
    exact ⟨_, _,
      Config.IndexedStep.to_step_yield_or_tau hstep₁'',
      Config.IndexedStep.to_step_yield_or_tau hstep₂'',
      heq,
    ⟩

theorem proc_strong_confl_at
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {s : Dataflow.Config Op χ V m n}
  (haff : s.proc.AffineChan) :
    Config.Step.StronglyConfluentAt
      Label.IsYieldOrSilentAndDet
      s
  := by
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  have ⟨hcompat₁, hcompat₂, hcompat₃⟩ := hcompat
  have := proc_strong_confl_at_mod Eq haff hstep₁ hstep₂
    (by simp [hcompat])
  simp at this
  exact this

/--
Converts `StronglyConfluentAtMod` of the base LTS to the guarded LTS.
-/
theorem Lts.guard_strong_confl_at_mod
  {Guard : E → E' → Prop}
  {EqS : C → C → Prop}
  {EqL : E → E → Prop}
  {EqL' : E' → E' → Prop}
  {Compat : E → E → Prop}
  (lts : Lts C E)
  (c : C)
  (hguard_congr : ∀ {l₁ l₂ l₁' l₂'}, Guard l₁ l₁' → Guard l₂ l₂' → EqL l₁ l₂ → EqL' l₁' l₂')
  (hconfl : lts.StronglyConfluentAtMod Compat EqS EqL c) :
    (lts.GuardStep Guard).StronglyConfluentAtMod
      (λ l₁' l₂' => ∀ {l₁ l₂},
        Guard l₁ l₁' →
        Guard l₂ l₂' →
        Compat l₁ l₂)
      EqS EqL' c
  := by
  intros s₁' s₂' l₁' l₂' hstep₁ hstep₂ hcompat
  rcases hstep₁ with ⟨hguard₁', hstep₁⟩
  rcases hstep₂ with ⟨hguard₂', hstep₂⟩
  have hcompat' := hcompat hguard₁' hguard₂'
  cases hconfl hstep₁ hstep₂ hcompat' with
  | inl heq =>
    left
    simp [heq.2, hguard_congr hguard₁' hguard₂' heq.1]
  | inr h =>
    right
    have ⟨s₁'', s₂'', hstep₁', hstep₂', heq⟩ := h
    exists s₁'', s₂''
    and_intros
    · exact ⟨hguard₂', hstep₁'⟩
    · exact ⟨hguard₁', hstep₂'⟩
    · exact heq

/--
Converts `StronglyConfluentAt` of the base LTS to the guarded LTS.
-/
theorem Lts.guard_strong_confl_at
  {Guard : E → E' → Prop}
  {Compat : E → E → Prop}
  (lts : Lts C E)
  (c : C)
  (hguard_congr : ∀ {l₁ l₂ l₁' l₂'},
    Guard l₁ l₁' → Guard l₂ l₂' → l₁ = l₂ → l₁' = l₂')
  (hconfl : lts.StronglyConfluentAt Compat c) :
    (lts.GuardStep Guard).StronglyConfluentAt
      (λ l₁' l₂' => ∀ {l₁ l₂},
        Guard l₁ l₁' →
        Guard l₂ l₂' →
        Compat l₁ l₂)
      c
  := by
  intros s₁' s₂' l₁' l₂' hstep₁ hstep₂ hcompat
  rcases hstep₁ with ⟨hguard₁', hstep₁⟩
  rcases hstep₂ with ⟨hguard₂', hstep₂⟩
  have hcompat' := hcompat hguard₁' hguard₂'
  cases hconfl hstep₁ hstep₂ hcompat' with
  | inl heq =>
    left
    simp [heq.2, hguard_congr hguard₁' hguard₂' heq.1]
  | inr h =>
    right
    have ⟨s', hstep₁', hstep₂'⟩ := h
    exists s'
    constructor
    · exact ⟨hguard₂', hstep₁'⟩
    · exact ⟨hguard₁', hstep₂'⟩

/-- Equal labels translate to equal labels through `OpSpec.Guard`. -/
theorem congr_spec_guard
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  {l₁' l₂' : Label Op V m n}
  (hguard₁ : opSpec.Guard ioSpec l₁ l₁')
  (hguard₂ : opSpec.Guard ioSpec l₂ l₂')
  (heq : l₁ = l₂) : l₁' = l₂' := by
  subst heq
  cases l₁ with
  | yield op inputs outputs =>
    cases op with
    | op op =>
      cases hguard₁
      rename_i inputs₁ outputs₁
      generalize hinputs₁' :
        (Vector.map Sum.inl inputs₁).push (Sum.inr (opSpec.pre op inputs₁)) = inputs₁'
      generalize houtputs₁' :
        (Vector.map Sum.inl outputs₁).push (Sum.inr (opSpec.post op inputs₁ outputs₁)) = outputs₁'
      rw [hinputs₁', houtputs₁'] at hguard₂
      cases hguard₂
      rename_i inputs₂ outputs₂
      simp [Vector.push_eq_push] at hinputs₁' houtputs₁'
      have heq₁ := Vector.inj_map (by simp [Function.Injective]) hinputs₁'.2
      have heq₂ := Vector.inj_map (by simp [Function.Injective]) houtputs₁'.2
      simp [heq₁, heq₂]
    | join k l req =>
      cases hguard₁ with | spec_join h₁ h₂ =>
      rename_i rem₁ toks₁ vals₁
      generalize h :
        (Vector.map Sum.inr rem₁ : Vector (V ⊕ T) _) ++
          (Vector.map Sum.inl toks₁ : Vector (V ⊕ T) _) = x
      rw [h] at hguard₂
      cases hguard₂
      rfl
  | input vals =>
    cases hguard₁ with | spec_input =>
    rename_i vals₁
    generalize h :
      (Vector.map Sum.inl vals₁).push (Sum.inr (ioSpec.pre vals₁)) = x
    rw [h] at hguard₂
    cases hguard₂
    simp [Vector.push_eq_push] at h
    have heq := Vector.inj_map (by simp [Function.Injective]) h.2
    simp [heq]
  | output vals =>
    cases hguard₁ with | spec_output =>
    rename_i vals₁
    generalize h :
      (Vector.map Sum.inl vals₁).push (Sum.inr (ioSpec.post vals₁)) = x
    rw [h] at hguard₂
    cases hguard₂
    simp [Vector.push_eq_push] at h
    have heq := Vector.inj_map (by simp [Function.Injective]) h.2
    simp [heq]
  | τ =>
    cases hguard₁
    cases hguard₂
    rfl

/-- Similar to `congr_spec_guard` but for `OpSpec.TrivGuard`. -/
theorem congr_triv_guard
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  {l₁' l₂' : Label Op V m n}
  (hguard₁ : opSpec.TrivGuard l₁ l₁')
  (hguard₂ : opSpec.TrivGuard l₂ l₂')
  (heq : Label.EqMod EqModGhost l₁ l₂) : l₁' = l₂' := by
  cases l₁ <;> cases l₂
    <;> cases hguard₁
    <;> cases hguard₂
    <;> simp [Label.EqMod] at heq
  any_goals rfl
  case yield.yield.triv_yield.triv_yield =>
    have ⟨h₁, heq₂, heq₃⟩ := heq
    subst h₁
    replace ⟨heq₂, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq₂
    replace ⟨heq₃, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq₃
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq₂
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq₃
    simp [heq₂, heq₃]
  case input.input.triv_input.triv_input =>
    replace ⟨heq, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq
    simp [heq]
  case output.output.triv_output.triv_output =>
    replace ⟨heq, _⟩ := Vector.forall₂_push_toList_to_forall₂ heq
    simp [Vector.toList_map, EqModGhost, Vector.toList_inj] at heq
    simp [heq]

/-- If the label pair generated by a guarded semantics
satisfies `Label.IsYieldOrSilentAndDet`, then the original
unchecked label must satisfy `Label.IsYieldOrSilentAndDet EqModGhost` -/
theorem invert_compat_spec_guard
  [Arity Op] [PCM T] [PCM.Cancellative T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁' l₂' : Label Op V m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  (hguard₁ : opSpec.Guard ioSpec l₁ l₁')
  (hguard₂ : opSpec.Guard ioSpec l₂ l₂')
  (hcompat : Label.IsYieldOrSilentAndDet l₁' l₂') :
    Label.IsYieldOrSilentAndDet l₁ l₂
  := by
  simp [Label.IsYieldOrSilentAndDet, Label.Deterministic]
  cases hguard₁ <;> cases hguard₂ <;> simp
  any_goals
    simp [Label.IsYieldOrSilentAndDet] at hcompat
  case spec_join.spec_join =>
    rename_i
      k₁ l₁ req₁ rem₁ toks₁ vals₁ outputs₁ houtputs₁₀ houtputs₁₁ hsum₁
      k₂ l₂ req₂ rem₂ toks₂ vals₂ outputs₂ houtputs₂₀ houtputs₂₁ hsum₂
    intros op inputs outputs₁' outputs₂' hop₁ hinputs₁' houtputs₁' hop₂ hinputs₂' houtputs₂'
    cases op <;> simp at hop₁
    have ⟨h₁, h₂, h₃⟩ := hop₁
    subst h₁; subst h₂; subst h₃
    simp at hop₂
    have ⟨h₁, h₂, h₃⟩ := hop₂
    subst h₁; subst h₂; subst h₃
    simp at hinputs₁'
    simp [← hinputs₁'] at hinputs₂'
    have ⟨h₁, h₂⟩ := Vector.append_inj hinputs₂'
    replace h₁ := Vector.inj_map (by simp [Function.Injective]) h₁
    replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂
    subst h₁; subst h₂
    have heq_rem : rem₁ = rem₂ := by
      simp [← hsum₂] at hsum₁
      exact PCM.Cancellative.cancel_left hsum₁
    subst heq_rem
    simp at houtputs₁' houtputs₂'
    simp [← houtputs₁', ← houtputs₂']
    apply Vector.ext
    intros i hi
    match h : i with
    | 0 => simp [houtputs₁₀, houtputs₂₀]
    | 1 => simp [houtputs₁₁, houtputs₂₁]
  case spec_yield.spec_yield =>
    rename_i
      op₁ inputs₁ outputs₁
      op₂ inputs₂ outputs₂
    intros op inputs outputs₁' outputs₂'
      hop₁ hinputs₁' houtputs₁'
      hop₂ hinputs₂' houtputs₂'
    cases op <;> simp at hop₁
    subst hop₁
    simp at hop₂
    subst hop₂
    simp only [heq_eq_eq] at *
    simp [← hinputs₁', Vector.push_eq_push] at hinputs₂'
    have heq_inputs := Vector.inj_map (by simp [Function.Injective]) hinputs₂'.2
    subst heq_inputs
    simp [← houtputs₁', ← houtputs₂', Vector.push_eq_push]
    simp [Label.Deterministic] at hcompat
    have heq_outputs : outputs₁ = outputs₂ := by
      apply hcompat
      any_goals rfl
    simp [heq_outputs]
  all_goals
    intros op
    cases op <;> simp

/-- Similar to `invert_compat_triv_guard` but for `OpSpec.TrivGuard`. -/
theorem invert_compat_triv_guard
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {l₁' l₂' : Label Op V m n}
  {l₁ l₂ : Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)}
  (hguard₁ : opSpec.TrivGuard l₁ l₁')
  (hguard₂ : opSpec.TrivGuard l₂ l₂')
  (hcompat : Label.IsYieldOrSilentAndDet l₁' l₂') :
    Label.IsYieldOrSilentAndDetMod EqModGhost l₁ l₂
  := by
  cases l₁ <;> cases l₂
    <;> cases hguard₁
    <;> cases hguard₂
    <;> simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at hcompat
    <;> simp [Label.IsYieldOrSilentAndDetMod, Label.DeterministicMod]
  any_goals
    intros op
    cases op <;> simp
  case yield.yield.triv_yield.triv_yield.op =>
    rename_i
      op₁ inputs₁ outputs₁ tok₁₁ tok₁₂
      op₂ inputs₂ outputs₂ tok₂₁ tok₂₂ _
    intros inputs' outputs₁' outputs₂'
      hop₁ hinputs₁' houtputs₁'
      hop₂ hinputs₂' houtputs₂'
    subst hop₁; subst hop₂
    have heq_inputs : inputs₁ = inputs₂ := by
      simp at hinputs₁' hinputs₂'
      simp [← hinputs₁', Vector.push_eq_push] at hinputs₂'
      have heq_inputs := Vector.inj_map (by simp [Function.Injective]) hinputs₂'.2
      simp [heq_inputs]
    subst heq_inputs
    have heq_outputs : outputs₁ = outputs₂ := by
      apply hcompat
      any_goals rfl
    subst heq_outputs
    simp at houtputs₁' houtputs₂'
    simp [← houtputs₁', ← houtputs₂']
    apply Vector.forall₂_to_forall₂_push_toList
    · simp [EqModGhost]
    · simp [EqModGhost]
  case yield.yield.triv_join.triv_join.join =>
    intros
    rename_i houtputs₁ _ _ _ _ houtputs₂
    simp [← houtputs₁, ← houtputs₂, Vector.toList_map, EqModGhost]
    apply List.forall₂_iff_get.mpr
    simp

theorem proc_indexed_guard_spec_strong_confl_at
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n}
  (haff : s.proc.AffineChan) :
    (Config.IdxGuardStep opSpec ioSpec).StronglyConfluentAt
      (λ (i₁, l₁) (i₂, l₂) => i₁ = i₂ → Label.IsYieldOrSilentAndDet l₁ l₂)
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAt _ _ _ :=
    proc_indexed_strong_confl_at haff
  have hconfl_guard : Lts.StronglyConfluentAt _ _ _ :=
    Lts.guard_strong_confl_at
      (Guard := IndexedGuard (opSpec.Guard ioSpec))
      _ _ (λ hguard₁ hguard₂ heq => by
        have ⟨hguard₁⟩ := hguard₁
        have ⟨hguard₂⟩ := hguard₂
        have := congr_spec_guard hguard₁ hguard₂
        simp [heq] at this
        simp [heq, this]) hconfl_base
  apply Lts.strong_confl_at_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      IndexedGuard (opSpec.Guard ioSpec) l₁ l₁' →
      IndexedGuard (opSpec.Guard ioSpec) l₂ l₂' →
      l₁.1 = l₂.1 → Label.IsYieldOrSilentAndDet l₁.2 l₂.2)
  · intros
    rename_i hguard₁ hguard₂ heq
    have ⟨hguard₁⟩ := hguard₁
    have ⟨hguard₂⟩ := hguard₂
    apply invert_compat_spec_guard hguard₁ hguard₂
    rename_i hcompat
    simp at hcompat
    exact hcompat heq
  · exact hconfl_guard

theorem proc_guard_spec_strong_confl_at
  [Arity Op] [PCM T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n}
  (haff : s.proc.AffineChan) :
    (Config.GuardStep opSpec ioSpec).StronglyConfluentAt
      Label.IsYieldOrSilentAndDet
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAt _ _ _ :=
    proc_strong_confl_at haff
  have hconfl_guard : Lts.StronglyConfluentAt _ _ _ :=
    Lts.guard_strong_confl_at
      (Guard := opSpec.Guard ioSpec)
      _ _ congr_spec_guard hconfl_base
  apply Lts.strong_confl_at_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      opSpec.Guard ioSpec l₁ l₁' →
      opSpec.Guard ioSpec l₂ l₂' →
      Label.IsYieldOrSilentAndDet l₁ l₂)
  · intros
    apply invert_compat_spec_guard
    all_goals assumption
  · exact hconfl_guard

theorem proc_indexed_guard_triv_strong_confl_at_mod
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  (s : ConfigWithSpec opSpec χ m n)
  (haff : s.proc.AffineChan) :
    (Config.IdxTrivStep opSpec).StronglyConfluentAtMod
      (λ (i, l) (i', l') =>
        i = i' → Label.IsYieldOrSilentAndDet l l')
      (Config.EqMod EqModGhost)
      Eq s
  := by
  have hconfl_base : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    proc_indexed_strong_confl_at_mod EqModGhost haff
  simp at hconfl_base
  have hconfl_guard : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    Lts.guard_strong_confl_at_mod
      (Guard := IndexedGuard opSpec.TrivGuard)
      (EqS := Config.EqMod EqModGhost)
      (EqL := λ (i, l) (i', l') => i = i' ∧ Label.EqMod EqModGhost l l')
      (EqL' := Eq)
      (Compat := λ (i, l) (i', l') => i = i' → Label.IsYieldOrSilentAndDetMod EqModGhost l l')
      (lts := Config.IndexedStep)
      (c := s)
      (by
        intros
        rename_i hguard₁ hguard₂ heq
        rcases hguard₁ with ⟨hguard₁⟩
        rcases hguard₂ with ⟨hguard₂⟩
        simp at heq
        simp [heq]
        apply congr_triv_guard hguard₁ hguard₂ heq.2)
      hconfl_base
  apply Lts.strong_confl_at_mod_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      (IndexedGuard opSpec.TrivGuard) l₁ l₁' →
      (IndexedGuard opSpec.TrivGuard) l₂ l₂' →
      l₁.1 = l₂.1 → Label.IsYieldOrSilentAndDetMod EqModGhost l₁.2 l₂.2)
  · intros l₁' l₂' hcompat
    cases l₁'
    cases l₂'
    intros _ _ hguard₁ hguard₂ heq
    rcases hguard₁ with ⟨hguard₁⟩
    rcases hguard₂ with ⟨hguard₂⟩
    simp at heq hcompat ⊢
    apply invert_compat_triv_guard hguard₁ hguard₂ (hcompat heq)
  · exact hconfl_guard

theorem proc_guard_triv_strong_confl_at_mod
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  (s : ConfigWithSpec opSpec χ m n)
  (haff : s.proc.AffineChan) :
    (Config.TrivStep opSpec).StronglyConfluentAtMod
      Label.IsYieldOrSilentAndDet
      (Config.EqMod EqModGhost)
      Eq
      s
  := by
  have hconfl_base : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    proc_strong_confl_at_mod EqModGhost haff
  have hconfl_guard : Lts.StronglyConfluentAtMod _ _ _ _ _ :=
    Lts.guard_strong_confl_at_mod
      (Guard := opSpec.TrivGuard)
      (EqS := Config.EqMod EqModGhost)
      (EqL := Label.EqMod EqModGhost)
      (EqL' := Eq)
      (Compat := Label.IsYieldOrSilentAndDetMod EqModGhost)
      Config.Step s
      congr_triv_guard
      hconfl_base
  apply Lts.strong_confl_at_mod_imp_compat
    (Compat₁ := λ l₁' l₂' => ∀ {l₁ l₂},
      opSpec.TrivGuard l₁ l₁' →
      opSpec.TrivGuard l₂ l₂' →
      Label.IsYieldOrSilentAndDetMod EqModGhost l₁ l₂)
  · intros
    apply invert_compat_triv_guard
    all_goals assumption
  · exact hconfl_guard

theorem proc_indexed_interp_strong_confl_at
  [Arity Op]
  [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n × opInterp.S}
  -- Confluent and deterministic operator interpretation
  (hconfl : OpSpec.Confluent opSpec opInterp)
  (hdet : opInterp.Deterministic)
  -- Some required state invariants
  (haff : s.1.proc.AffineChan)
  (hdisj : s.1.DisjointTokens) :
    (Config.IdxInterpGuardStep opSpec ioSpec).StronglyConfluentAt
      (λ (_, l₁) (_, l₂) => l₁.isSilent ∧ l₂.isSilent)
      s
  := by
  rcases s with ⟨s, t⟩
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases s₁' with ⟨s₁', t₁'⟩
  rcases s₂' with ⟨s₂', t₂'⟩
  rcases l₁ with ⟨i₁, l₁⟩
  rcases l₂ with ⟨i₂, l₂⟩
  cases hstep₁ <;> cases hstep₂ <;> simp at hcompat
  case step_tau.step_tau hstep₁ hstep₂ =>
    have := proc_indexed_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq =>
      left
      simp at heq
      simp [heq]
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t)
      exact ⟨
        .step_tau hstep₁',
        .step_tau hstep₂'
      ⟩
  case step_tau.step_yield hstep₁ _ _ _ hstep₂ hstep_op₂ =>
    have := proc_indexed_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₂')
      exact ⟨
        .step_yield hstep₁' hstep_op₂,
        .step_tau hstep₂',
      ⟩
  case step_yield.step_tau _ _ _ _ hstep₁ hstep_op₁ hstep₂ =>
    have := proc_indexed_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₁')
      exact ⟨
        .step_tau hstep₁',
        .step_yield hstep₂' hstep_op₁,
      ⟩
  case step_yield.step_yield
    op₁ inputVals₁ _ hstep₁ hstep_op₁
    op₂ inputVals₂ _ hstep₂ hstep_op₂ =>
    have hconfl_sem := proc_indexed_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by
        -- By `hdet`
        intros heq
        simp only [Label.IsYieldOrSilentAndDet, Label.Deterministic]
        and_intros
        · simp
        · simp
        · intros op inputVals outputVals₁ outputVals₂ heq_yield₁ heq_yield₂
          simp at heq_yield₁ heq_yield₂
          have ⟨heq_op₁, heq_inputs₁, heq_outputs₁⟩ := heq_yield₁
          have ⟨heq_op₂, heq_inputs₂, heq_outputs₂⟩ := heq_yield₂
          subst heq_op₁; subst heq_inputs₁; subst heq_outputs₁
          subst heq_op₂; subst heq_inputs₂; subst heq_outputs₂
          simp [hdet hstep_op₁ hstep_op₂])
    cases hconfl_sem with
    | inl heq =>
      left
      simp at heq
      have ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ := heq
      subst h₁; subst h₂; subst h₃; subst h₄; subst h₅
      simp [hdet hstep_op₁ hstep_op₂]
    | inr h =>
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      cases hguard₁
      cases hguard₂
      cases hstep₁ with | step_op _ hget₁ hpop₁ =>
      cases hstep₂ with | step_op _ hget₂ hpop₂ =>
      by_cases heq_ij : i₁ = i₂
      · -- Firing the same atom, so the result must be the same by `hdet`
        left
        subst heq_ij
        simp [hget₁] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp [hpop₁, Vector.push_eq_push] at hpop₂
        have ⟨⟨h₄, h₅⟩, h₆⟩ := hpop₂
        replace h₅ := Vector.inj_map (by simp [Function.Injective]) h₅
        subst h₅; subst h₆
        -- simp [h₄, htok₁', htok₂']
        have ⟨h₇, h₈⟩ := hdet hstep_op₁ hstep_op₂
        subst h₈
        constructor
        · rfl
        · simp [h₇]
      · right
        have ⟨t', hstep_op₁', hstep_op₂'⟩ := hconfl hstep_op₁ hstep_op₂
          (by
            -- Firing different atoms, so the tokens must be disjoint by `DisjointTokens`.
            simp [OpSpec.CompatLabels]
            have := haff.atom_inputs_disjoint
              ⟨i₁, by assumption⟩ ⟨i₂, by assumption⟩ (by simp [heq_ij])
            simp [hget₁, hget₂, AtomicProc.inputs] at this
            have := pop_vals_disj_preserves_pairwise hdisj this hpop₁ hpop₂
            apply this (.inr (opSpec.pre op₁ inputVals₁)) (.inr (opSpec.pre op₂ inputVals₂))
            all_goals simp)
        replace ⟨s', hstep₁', hstep₂'⟩ := h
        exists (s', t')
        exact ⟨
          .step_yield hstep₁' hstep_op₁',
          .step_yield hstep₂' hstep_op₂',
        ⟩

/--
Strong confluence of a `ProcWithSpec` when interpreted with
a sound and deterministic interpretation.

TODO: this is probably generalizable to a general confluent `Semantics`.
TODO: use `proc_indexed_interp_strong_confl_at` to prove this.
-/
theorem proc_interp_strong_confl_at
  [Arity Op]
  [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s : ConfigWithSpec opSpec χ m n × opInterp.S}
  -- Confluent and deterministic op interpretation
  (hconfl : OpSpec.Confluent opSpec opInterp)
  (hdet : opInterp.Deterministic)
  -- Some required state invariants
  (haff : s.1.proc.AffineChan)
  (hdisj : s.1.DisjointTokens) :
    (Config.InterpGuardStep opSpec ioSpec).StronglyConfluentAt
      (λ l₁ l₂ => l₁.isSilent ∧ l₂.isSilent)
      s
  := by
  rcases s with ⟨s, t⟩
  intros s₁' s₂' l₁ l₂ hstep₁ hstep₂ hcompat
  rcases s₁' with ⟨s₁', t₁'⟩
  rcases s₂' with ⟨s₂', t₂'⟩
  cases hstep₁ <;> cases hstep₂ <;> simp at hcompat
  case step_tau.step_tau hstep₁ hstep₂ =>
    have := proc_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp [heq]
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t)
      exact ⟨
        .step_tau hstep₁',
        .step_tau hstep₂'
      ⟩
  case step_tau.step_yield hstep₁ _ _ _ hstep₂ hstep_op₂ =>
    have := proc_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₂')
      exact ⟨
        .step_yield hstep₁' hstep_op₂,
        .step_tau hstep₂',
      ⟩
  case step_yield.step_tau _ _ _ _ hstep₁ hstep_op₁ hstep₂ =>
    have := proc_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by simp [Label.IsYieldOrSilentAndDet, Label.Deterministic])
    cases this with
    | inl heq => simp at heq
    | inr h =>
      right
      replace ⟨s', hstep₁', hstep₂'⟩ := h
      exists (s', t₁')
      exact ⟨
        .step_tau hstep₁',
        .step_yield hstep₂' hstep_op₁,
      ⟩
  case step_yield.step_yield
    op₁ inputVals₁ _ hstep₁ hstep_op₁
    op₂ inputVals₂ _ hstep₂ hstep_op₂ =>
    have hconfl_sem := proc_guard_spec_strong_confl_at haff hstep₁ hstep₂
      (by
        -- By `hdet`
        simp only [Label.IsYieldOrSilentAndDet, Label.Deterministic]
        and_intros
        · simp
        · simp
        · intros op inputVals outputVals₁ outputVals₂ heq_yield₁ heq_yield₂
          simp at heq_yield₁ heq_yield₂
          have ⟨heq_op₁, heq_inputs₁, heq_outputs₁⟩ := heq_yield₁
          have ⟨heq_op₂, heq_inputs₂, heq_outputs₂⟩ := heq_yield₂
          subst heq_op₁; subst heq_inputs₁; subst heq_outputs₁
          subst heq_op₂; subst heq_inputs₂; subst heq_outputs₂
          simp [hdet hstep_op₁ hstep_op₂])
    cases hconfl_sem with
    | inl heq =>
      left
      simp at heq
      have ⟨⟨h₁, h₂, h₃⟩, h₄⟩ := heq
      subst h₁; subst h₂; subst h₃
      simp [h₄, hdet hstep_op₁ hstep_op₂]
    | inr h =>
      cases hstep₁ with | step hguard₁ hstep₁ =>
      cases hstep₂ with | step hguard₂ hstep₂ =>
      cases hguard₁ with | spec_yield =>
      -- rename_i tok₁ tok₁'
      cases hguard₂ with | spec_yield =>
      -- rename_i tok₂ tok₂'
      cases hstep₁ with | step_op hmem₁ hpop₁ =>
      cases hstep₂ with | step_op hmem₂ hpop₂ =>
      have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
      have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem₂
      by_cases heq_ij : i = j
      · -- Firing the same atom, so the result must be the same by `hdet`
        left
        subst heq_ij
        simp [hget_i] at hget_j
        have ⟨h₁, h₂, h₃⟩ := hget_j
        subst h₁; subst h₂; subst h₃
        simp [hpop₁, Vector.push_eq_push] at hpop₂
        have ⟨⟨h₄, h₅⟩, h₆⟩ := hpop₂
        replace h₅ := Vector.inj_map (by simp [Function.Injective]) h₅
        subst h₅; subst h₆
        -- simp [h₄, htok₁', htok₂']
        have ⟨h₇, h₈⟩ := hdet hstep_op₁ hstep_op₂
        subst h₈
        constructor
        · rfl
        · simp [h₇]
      · right
        have ⟨t', hstep_op₁', hstep_op₂'⟩ := hconfl hstep_op₁ hstep_op₂
          (by
            -- Firing different atoms, so the tokens must be disjoint by `DisjointTokens`.
            simp [OpSpec.CompatLabels]
            -- apply PCM.eq_congr_disj htok₁ htok₂
            have := haff.atom_inputs_disjoint ⟨i, hi⟩ ⟨j, hj⟩ (by simp [heq_ij])
            simp [hget_i, hget_j, AtomicProc.inputs] at this
            have := pop_vals_disj_preserves_pairwise hdisj this hpop₁ hpop₂
            -- have := this (.inr _) (.inr _)
            apply this (.inr (opSpec.pre op₁ inputVals₁)) (.inr (opSpec.pre op₂ inputVals₂))
            all_goals simp)
        replace ⟨s', hstep₁', hstep₂'⟩ := h
        exists (s', t')
        exact ⟨
          .step_yield hstep₁' hstep_op₁',
          .step_yield hstep₂' hstep_op₂',
        ⟩

/--
Having a terminating trace in a confluent LTS means that
all other traces can go to the same final state.
-/
theorem strong_confl_final_confl_tau
  {lts : Lts C E} {c : C} {τ : E}
  {Compat : E → E → Prop}
  (hinv : lts.IsInvariantAt (lts.StronglyConfluentAt Compat) c)
  (htau : ∀ {l l'}, Compat l l' ↔ l = τ ∧ l' = τ)
  (hsteps₁ : lts.TauStar τ c c₁)
  (hterm : lts.IsFinalFor (· = τ) c₁)
  (hstep₂ : lts.Step c τ c₂) : lts.TauStar τ c₂ c₁
  := by
  induction hsteps₁
    using Lts.TauStar.reverse_induction
    generalizing c₂ with
  | refl =>
    exact False.elim (hterm (by rfl) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i c c'
    have ⟨hconfl', hinv'⟩ := hinv.unfold hstep₁
    have := hinv.base hstep₁ hstep₂ (by simp [htau])
    cases this with
    | inl heq => simp [← heq, htail₁]
    | inr h =>
      have ⟨c'', hstep₁', hstep₂'⟩ := h
      have := ih hinv' hstep₁'
      exact this.prepend hstep₂'

-- theorem proc_guarded_weak_normalization_confl
--   [Arity Op] [PCM T] [PCM.Lawful T]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {opSpec : OpSpec Op V T}
--   {opInterp : OpInterp Op V}
--   {ioSpec : IOSpec V T m n}
--   (proc : ProcWithSpec opSpec χ m n)
--   {s s₁ s₂ : proc.semantics.S × opInterp.S}
--   (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar .τ s s₁)
--   (hterm : proc.semantics.IsFinal s₁.1)
--   (hstep₂ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.Step s .τ s₂) :
--     ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar .τ s₂ s₁
--   := by
--   induction htrace₁
--     using Lts.TauStar.reverse_induction with
--   | refl =>
--     match hstep₂ with
--     | .step_tau hstep₂ =>
--       cases hstep₂ with | step _ hstep₂ =>
--       exact False.elim (hterm hstep₂)
--     | .step_yield hstep₂ _ =>
--       cases hstep₂ with | step _ hstep₂ =>
--       exact False.elim (hterm hstep₂)
--   | head hstep₁ htail₁ ih =>
--     rename_i s s'
--     apply ih
--     sorry

-- theorem proc_unguarded_step_congr_mod_ghost
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {opSpec : OpSpec Op V T}
--   {opInterp : OpInterp Op V}
--   (proc : ProcWithSpec opSpec χ m n)
--   {s₁ s₁' s₂ : proc.semantics.S × opInterp.S}
--   (hstep : ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.Step s₁ .τ s₂)
--   (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
--     ∃ s₂',
--       ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.Step s₁' .τ s₂' ∧
--       Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
--       s₂.2 = s₂'.2
--   := sorry

-- theorem proc_unguarded_steps_congr_mod_ghost
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {opSpec : OpSpec Op V T}
--   {opInterp : OpInterp Op V}
--   (proc : ProcWithSpec opSpec χ m n)
--   {s₁ s₁' s₂ : proc.semantics.S × opInterp.S}
--   (hstep : ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar .τ s₁ s₂)
--   (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
--     ∃ s₂',
--       ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar .τ s₁' s₂' ∧
--       Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
--       s₂.2 = s₂'.2
--   := by
--   induction hstep with
--   | refl =>
--     exists s₁'
--     constructor
--     · exact .refl
--     · exact heq
--   | tail pref tail ih =>
--     have ⟨s₂'', hpref', heq'⟩ := ih
--     have ⟨s₂', htau, heq⟩ := proc_unguarded_step_congr_mod_ghost proc tail heq'
--     exists s₂'
--     constructor
--     · exact .tail hpref' htau
--     · exact heq

theorem proc_indexed_guarded_step_unique_label
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₂) s₂)
  (hdet : Label.IsYieldOrSilentAndDet l₁ l₂) :
    l₁ = l₂
  := by
    cases hstep₁ with | step hguard₁ hstep₁
    cases hstep₂ with | step hguard₂ hstep₂
    cases hguard₁ with | _ hguard₁
    cases hguard₂ with | _ hguard₂
    case step.step.idx_guard.idx_guard =>
    cases hguard₁ <;> cases hguard₂
      <;> simp [Label.IsYieldOrSilentAndDet] at hdet
    case spec_yield.spec_yield =>
      have := Config.IndexedStep.unique_index hstep₁ hstep₂
        (by
          constructor; simp
          constructor; simp
          intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
          simp at hyield₁ hyield₂
          have ⟨h₁, h₂, h₃⟩ := hyield₁
          have ⟨h₁', h₂', h₃'⟩ := hyield₂
          simp [← h₁] at h₁'
          subst h₁'
          have := HEq.trans h₂ h₂'.symm
          simp [Vector.push_eq_push] at this
          replace this := Vector.inj_map (by simp [Function.Injective]) this.2
          subst this
          rename_i outputVals₁' _ outputVals₂'
          have : outputVals₁' = outputVals₂' := by
            symm
            apply hdet
            all_goals rfl
          subst this
          rw [← heq_eq_eq _ _]
          apply HEq.trans h₃.symm h₃')
      simp at this
      have ⟨⟨h₁, h₂, h₃⟩, _⟩ := this
      subst h₁
      simp [Vector.push_eq_push] at h₂
      replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂.2
      subst h₂
      simp [Vector.push_eq_push] at h₃
      replace h₃ := Vector.inj_map (by simp [Function.Injective]) h₃.2
      subst h₃
      rfl
    any_goals rfl
    any_goals
      have := Config.IndexedStep.unique_index hstep₁ hstep₂
      simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at this

-- theorem proc_indexed_unguarded_step_unique_label
--   [Arity Op] [PCM T]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {opSpec : OpSpec Op V T}
--   {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
--   {l₁ l₂ : Label Op V m n}
--   (hstep₁ : (Config.IdxTrivStep opSpec).Step s (i, l₁) s₁)
--   (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l₂) s₂)
--   (hdet : Label.IsYieldOrSilentAndDet l₁ l₂) :
--     l₁ = l₂
--   := by
--     cases hstep₁ with | step hguard₁ hstep₁
--     cases hstep₂ with | step hguard₂ hstep₂
--     cases hguard₁ with | _ hguard₁
--     cases hguard₂ with | _ hguard₂
--     case step.step.idx_guard.idx_guard =>
--     cases hguard₁ <;> cases hguard₂
--       <;> simp [Label.IsYieldOrSilentAndDet] at hdet
--     case triv_yield.triv_yield =>
--       have := Config.IndexedStep.unique_index hstep₁ hstep₂
--         (by
--           constructor; simp
--           constructor; simp
--           intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
--           simp at hyield₁ hyield₂
--           have ⟨h₁, h₂, h₃⟩ := hyield₁
--           have ⟨h₁', h₂', h₃'⟩ := hyield₂
--           simp [← h₁] at h₁'
--           subst h₁'
--           have := HEq.trans h₂ h₂'.symm
--           simp [Vector.push_eq_push] at this
--           replace this := Vector.inj_map (by simp [Function.Injective]) this.2
--           subst this
--           rename_i outputVals₁' _ outputVals₂'
--           stop
--           have : outputVals₁' = outputVals₂' := by
--             symm
--             apply hdet
--             all_goals rfl
--           subst this
--           rw [← heq_eq_eq _ _]
--           apply HEq.trans h₃.symm h₃')
--       simp at this
--       have ⟨⟨h₁, h₂, h₃⟩, _⟩ := this
--       subst h₁
--       simp [Vector.push_eq_push] at h₂
--       replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂.2
--       subst h₂
--       simp [Vector.push_eq_push] at h₃
--       replace h₃ := Vector.inj_map (by simp [Function.Injective]) h₃.2
--       subst h₃
--       rfl
--     any_goals rfl
--     any_goals
--       have := Config.IndexedStep.unique_index hstep₁ hstep₂
--       simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at this

-- theorem proc_indexed_guarded_step_unique_label_alt
--   [Arity Op] [PCM T]
--   [DecidableEq χ]
--   [InterpConsts V]
--   (opSpec : OpSpec Op V T)
--   (ioSpec : IOSpec V T m n)
--   {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
--   {l₁ l₂ : IndexedLabel Op V}
--   (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
--   (hstep₂ : (Config.IndexedStep.Guard (IndexedGuard (m := m) (n := n) opSpec.TrivGuard)).Step s (i, l₂) s₂)
--   (hdet : IndexedLabel.Deterministic l₁ l₂) :
--     l₁ = l₂
--   := by
--     cases hstep₁ with | step hguard₁ hstep₁
--     cases hstep₂ with | step hguard₂ hstep₂
--     cases hguard₁ <;> cases hguard₂
--     case step.step.guard_yield.guard_yield =>
--       sorry
--     any_goals rfl
--     any_goals
--       rename opSpec.Guard ioSpec _ _ => hguard
--       cases hguard
--       have := Config.IndexedStep.unique_index hstep₁ hstep₂
--       simp [IndexedLabel.Deterministic] at this

/-- Converts an indexed guarded step to a guarded step. -/
theorem proc_indexed_guarded_step_to_guarded_step
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s') :
    (Config.GuardStep opSpec ioSpec) s l s'
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> simp at hl
  case spec_yield =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .spec_yield this
  case spec_join h₁ h₂ h₃ =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step (.spec_join h₁ h₂ h₃) this
  case spec_tau =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .spec_tau this

/-- Converts a guarded step to an indexed guarded step. -/
theorem proc_guarded_step_to_indexed_guarded_step
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : (Config.GuardStep opSpec ioSpec) s l s') :
    ∃ i, (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s'
  := by
  cases hstep with | step hguard hstep
  cases hguard <;> simp at hl
  case step.spec_yield =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard .spec_yield) hstep'⟩
  case step.spec_join h₁ h₂ h₃ =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard (.spec_join h₁ h₂ h₃)) hstep'⟩
  case step.spec_tau =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, .step (.idx_guard .spec_tau) hstep'⟩

/-- Converts an indexed unguarded step to an unguarded step. -/
theorem proc_indexed_unguarded_step_to_unguarded_step
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : (Config.IdxTrivStep opSpec).Step s (i, l) s') :
    (Config.TrivStep opSpec) s l s'
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> simp at hl
  case triv_yield =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_yield this
  case triv_join =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_join this
  case triv_tau =>
    have := Config.IndexedStep.to_step_yield_or_tau hstep
    exact .step .triv_tau this

/-- Converts an unguarded step to an indexed unguarded step. -/
theorem proc_unguarded_step_to_indexed_unguarded_step
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hl : l.isYield ∨ l.isSilent)
  (hstep : (Config.TrivStep opSpec) s l s') :
    ∃ i, (Config.IdxTrivStep opSpec).Step s (i, l) s'
  := by
  cases hstep with | step hguard hstep
  cases hguard <;> simp at hl
  case step.triv_yield =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard .triv_yield) hstep'⟩
  case step.triv_join =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_yield hstep
    exact ⟨i, .step (.idx_guard .triv_join) hstep'⟩
  case step.triv_tau =>
    have ⟨i, hstep'⟩ := Config.IndexedStep.from_step_tau hstep
    exact ⟨i, .step (.idx_guard .triv_tau) hstep'⟩

theorem proc_indexed_guarded_step_label
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hstep : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s') :
    l.isYield ∨ l.isSilent
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> cases hstep <;> simp

theorem proc_indexed_unguarded_step_label
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hstep : (Config.IdxTrivStep opSpec).Step s (i, l) s') :
    l.isYield ∨ l.isSilent
  := by
  rcases hstep with ⟨⟨hguard⟩, hstep⟩
  cases hguard <;> cases hstep <;> simp

theorem proc_indexed_unguarded_step_same_label_kind
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ l₃ : Label Op V m n}
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s₁ (j, l₂) s₂)
  (hstep₂' : (Config.IdxTrivStep opSpec).Step s (j, l₃) s₁') :
    l₂.isYield ↔ l₃.isYield
  := by
    by_cases hij : i = j
    · subst hij
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      have hl := Config.IndexedStep.same_label_kind hstep₁ hstep₂ hstep₂'
      cases hstep₁ with | _ _ hget₁
        <;> cases hstep₂ with | _ _ hget₂
        <;> cases hstep₂' with | _ _ hget₂'
        <;> (simp at hget₂; try simp [hget₂] at hget₂')
        <;> cases hguard₁ <;> try cases hguard₂ <;> try cases hguard₂'
      any_goals simp at hl
      any_goals simp
      any_goals simp at hget₂'
    · rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      have hl := Config.IndexedStep.same_label_kind hstep₁ hstep₂ hstep₂'
      cases hstep₁ with | _ _ hget₁
        <;> cases hstep₂ with | _ _ hget₂
        <;> cases hstep₂' with | _ _ hget₂'
        <;> (simp [hij] at hget₂; simp [hget₂] at hget₂')
        <;> cases hguard₁ <;> try cases hguard₂ <;> try cases hguard₂'
      any_goals simp at hl
      any_goals simp
      any_goals simp at hget₂'

/--
If we can make two guarded steps, where the second operator can be already
run in the first step (even in a unguarded way), then we can turn that
unguarded step to a guarded step.

Base case of `proc_unguarded_to_guarded`.
-/
theorem proc_indexed_unguarded_to_guarded_single
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ : Label Op V m n}
  (haff : s.proc.AffineChan)
  (hstep₁ : (Config.IdxGuardStep opSpec ioSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxGuardStep opSpec ioSpec).Step s₁ (j, l₂) s₂)
  (hstep₂' : (Config.IdxTrivStep opSpec).Step s (j, l₂) s₁') :
    ∃ s₁'',
      (Config.IdxGuardStep opSpec ioSpec).Step s (j, l₂) s₁''
  := by
  have hl₁ := proc_indexed_guarded_step_label hstep₁
  have hl₂ := proc_indexed_guarded_step_label hstep₂
  by_cases hij : i = j
  · subst hij
    by_cases heq_label : l₁ = l₂
    · subst heq_label
      exact ⟨_, hstep₁⟩
    · cases hstep₁ with | step hguard₁ hstep₁
      cases hstep₂' with | step hguard₂ hstep₂'
      case neg.step.step =>
      cases hguard₁ with | _ hguard₁ =>
      cases hguard₂ with | _ hguard₂ =>
      cases hguard₁ <;> cases hguard₂ <;> simp at heq_label
      case idx_guard.idx_guard.spec_yield.triv_yield =>
        -- NOTE: allowing yield to be non-deterministic here
        rename_i op inputVals₂ outputVals₂ _
        cases hstep₁ with | step_op _ hget₁ hpop₁ =>
        rename_i inputs₁ outputs₁
        cases hstep₂' with | step_op hi hget₂ hpop₂ =>
        rename_i inputs₂ outputs₂
        simp [hget₂] at hget₁
        have ⟨h₁, h₂, h₃⟩ := hget₁
        subst h₁; subst h₂; subst h₃
        simp [hpop₁] at hpop₂
        have ⟨h₁, _⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁
        replace h₁ := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst h₁
        exact ⟨_,
          by
            apply Lts.GuardStep.step
            · apply IndexedGuard.idx_guard
              apply OpSpec.Guard.spec_yield
            · exact .step_op hi hget₂ hpop₁
        ⟩
      any_goals
        simp at hl₁ hl₂
      any_goals
        have := Config.IndexedStep.unique_index hstep₁ hstep₂'
        simp [Label.IsYieldOrSilentAndDet, Label.Deterministic] at this
  · case neg =>
    cases hstep₁ with | step hguard₁ hstep₁
    cases hstep₂ with | step hguard₂ hstep₂
    cases hstep₂' with | step hguard₂' hstep₂'
    rename_i l₁' l₂' l₃'
    rcases l₁' with ⟨i₁, l₁'⟩
    rcases l₂' with ⟨i₂, l₂'⟩
    rcases l₃' with ⟨i₃, l₃'⟩
    have : i = i₁ := by cases hguard₁; simp
    subst this
    have : j = i₂ := by cases hguard₂; simp
    subst this
    have : j = i₃ := by cases hguard₂'; simp
    subst this
    have hl := Config.IndexedStep.same_label_kind hstep₁ hstep₂ hstep₂'
    cases hstep₁ with
    | step_op _ hget₁ hpop₁ =>
      cases hstep₂ with
      | step_op _ hget₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
            <;> rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          all_goals
            simp at hl
            simp [hget₂'] at hget₂
          case spec_yield.triv_yield =>
            have ⟨h₁, h₂⟩ := hget₂
            subst h₁; subst h₂
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [Vector.push_eq_push] at h₁ h₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard .spec_yield)
              (.step_op (by assumption) hget₂' hpop₂')⟩
          case spec_join.triv_join =>
            have ⟨⟨h₁, h₂, h₃⟩, h₄, h₅⟩ := hget₂
            subst h₁; subst h₂; subst h₃; subst h₄; subst h₅
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard (.spec_join (by assumption) (by assumption) (by assumption)))
              (.step_op (by assumption) hget₂' hpop₂')⟩
        | step_async => simp at hl
      | step_async _ hget₂ hinterp₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂ hpop₂ => simp at hl
        | step_async _ hget₂' hinterp₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
          rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          simp [hget₂'] at hget₂
          have ⟨h₁, h₂, h₃⟩ := hget₂
          subst h₁; subst h₂; subst h₃
          simp at hpop₂
          have := async_op_interp_det_inputs hinterp₂' hinterp₂
          have ⟨h₁, h₂⟩ := Vector.toList_inj_heq this
          subst h₁; subst h₂
          have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (List.disjoint_of_subset_right
              (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs) hpop₁ hpop₂'
          rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
          simp at hpop₂
          have ⟨h₁, h₂⟩ := hpop₂
          subst h₁
          exact ⟨_, .step
            (.idx_guard .spec_tau)
            (.step_async (by assumption) hget₂' hinterp₂' hpop₂')⟩
    | step_async _ hget₁ hinterp₁ hpop₁ =>
      cases hstep₂ with
      | step_op _ hget₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
            <;> rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          all_goals
            simp at hl
            simp [hget₂', hij] at hget₂
          case spec_yield.triv_yield =>
            have ⟨h₁, h₂⟩ := hget₂
            subst h₁; subst h₂
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
              (List.disjoint_of_subset_right
                (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm
              hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [Vector.push_eq_push] at h₁ h₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard .spec_yield)
              (.step_op (by assumption) hget₂' hpop₂')⟩
          case spec_join.triv_join =>
            have ⟨⟨h₁, h₂, h₃⟩, h₄, h₅⟩ := hget₂
            subst h₁; subst h₂; subst h₃; subst h₄; subst h₅
            simp at hpop₂
            have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
            simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
            have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
              (List.disjoint_of_subset_right
                (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm
              hpop₁ hpop₂'
            rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
            simp at hpop₂
            have ⟨h₁, h₂⟩ := hpop₂
            simp [h₁] at hpop₂'
            exact ⟨_, .step
              (.idx_guard (.spec_join (by assumption) (by assumption) (by assumption)))
              (.step_op (by assumption) hget₂' hpop₂')⟩
        | step_async => simp at hl
      | step_async _ hget₂ hinterp₂ hpop₂ =>
        cases hstep₂' with
        | step_op _ hget₂ hpop₂ => simp at hl
        | step_async _ hget₂' hinterp₂' hpop₂' =>
          rcases hguard₂ with ⟨⟨hguard₂⟩⟩
          rcases hguard₂' with ⟨⟨hguard₂'⟩⟩
          simp [hget₂', hij] at hget₂
          have ⟨h₁, h₂, h₃⟩ := hget₂
          subst h₁; subst h₂; subst h₃
          simp at hpop₂
          have := async_op_interp_det_inputs hinterp₂' hinterp₂
          have ⟨h₁, h₂⟩ := Vector.toList_inj_heq this
          subst h₁; subst h₂
          have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
          simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (by
              have := (List.disjoint_of_subset_right
                (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm
              have := (List.disjoint_of_subset_right
                (async_op_interp_input_sublist hinterp₂').subset this)
              exact this) hpop₁ hpop₂'
          rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
          simp at hpop₂
          have ⟨h₁, h₂⟩ := hpop₂
          subst h₁
          exact ⟨_, .step
            (.idx_guard .spec_tau)
            (.step_async (by assumption) hget₂' hinterp₂' hpop₂')⟩

theorem proc_indexed_guarded_step_to_unguarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n} :
    (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s' →
    (Config.IdxTrivStep opSpec).Step s (i, l) s'
  := Guard.map_guard (λ ⟨hguard⟩ => ⟨OpSpec.spec_guard_implies_triv_guard hguard⟩)

theorem proc_indexed_interp_guarded_step_to_unguarded
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n × opInterp.S} :
    (Config.IdxInterpGuardStep opSpec ioSpec).Step s (i, l) s' →
    (Config.IdxInterpTrivStep opSpec).Step s (i, l) s'
  := Lts.IndexedInterpStep.map_step proc_indexed_guarded_step_to_unguarded

theorem proc_indexed_unguarded_step_det_label_mod
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {l₁ l₂ : Label Op V m n}
  (hstep₁ : (Config.IdxTrivStep opSpec).Step s (i, l₁) s₁)
  (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l₂) s₂) :
    Label.EqModYieldOutputs l₁ l₂
  := by
  have hl₁ := proc_indexed_unguarded_step_label hstep₁
  have hl₂ := proc_indexed_unguarded_step_label hstep₂
  rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
  rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
  have heq := Config.IndexedStep.unique_label_mod_outputs hstep₁ hstep₂
  rename_i l₁' l₂'
  cases l₁ <;> cases l₂ <;> simp at hl₁ hl₂
  case yield.yield =>
    cases hguard₁
    cases hguard₂
    simp [Label.EqModYieldOutputs] at heq ⊢
    have ⟨h₁, h₂⟩ := heq
    subst h₁
    simp [Vector.push_eq_push] at h₂
    replace h₂ := Vector.inj_map (by simp [Function.Injective]) h₂.2
    subst h₂
    simp
  any_goals cases hguard₁ <;> cases hguard₂
  any_goals simp [Label.EqModYieldOutputs] at heq ⊢

theorem proc_indexed_unguarded_step_det_mod
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {l : Label Op V m n}
  (hstep₁ : (Config.IdxTrivStep opSpec).Step s (i, l) s₁)
  (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l) s₂) :
    Config.EqMod EqModGhost s₁ s₂
  := by
  rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
  rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
  apply (Config.IndexedStep.unique_index_mod hstep₁ hstep₂ _).2
  constructor
  · cases hstep₁ <;> simp
  · constructor
    · cases hstep₂ <;> simp
    · cases hguard₁ <;> cases hguard₂
      case triv_yield.triv_yield =>
        intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
        simp at hyield₁ hyield₂
        have ⟨h₁, h₂, h₃⟩ := hyield₁
        have ⟨h₁', h₂', h₃'⟩ := hyield₂
        subst h₁
        simp at h₂ h₃ h₂' h₃'
        simp [← h₃, ← h₃']
        apply Vector.forall₂_to_forall₂_push_toList
        · simp [EqModGhost]
        · simp [EqModGhost]
      case triv_join.triv_join =>
        intros op inputVals outputVals₁ outputVals₂ hyield₁ hyield₂
        simp at hyield₁ hyield₂
        have ⟨h₁, h₂, h₃⟩ := hyield₁
        have ⟨h₁', h₂', h₃'⟩ := hyield₂
        subst h₁
        simp at h₂ h₃ h₂' h₃'
        simp [← h₃, ← h₃', Vector.toList_map, EqModGhost]
        apply List.forall₂_of_length_eq_of_get
        all_goals simp
      all_goals simp [Label.DeterministicMod]

theorem proc_indexed_interp_unguarded_step_det_mod
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hdet : opInterp.Deterministic)
  (hstep₁ : (Config.IdxInterpTrivStep opSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (i, .τ) s₂) :
    Config.EqMod EqModGhost s₁.1 s₂.1 ∧
    s₁.2 = s₂.2
  := by
  cases hstep₁ <;> cases hstep₂
  case step_yield.step_yield =>
    rename_i hinterp₁ hstep₁ _ _ _ _ _ hinterp₂ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this
    have ⟨h₁, h₂⟩ := this
    subst h₁; subst h₂
    have ⟨h₁, h₂⟩ := hdet hinterp₁ hinterp₂
    subst h₁; subst h₂
    have := proc_indexed_unguarded_step_det_mod hstep₁ hstep₂
    simp [this]
  case step_tau.step_tau =>
    rename_i hstep₁ _ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this
    have := proc_indexed_unguarded_step_det_mod hstep₁ hstep₂
    simp [this]
  case step_tau.step_yield =>
    rename_i hstep₁ _ _ _ _ _ _ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this
  case step_yield.step_tau =>
    rename_i hstep₁ _ hstep₂
    have := proc_indexed_unguarded_step_det_label_mod hstep₁ hstep₂
    simp [Label.EqModYieldOutputs] at this

/--
Corollary of `proc_indexed_unguarded_to_guarded_single`.
-/
theorem proc_indexed_interp_unguarded_to_guarded_single
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hdet : opInterp.Deterministic)
  (haff : s.1.proc.AffineChan)
  (hstep₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpGuardStep opSpec ioSpec).Step s₁ (j, .τ) s₂)
  (hstep₂' : (Config.IdxInterpTrivStep opSpec).Step s (j, .τ) s₁') :
    ∃ s₁'',
      (Config.IdxInterpGuardStep opSpec ioSpec).Step s (j, .τ) s₁'' ∧
      Config.EqMod EqModGhost s₁'.1 s₁''.1 ∧
      s₁'.2 = s₁''.2
  := by
  have hdet_mod {s₂} hstep := proc_indexed_interp_unguarded_step_det_mod
    (s₂ := s₂) hdet hstep₂' hstep
  by_cases hij : i = j
  · subst hij
    have := hdet_mod (proc_indexed_interp_guarded_step_to_unguarded hstep₁)
    exact ⟨_, hstep₁, this⟩
  · cases hstep₁ with | _ hstep₁
      <;> cases hstep₂ with | _ hstep₂
      <;> cases hstep₂' with | _ hstep₂'
    -- Rule out some cases where `hstep₂` and `hstep₂'` don't have the same label
    any_goals
      have := proc_indexed_unguarded_step_same_label_kind hstep₁ hstep₂ hstep₂'
      simp at this
    -- Some τ cases can be delegated
    case neg.step_tau.step_tau.step_tau
      | neg.step_yield.step_tau.step_tau =>
      have ⟨s', hstep'⟩ := proc_indexed_unguarded_to_guarded_single haff hstep₁ hstep₂ hstep₂'
      simp at hstep'
      exact ⟨_, Lts.IndexedInterpStep.step_tau hstep',
        by
          have := hdet_mod (proc_indexed_interp_guarded_step_to_unguarded (.step_tau hstep'))
          simp at this
          simp [this]⟩
    -- Other cases need a bit more work as they involve
    -- some interaction with `opInterp`'s determinism
    case neg.step_tau.step_yield.step_yield =>
      rename_i hinterp₂ _ _ _ _ _ hinterp₂'
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      cases hguard₂
      cases hguard₂'
      cases hstep₂ with | step_op _ hget₂ hpop₂
      cases hstep₂' with | step_op _ hget₂' hpop₂'
      cases hstep₁ with
      | step_op _ hget₁ hpop₁ =>
        simp [hget₂'] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp at hpop₂
        have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
        rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
        simp at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁ h₂
        simp [h₁] at hpop₂'
        have := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst this
        have ⟨h₁, h₂⟩ := hdet hinterp₂' hinterp₂
        subst h₁; subst h₂
        have : (Config.IdxInterpGuardStep opSpec ioSpec).Step _ _ _ :=
          Lts.IndexedInterpStep.step_yield (.step
            (.idx_guard .spec_yield)
            (.step_op (by assumption) hget₂' hpop₂')) hinterp₂'
        exact ⟨_, this,
          by
            have := hdet_mod (proc_indexed_interp_guarded_step_to_unguarded this)
            simp at this
            simp [this],
        ⟩
      | step_async _ hget₁ hinterp₁ hpop₁ =>
        simp [hij, hget₂'] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp at hpop₂
        have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (List.disjoint_of_subset_right
            (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm
          hpop₁ hpop₂'
        rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
        simp at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁ h₂
        simp [h₁] at hpop₂'
        have := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst this
        have ⟨h₁, h₂⟩ := hdet hinterp₂' hinterp₂
        subst h₁; subst h₂
        have : (Config.IdxInterpGuardStep opSpec ioSpec).Step _ _ _ :=
          .step_yield (.step
            (.idx_guard .spec_yield)
            (.step_op (by assumption) hget₂' hpop₂')) hinterp₂'
        exact ⟨_, this,
          by
            have := hdet_mod (proc_indexed_interp_guarded_step_to_unguarded this)
            simp at this
            simp [this],
        ⟩
    case neg.step_yield.step_yield.step_yield =>
      rename_i hinterp₁ _ _ _ _ _ hinterp₂ _ _ _ _ _ hinterp₂'
      rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      rcases hstep₂' with ⟨⟨hguard₂'⟩, hstep₂'⟩
      cases hguard₁
      cases hguard₂
      cases hguard₂'
      cases hstep₂ with | step_op _ hget₂ hpop₂
      cases hstep₂' with | step_op _ hget₂' hpop₂'
      cases hstep₁ with
      | step_op _ hget₁ hpop₁ =>
        simp [hget₂'] at hget₂
        have ⟨h₁, h₂, h₃⟩ := hget₂
        subst h₁; subst h₂; subst h₃
        simp at hpop₂
        have hdisj_inputs := haff.atom_inputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        have hdisj_outputs := haff.atom_outputs_disjoint ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hij])
        simp [hget₂', hget₁, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂'
        rw [pop_vals_push_vals_commute hpop₁₂] at hpop₂
        simp at hpop₂
        have ⟨h₁, h₂⟩ := hpop₂
        simp [Vector.push_eq_push] at h₁ h₂
        simp [h₁] at hpop₂'
        have := Vector.inj_map (by simp [Function.Injective]) h₁.2
        subst this
        have : (Config.IdxInterpGuardStep opSpec ioSpec).Step _ _ _ :=
          .step_yield (.step
            (.idx_guard .spec_yield)
            (.step_op (by assumption) hget₂' hpop₂')) hinterp₂'
        exact ⟨_, this,
          by
            have := hdet_mod (proc_indexed_interp_guarded_step_to_unguarded this)
            simp at this
            simp [this],
        ⟩

/--
If there is a guarded τ trace from `s` to a final state `s₁`,
then we can turn any *unguarded* τ step from `s` to `s₂`,
into a guarded τ step, modulo potentially different ghost tokens.
-/
theorem proc_indexed_unguarded_to_guarded
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n}
  {tr : Trace (Nat × Label Op V m n)}
  {l : Label Op V m n}
  (haff : (Config.IdxGuardStep opSpec ioSpec).IsInvariantAt
    (λ s => s.proc.AffineChan) s)
  (htrace₁ : (Config.IdxGuardStep opSpec ioSpec).Star s tr s₁)
  -- The first label in the trace that matches the index should emit the same event
  (hdom : tr.find? (·.1 = i) = .some (i, l))
  (hstep₂ : (Config.IdxTrivStep opSpec).Step s (i, l) s₂) :
    ∃ s₂',
      (Config.IdxGuardStep opSpec ioSpec).Step s (i, l) s₂' ∧
      Config.EqMod EqModGhost s₂' s₂
  := by
  induction htrace₁
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl => simp at hdom
  | head hstep₁ htail₁ ih =>
    rename_i s s₂' l' tr'
    rcases l' with ⟨i', l'⟩
    by_cases hk : (i, l) = (i', l')
    · simp at hk
      have ⟨h₁, h₂⟩ := hk
      subst h₁; subst h₂
      exists s₂'
      simp [hstep₁]
      exact proc_indexed_unguarded_step_det_mod
        (proc_indexed_guarded_step_to_unguarded hstep₁) hstep₂
    · simp at hdom hk
      cases hdom
      · rename_i h
        simp [h] at hk
      rename_i hdom
      have hstep₁' := proc_indexed_guarded_step_to_unguarded hstep₁
      have := proc_indexed_guard_triv_strong_confl_at_mod
        s haff.base hstep₁' hstep₂
        (by
          intros h
          exact False.elim (hdom.1 h))
      cases this with
      | inl h =>
        simp at h
        exact False.elim (hk h.1.1.symm h.1.2.symm)
      | inr h =>
        have ⟨s₃', s₃, hstep₃', hstep₃, heq₃⟩ := h
        replace ⟨s₃', hstep₃', heq₃⟩ := ih
          (haff.unfold hstep₁).2
          hdom.2
          hstep₃'
        have ⟨s₂', hstep₂'⟩ := proc_indexed_unguarded_to_guarded_single
          haff.base
          hstep₁ hstep₃' hstep₂
        exact ⟨
          _, hstep₂',
          proc_indexed_unguarded_step_det_mod
            (proc_indexed_guarded_step_to_unguarded hstep₂') hstep₂,
        ⟩

theorem proc_indexed_interp_unguarded_step_label
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {interp : Lts S' (RespLabel Op V)}
  {s s' : ConfigWithSpec opSpec χ m n × S'}
  {l : Label Semantics.Empty V m n}
  (hstep : ((Config.IdxTrivStep opSpec).IndexedInterpStep interp).Step
    s (i, l) s') :
    l = .τ
  := by
  cases hstep with
  | step_yield hstep
  | step_tau hstep =>
    rcases hstep with ⟨⟨hguard⟩, hstep⟩
    cases hguard <;> cases hstep <;> simp
  | _ hstep =>
    have hl := proc_indexed_unguarded_step_label hstep
    simp at hl

theorem proc_indexed_interp_guarded_step_label
  [Arity Op] [PCM T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {interp : Lts S' (RespLabel Op V)}
  {s s' : ConfigWithSpec opSpec χ m n × S'}
  {l : Label Semantics.Empty V m n}
  (hstep : ((Config.IdxGuardStep opSpec ioSpec).IndexedInterpStep interp).Step
    s (i, l) s') :
    l = .τ
  := by
  cases hstep with
  | step_yield hstep
  | step_tau hstep =>
    rcases hstep with ⟨⟨hguard⟩, hstep⟩
    cases hguard <;> cases hstep <;> simp
  | _ hstep =>
    have hl := proc_indexed_guarded_step_label hstep
    simp at hl

theorem proc_indexed_interp_tau_step_to_step
  [Arity Op] [Arity Op']
  {S S'}
  {Guard : Label Op' V' m' n' → Label Op V m n → Prop}
  {base : Lts S (ℕ × Label Op' V' m' n')}
  {interp : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hstep : ((base.GuardStep (IndexedGuard Guard)).IndexedInterpStep interp).Step s (i, .τ) s') :
    ∃ l,
      (base.GuardStep (IndexedGuard Guard)).Step s.1 (i, l) s'.1 ∧
      (
        (l.isYield ∧ ∃ l', l'.MatchLabel l ∧ interp.Step s.2 l' s'.2) ∨
        (l.isSilent ∧ s.2 = s'.2)
      )
  := by
  cases hstep with
  | step_yield hstep hinterp =>
    exact ⟨_, hstep,
      by simp; exact ⟨_, by simp [RespLabel.MatchLabel], hinterp⟩⟩
  | step_tau hstep => exact ⟨_, hstep, by simp⟩

/-- If two operators can fire at the same state, then one can fire after another.
(although no guarantee about the final state).

TODO: Simplify this proof. -/
theorem proc_commute_unguarded_steps
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hnb : opInterp.NonBlocking)
  (haff : s.1.proc.AffineChan)
  (hstep₁ : (Config.IdxInterpTrivStep opSpec).Step s (i, .τ) s₁)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (j, .τ) s₂)
  (hne : i ≠ j) :
    ∃ s₂', (Config.IdxInterpTrivStep opSpec).Step s₁ (j, .τ) s₂'
  := by
  cases hstep₁ with
  | step_yield hstep₁ hinterp₁ =>
    rcases hstep₁ with ⟨⟨⟨hguard₁⟩⟩, hstep₁⟩
    cases hstep₁ with | step_op _ hget₁ hpop₁ =>
    cases hstep₂ with
    | step_yield hstep₂ hinterp₂ =>
      rcases hstep₂ with ⟨⟨⟨hguard₂⟩⟩, hstep₂⟩
      cases hstep₂ with | step_op _ hget₂ hpop₂ =>
      have ⟨_, _, hinterp₂'⟩ := hnb hinterp₁ hinterp₂
      have hdisj_inputs := haff.atom_inputs_disjoint
        ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
      have hdisj_outputs := haff.atom_outputs_disjoint
        ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
      simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
      have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
      exact ⟨_,
        .step_yield (.step
          (.idx_guard (.triv_yield (tok₂ := PCM.zero)))
          (.step_op
            (by assumption)
            hget₂
            (pop_vals_push_vals_commute hpop₁₂)))
            hinterp₂'
      ⟩
    | step_tau hstep₂ =>
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      cases hguard₂ with
      | triv_join =>
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        exact ⟨_,
          .step_tau (.step
            (.idx_guard (.triv_join (outputs := #v[PCM.zero, PCM.zero])))
            (.step_op
              (by assumption)
              hget₂
              (pop_vals_push_vals_commute hpop₁₂)))
        ⟩
      | triv_tau =>
        cases hstep₂ with | step_async _ hget₂ hinterp₂ hpop₂ =>
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (List.disjoint_of_subset_right
            (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs) hpop₁ hpop₂
        exact ⟨_,
          .step_tau (.step
            (.idx_guard .triv_tau)
            (.step_async
              (by assumption)
              hget₂
              hinterp₂
              (pop_vals_push_vals_commute hpop₁₂)))
        ⟩
  | step_tau hstep₁ =>
    rcases hstep₁ with ⟨⟨hguard₁⟩, hstep₁⟩
    cases hguard₁ with
    | triv_join =>
      cases hstep₁ with | step_op _ hget₁ hpop₁ =>
      cases hstep₂ with
      | step_yield hstep₂ hinterp₂ =>
        rcases hstep₂ with ⟨⟨⟨hguard₂⟩⟩, hstep₂⟩
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        -- have ⟨_, _, hinterp₂'⟩ := hnb hinterp₁ hinterp₂
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
        exact ⟨_,
          .step_yield (.step
            (.idx_guard (.triv_yield (tok₂ := PCM.zero)))
            (.step_op
              (by assumption)
              hget₂
              (pop_vals_push_vals_commute hpop₁₂)))
              hinterp₂
        ⟩
      | step_tau hstep₂ =>
        rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
        cases hguard₂ with
        | triv_join =>
          cases hstep₂ with | step_op _ hget₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute hdisj_inputs hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard (.triv_join (outputs := #v[PCM.zero, PCM.zero])))
              (.step_op
                (by assumption)
                hget₂
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩
        | triv_tau =>
          cases hstep₂ with | step_async _ hget₂ hinterp₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (List.disjoint_of_subset_right
              (async_op_interp_input_sublist hinterp₂).subset hdisj_inputs) hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard .triv_tau)
              (.step_async
                (by assumption)
                hget₂
                hinterp₂
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩
    | triv_tau =>
      cases hstep₁ with | step_async _ hget₁ hinterp₁ hpop₁ =>
      cases hstep₂ with
      | step_yield hstep₂ hinterp₂ =>
        rcases hstep₂ with ⟨⟨⟨hguard₂⟩⟩, hstep₂⟩
        cases hstep₂ with | step_op _ hget₂ hpop₂ =>
        -- have ⟨_, _, hinterp₂'⟩ := hnb hinterp₁ hinterp₂
        have hdisj_inputs := haff.atom_inputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        have hdisj_outputs := haff.atom_outputs_disjoint
          ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
        simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (List.disjoint_of_subset_right
            (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm hpop₁ hpop₂
        exact ⟨_,
          .step_yield (.step
            (.idx_guard (.triv_yield (tok₂ := PCM.zero)))
            (.step_op
              (by simp; assumption)
              (by simp [hne]; exact hget₂)
              (pop_vals_push_vals_commute hpop₁₂)))
              hinterp₂
        ⟩
      | step_tau hstep₂ =>
        rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
        cases hguard₂ with
        | triv_join =>
          cases hstep₂ with | step_op _ hget₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (List.disjoint_of_subset_right
              (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard (.triv_join (outputs := #v[PCM.zero, PCM.zero])))
              (.step_op
                (by simp; assumption)
                (by simp [hne]; exact hget₂)
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩
        | triv_tau =>
          cases hstep₂ with | step_async _ hget₂ hinterp₂ hpop₂ =>
          have hdisj_inputs := haff.atom_inputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          have hdisj_outputs := haff.atom_outputs_disjoint
            ⟨i, by assumption⟩ ⟨j, by assumption⟩ (by simp [hne])
          simp [hget₁, hget₂, AtomicProc.inputs, AtomicProc.outputs] at hdisj_inputs hdisj_outputs
          have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
            (by
              have := (List.disjoint_of_subset_right
                (async_op_interp_input_sublist hinterp₁).subset hdisj_inputs.symm).symm
              have := (List.disjoint_of_subset_right
                (async_op_interp_input_sublist hinterp₂).subset this)
              exact this) hpop₁ hpop₂
          exact ⟨_,
            .step_tau (.step
              (.idx_guard .triv_tau)
              (.step_async
                (by simp; assumption)
                (by simp [hne]; exact hget₂)
                hinterp₂
                (pop_vals_push_vals_commute hpop₁₂)))
          ⟩

/-- If the "good-behaving" semantics of `Config.IdxInterpGuardStep`
has a terminating trace, then any unguarded step can be turned
into a guarded step. -/
theorem proc_indexed_interp_unguarded_to_guarded
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr : Trace (Nat × Label Semantics.Empty V m n)}
  {l : Label Semantics.Empty V m n}
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hdom : ∃ l', (i, l') ∈ tr)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (i, l) s₂) :
    ∃ s₂',
      (Config.IdxInterpGuardStep opSpec ioSpec).Step s (i, l) s₂' ∧
      Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
      s₂.2 = s₂'.2
  := by
  have hl := proc_indexed_interp_unguarded_step_label hstep₂
  subst hl
  induction htrace₁
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl => simp at hdom
  | head hstep₁ htail₁ ih =>
    rename_i s s' l' tr'
    rcases l' with ⟨i', l'⟩
    have this := proc_indexed_interp_guarded_step_label hstep₁
    subst this
    by_cases hii' : i = i'
    · subst hii'
      have := proc_indexed_interp_unguarded_step_det_mod hdet
        hstep₂ (proc_indexed_interp_guarded_step_to_unguarded hstep₁)
      exists s'
    · have hstep₁' := proc_indexed_interp_guarded_step_to_unguarded hstep₁
      have ⟨s₂'', hstep₂''⟩ := proc_commute_unguarded_steps hnb haff.base hstep₁' hstep₂ (Ne.symm hii')
      have ⟨s₁'', hstep₁'', heq⟩ := ih (haff.unfold hstep₁).2
        (by
          have ⟨l', hl'⟩ := hdom
          exists l'
          simp [hii'] at hl'
          simp [hl'])
        hstep₂''
      exact proc_indexed_interp_unguarded_to_guarded_single
        hdet haff.base hstep₁ hstep₁'' hstep₂

/-- If a guarded trace terminates, then any unguarded step from the same state
must fire one of the operators fired in the guarded trace. -/
theorem proc_indexed_interp_unguarded_term_dom
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr : Trace (Nat × Label Semantics.Empty V m n)}
  {l : Label Semantics.Empty V m n}
  (hnb : opInterp.NonBlocking)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (_, l) => l.isYield ∨ l.isSilent) s₁.1)
  (hstep₂ : (Config.IdxInterpTrivStep opSpec).Step s (i, l) s₂) :
    ∃ l', (i, l') ∈ tr
  := by
  have hl := proc_indexed_interp_unguarded_step_label hstep₂
  subst hl
  induction htrace₁
    using Lts.Star.reverse_induction
    generalizing s₂ with
  | refl =>
    match hstep₂ with
    | .step_tau hstep₂
    | .step_yield hstep₂ _ =>
      rcases hstep₂ with ⟨⟨hguard₂⟩, hstep₂⟩
      cases hguard₂ <;> exact False.elim (hterm (by simp) hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i s s' l' tr'
    rcases l' with ⟨i', l'⟩
    have this := proc_indexed_interp_guarded_step_label hstep₁
    subst this
    by_cases hii' : i = i'
    · simp [hii']
    · simp [hii']
      have hstep₁' := proc_indexed_interp_guarded_step_to_unguarded hstep₁
      have ⟨s₂'', hstep₂''⟩ := proc_commute_unguarded_steps hnb haff.base hstep₁' hstep₂ (Ne.symm hii')
      exact ih (haff.unfold hstep₁).2 hstep₂''

theorem proc_indexed_interp_guarded_trace_to_unguarded
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s' : ConfigWithSpec opSpec χ m n × opInterp.S}
  (htrace : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s') :
    (Config.IdxInterpTrivStep opSpec).Star s tr s'
  := htrace.map_step proc_indexed_interp_guarded_step_to_unguarded

theorem proc_indexed_interp_unguarded_congr
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (hstep : (Config.IdxInterpTrivStep opSpec).Step s₁ l s₂)
  (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      (Config.IdxInterpTrivStep opSpec).Step s₁' l s₂' ∧
      Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
      s₂.2 = s₂'.2
  := by

  sorry

theorem proc_indexed_interp_unguarded_steps_congr
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {s₁ s₁' s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (htrace : (Config.IdxInterpTrivStep opSpec).Star s₁ tr s₂)
  (heq : Config.EqMod EqModGhost s₁.1 s₁'.1 ∧ s₁.2 = s₁'.2) :
    ∃ s₂',
      (Config.IdxInterpTrivStep opSpec).Star s₁' tr s₂' ∧
      Config.EqMod EqModGhost s₂.1 s₂'.1 ∧
      s₂.2 = s₂'.2
  := by
  induction htrace
    using Lts.Star.reverse_induction
    generalizing s₁' with
  | refl => exact ⟨s₁', .refl, heq⟩
  | head hstep htail ih =>
    have ⟨_, hstep', heq₁⟩ := proc_indexed_interp_unguarded_congr hstep heq
    have ⟨_, htail', heq₂⟩ := ih heq₁
    exact ⟨_, htail'.prepend hstep', heq₂⟩

theorem proc_indexed_interp_guarded_term_confl
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  (htrace : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (i, l) => l.isYield ∨ l.isSilent) s₁.1)
  (hstep : (Config.IdxInterpGuardStep opSpec ioSpec).Step s l s₂) :
    ∃ tr', (Config.IdxInterpGuardStep opSpec ioSpec).Star s₂ tr' s₁
  := sorry

theorem proc_indexed_interp_unguarded_weak_norm
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr₁ tr₂ : Trace (Nat × Label Semantics.Empty V m n)}
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  -- (hconfl : opSpec.Confluent opInterp)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (hdisj : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.DisjointTokens) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr₁ s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (_, l) => l.isYield ∨ l.isSilent) s₁.1)
  (htrace₂ : (Config.IdxInterpTrivStep opSpec).Star s tr₂ s₂) :
    ∃ s₁' tr₃,
      (Config.IdxInterpTrivStep opSpec).Star s₂ tr₃ s₁' ∧
      Config.EqMod EqModGhost s₁.1 s₁'.1 ∧
      s₁.2 = s₁'.2
  := by
  cases htrace₂
    using Lts.Star.reverse_induction with
  | refl =>
    exact ⟨_, _, proc_indexed_interp_guarded_trace_to_unguarded htrace₁,
      by simp [IsRefl.refl]⟩
  | head hstep₂ htail₂ ih =>
    rename_i s s' l' tr₂'
    have := proc_indexed_interp_unguarded_term_dom
      hnb haff htrace₁ hterm hstep₂
    have ⟨s'', hstep₂', heq⟩ := proc_indexed_interp_unguarded_to_guarded
      hdet hnb haff htrace₁ this hstep₂
    have ⟨_, htail₂', heq'⟩ := proc_indexed_interp_unguarded_steps_congr htail₂ heq
    have ⟨_, htrace₁'⟩ := proc_indexed_interp_guarded_term_confl htrace₁ hterm hstep₂'
    have ⟨_, _, htrace₂', heq₂'⟩ := proc_indexed_interp_unguarded_weak_norm
      hdet hnb
      (haff.unfold hstep₂').2
      (hdisj.unfold hstep₂').2
      htrace₁' hterm htail₂'
    have := proc_indexed_interp_unguarded_steps_congr htrace₂'
      (by
        constructor
        · exact IsSymm.symm _ _ heq'.1
        · simp [heq'.2])
    have ⟨_, htrace₂'', heq₂''⟩ := this
    exact ⟨
      _, _, htrace₂'',
      by
        constructor
        · exact IsTrans.trans _ _ _ heq₂'.1 heq₂''.1
        · simp [← heq₂''.2, heq₂'.2]
    ⟩

theorem proc_indexed_interp_unguarded_bound
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp Op V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {s s₁ s₂ : ConfigWithSpec opSpec χ m n × opInterp.S}
  {tr tr' : Trace (Nat × Label Semantics.Empty V m n)}
  {l : Label Semantics.Empty V m n}
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  -- (hconfl : opSpec.Confluent opInterp)
  (haff : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.proc.AffineChan) s)
  (hdisj : (Config.IdxInterpGuardStep opSpec ioSpec).IsInvariantAt (·.1.DisjointTokens) s)
  (htrace₁ : (Config.IdxInterpGuardStep opSpec ioSpec).Star s tr s₁)
  (hterm : Config.IndexedStep.IsFinalFor (λ (i, l) => l.isYield ∨ l.isSilent) s₁.1)
  (htrace₂ : (Config.IdxInterpTrivStep opSpec).Star s tr' s₂) :
    tr'.length ≤ tr.length
  := by sorry

theorem proc_interp_tau_step_to_step
  [Arity Op] [Arity Op']
  [InterpConsts V]
  {Guard : Label Op' V' m' n' → Label Op V m n → Prop}
  {opInterp : OpInterp Op V}
  {sem : Semantics Op' V' m' n'}
  {s s' : sem.S × opInterp.S}
  (hstep : ((sem.guard Guard).interpret opInterp).lts.Step s .τ s') :
    ∃ l,
      (sem.guard Guard).lts.Step s.1 l s'.1 ∧
      (
        (l.isYield ∧ ∃ l', l'.MatchLabel l ∧ opInterp.lts.Step s.2 l' s'.2) ∨
        (l.isSilent ∧ s.2 = s'.2)
      )
  := by
  cases hstep with
  | step_yield hstep hinterp =>
    exact ⟨_, hstep,
      by simp; exact ⟨_, by simp [RespLabel.MatchLabel], hinterp⟩⟩
  | step_tau hstep => exact ⟨_, hstep, by simp⟩

theorem proc_guarded_termination
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {opInterp : OpInterp Op V}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec χ m n)
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  {s s₁ s₂ : proc.semantics.S × opInterp.S}
  (htrace₁ : ((proc.semantics.guard (opSpec.Guard ioSpec)).interpret opInterp).lts.TauStar .τ s s₁)
  (hterm : proc.semantics.IsFinal s₁.1)
  (hstep₂ : ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.Step s .τ s₂) :
    ∃ s₁',
      ((proc.semantics.guard opSpec.TrivGuard).interpret opInterp).lts.TauStar .τ s₂ s₁' ∧
      Config.EqMod EqModGhost s₁.1 s₁'.1 ∧
      s₁.2 = s₁'.2
  := by
  induction htrace₁
    using Lts.TauStar.reverse_induction
    generalizing s₂ with
  | refl =>
    match hstep₂ with
    | .step_tau hstep₂ =>
      cases hstep₂ with | step hguard hstep₂ =>
      cases hguard <;> exact False.elim (hterm hstep₂)
    | .step_yield hstep₂ _ =>
      cases hstep₂ with | step hguard hstep₂ =>
      cases hguard
      exact False.elim (hterm hstep₂)
  | head hstep₁ htail₁ ih =>
    rename_i s s₁'
    replace ⟨l₁, hstep₁, hl₁⟩ := proc_interp_tau_step_to_step hstep₁
    replace ⟨l₂, hstep₂, hl₂⟩ := proc_interp_tau_step_to_step hstep₂

    sorry

end Wavelet.Compile

/-
Proof sketch (for a single `Fn`):

We show that

```
fn.semantics
  ≲ᵣ fn'.semantics.guard
  ≲ᵣ (compileFn ... fn').semantics.guard ... (by fn'.semantics ≲ᵣ (compileFn ... fn').semantics)
  (... maybe some optimization passes)
```

Also for any `proc`
1. `proc.semantics.guard ...` is strongly confluent
2. `proc.semantics.guard P ≲ᵣ proc.semantics.guard P'`
   if `P → P'` (and in particular for trivial `P'`)
3. If we have a terminating trace in `proc.semantics.guard P`,
   then any trace in `proc.semantics` goes to the same final state.
-/
