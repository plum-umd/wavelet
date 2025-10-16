import Mathlib.Control.ULiftable

import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Reasoning about the determinacy of semantics. -/

namespace Wavelet.Semantics

open Semantics

/-- Restricts an LTS by imposing a state invariant. -/
inductive Lts.Guard {S} (Inv : S → Prop) (lts : Lts S E) : Lts S E where
  | step : Inv s → Inv s' → lts.Step s e s' → Guard Inv lts s e s'

/-- Guards the transition of a semantics with the given invariant. -/
def guard
  [Arity Op]
  (sem : Semantics Op V m n)
  (Inv : sem.S → Prop) :
  Semantics Op V m n :=
  {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.Guard Inv,
    -- TODO: this is actually not true,
    -- maybe remove this requirement?
    yields_functional := sorry
  }

/-- Modifies labels with a relation. -/
inductive Lts.InterpLabelStep {S} (Interp : E → E' → Prop) (lts : Lts S E) : Lts S E' where
  | step : Interp e e' → lts.Step s e s' → InterpLabelStep Interp lts s e' s'

/-- Interprets the labels as another set of operators. -/
def interpLabel
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (Interp : Label Op V m n → Label Op' V' m' n' → Prop) :
  Semantics Op' V' m' n' :=
  {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.InterpLabelStep Interp,
    yields_functional := sorry
  }

/-- Some well-formedness constraints on label interpretations. -/
class LawfulLabelInterp [Arity Op] [Arity Op']
  (Interp : Label Op V m n → Label Op' V' m' n' → Prop) where
  label_interp_tau : Interp .τ .τ
  label_interp_tau_only : ∀ {l}, Interp .τ l → l.isSilent
  label_interp_input : ∀ {vals l}, Interp (.input vals) l → l.isSilent ∨ l.isInput
  label_interp_output : ∀ {vals l}, Interp (.output vals) l → l.isSilent ∨ l.isOutput
  label_interp_yield : ∀ {op inputs outputs l}, Interp (.yield op inputs outputs) l → l.isSilent ∨ l.isYield

/-- `interpLabel` preserves IO-restricted simulation. -/
theorem sim_interp_label
  [Arity Op] [Arity Op']
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  [InterpConsts V']
  {sem₁ sem₂ : Semantics Op V m n}
  {Interp : Label Op V m n → Label Op' V' m' n' → Prop}
  [hinterp : LawfulLabelInterp Interp]
  (hsim : sem₁ ≲ᵣ sem₂) :
  sem₁.interpLabel Interp ≲ᵣ sem₂.interpLabel Interp
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    simp [Semantics.interpLabel] at hstep
    cases hstep with | step hlabel hstep =>
    rename Label Op V m n => l'
    have ⟨s₂', hstep_s₂, hR₂⟩ := hsim.sim_step _ _ _ _ hR hstep
    exists s₂'
    constructor
    · cases hstep_s₂ with
      | step_yield hstep_yield_s₂ =>
        replace hstep_yield_s₂ := Lts.InterpLabelStep.step hlabel hstep_yield_s₂
        cases hinterp.label_interp_yield hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (.single hstep_yield_s₂)
        · exact .step_yield hstep_yield_s₂
      | step_input hstep_input_s₂ hstep_tau =>
        replace hstep_input_s₂ := Lts.InterpLabelStep.step hlabel hstep_input_s₂
        replace hstep_tau := hstep_tau.map (Lts.InterpLabelStep.step hinterp.label_interp_tau)
        cases hinterp.label_interp_input hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.prepend hstep_input_s₂)
        · exact .step_input hstep_input_s₂ hstep_tau
      | step_output hstep_tau hstep_output_s₂ =>
        replace hstep_output_s₂ := Lts.InterpLabelStep.step hlabel hstep_output_s₂
        replace hstep_tau := hstep_tau.map (Lts.InterpLabelStep.step hinterp.label_interp_tau)
        cases hinterp.label_interp_output hlabel <;>
          rename_i h₁ <;> cases l <;> simp at h₁
        · exact .step_tau (hstep_tau.tail hstep_output_s₂)
        · exact .step_output hstep_tau hstep_output_s₂
      | step_tau hstep_tau_s₂ =>
        replace hstep_tau_s₂ := hstep_tau_s₂.map (Lts.InterpLabelStep.step hinterp.label_interp_tau)
        have := hinterp.label_interp_tau_only hlabel
        cases l <;> simp at this
        exact .step_tau hstep_tau_s₂
    · exact hR₂

/-- PCM specification of an operator set -/
structure OpSpec Op V T [Arity Op] [PCM T] where
  pre : (op : Op) → Vector V (Arity.ι op) → T
  post : (op : Op) → Vector V (Arity.ι op) → Vector V (Arity.ω op) → T
  frame_preserving : ∀ op inputs outputs, pre op inputs ⟹ post op inputs outputs

/-- Specification on input/output labels. -/
structure IOSpec V T [PCM T] m n where
  pre : Vector V m → T
  -- This can only depend on the outputs, due
  -- to a technical issue that we can't access
  -- the input values at an output event.
  post : Vector V n → T

/-- Augments the operator set with an additional ghost argument
to pass a PCM token, as well as two operators to split and join PCMs. -/
inductive WithSpec (Op : Type u) [Arity Op] [PCM T] (spec : OpSpec Op V T) where
  | op (op : Op)
  | join (k : Nat) -- Number of input tokens to combine

/-- Uses only the LHS `InterpConsts` of a sum for constants. -/
instance instInterpConstsSum [left : InterpConsts V] : InterpConsts (V ⊕ V') where
  junkVal := .inl (left.junkVal)
  toBool
    | .inl v => left.toBool v
    | .inr _ => none
  fromBool := .inl ∘ left.fromBool
  unique_fromBool_toBool b := left.unique_fromBool_toBool b
  unique_toBool_fromBool b v hv := by
    split at hv
    · rename_i v'
      have := left.unique_toBool_fromBool b v' hv
      simp [this]
    · contradiction

instance instArityWithSpec
  [arity : Arity Op] [PCM T]
  {spec : OpSpec Op V T} :
  Arity (WithSpec Op spec) where
  ι | .op o => arity.ι o + 1
    | .join k => k
  ω | .op o => arity.ω o + 1
    | .join _ => 2

/-- Interprets the labels with ghost values using the base operators,
but with dynamic checks for ghost tokens satisfying the specs. -/
inductive SpecLabelInterp [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) →
  Label Op V m n → Prop where
  | spec_yield
    {op}
    {inputs : Vector V (Arity.ι op)}
    {outputs : Vector V (Arity.ω op)} :
    tok₁ ≡ opSpec.pre op inputs →
    tok₂ ≡ opSpec.post op inputs outputs →
    SpecLabelInterp opSpec ioSpec
      (.yield (.op op)
        ((inputs.map .inl).push (.inr tok₁))
        ((outputs.map .inl).push (.inr tok₂)))
      (.yield op inputs outputs)
  -- NOTE: the exact output split of permissions
  -- is intentionally left unspecified, because
  -- we want this to be dynamic without restricting
  -- to a static annotation.
  | spec_join
    {toks : Vector T k}
    {outputs : Vector (V ⊕ T) 2} :
    outputs[0] = .inr tok₁ →
    outputs[1] = .inr tok₂ →
    tok₁ ⊔ tok₂ ≡ PCM.sum toks.toList →
    SpecLabelInterp opSpec ioSpec
      (.yield (.join k) (toks.map .inr) outputs) .τ
  | spec_input {tok vals} :
    tok ≡ ioSpec.pre vals →
    SpecLabelInterp opSpec ioSpec
      (.input ((vals.map .inl).push (.inr tok))) (.input vals)
  | spec_output :
    tok ≡ ioSpec.post vals →
    SpecLabelInterp opSpec ioSpec
      (.output ((vals.map .inl).push (.inr tok))) (.output vals)
  | spec_tau :
    SpecLabelInterp opSpec ioSpec .τ .τ

instance
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n} : LawfulLabelInterp (SpecLabelInterp opSpec ioSpec) where
  label_interp_tau := .spec_tau
  label_interp_tau_only h := by cases h; rfl
  label_interp_input h := by cases h; simp
  label_interp_output h := by cases h; simp
  label_interp_yield h := by cases h <;> simp

/--
Same signature as `SpecLabelInterp` but does not dynamically
check the well-formedness of the tokens.
-/
inductive SpecLabelInterpUnchecked [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T} :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) →
  Label Op V m n → Prop where
  | spec_yield
    {op}
    {inputs : Vector V (Arity.ι op)}
    {outputs : Vector V (Arity.ω op)} :
    SpecLabelInterpUnchecked
      (.yield (.op op)
        ((inputs.map .inl).push tok₁)
        ((outputs.map .inl).push tok₂))
      (.yield op inputs outputs)
  | spec_join :
    SpecLabelInterpUnchecked
      (.yield (.join k) toks outputs) .τ
  | spec_input :
    SpecLabelInterpUnchecked
      (.input ((vals.map .inl).push tok)) (.input vals)
  | spec_output :
    SpecLabelInterpUnchecked
      (.output ((vals.map .inl).push tok)) (.output vals)
  | spec_tau :
    SpecLabelInterpUnchecked .τ .τ

end Wavelet.Semantics

namespace Wavelet.Seq

open Semantics Compile

def VarMap.DisjointTokens
  [PCM T]
  (vars : VarMap χ (V ⊕ T)) : Prop :=
  ∀ x₁ x₂ t₁ t₂,
    x₁ ≠ x₂ →
    vars.getVar x₁ = some (.inr t₁) →
    vars.getVar x₂ = some (.inr t₂) →
    t₁ ⊥ t₂

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

def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  ∀ x₁ x₂
    (buf₁ buf₂ : List (V ⊕ T))
    (i : Fin buf₁.length) (j : Fin buf₂.length)
    t₁ t₂,
    x₁ ≠ x₂ ∨ i.val ≠ j.val →
    c.chans x₁ = some buf₁ →
    c.chans x₂ = some buf₂ →
    buf₁[i] = .inr t₁ →
    buf₂[j] = .inr t₂ →
    t₁ ⊥ t₂

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

theorem sim_compile_fn'
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (fn : FnWithSpec opSpec χ m n)
  (hwf : fn.AffineVar) :
  fn.semantics.guard Config.DisjointTokens
    ≲ᵣ (compileFn (by simp) fn).semantics.guard Config.DisjointTokens
  := sorry

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
    (proc.semantics.guard Config.DisjointTokens).interpLabel (SpecLabelInterp opSpec ioSpec)
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
  (proc.semantics.guard Config.DisjointTokens).interpLabel (SpecLabelInterp opSpec ioSpec)
    ≲ᵣ (eraseGhost proc).semantics
  := sorry

/--
TODO: this needs to assume more about how
the operator semantics satisfies the spec.

TODO: not true in general, need to assume that
trace₁ "dominates" trace₂ in some sense.
-/
theorem guarded_confluence
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {proc : ProcWithSpec opSpec χ m n}
  {trace₁ trace₂ : Trace (Label Op V m n)}
  {s₁ s₂ : proc.semantics.S}
  (haff : proc.AffineChan)
  (htrace₁ :
    ((proc.semantics.guard Config.DisjointTokens).interpLabel (SpecLabelInterp opSpec ioSpec)).lts.Star
      proc.semantics.init trace₁ s₁)
  (htrace₂ :
    (proc.semantics.interpLabel SpecLabelInterpUnchecked).lts.Star
      proc.semantics.init trace₂ s₂) :
  ∃ trace₁' trace₂' s',
    (proc.semantics.interpLabel SpecLabelInterpUnchecked).lts.Star s₁ trace₁' s' ∧
    (proc.semantics.interpLabel SpecLabelInterpUnchecked).lts.Star s₂ trace₂' s' ∧
    trace₁ ++ trace₁' = trace₂ ++ trace₂'
  := sorry

/-- If a list of channels already have values ready to pop,
then it can commute with any `pushVals` operation. -/
theorem pop_vals_push_vals_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hpop : chans.popVals vars₂ = some (vals₂, chans')) :
  (chans.pushVals vars₁ outputVals₁).popVals vars₂ =
    some (vals₂, chans'.pushVals vars₁ outputVals₁)
  := sorry

theorem pop_vals_pop_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : vars₁.toList.Disjoint vars₂.toList)
  (hpop₁ : chans.popVals vars₁ = some (vals₁, chans₁))
  (hpop₂ : chans.popVals vars₂ = some (vals₂, chans₂)) :
  ∃ chans',
    chans₁.popVals vars₂ = some (vals₂, chans') ∧
    chans₂.popVals vars₁ = some (vals₁, chans')
  := sorry

theorem push_vals_push_vals_disj_commute
  [DecidableEq χ]
  {chans : ChanMap χ V}
  (hdisj : vars₁.toList.Disjoint vars₂.toList) :
  (chans.pushVals vars₁ vals₁).pushVals vars₂ vals₂
    = (chans.pushVals vars₂ vals₂).pushVals vars₁ vals₁
  := sorry

/-- Without considering the shared operator states
a `Proc` has a strongly confluent (and thus confluence) semantics
(when restricted to silent/yield labels). -/
theorem proc_strong_confluence
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  {proc : Proc Op χ V m n}
  {s s₁' s₂' : proc.semantics.S}
  {l₁ l₂ : Label Op V m n}
  (haff : s.proc.AffineChan)
  (hlabel₁ : l₁.isYield ∨ l₁.isSilent)
  (hlabel₂ : l₂.isYield ∨ l₂.isSilent)
  -- Only consider the case when the operators are deterministic
  (hyield_det : ∀ {op inputVals outputVals₁ outputVals₂},
    l₁ = .yield op inputVals outputVals₁ →
    l₂ = .yield op inputVals outputVals₂ →
    outputVals₁ = outputVals₂)
  (hstep₁ : proc.semantics.lts.Step s l₁ s₁')
  (hstep₂ : proc.semantics.lts.Step s l₂ s₂')
  : s₁' = s₂' ∨ (∃ s', proc.semantics.lts.Step s₁' l₂ s' ∧ proc.semantics.lts.Step s₂' l₁ s')
  := by
  have ⟨haff_nodup, haff_disj⟩ := haff
  by_cases h₁ : s₁' = s₂'
  · exact .inl h₁
  · right
    -- Keep some acronyms so that they don't get expanded
    generalize hs₁' : s₁' = s₁''
    generalize hs₂' : s₂' = s₂''
    cases hstep₁ <;> cases hstep₂
    any_goals
      simp at hlabel₁ hlabel₂
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
        simp at h₁
      · have ⟨hdisj_inputs, hdisj_outputs⟩ := haff_disj ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h])
        simp [hget_i, hget_j, AtomicProc.inputs] at hdisj_inputs hdisj_outputs
        have ⟨chans', hpop₁₂, hpop₂₁⟩ := pop_vals_pop_vals_disj_commute
          (by
            exact hdisj_inputs)
          hpop₁ hpop₂
        have hstep₁' : proc.semantics.lts.Step s₁'' _ _ :=
          .step_op
            (outputVals := outputVals₂)
            (by
              simp [← hs₁']
              exact hmem₂)
            (by
              simp [← hs₁']
              exact pop_vals_push_vals_commute hpop₁₂)
        have hstep₂' : proc.semantics.lts.Step s₂'' _ _ :=
          .step_op
            (outputVals := outputVals₁)
            (by
              simp [← hs₂']
              exact hmem₁)
            (by
              simp [← hs₂']
              exact pop_vals_push_vals_commute hpop₂₁)
        rw [push_vals_push_vals_disj_commute hdisj_outputs] at hstep₁'
        simp [← hs₁'] at hstep₁' ⊢
        simp [← hs₂'] at hstep₂' ⊢
        exact ⟨_, hstep₁', hstep₂'⟩
    all_goals sorry


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
    WellPermTyped ioSpec ctx'' cont cont' →
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

/-- Introduces a `InterpLabelStep ∘ Guard` step from a single step in the base LTS. -/
theorem guard_interp_label_single
  {S : Type u}
  {lts : Lts S E}
  {Inv : S → Prop}
  {Interp : E → E' → Prop}
  {s s' : S}
  (hstep : lts.Step s e s')
  (hinv₁ : Inv s)
  (hinv₂ : Inv s')
  (hinterp : Interp e e') :
  (lts.Guard Inv).InterpLabelStep Interp s e' s'
:= by
  apply Lts.InterpLabelStep.step hinterp
  apply Lts.Guard.step hinv₁ hinv₂ hstep

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
      ((fn'.semantics.guard Config.DisjointTokens).interpLabel
          (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).init
  := by
  simp [Fn.semantics, Semantics.guard, Semantics.interpLabel, Config.init]
  simp [Fn.WellPermTyped] at hwt
  and_intros
  · simp [hwt]
  · simp [hwt]
  · simp [Config.DisjointTokens, VarMap.DisjointTokens, VarMap.getVar, VarMap.empty]
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
      ((fn'.semantics.guard Config.DisjointTokens).interpLabel
        (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep
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
  simp [Fn.semantics, Semantics.guard, Semantics.interpLabel, Config.init]
  have hstep₂ :
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.Step
      s₂ (.input args) _ :=
    guard_interp_label_single
      (.step_init
        (args := (args.map .inl).push (.inr ioSpec.pre))
        hcont₂)
      hdisj
      (by exact var_map_init_disjoint_tokens)
      (by
        apply SpecLabelInterp.spec_input (tok := ioSpec.pre)
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
      ((fn'.semantics.guard Config.DisjointTokens).interpLabel
        (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep
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
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.Step
      s₂ _ _ :=
    guard_interp_label_single
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
      (SpecLabelInterp.spec_join (by rfl) (by rfl) hacq₃)
  -- Run the actual return expression
  have hsteps₂ :
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ (.output retVals) _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_interp_label_single
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
        simp [VarMap.empty, VarMap.getVar, VarMap.DisjointTokens])
      (by
        apply SpecLabelInterp.spec_output
        apply pcm.eq_refl))
  simp at hsteps₂
  exact ⟨_, hsteps₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · simp [VarMap.empty, VarMap.getVar, VarMap.DisjointTokens]
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
      ((fn'.semantics.guard Config.DisjointTokens).interpLabel
        (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep
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
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.Step
      s₂ _ _ :=
    guard_interp_label_single
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
      (SpecLabelInterp.spec_join (by rfl) (by rfl) hacq₃)
  -- Run the actual return expression
  have hsteps₂ :
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ .τ _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_interp_label_single
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
      SpecLabelInterp.spec_tau)
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
      ((fn'.semantics.guard Config.DisjointTokens).interpLabel
        (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep
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
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.Step
      s₂ .τ _ :=
    guard_interp_label_single
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
      (SpecLabelInterp.spec_join (by rfl) (by rfl) hacq₃)
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
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep .τ
      s₂ (.yield op inputVals outputVals) _ := (Lts.WeakStep.single hstep₂).tail_non_tau
    (guard_interp_label_single
      hstep₂'
      (by
        simp [hs₂']
        -- TODO: remove tokens and add new tokens
        sorry)
      (by
        simp [hs₂']
        sorry)
      (by
        apply SpecLabelInterp.spec_yield
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
        and_intros; exact hwt'
        sorry
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
      ((fn'.semantics.guard Config.DisjointTokens).interpLabel
        (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.WeakStep
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
    ((fn'.semantics.guard _).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.Step
      s₂ .τ _ :=
    guard_interp_label_single
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
      SpecLabelInterp.spec_tau
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
    (fn'.semantics.guard Config.DisjointTokens).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))
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
