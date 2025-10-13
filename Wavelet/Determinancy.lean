import Mathlib.Control.ULiftable

import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Reasoning about the determinancy of semantics. -/

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
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) → Label Op V m n → Prop where
  | spec_yield :
    inputs'.pop = inputs.map .inl →
    outputs'.pop = outputs.map .inl →
    inputs'.back = .inr tok₁ →
    outputs'.back = .inr tok₂ →
    tok₁ ≡ opSpec.pre op inputs →
    tok₂ ≡ opSpec.post op inputs outputs →
    SpecLabelInterp opSpec ioSpec
      (.yield (.op op) inputs' outputs')
      (.yield op inputs outputs)
  -- NOTE: the exact output split of permissions
  -- is intentionally left unspecified, because
  -- we want this to be dynamic without restricting
  -- to a static annotation.
  | spec_join
    {inputs : Vector (V ⊕ T) k}
    {toks : Vector T k}
    {outputs : Vector (V ⊕ T) 2} :
    inputs = toks.map .inr →
    outputs[0] = .inr tok₁ →
    outputs[1] = .inr tok₂ →
    tok₁ ⊔ tok₂ ≡ PCM.sum toks.toList →
    SpecLabelInterp opSpec ioSpec
      (.yield (.join k) inputs outputs) .τ
  | spec_input :
    vals'.pop = vals.map .inl →
    vals'.back = .inr tok →
    tok ≡ ioSpec.pre vals →
    SpecLabelInterp opSpec ioSpec
      (.input vals') (.input vals)
  | spec_output :
    vals'.pop = vals.map .inl →
    vals'.back = .inr tok →
    tok ≡ ioSpec.post vals →
    SpecLabelInterp opSpec ioSpec
      (.output vals') (.output vals)
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

end Wavelet.Semantics

namespace Wavelet.Seq

open Semantics Compile

def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  ∀ x₁ x₂ t₁ t₂,
    x₁ ≠ x₂ →
    c.vars.getVar x₁ = some (.inr t₁) →
    c.vars.getVar x₂ = some (.inr t₂) →
    t₁ ⊥ t₂

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
fn.semantics
  ≲ᵣ fn'.semantics.guard ...
  ≲ᵣ (compileFn ... fn').semantics.guard ...
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
-/
theorem guarded_confluence
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {proc : ProcWithSpec opSpec χ m n}
  {trace₁ trace₂ : Trace (Label Op V m n)}
  {sem : Semantics Op V m n}
  {s₁ s₂ : sem.S}
  {hguard : sem = (proc.semantics.guard Config.DisjointTokens).interpLabel (SpecLabelInterp opSpec ioSpec)}
  (htrace₁ : sem.lts.Star sem.init trace₁ s₁)
  (htrace₂ : sem.lts.Star sem.init trace₂ s₂) :
  ∃ trace₁' trace₂' s₁' s₂',
    sem.lts.Star s₁ trace₁' s₁' ∧
    sem.lts.Star s₂ trace₂' s₂' ∧
    trace₁ ++ trace₁' = trace₂ ++ trace₂' ∧
    s₁' = s₂'
  := sorry

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

inductive TypedName χ where
  | var (x : χ)
  | tok (i : Nat)
  deriving DecidableEq

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
      (toks.toVector.map .tok)
      #v[.tok numToks, .tok (numToks + 1)]
      (.ret ((args.map .var).push (.tok numToks)))
  | .tail args => do
    let toks ← tryAcquire ctx numToks ioSpec.pre
    return .op (.join toks.length)
      (toks.toVector.map .tok)
      #v[.tok numToks, .tok (numToks + 1)]
      (.tail ((args.map .var).push (.tok numToks)))
  | .op o args bind cont => do
    let toks ← tryAcquire ctx numToks (opSpec.pre o)
    let tok₁ := .tok numToks
    let tok₂ := .tok (numToks + 1)
    let tok₃ := .tok (numToks + 2)
    let newCtx₁ := λ i => if i ∈ toks then none else ctx i
    let newCtx₂ := Function.update newCtx₁ numToks (some (opSpec.pre o))
    let sumToks ← toks.foldlM (λ acc i => return acc ⊔ (← ctx i)) PCM.zero
    if h : opSpec.pre o ≤ sumToks then
      let newCtx₃ := Function.update newCtx₂ (numToks + 1) (some (PCM.sub sumToks (opSpec.pre o) h))
      let newCtx₄ := Function.update newCtx₃ (numToks + 2) (some (opSpec.post o))
      return .op (.join toks.length) (toks.toVector.map .tok) #v[tok₁, tok₂]
        (.op (.op o)
          ((args.map .var).push tok₁)
          ((bind.map .var).push tok₃)
          (← typeCheckInternal opSpec ioSpec newCtx₄ (numToks + 3) cont))
    else
      none
  | .br cond left right => do
    let left' ← typeCheckInternal opSpec ioSpec ctx numToks left
    let right' ← typeCheckInternal opSpec ioSpec ctx numToks right
    return .br (.var cond) left' right'

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
    params := (fn.params.map TypedName.var).push (TypedName.tok 0),
    body := ← typeCheckInternal opSpec ioSpec
      (Function.update (Function.const _ none) 0 (some ioSpec.pre)) 1 fn.body,
  }

/-- Map from ghost variable names to their concrete permission. -/
structure PermCtx T where
  map : Nat → Option T
  numVars : Nat

/-- Defines when a (disjoint) list of variable indices
has a total permission equal to the sum of `req` and `rem`. -/
def PermCtx.Acquire
  [PCM T]
  (ctx : PermCtx T) (req : T) (rem : T)
  (idxs : List Nat) : Prop :=
  idxs.Nodup ∧
  ∃ ts : List T,
    idxs.mapM ctx.map = some ts ∧
    req ⊔ rem ≤ PCM.sum ts

def PermCtx.getVar
  [PCM T] (ctx : PermCtx T) (idx : Nat) : Option T := ctx.map idx

/-- Insert `n` new permission tokens and return the fresh indices -/
def PermCtx.insertVars
  [PCM T]
  (ctx : PermCtx T) (tys : Vector T n) :
  Vector Nat n × PermCtx T :=
  let newIdxs := (Vector.range n).map (· + ctx.numVars)
  (
    newIdxs,
    {
      map idx :=
        if _ : ctx.numVars ≤ idx ∧ idx < ctx.numVars + n then
          some (tys[idx - ctx.numVars]'(by omega))
        else ctx.map idx,
      numVars := ctx.numVars + n
    }
  )

def PermCtx.removeVars
  [PCM T]
  (ctx : PermCtx T) (idxs : List Nat) : PermCtx T :=
  { ctx with map := λ i => if i ∈ idxs then none else ctx.map i }

/-- Initial context with a single permission variable. -/
def PermCtx.init
  [PCM T] (init : T) : PermCtx T :=
  {
    map idx := if idx = 0 then some init else none,
    numVars := 1
  }

/-- Relational definition for a function to be well-typed
as a more elaborated `FnWithSpec` with explicit permissions. -/
inductive Expr.WellPermTyped
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T) :
  PermCtx T → Expr Op χ m n →
  ExprWithSpec (opSpec.toOpSpec V) (TypedName χ) m n → Prop where
  | wpt_ret :
    ctx.Acquire ioSpec.post rem toks →
    ctx.insertVars #v[ioSpec.post, rem] = (joined, ctx') →
    toks' = toks.map .tok →
    vars' = (vars.map .var).push (.tok joined[0]) →
    WellPermTyped ioSpec ctx
      (.ret vars)
      (.op (.join toks'.length) toks'.toVector (joined.map .tok)
        (.ret vars'))
  | wpt_tail :
    -- The returned permission should exactly match since the token is non-dependent
    ctx.Acquire ioSpec.pre rem toks →
    ctx.insertVars #v[ioSpec.pre, rem] = (joined, ctx') →
    toks' = toks.map .tok →
    args' = (args.map .var).push (.tok joined[0]) →
    WellPermTyped ioSpec ctx
      (.tail args)
      (.op (.join toks'.length) toks'.toVector (joined.map .tok)
        (.tail args'))
  | wpt_op {bind} :
    ctx.Acquire (opSpec.pre o) rem toks →
    ctx.removeVars toks = ctx' →
    ctx'.insertVars #v[opSpec.pre o, rem, opSpec.post o] = (joined, ctx'') →
    WellPermTyped ioSpec ctx'' cont cont' →
    toks' = toks.map .tok →
    WellPermTyped ioSpec ctx
      (.op o args bind cont)
      (.op (.join toks'.length) -- First call join to collect required permissions
        toks'.toVector
        #v[.tok joined[0], .tok joined[1]]
        (.op (.op o) -- Then call the actual operator
        ((args.map .var).push (.tok joined[0]))
        ((bind.map .var).push (.tok joined[2])) cont'))
  | wpt_br :
    WellPermTyped ioSpec ctx left left' →
    WellPermTyped ioSpec ctx right right' →
    WellPermTyped ioSpec ctx (.br cond left right) (.br (.var cond) left' right')

def Fn.WellPermTyped
  [Arity Op] [PCM T]
  {opSpec : SimpleOpSpec Op T}
  (ioSpec : SimpleIOSpec T)
  (fn : Fn Op χ V m n)
  (fn' : FnWithSpec (opSpec.toOpSpec V) (TypedName χ) m n) :
  Prop :=
  fn'.params = (fn.params.map .var).push (.tok 0) ∧
  Expr.WellPermTyped ioSpec (.init (ioSpec.pre)) fn.body fn'.body

def SimRel.ghostVars
  {χ : Type u} {V : Type v} {T : Type w}
  [PCM T]
  (vars : VarMap χ V)
  (ctx : PermCtx T) :
  VarMap (TypedName χ) (V ⊕ T) :=
  λ var =>
    match var with
    | .var v => return .inl (← ULiftable.up (vars.getVar v)).down
    | .tok i => return .inr (← ULiftable.up (ctx.getVar i)).down

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
      s₂.vars = SimRel.ghostVars s₁.vars ctx)

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
  · simp [Config.DisjointTokens, VarMap.getVar, VarMap.empty]
  · simp
  · simp

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
  have hstep₂ : fn'.semantics.lts.Step s₂ _ _ :=
    .step_init
      (args := (args.map .inl).push (.inr ioSpec.pre))
      (c := s₂) hcont₂
  replace hstep₂ : (fn'.semantics.guard Config.DisjointTokens).lts.Step s₂ _ _ :=
    .step hdisj (by
      simp [Config.DisjointTokens, VarMap.getVar]
      -- TODO: should be easy, only added one token
      sorry) hstep₂
  replace hstep₂ :
    ((fn'.semantics.guard Config.DisjointTokens).interpLabel
      (SpecLabelInterp (opSpec.toOpSpec V) (ioSpec.toIOSpec m n))).lts.Step
      s₂ (.input args) _ :=
    .step (by
      apply SpecLabelInterp.spec_input (tok := ioSpec.pre)
      · simp
      · simp
      · simp [SimpleIOSpec.toIOSpec]
        apply pcm.eq_refl) hstep₂
  exact ⟨_, .single hstep₂,
    by
      and_intros
      · simp [hwt_fn.1]
      · simp [hwt_fn.2]
      · -- TODO same as the TODO above
        sorry
      · simp
      · simp
        exists PermCtx.init ioSpec.pre
        sorry
  ⟩

theorem sim_get_vars
  [PCM T]
  {ctx : PermCtx T}
  (hget : vars.getVars xs = some vs) :
  (SimRel.ghostVars vars ctx).getVars (xs.map TypedName.var) = some (vs.map .inl)
  := sorry

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
    have ⟨ctx, hvars⟩ := hcont _ hexpr
    have := sim_get_vars (ctx := ctx) hget_vars

    sorry

/-- Type soundness theorem formulated as a simulation. -/
theorem sim_type_check
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
  -- (hwt : typeCheck opSpec ioSpec fn = some fn') :
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
    | init => apply sim_type_check_input hsim h₁ hstep
    | expr => sorry

end Wavelet.Seq
