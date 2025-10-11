import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Reasoning about the determinancy of semantics. -/

namespace Wavelet.Semantics

open Semantics

/-- Restricts an LTS by imposing a state invariant,
and also transforms the label. -/
inductive Lts.Guard {S} (InvS : S → Prop) (InvE : E → E' → Prop) (lts : Lts S E) : Lts S E' where
  | step :
    InvS s → InvE e e' → InvS s' →
    lts.Step s e s' →
    Guard InvS InvE lts s e' s'

/-- Guard the transition of a semantics with the given invariant. -/
def guard
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (InvS : sem.S → Prop)
  (InvE : Label Op V m n → Label Op' V' m' n' → Prop) :
  Semantics Op' V' m' n' :=
  {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.Guard InvS InvE,
    -- TODO: this is actually not true,
    -- maybe remove this requirement?
    yields_functional := sorry
  }

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
  | split
  | join

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
    | .split => 1
    | .join => 2
  ω | .op o => arity.ω o + 1
    | .split => 2
    | .join => 1

/-- Interprets the labels with ghost values using the base operators,
but with dynamic checks for ghost tokens satisfying the specs. -/
inductive SpecLabelInv [Arity Op] [PCM T]
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
    SpecLabelInv opSpec ioSpec
      (.yield (.op op) inputs' outputs')
      (.yield op inputs outputs)
  -- NOTE: the exact split of permissions is
  -- intentionally left unspecified, because
  -- we want this to be dynamic without restricting
  -- to a static annotation.
  | spec_split
    {inputs : Vector (V ⊕ T) 1}
    {outputs : Vector (V ⊕ T) 2} :
    inputs[0] = .inr tok₁ →
    outputs[0] = .inr tok₂ →
    outputs[1] = .inr tok₃ →
    tok₁ ≡ tok₂ ⊔ tok₃ →
    SpecLabelInv opSpec ioSpec
      (.yield .split inputs outputs) .τ
  | spec_join
    {inputs : Vector (V ⊕ T) 2}
    {outputs : Vector (V ⊕ T) 1} :
    inputs[0] = .inr tok₁ →
    inputs[1] = .inr tok₂ →
    outputs[0] = .inr tok₃ →
    tok₃ ≡ tok₁ ⊔ tok₂ →
    SpecLabelInv opSpec ioSpec
      (.yield .join inputs outputs) .τ
  | spec_input :
    vals'.pop = vals.map .inl →
    vals'.back = .inr tok →
    tok ≡ ioSpec.pre vals →
    SpecLabelInv opSpec ioSpec
      (.input vals') (.input vals)
  | spec_output :
    vals'.pop = vals.map .inl →
    vals'.back = .inr tok →
    tok ≡ ioSpec.post vals →
    SpecLabelInv opSpec ioSpec
      (.output vals') (.output vals)

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

abbrev FnWithSpec
  [Arity Op] [PCM T]
  (opSpec : Semantics.OpSpec Op V T)
  (_ioSpec : IOSpec V T m n) χ m n
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
  (opSpec : Semantics.OpSpec Op V T)
  (_ioSpec : IOSpec V T m n) χ m n
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
  (fn : FnWithSpec opSpec ioSpec χ m n)
  (hwf : fn.AffineVar) :
  fn.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
    ≲ᵣ (compileFn (by simp) fn).semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
  := sorry

theorem sim_guard_label
  [Arity Op] [Arity Op']
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  [InterpConsts V']
  {sem₁ sem₂ : Semantics Op V m n}
  {InvE : Label Op V m n → Label Op' V' m' n' → Prop}
  (htau : InvE .τ .τ)
  (hinput : ∀ {vals l}, InvE (.input vals) l → l.isSilent ∨ l.isInput)
  (houtput : ∀ {vals l}, InvE (.output vals) l → l.isSilent ∨ l.isOutput)
  (hyield : ∀ {op inputs outputs l}, InvE (.yield op inputs outputs) l → l.isSilent ∨ l.isYield)
  (hsim : sem₁ ≲ᵣ sem₂) :
  sem₁.guard (λ _ => True) InvE ≲ᵣ sem₂.guard (λ _ => True) InvE
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    simp [Semantics.guard] at hstep
    cases hstep with | step _ hlabel _ hstep =>
    rename Label Op V m n => l'
    have ⟨s₂', hstep_s₂, hR₂⟩ := hsim.sim_step _ _ _ _ hR hstep
    exists s₂'
    constructor
    · cases l' with
      | yield => sorry
      | input =>
        cases hstep_s₂ with | step_input hstep_input_s₂ hstep_tau =>
        sorry
      | output => sorry
      | τ => sorry
    · exact hR₂

/-- Type check a function against the given specs,
and insert split/join to concretize the flow of permissions. -/
def typeCheck
  [Arity Op]
  [PCM T]
  (opSpec : Semantics.OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  (fn : Fn Op χ V m n) : Option (FnWithSpec opSpec ioSpec χ m n) := sorry

/-- Type soundness theorem formulated as a simulation. -/
theorem fn_progress
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (fn : Fn Op χ V m n)
  {fn' : FnWithSpec opSpec ioSpec χ m n}
  (hwf : fn.AffineVar)
  (hwt : typeCheck opSpec ioSpec fn = some fn') :
  fn.semantics ≲ᵣ fn'.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
  := sorry

/-- Erase ghost tokens. -/
def eraseGhost
  [Arity Op] [PCM T]
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec ioSpec χ m n) : Proc Op χ V m n
  := sorry

/-- Backward simulation for `eraseGhost`. -/
theorem sim_erase_ghost
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec ioSpec χ m n) :
  (eraseGhost proc).semantics ≲ᵣ
    proc.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
  := sorry

/-- Forward simulation for liveness. -/
theorem sim_erase_ghost_forward
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  (proc : ProcWithSpec opSpec ioSpec χ m n) :
  proc.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
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
  {proc : ProcWithSpec opSpec ioSpec χ m n}
  {trace₁ trace₂ : Trace (Label Op V m n)}
  {sem : Semantics Op V m n}
  {s₁ s₂ : sem.S}
  {hguard : sem = proc.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)}
  (htrace₁ : sem.lts.Star sem.init trace₁ s₁)
  (htrace₂ : sem.lts.Star sem.init trace₂ s₂) :
  ∃ trace₁' trace₂' s₁' s₂',
    sem.lts.Star s₁ trace₁' s₁' ∧
    sem.lts.Star s₂ trace₂' s₂' ∧
    trace₁ ++ trace₁' = trace₂ ++ trace₂' ∧
    s₁' = s₂'
  := sorry

end Wavelet.Compile
