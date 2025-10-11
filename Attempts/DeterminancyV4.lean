import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Reasoning about the determinancy of semantics. -/

namespace Wavelet.Semantics

open Semantics

/-
Three pieces:
- A state invariant `P : S → Prop` on each semantics
- A guarded transition that enforces the invariant on the base transition
- Proof obligations
  - Simulation between guarded transitions
  - Invariant implies compatibility relation of values (obligation of the semantics)
  - Compatibility relation implies commutative operators (obligation of op interp)
  - Typing in Seq implies progress in the guarded transition

Maybe just specialize to PCMs?

class WithToken V where
  token : V → PCM

State invariant on Seq: for any two values v₁ v₂ in the config, token v₁ ⊥ token v₂
-/

/-
Maybe easier to directly do the Label translation in `GuardedLts`?
-/

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

/-- PCM specification of an operator set.
TODO: generalize to dependent tokens. -/
structure OpSpec Op T [Arity Op] [PCM T] where
  pre : (op : Op) → T
  post : (op : Op) → T
  frame_preserving : ∀ op, pre op ⟹ post op

/-- Specification on input/output labels.
TODO: generalize to dependent tokens. -/
structure IOSpec T [PCM T] where
  pre : T
  post : T

/-- Augments the operator set with an additional ghost argument
to pass a PCM token, as well as two operators to split and join PCMs. -/
inductive WithSpec (Op : Type u) [Arity Op] [PCM T] (spec : OpSpec Op T) where
  | op (op : Op)
  | join (k : Nat)

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
  {spec : OpSpec Op T} :
  Arity (WithSpec Op spec) where
  ι | .op o => arity.ι o + 1
    | .join n => n
  ω | .op o => arity.ω o + 1
    | .join _ => 2

/-- Interprets the labels with ghost values using the base operators,
but with dynamic checks for ghost tokens satisfying the specs. -/
inductive SpecLabelInv [Arity Op] [PCM T]
  (opSpec : OpSpec Op T)
  (ioSpec : IOSpec T) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) → Label Op V m n → Prop where
  | spec_yield :
    inputs'.pop = inputs.map .inl →
    outputs'.pop = outputs.map .inl →
    inputs'.back = .inr tok₁ →
    outputs'.back = .inr tok₂ →
    tok₁ ≡ opSpec.pre op →
    tok₂ ≡ opSpec.post op →
    SpecLabelInv opSpec ioSpec
      (.yield (.op op) inputs' outputs')
      (.yield op inputs outputs)
  -- NOTE: the exact split of permissions is
  -- intentionally left unspecified, because
  -- we want this to be dynamic without restricting
  -- to a static annotation.
  | spec_join
    {inputs : Vector (V ⊕ T) k}
    {toks : Vector T k}
    {outputs : Vector (V ⊕ T) 2} :
    inputs = toks.map .inr →
    outputs[0] = .inr tok₁ →
    outputs[1] = .inr tok₂ →
    tok₁ ⊔ tok₂ ≡ toks.foldl (· ⊔ ·) zero →
    SpecLabelInv opSpec ioSpec
      (.yield (.join k) inputs outputs) .τ
  | spec_input :
    vals'.pop = vals.map .inl →
    vals'.back = .inr tok →
    tok ≡ ioSpec.pre →
    SpecLabelInv opSpec ioSpec
      (.input vals') (.input vals)
  | spec_output :
    vals'.pop = vals.map .inl →
    vals'.back = .inr tok →
    tok ≡ ioSpec.post →
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
  (opSpec : Semantics.OpSpec Op T)
  (_ioSpec : IOSpec T) χ V m n
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
  (opSpec : Semantics.OpSpec Op T)
  (_ioSpec : IOSpec T) χ V m n
  := Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow

theorem sim_compile_fn'
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  {opSpec : Semantics.OpSpec Op T}
  {ioSpec : IOSpec T}
  (fn : FnWithSpec opSpec ioSpec χ V m n)
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
def typeCheckInternal
  [Arity Op]
  [PCM T]
  (opSpec : Semantics.OpSpec Op T)
  (ioSpec : IOSpec T)
  (ctx : Nat → Option T)
  (numToks : Nat) :
  Expr Op χ m n → Option (Expr (WithSpec Op opSpec) (TypedName χ) (m + 1) (n + 1))
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
    let newCtx₃ := Function.update newCtx₂ (numToks + 1) sorry -- sum of toks - opSpec.pre o
    let newCtx₄ := Function.update newCtx₃ (numToks + 2) (some (opSpec.post o))
    return .op (.join toks.length) (toks.toVector.map .tok) #v[tok₁, tok₂]
      (.op (.op o)
        ((args.map .var).push tok₁)
        ((bind.map .var).push tok₃)
        (← typeCheckInternal opSpec ioSpec newCtx₄ (numToks + 3) cont))
  | .br cond left right => do
    let left' ← typeCheckInternal opSpec ioSpec ctx numToks left
    let right' ← typeCheckInternal opSpec ioSpec ctx numToks right
    return .br (.var cond) left' right'

/-- Type check a function against the given specs,
and insert split/join to concretize the flow of permissions. -/
def typeCheck
  [Arity Op]
  [PCM T]
  (opSpec : Semantics.OpSpec Op T)
  (ioSpec : IOSpec T)
  (fn : Fn Op χ V m n) :
  Option (FnWithSpec opSpec ioSpec (TypedName χ) V m n)
  := return {
    params := (fn.params.map TypedName.var).push (TypedName.tok 0),
    body := ← typeCheckInternal opSpec ioSpec
      (Function.update (Function.const _ none) 0 (some ioSpec.pre)) 1 fn.body,
  }

/-- Type soundness theorem formulated as a simulation. -/
theorem fn_progress
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  {opSpec : Semantics.OpSpec Op T}
  {ioSpec : IOSpec T}
  (fn : Fn Op χ V m n)
  {fn' : FnWithSpec opSpec ioSpec (TypedName χ) V m n}
  (hwf : fn.AffineVar)
  (hwt : typeCheck opSpec ioSpec fn = some fn') :
  fn.semantics ≲ᵣ fn'.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
  := sorry

/-- Erase ghost tokens. -/
def eraseGhost
  [Arity Op] [PCM T]
  {opSpec : Semantics.OpSpec Op T}
  {ioSpec : IOSpec T}
  (proc : ProcWithSpec opSpec ioSpec χ V m n) : Proc Op χ V m n
  := sorry

/-- Backward simulation for `eraseGhost`. -/
theorem sim_erase_ghost
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op T}
  {ioSpec : IOSpec T}
  (proc : ProcWithSpec opSpec ioSpec χ V m n) :
  (eraseGhost proc).semantics ≲ᵣ
    proc.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
  := sorry

/-- Or maybe forward simulation? -/
theorem sim_erase_ghost_forward
  [Arity Op] [PCM T]
  [InterpConsts V]
  [DecidableEq χ]
  [DecidableEq χ']
  {opSpec : Semantics.OpSpec Op T}
  {ioSpec : IOSpec T}
  (proc : ProcWithSpec opSpec ioSpec χ V m n) :
  proc.semantics.guard Config.DisjointTokens (SpecLabelInv opSpec ioSpec)
    ≲ᵣ (eraseGhost proc).semantics
  := sorry

/-
We now have

fn.semantics
  ≲ᵣ fn'.semantics.guard ...
  ≲ᵣ (compileFn ... fn').semantics.guard ...
  ... some optimization passes
  ≲ᵣ proc.semantics.guard ...
  ≲ᵣ (eraseGhost proc).semantics

and also

(eraseGhost proc).semantics
  ≲ᵣ proc.semantics.guard ...

Final correctness theorem will say something like:

For any trace of `fn.semantics`
there exists a corresponding trace `T₁` of `proc.semantics.guard ...`

For any trace of `(eraseGhost proc).semantics`
there exists a corresponding trace `T₂` of `proc.semantics.guard ...`

If `T₁` "dominates" `T₂`, then `T₂` converge to `T₁`.

(But this doesn't say anything about deadlock?)

-/

end Wavelet.Compile
