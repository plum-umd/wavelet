import Wavelet.Semantics.Defs
import Wavelet.Semantics.OpInterp
import Wavelet.Semantics.Guard
import Wavelet.Semantics.PCM

/-! Putting a resource specification on an operator set. -/

namespace Wavelet.Semantics

/-- PCM specification of an operator set -/
structure OpSpec Op V T [Arity Op] [PCM T] where
  pre : (op : Op) → Vector V (Arity.ι op) → T
  post : (op : Op) → Vector V (Arity.ι op) → Vector V (Arity.ω op) → T
  frame_preserving : ∀ op inputs outputs, pre op inputs ⟹ post op inputs outputs

/-- Two labels are compatible if their inputs correspond to disjoint resources
and are deterministic. -/
def OpSpec.CompatLabels
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T) :
  RespLabel Op V → RespLabel Op V → Prop
  | .respond op₁ inputs₁ _, .respond op₂ inputs₂ _ =>
    (opSpec.pre op₁ inputs₁) ⊥ (opSpec.pre op₂ inputs₂)

def OpSpec.Sound
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T)
  (interp : OpInterp Op V) : Prop :=
  ∀ {s s₁ s₂ l₁ l₂},
    -- Confluence like the following is not sufficient, since we
    -- need to allow firing the same operator twice.
    -- `interp.lts.StronglyConfluentAt (OpSpec.CompatLabels opSpec) s`
    interp.lts.Step s l₁ s₁ →
    interp.lts.Step s l₂ s₂ →
    opSpec.CompatLabels l₁ l₂ →
    ∃ s',
      interp.lts.Step s₁ l₂ s' ∧
      interp.lts.Step s₂ l₁ s'

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
inductive OpSpec.Guard
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) →
  Label Op V m n → Prop where
  | spec_yield
    {op}
    {inputs : Vector V (Arity.ι op)}
    {outputs : Vector V (Arity.ω op)} :
    tok₁ ≡ opSpec.pre op inputs →
    tok₂ = opSpec.post op inputs outputs → -- Using `=` here for less determinism
    Guard opSpec ioSpec
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
    Guard opSpec ioSpec
      (.yield (.join k) (toks.map .inr) outputs) .τ
  | spec_input {tok vals} :
    tok ≡ ioSpec.pre vals →
    Guard opSpec ioSpec
      (.input ((vals.map .inl).push (.inr tok))) (.input vals)
  | spec_output :
    tok ≡ ioSpec.post vals →
    Guard opSpec ioSpec
      (.output ((vals.map .inl).push (.inr tok))) (.output vals)
  | spec_tau :
    Guard opSpec ioSpec .τ .τ

/--
Same signature as `OpSpec.TrivGuard` but does not dynamically
check the well-formedness of the tokens.
-/
inductive OpSpec.TrivGuard [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) →
  Label Op V m n → Prop where
  | spec_yield :
    opSpec.TrivGuard
      (.yield (.op op) ((inputs.map .inl).push tok₁) ((outputs.map .inl).push tok₂))
      (.yield op inputs outputs)
  | spec_join : opSpec.TrivGuard (.yield (.join k) toks outputs) .τ
  | spec_input : opSpec.TrivGuard (.input ((vals.map .inl).push tok)) (.input vals)
  | spec_output : opSpec.TrivGuard (.output ((vals.map .inl).push tok)) (.output vals)
  | spec_tau : opSpec.TrivGuard .τ .τ

instance
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n} : LawfulGuard (opSpec.Guard ioSpec) where
  guard_tau := .spec_tau
  guard_tau_only h := by cases h; rfl
  guard_input h := by cases h; simp
  guard_output h := by cases h; simp
  guard_yield h := by cases h <;> simp

instance
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T} : LawfulGuard (opSpec.TrivGuard (m := m) (n := n)) where
  guard_tau := .spec_tau
  guard_tau_only h := by cases h; rfl
  guard_input h := by cases h; simp
  guard_output h := by cases h; simp
  guard_yield h := by cases h <;> simp

end Wavelet.Semantics
