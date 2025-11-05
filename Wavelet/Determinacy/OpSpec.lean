import Wavelet.Semantics.Defs
import Wavelet.Semantics.OpInterp
import Wavelet.Semantics.Guard

import Wavelet.Seq.Fn
import Wavelet.Seq.Prog
import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.EqMod

import Wavelet.Determinacy.PCM

/-! Putting a resource specification on an operator set. -/

namespace Wavelet.Determinacy

open Semantics

/-- PCM specification of an operator set -/
structure OpSpec Op V T [Arity Op] where
  pre : (op : Op) → Vector V (Arity.ι op) → T
  post : (op : Op) → Vector V (Arity.ι op) → Vector V (Arity.ω op) → T

/-- Two labels are compatible if their inputs correspond to disjoint resources
and are deterministic. -/
def OpSpec.CompatLabels
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T) :
  RespLabel Op V → RespLabel Op V → Prop
  | .respond op₁ inputs₁ _, .respond op₂ inputs₂ _ =>
    (opSpec.pre op₁ inputs₁) ⊥ (opSpec.pre op₂ inputs₂)

def OpSpec.Valid
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T) : Prop :=
  (∀ op inputs, ✓ (opSpec.pre op inputs)) ∧
  (∀ op inputs outputs, ✓ (opSpec.post op inputs outputs))

/-- The given operator interpretation is confluent for operator
firings that are compatible according to the `OpSpec`. -/
def OpSpec.Confluent
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

/-- For any operator and inputs/outputs, the change from
the pre-condition to the post-condition is valid in any PCM frame. -/
def OpSpec.FramePreserving
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T) : Prop :=
  (∀ op inputs outputs,
    opSpec.pre op inputs ⟹ opSpec.post op inputs outputs)

/-- Specification on input/output labels. -/
structure IOSpec V T m n where
  k : Nat
  neZero : NeZero k
  -- We allow multiple input permission tokens for pipelining.
  pre : Vector V m → Vector T k
  -- This can only depend on the outputs, due
  -- to a technical issue that we can't access
  -- the input values at an output event.
  post : Vector V n → T

instance {ioSpec : IOSpec V T m n} : NeZero ioSpec.k := ioSpec.neZero

def IOSpec.Valid
  [PCM T] (ioSpec : IOSpec V T m n) : Prop :=
  (∀ inputs, ✓ PCM.sum (ioSpec.pre inputs).toList) ∧
  (∀ outputs, ✓ ioSpec.post outputs)

/-- Augments the operator set with an additional ghost argument
to pass a PCM token, as well as two operators to split and join PCMs. -/
inductive WithSpec {T : Type u} (Op : Type u) [Arity Op] (spec : OpSpec Op V T) where
  | op (ghost : Bool) (op : Op)
  | join
      (k : Nat) -- Number of input tokens to combine
      (l : Nat) -- Number of values that the token depends on
      (req : Vector V l → T)
      [NeZero k]

instance [Arity Op] [Repr Op] {opSpec : OpSpec Op V T} : Repr (WithSpec Op opSpec) where
  reprPrec
    | .op true o, _ => "WithSpec.op true " ++ repr o
    | .op false o, _ => "WithSpec.op false " ++ repr o
    | WithSpec.join k l _, _ => "WithSpec.join " ++ repr k ++ " " ++ repr l

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
  isClonable
    | .inl v => left.isClonable v
    | .inr _ => false
  bool_clonable b := left.bool_clonable b

instance instArityWithSpec
  [arity : Arity Op]
  {spec : OpSpec Op V T} :
  Arity (WithSpec Op spec) where
  ι | .op true o => arity.ι o + 1
    | .op false o => arity.ι o
    | WithSpec.join k l _ => k + l
  ω | .op _ o => arity.ω o + 1
    | WithSpec.join _ _ _ => 2

instance [Arity Op] [NeZeroArity Op] {spec : OpSpec Op V T} : NeZeroArity (WithSpec Op spec) where
  neZeroᵢ | .op true o => by infer_instance
          | .op false o => by simp [Arity.ι]; infer_instance
          | WithSpec.join k l _ => by
            simp [Arity.ι]
            infer_instance
  neZeroₒ | .op _ o => by infer_instance
          | WithSpec.join _ _ _ => by infer_instance

/-- Constructs the desired operator inputs depending on whether it accepts ghost tokens. -/
def WithSpec.opInputs
  [Arity Op]
  {opSpec : OpSpec Op V T}
  (ghost : Bool) (o : Op)
  (inputs : Vector V (Arity.ι o))
  (tok : T) : Vector (V ⊕ T) (Arity.ι (WithSpec.op (spec := opSpec) ghost o)) :=
  if h : ghost then
    ((inputs.map .inl).push (.inr tok)).cast (by simp [h]; rfl)
  else
    (inputs.map .inl).cast (by simp [h]; rfl)

@[simp]
theorem WithSpec.opInputs.inj
  [Arity Op] {o : Op}
  {opSpec : OpSpec Op V T}
  {inputs₁ : Vector V (Arity.ι o)}
  {inputs₂ : Vector V (Arity.ι o)} :
    (opInputs (opSpec := opSpec) ghost o inputs₁ tok₁ =
      opInputs (opSpec := opSpec) ghost o inputs₂ tok₂)
    ↔ (inputs₁ = inputs₂ ∧ (ghost → tok₁ = tok₂))
  := by
  constructor
  · intros h
    if h₁ : ghost then
      subst h₁
      simp [opInputs, Vector.push_eq_push] at h
      simp [h]
    else
      simp at h₁
      subst h₁
      simp [opInputs] at h
      simp [h]
  · intros h
    have ⟨h₁, h₂⟩ := h
    if h₃ : ghost then
      simp [h₃] at h₂
      subst h₁ h₂
      rfl
    else
      simp [h₁, opInputs, h₃]

/-- Interprets the labels with ghost values using the base operators,
but with dynamic checks for ghost tokens satisfying the specs. -/
inductive OpSpec.Guard
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + ioSpec.k) (n + 1) →
  Label Op V m n → Prop where
  | spec_yield
    {op} {ghost : Bool}
    {inputs : Vector V (Arity.ι op)}
    {outputs : Vector V (Arity.ω op)} :
    (¬ ghost → opSpec.pre op inputs = PCM.zero) →
    Guard opSpec ioSpec
      (.yield (.op ghost op)
        (WithSpec.opInputs ghost op inputs (opSpec.pre op inputs))
        ((outputs.map .inl).push (.inr (opSpec.post op inputs outputs))))
      (.yield op inputs outputs)
  | spec_join [NeZero k]
    {toks : Vector T k}
    {vals : Vector V l}
    {outputs : Vector (V ⊕ T) 2} :
    outputs[0] = .inr (req vals) →
    outputs[1] = .inr rem →
    -- For this to be deterministic, we need a `Cancellative` PCM.
    req vals ⊔ rem = PCM.sum toks.toList →
    Guard opSpec ioSpec
      (.yield (.join k l req)
        ((toks.map .inr : Vector (V ⊕ T) k) ++
          (vals.map .inl : Vector (V ⊕ T) l)) outputs) .τ
  | spec_input :
    Guard opSpec ioSpec
      (.input
        ((vals.map .inl  : Vector (V ⊕ T) _) ++
          ((ioSpec.pre vals).map .inr : Vector (V ⊕ T) _)))
      (.input vals)
  | spec_output :
    Guard opSpec ioSpec
      (.output ((vals.map .inl).push (.inr (ioSpec.post vals)))) (.output vals)
  | spec_tau :
    Guard opSpec ioSpec .τ .τ

/--
Same signature as `OpSpec.TrivGuard` but does not dynamically
check the well-formedness of the tokens.
-/
inductive OpSpec.TrivGuard [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + ioSpec.k) (n + 1) →
  Label Op V m n → Prop where
  | triv_yield {op ghost inputs outputs tok₁ tok₂} :
    opSpec.TrivGuard ioSpec
      (.yield (.op ghost op)
        (WithSpec.opInputs ghost op inputs tok₁)
        ((outputs.map .inl).push (.inr tok₂)))
      (.yield op inputs outputs)
  | triv_join [NeZero k]
    {toks : Vector T k}
    {vals : Vector V l}
    {outputs : Vector T 2} :
    opSpec.TrivGuard ioSpec (.yield (.join k l req)
      ((toks.map .inr : Vector (V ⊕ T) k) ++
        (vals.map .inl : Vector (V ⊕ T) l))
      (outputs.map .inr)) .τ
  | triv_input
    {toks : Vector T ioSpec.k} :
    opSpec.TrivGuard ioSpec
      (.input ((vals.map .inl : Vector (V ⊕ T) _) ++ (toks.map .inr : Vector (V ⊕ T) _)))
      (.input vals)
  | triv_output :
    opSpec.TrivGuard ioSpec (.output ((vals.map .inl).push (.inr tok))) (.output vals)
  | triv_tau : opSpec.TrivGuard ioSpec .τ .τ

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
  [Arity Op]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n} : LawfulGuard (opSpec.TrivGuard ioSpec) where
  guard_tau := .triv_tau
  guard_tau_only h := by cases h; rfl
  guard_input h := by cases h; simp
  guard_output h := by cases h; simp
  guard_yield h := by cases h <;> simp

theorem OpSpec.spec_guard_implies_triv_guard
  [Arity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {l₁ l₂} :
    opSpec.Guard ioSpec l₁ l₂ → opSpec.TrivGuard ioSpec l₁ l₂
  | .spec_yield .. => by exact .triv_yield
  | OpSpec.Guard.spec_join .. => by
    rename_i k l req rem _ toks vals outputs h₁ h₂ hsum
    have : outputs = #v[req vals, rem].map .inr := by
      apply Vector.ext
      intros i hi
      match i with
      | 0 => simp [h₁]
      | 1 => simp [h₂]
    simp only [this]
    exact .triv_join
  | .spec_input => by exact .triv_input
  | .spec_output => by exact .triv_output
  | .spec_tau => by exact .triv_tau

def EqModGhost : V ⊕ T → V ⊕ T → Prop
  | .inl v₁, .inl v₂ => v₁ = v₂
  | .inr _, .inr _ => True
  | _, _ => False

instance : IsRefl (V ⊕ T) EqModGhost where
  refl v := by cases v <;> simp [EqModGhost]

instance : IsSymm (V ⊕ T) EqModGhost where
  symm v₁ v₂ := by cases v₁ <;> cases v₂ <;> grind only [EqModGhost]

instance : IsTrans (V ⊕ T) EqModGhost where
  trans v₁ v₂ v₃ := by cases v₁ <;> cases v₂ <;> cases v₃ <;> grind only [EqModGhost]

end Wavelet.Determinacy

namespace Wavelet.Semantics

open Determinacy

abbrev LabelWithSpec
  [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) :=
  Label (WithSpec Op opSpec) (V ⊕ T) (m + ioSpec.k) (n + 1)

end Wavelet.Semantics

/-! Some abbreviations for `Seq`. -/
namespace Wavelet.Seq

open Semantics Determinacy

abbrev ExprWithSpec
  [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) χ
  := Expr (WithSpec Op opSpec) χ (m + ioSpec.k) (n + 1)

abbrev FnWithSpec
  [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) χ
  := Fn (WithSpec Op opSpec) χ (V ⊕ T) (m + ioSpec.k) (n + 1)

/-- A collection of `IOSpec`s for `Fn`s in a `Prog`. -/
abbrev ProgSpec V T (sigs : Sigs k) :=
  (i : Fin k) → IOSpec V T (sigs i).ι (sigs i).ω

def ProgSpec.Valid
  [PCM T] {sigs : Sigs k}
  (progSpec : ProgSpec V T sigs) : Prop := ∀ i, (progSpec i).Valid

abbrev ConfigWithSpec [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) χ
  := Config (WithSpec Op opSpec) χ (V ⊕ T) (m + ioSpec.k) (n + 1)

abbrev extendSigs (sigs : Sigs k) (progSpec : ProgSpec V T sigs) : Sigs k :=
  λ i => { ι := (sigs i).ι + (progSpec i).k, ω := (sigs i).ω + 1 }

instance : NeZeroSigs (extendSigs sigs progSpec) where
  neZeroᵢ i := by simp; infer_instance
  neZeroₒ i := by infer_instance

/-- Extends functions with one extra argument and return value for ghost tokens. -/
abbrev ProgWithSpec [Arity Op]
  {sigs : Sigs k}
  (opSpec : OpSpec Op V T)
  (progSpec : ProgSpec V T sigs) χ :=
  Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs progSpec)

end Wavelet.Seq

/-! Some abbreviations for `Proc`. -/
namespace Wavelet.Dataflow

open Semantics Determinacy

abbrev ProcWithSpec
  [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) χ
  := Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + ioSpec.k) (n + 1)

abbrev ConfigWithSpec
  [Arity Op]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n) χ
  := Config (WithSpec Op opSpec) χ (V ⊕ T) (m + ioSpec.k) (n + 1)

infix:50 " ≈ " => AsyncOp.EqMod EqModGhost
infix:50 " ≈ " => AtomicProc.EqMod EqModGhost
infix:50 " ≈ " => Proc.EqMod EqModGhost
infix:50 " ≈ " => Config.EqMod EqModGhost

end Wavelet.Dataflow
