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
  -- frame_preserving : ∀ op inputs outputs, pre op inputs ⟹ post op inputs outputs

/-- Two labels are compatible if their inputs correspond to disjoint resources
and are deterministic. -/
def OpSpec.CompatLabels
  [Arity Op] [PCM T]
  (opSpec : OpSpec Op V T) :
  RespLabel Op V → RespLabel Op V → Prop
  | .respond op₁ inputs₁ _, .respond op₂ inputs₂ _ =>
    (opSpec.pre op₁ inputs₁) ⊥ (opSpec.pre op₂ inputs₂)

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

/-- Specification on input/output labels. -/
structure IOSpec V T m n where
  pre : Vector V m → T
  -- This can only depend on the outputs, due
  -- to a technical issue that we can't access
  -- the input values at an output event.
  post : Vector V n → T

/-- Augments the operator set with an additional ghost argument
to pass a PCM token, as well as two operators to split and join PCMs. -/
inductive WithSpec {T : Type u} (Op : Type u) [Arity Op] (spec : OpSpec Op V T) where
  | op (op : Op)
  | join
      (k : Nat) -- Number of input tokens to combine
      (l : Nat) -- Number of values that the token depends on
      (req : Vector V l → T)

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
  [arity : Arity Op]
  {spec : OpSpec Op V T} :
  Arity (WithSpec Op spec) where
  ι | .op o => arity.ι o + 1
    | .join k l _ => k + l
  ω | .op o => arity.ω o + 1
    | .join _ _ _ => 2

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
    Guard opSpec ioSpec
      (.yield (.op op)
        ((inputs.map .inl).push (.inr (opSpec.pre op inputs)))
        ((outputs.map .inl).push (.inr (opSpec.post op inputs outputs))))
      (.yield op inputs outputs)
  | spec_join
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
      (.input ((vals.map .inl).push (.inr (ioSpec.pre vals)))) (.input vals)
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
  (opSpec : OpSpec Op V T) :
  Label (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1) →
  Label Op V m n → Prop where
  | triv_yield :
    opSpec.TrivGuard
      (.yield (.op op) ((inputs.map .inl).push (.inr tok₁)) ((outputs.map .inl).push (.inr tok₂)))
      (.yield op inputs outputs)
  | triv_join
    {toks : Vector T k}
    {vals : Vector V l}
    {outputs : Vector T 2} :
    opSpec.TrivGuard (.yield (.join k l req)
      ((toks.map .inr : Vector (V ⊕ T) k) ++
        (vals.map .inl : Vector (V ⊕ T) l))
      (outputs.map .inr)) .τ
  | triv_input : opSpec.TrivGuard (.input ((vals.map .inl).push (.inr tok))) (.input vals)
  | triv_output : opSpec.TrivGuard (.output ((vals.map .inl).push (.inr tok))) (.output vals)
  | triv_tau : opSpec.TrivGuard .τ .τ

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
  {opSpec : OpSpec Op V T} : LawfulGuard (opSpec.TrivGuard (m := m) (n := n)) where
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
    opSpec.Guard ioSpec l₁ l₂ → opSpec.TrivGuard l₁ l₂
  | .spec_yield => by exact .triv_yield
  | .spec_join .. => by
    rename_i k l req rem toks vals outputs h₁ h₂ hsum
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

/-! Some abbreviations for `Seq`. -/
namespace Wavelet.Seq

open Semantics Determinacy

abbrev ExprWithSpec
  [Arity Op] (opSpec : OpSpec Op V T) χ m n
  := Expr (WithSpec Op opSpec) χ (m + 1) (n + 1)

abbrev FnWithSpec
  [Arity Op] (opSpec : OpSpec Op V T) χ m n
  := Fn (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

/-- A collection of `IOSpec`s for `Fn`s in a `Prog`. -/
abbrev ProgSpec (Op : Type u) V T [Arity Op] (sigs : Sigs k) :=
  (i : Fin k) → IOSpec V T (sigs i).ι (sigs i).ω

abbrev ConfigWithSpec [Arity Op] (opSpec : OpSpec Op V T) χ m n
  := Config (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

-- /-- Extend the operator signature with the first `k'` function specs
-- in the given program spec. -/
-- def extendSpec
--   [Arity Op]
--   {sigs : Vector Sig k}
--   (opSpec : OpSpec Op V T)
--   (progSpec : ProgSpec Op V T sigs)
--   (k' : Fin (k + 1)) :
--     OpSpec (Op ⊕ SigOps sigs k') V T
--   := {
--     pre | .inl op, inputs => opSpec.pre op inputs
--         | .inr (.call i), inputs => (progSpec ⟨i, by omega⟩).pre inputs,
--     post | .inl op, inputs, outputs => opSpec.post op inputs outputs
--          | .inr (.call i), inputs, _ => (progSpec ⟨i, by omega⟩).pre inputs,
--   }

-- def ProgSpec.toOpSpec
--   [Arity Op]
--   {sigs : Vector Sig k}
--   (progSpec : ProgSpec Op V T sigs)
--   (k' : Fin (k + 1)) :
--     OpSpec (SigOps sigs k') V T
--   := {
--     pre | (.call i), inputs => (progSpec ⟨i, by omega⟩).pre inputs,
--     post | (.call i), inputs, _ => (progSpec ⟨i, by omega⟩).pre inputs,
--   }

abbrev extendSigs (sigs : Sigs k) : Sigs k :=
  λ i => { ι := (sigs i).ι + 1, ω := (sigs i).ω + 1 }

/-- Extends functions with one extra argument and return value for ghost tokens. -/
abbrev ProgWithSpec χ [Arity Op]
  (sigs : Sigs k)
  (opSpec : OpSpec Op V T) :=
  Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs)

-- def ProgWithSpecAlt
--   {Op T : Type u} -- Since join uses `T`
--   χ [Arity Op]
--   {sigs : Vector Sig k}
--   (opSpec : OpSpec Op V T)
--   (progSpec : ProgSpec Op V T sigs) :=
--   (i : Fin k) →
--     FnWithSpec (extendSpec opSpec progSpec i.castSucc) χ sigs[i].ι sigs[i].ω

-- def ProgWithSpec.semantics
--   [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
--   {sigs : Vector Sig k}
--   {opSpec : OpSpec Op V T}
--   {progSpec : ProgSpec Op V T sigs}
--   (prog : ProgWithSpec χ opSpec progSpec)
--   (i : Fin k) :
--     Semantics Op V sigs[i].ι sigs[i].ω := sorry
--   -- := Semantics.link
--   --   ((prog i).semantics.guard (opSpec.Guard (progSpec i)))
--   --   (λ op => ProgWithSpec.semantics prog sorry)

-- def Expr.toLinkable
--   [Arity Op]
--   {sigs : Vector Sig k}
--   {opSpec : OpSpec Op V T}
--   {progSpec : ProgSpec Op V T sigs}
--   {i : Fin k} :
--     Expr (WithSpec (Op ⊕ SigOps sigs i.castSucc) (extendSpec opSpec progSpec i.castSucc))
--       χ (sigs[i].ι + 1) (sigs[i].ω + 1) →
--     Expr (WithSpec Op opSpec ⊕ SigOps (extendSigs sigs) i.castSucc)
--       χ (extendSigs sigs)[i].ι (extendSigs sigs)[i].ω
--   | .op (.op (.inl o)) inputs outputs cont => .op (.inl (.op o)) inputs outputs cont.toLinkable
--   | .op (.op (.inr (.call j))) inputs outputs cont =>
--     .op (.inr (.call j : SigOps (extendSigs sigs) i.castSucc))
--       (inputs.cast (by
--         have : j < k := by omega
--         simp [extendSigs, Arity.ι]
--         grind only [= Fin.getElem_fin, = Vector.getElem_map]))
--       (outputs.cast (by
--         have : j < k := by omega
--         simp [extendSigs, Arity.ω]
--         grind only [= Fin.getElem_fin, = Vector.getElem_map])) cont.toLinkable
--   | .op (.join k l req) inputs outputs cont => .op (.inl (.join k l req)) inputs outputs cont.toLinkable
--   | .ret vars => .ret (vars.cast (by simp))
--   | .tail vars => .tail (vars.cast (by simp))
--   | .br c left right => .br c left.toLinkable right.toLinkable

-- def FnWithSpec.toLinkable
--   [Arity Op]
--   {sigs : Vector Sig k}
--   {opSpec : OpSpec Op V T}
--   {progSpec : ProgSpec Op V T sigs}
--   {i : Fin k}
--   (fn : FnWithSpec (extendSpec opSpec progSpec i.castSucc) χ sigs[i].ι sigs[i].ω) :
--     Fn (WithSpec Op opSpec ⊕ SigOps (extendSigs sigs) i.castSucc) χ (V ⊕ T) (extendSigs sigs)[i].ι (extendSigs sigs)[i].ω
--   := {
--     params := fn.params.cast (by simp [extendSigs]),
--     body := fn.body.toLinkable,
--   }

-- def ProgWithSpecAlt.toLinkable
--   [Arity Op]
--   {sigs : Vector Sig k}
--   {opSpec : OpSpec Op V T}
--   {progSpec : ProgSpec Op V T sigs}
--   (prog : ProgWithSpecAlt χ opSpec progSpec) :
--     ProgWithSpec χ sigs opSpec :=
--   λ i => (prog i).toLinkable

end Wavelet.Seq

/-! Some abbreviations for `Proc`. -/
namespace Wavelet.Dataflow

open Semantics Determinacy

abbrev ProcWithSpec
  [Arity Op] (opSpec : OpSpec Op V T) χ m n
  := Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

abbrev ConfigWithSpec
  [Arity Op] (opSpec : OpSpec Op V T) χ m n
  := Config (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)

infix:50 " ≈ " => AsyncOp.EqMod EqModGhost
infix:50 " ≈ " => AtomicProc.EqMod EqModGhost
infix:50 " ≈ " => Proc.EqMod EqModGhost
infix:50 " ≈ " => Config.EqMod EqModGhost

end Wavelet.Dataflow
