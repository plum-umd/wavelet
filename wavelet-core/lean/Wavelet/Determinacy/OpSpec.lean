import Wavelet.Semantics.Defs

import Wavelet.Seq.Fn
import Wavelet.Seq.Prog
import Wavelet.Dataflow.Proc

import Wavelet.Determinacy.PCM

/-! Resource specification on an operator set. -/

namespace Wavelet.Determinacy

open Semantics

/-- PCM specification of an operator set -/
structure OpSpec Op V T [Arity Op] where
  pre : (op : Op) → Vector V (Arity.ι op) → T
  post : (op : Op) → Vector V (Arity.ι op) → Vector V (Arity.ω op) → T

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
  ω | .op true o => arity.ω o + 1
    | .op false o => arity.ω o
    | WithSpec.join _ _ _ => 2

instance [Arity Op] [NeZeroArity Op] {spec : OpSpec Op V T} : NeZeroArity (WithSpec Op spec) where
  neZeroᵢ | .op true o => by infer_instance
          | .op false o => by simp [Arity.ι]; infer_instance
          | WithSpec.join k l _ => by
            simp [Arity.ι]
            infer_instance
  neZeroₒ | .op true o => by infer_instance
          | .op false o => by simp [Arity.ω]; infer_instance
          | WithSpec.join _ _ _ => by infer_instance

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

end Wavelet.Dataflow
