import Batteries.Data.List.Basic

/-! Defines the syntax and semantics of operator sets. -/

namespace Wavelet.Op

class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop
  eq : C → C → Prop

infix:60 " ⬝ " => PCM.add
infix:50 " ≡ " => PCM.eq

abbrev valid {R : Type u} [PCM R] (a : R) := PCM.valid a

class LawfulPCM (R : Type u) [inst : PCM R] where
  add_comm : ∀ a b : R, a ⬝ b ≡ b ⬝ a
  add_assoc : ∀ a b c : R, (a ⬝ b) ⬝ c ≡ a ⬝ (b ⬝ c)
  add_ident : ∀ a : R, a ⬝ inst.zero ≡ a
  valid_add : ∀ a b : R, valid (a ⬝ b) → valid a
  valid_zero : valid inst.zero
  valid_eq : ∀ a b : R, a ≡ b → valid a → valid b
  eq_refl : ∀ a : R, a ≡ a
  eq_symm : ∀ a b : R, a ≡ b → b ≡ a
  eq_trans : ∀ a b c : R, a ≡ b → b ≡ c → a ≡ c

def HasTypes (typeOf : V → T) (ins : List V) (inTys : List T) : Prop :=
  List.Forall₂ (λ v t => typeOf v = t) ins inTys

structure OpSpec (T : Type u) (V : Type v) (R : Type w) (typeOf : V → T) where
  inTys : List T
  outTys : List T
  /-- Requires clause -/
  req : ∀ ins : List V, HasTypes typeOf ins inTys → R
  /-- Ensures clause -/
  ens : ∀ ins outs : List V,
    HasTypes typeOf ins inTys →
    HasTypes typeOf outs outTys →
    R

structure OpSet where
  /-- Base types -/
  T : Type u
  /-- Base values -/
  V : Type v
  /-- Ghost resource algebra -/
  R : Type w
  /-- Operators -/
  Op : Type
  /-- Value types -/
  typeOf : V → T
  /-- Operator specs -/
  specOf : Op → OpSpec T V R typeOf

class OpSemantics (os : OpSet) [PCM os.R] where
  /-- States -/
  S : Type

  /-- TODO: use more general monads? -/
  runOp : os.Op → List os.V → StateT S Option (List os.V)

  /-- Given well-typed inputs and a valid resource, produce well-typed outputs and a valid resource -/
  op_satisfies_spec (op : os.Op) (ins : List os.V)
    (hwt_ins : HasTypes os.typeOf ins (os.specOf op).inTys) :
    valid ((os.specOf op).req ins hwt_ins) →
    ∀ (s s' : S) (outs : List os.V),
      (runOp op ins).run s = .some (outs, s') →
      (hwt_outs : HasTypes os.typeOf outs (os.specOf op).outTys) →
      valid ((os.specOf op).ens ins outs hwt_ins hwt_outs)

  /- If resource inputs to two operators are disjoint, their interpretations commute. -/
  op_disj_commute (op₁ op₂ : os.Op) (ins₁ ins₂ : List os.V)
    (hwt_ins₁ : HasTypes os.typeOf ins₁ (os.specOf op₁).inTys)
    (hwt_ins₂ : HasTypes os.typeOf ins₂ (os.specOf op₂).inTys)
    (hdisj : valid
      ((os.specOf op₁).req ins₁ hwt_ins₁ ⬝ (os.specOf op₂).req ins₂ hwt_ins₂)) :
    ∀ (s : S),
      (do let outs₁ ← runOp op₁ ins₁;
          let outs₂ ← runOp op₂ ins₂;
          return (outs₁, outs₂)).run s =
      (do let outs₂ ← runOp op₂ ins₂;
          let outs₁ ← runOp op₁ ins₁;
          return (outs₁, outs₂)).run s

end Wavelet.Op
