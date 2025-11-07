import Wavelet.Data.List
import Wavelet.Data.Except

import Wavelet.Seq.Fn

namespace Wavelet.Seq

open Semantics

/--
Enforces that the use of variables is affine,
bound variables are disjoint, and there is no shadowing.
-/
inductive Expr.AffineVar [Arity Op] [DecidableEq χ]
  : List χ → List χ → Expr Op χ n m → Prop where
  | wf_ret :
    vars.toList.Nodup →
    vars.toList ⊆ definedVars →
    AffineVar usedVars definedVars (.ret vars)
  | wf_tail :
    vars.toList.Nodup →
    vars.toList ⊆ definedVars →
    AffineVar usedVars definedVars (.tail vars)
  | wf_op :
    args.toList.Nodup →
    rets.toList.Nodup →
    -- Cannot redefine a used variable (to avoid variables mapping to the same channel)
    usedVars.Disjoint rets.toList →
    definedVars.Disjoint rets.toList →
    args.toList ⊆ definedVars →
    AffineVar (usedVars ++ args.toList) ((definedVars.removeAll args.toList) ++ rets.toList) cont →
    AffineVar usedVars definedVars (.op o args rets cont)
  | wf_br :
    c ∈ definedVars →
    AffineVar (c :: usedVars) (definedVars.removeAll [c]) left →
    AffineVar (c :: usedVars) (definedVars.removeAll [c]) right →
    AffineVar usedVars definedVars (.br c left right)

def Fn.AffineVar [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Prop :=
  fn.params.toList.Nodup ∧
  fn.body.AffineVar [] fn.params.toList

def Expr.checkAffineVar
  [Arity Op] [DecidableEq χ] [Repr χ]
  (usedVars : List χ)
  (definedVars : List χ) :
    (expr : Expr Op χ n m) →
    ExceptDec String (expr.AffineVar usedVars definedVars)
  | .ret vars => do
    let h₁ ← ExceptDec.check vars.toList.Nodup s!"duplicate return vars {repr vars.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₂ ← ExceptDec.check (vars.toList ⊆ definedVars) s!"undefined return vars {repr vars.toList}"
      |>.necessary λ h => by cases h; assumption
    return ⟨.wf_ret h₁.down h₂.down⟩
  | .tail vars => do
    let h₁ ← ExceptDec.check vars.toList.Nodup s!"duplicate tail args {repr vars.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₂ ← ExceptDec.check (vars.toList ⊆ definedVars) s!"undefined tail args {repr vars.toList}"
      |>.necessary λ h => by cases h; assumption
    return ⟨.wf_tail h₁.down h₂.down⟩
  | .op o args rets cont => do
    let h₁ ← ExceptDec.check args.toList.Nodup s!"duplicate operator args {repr args.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₂ ← ExceptDec.check rets.toList.Nodup s!"duplicate operator return variables {repr rets.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₃ ← ExceptDec.check (usedVars.Disjoint rets.toList)
      s!"redefining used variables {repr rets.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₄ ← ExceptDec.check (definedVars.Disjoint rets.toList)
      s!"redefining variables {repr rets.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₅ ← ExceptDec.check (args.toList ⊆ definedVars)
      s!"one or more operator args not defined: {repr args.toList}"
      |>.necessary λ h => by cases h; assumption
    let h₆ ← cont.checkAffineVar
      (usedVars ++ args.toList)
      ((definedVars.removeAll args.toList) ++ rets.toList)
      |>.necessary λ h => by cases h; assumption
    return ⟨.wf_op h₁.down h₂.down h₃.down h₄.down h₅.down h₆.down⟩
  | .br c left right => do
    let h₁ ← ExceptDec.check (c ∈ definedVars)
      s!"undefined branch condition {repr c}"
      |>.necessary λ h => by cases h; assumption
    let h₂ ← left.checkAffineVar
      (c :: usedVars)
      (definedVars.removeAll [c])
      |>.necessary λ h => by cases h; assumption
    let h₃ ← right.checkAffineVar
      (c :: usedVars)
      (definedVars.removeAll [c])
      |>.necessary λ h => by cases h; assumption
    return ⟨.wf_br h₁.down h₂.down h₃.down⟩

def Fn.checkAffineVar
  [Arity Op] [DecidableEq χ] [Repr χ]
  (fn : Fn Op χ V m n) :
    ExceptDec String (fn.AffineVar) := do
  let h₁ ← ExceptDec.check fn.params.toList.Nodup
    s!"duplicate function params {repr fn.params.toList}"
    |>.necessary λ h => by cases h; assumption
  let h₂ ← fn.body.checkAffineVar [] fn.params.toList
    |>.necessary λ h => by cases h; assumption
  return ⟨h₁.down, h₂.down⟩

/-- Executable version of `Expr.AffineVar` -/
instance
  [Arity Op] [DecidableEq χ] [Repr χ]
  {usedVars : List χ}
  {definedVars : List χ}
  {expr : Expr Op χ n m} :
  Decidable (expr.AffineVar usedVars definedVars) :=
  (expr.checkAffineVar usedVars definedVars).toDecidable

/-- Executable version of `Fn.AffineVar` -/
instance Fn.AffineVar.instDecidable [Arity Op] [DecidableEq χ] [Repr χ]
  (fn : Fn Op χ V m n) : Decidable (fn.AffineVar) :=
  (fn.checkAffineVar).toDecidable

end Wavelet.Seq
