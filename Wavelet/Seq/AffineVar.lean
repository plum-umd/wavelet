import Wavelet.Data.List
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
    AffineVar usedVars definedVars (.ret vars)
  | wf_tail :
    vars.toList.Nodup →
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
    AffineVar (c :: usedVars) (definedVars.removeAll [c]) left →
    AffineVar (c :: usedVars) (definedVars.removeAll [c]) right →
    AffineVar usedVars definedVars (.br c left right)

def Fn.AffineVar [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Prop :=
  fn.params.toList.Nodup ∧
  fn.body.AffineVar [] fn.params.toList

/-- Executable version of `Expr.AffineVar` -/
instance Expr.AffineVar.instDecidable [Arity Op] [DecidableEq χ]
  {usedVars : List χ}
  {definedVars : List χ}
  {expr : Expr Op χ n m} : Decidable (expr.AffineVar usedVars definedVars) :=
  match expr with
  | .ret vars =>
    if h : vars.toList.Nodup then
      isTrue (Expr.AffineVar.wf_ret h)
    else
      isFalse (by
        intro h
        rcases h with ⟨hnodup⟩
        contradiction)
  | .tail vars =>
    if h : vars.toList.Nodup then
      isTrue (Expr.AffineVar.wf_tail h)
    else
      isFalse (by
        intro h
        rcases h with ⟨hnodup⟩
        contradiction)
  | .op o args rets cont =>
    have : Decidable
      (cont.AffineVar (usedVars ++ args.toList) ((definedVars.removeAll args.toList) ++ rets.toList))
      := instDecidable
    if h : args.toList.Nodup ∧
      rets.toList.Nodup ∧
      usedVars.Disjoint rets.toList ∧
      definedVars.Disjoint rets.toList ∧
      args.toList ⊆ definedVars ∧
      cont.AffineVar (usedVars ++ args.toList) ((definedVars.removeAll args.toList) ++ rets.toList) then
      isTrue (by
        have ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
        apply Expr.AffineVar.wf_op h₁ h₂ h₃ h₄ h₅ h₆)
    else
      isFalse (by intros h'; rcases h'; grind only)
  | .br c left right =>
    have : Decidable
      (left.AffineVar (c :: usedVars) (definedVars.removeAll [c]))
      := instDecidable
    have : Decidable
      (right.AffineVar (c :: usedVars) (definedVars.removeAll [c]))
      := instDecidable
    if h₁ :
      left.AffineVar (c :: usedVars) (definedVars.removeAll [c]) ∧
      right.AffineVar (c :: usedVars) (definedVars.removeAll [c]) then
      isTrue (by
        have ⟨hl, hr⟩ := h₁
        apply Expr.AffineVar.wf_br hl hr)
    else
      isFalse (by intros h'; rcases h'; grind only)

/-- Executable version of `Fn.AffineVar` -/
instance Fn.AffineVar.instDecidable [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Decidable (fn.AffineVar) :=
  if h : fn.params.toList.Nodup ∧ fn.body.AffineVar [] fn.params.toList then
    isTrue h
  else
    isFalse (by intros h'; rcases h'; grind only)

end Wavelet.Seq
