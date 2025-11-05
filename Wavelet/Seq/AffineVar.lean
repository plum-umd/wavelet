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

end Wavelet.Seq
