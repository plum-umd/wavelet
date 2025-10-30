import Wavelet.Seq.Fn

namespace Wavelet.Seq

open Semantics

/--
Enforces that the use of variables is affine,
bound variables are disjoint, and there is no shadowing.
-/
inductive Expr.AffineVar [Arity Op] [DecidableEq χ]
  : List χ → Expr Op χ n m → Prop where
  | wf_ret :
    vars.toList.Nodup →
    AffineVar definedVars (.ret vars)
  | wf_tail :
    vars.toList.Nodup →
    AffineVar definedVars (.tail vars)
  | wf_op :
    args.toList.Nodup →
    rets.toList.Nodup →
    definedVars.Disjoint rets.toList →
    args.toList ⊆ definedVars →
    AffineVar ((definedVars.removeAll args.toList) ++ rets.toList) cont →
    AffineVar definedVars (.op o args rets cont)
  | wf_br :
    AffineVar (definedVars.removeAll [c]) left →
    AffineVar (definedVars.removeAll [c]) right →
    AffineVar definedVars (.br c left right)

def Fn.AffineVar [Arity Op] [DecidableEq χ]
  (fn : Fn Op χ V m n) : Prop :=
  fn.params.toList.Nodup ∧
  fn.body.AffineVar fn.params.toList

end Wavelet.Seq
