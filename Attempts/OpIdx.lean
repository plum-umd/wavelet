import Wavelet.Dataflow.Proc

/-! Annotating operators with a unique atomic process index. -/

namespace Wavelet.Dataflow

open Semantics

inductive OpIdx Op where
  | op_at (i : Nat) (op : Op)

instance [Arity Op] : Arity (OpIdx Op) where
  ι | .op_at _ op => Arity.ι op
  ω | .op_at _ op => Arity.ω op

def Proc.indexed [Arity Op]
  (proc : Proc Op χ V m n) :
  Proc (OpIdx Op) χ V m n := sorry

end Wavelet.Dataflow
