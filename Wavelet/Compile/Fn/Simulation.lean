import Wavelet.Compile.Fn.Defs

/-! Simulation proofs for `compileFn`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

/-- TODO: Migrate the proofs of the older version over. -/
theorem sim_compile_fn
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (hnz : m > 0 ∧ n > 0)
  (fn : Fn Op χ V m n)
  (hwf : fn.WellFormed) :
  fn.semantics ≲ (compileFn hnz fn).semantics
  := sorry

end Wavelet.Compile
