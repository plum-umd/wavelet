import Wavelet.Determinacy
import Wavelet.Seq.AffineVar

/-! Typing soundness for `Seq`. -/

namespace Wavelet.Seq

open Semantics Determinacy

/-- TODO -/
def ProgWithSpec.WellPermTyped
  [Arity Op] [PCM T]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  (progSpec : ProgSpec V T sigs)
  (prog : ProgWithSpec χ sigs opSpec) : Prop := sorry

/-- Well-typing induces a simulation between unguarded
and guarded semantics of `Prog`. -/
theorem sim_wt_prog
  [Arity Op]
  [InterpConsts V]
  [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ[PreservesInit] (prog.semantics i).guard (opSpec.Guard (progSpec i))
  := by sorry

end Wavelet.Seq
