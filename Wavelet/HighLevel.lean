import Wavelet.Determinacy
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Typing

/-! Some high-level theorems and plans. -/

namespace Wavelet

open Semantics Determinacy Seq Dataflow Compile

/-- TODO -/
def ProgWithSpec.WellPermTyped
  [Arity Op] [PCM T]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  (progSpec : ProgSpec Op V T sigs)
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
  {progSpec : ProgSpec Op V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ (prog.semantics i).guard (opSpec.Guard (progSpec i))
  := by sorry

theorem compile_forward_sim
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (haff₁ : ∀ (i : Fin k), (prog i).AffineVar)
  (haff₂ : prog.AffineInrOp)
  (i : Fin k) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ (compileProg _ prog i).semantics.guard opSpec.TrivGuard
  := by
  apply IORestrictedSimilarity.trans
  · exact sim_wt_prog prog hwt
  apply IORestrictedSimilarity.trans
  · apply sim_guard
    apply sim_compile_prog.{_, _, _, 0} (extendSigs sigs) prog ↑i (by omega) haff₁ haff₂
  simp
  sorry

end Wavelet
