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

-- theorem compile_strong_norm
--   [Arity Op] [PCM T] [PCM.Lawful T]
--   [DecidableEq χ]
--   [InterpConsts V]
--   [opInterp : OpInterp Op V]
--   {sigs : Sigs k}
--   {opSpec : OpSpec Op V T}
--   {progSpec : ProgSpec Op V T sigs}
--   (prog : ProgWithSpec χ sigs opSpec)
--   (hwt : ProgWithSpec.WellPermTyped progSpec prog)
--   (haff₁ : ∀ (i : Fin k), (prog i).AffineVar)
--   (haff₂ : prog.AffineInrOp)
--   (i : Fin k)
--   {args : Vector V (sigs i).ι}
--   {outputVals : Vector V (sigs i).ω}

--   -- Semantics of the input function and the output dataflow graph after interpretation of operators
--   {sem₁ sem₂ : Semantics Semantics.Empty V (sigs i).ι (sigs i).ω}
--   (hsem₁ : sem₁ = (((prog.semantics i).guard opSpec.TrivGuard).interpret opInterp))
--   (hsem₂ : sem₂ = ((compileProg _ prog i).semantics.guard opSpec.TrivGuard).interpret opInterp)
--   {s s₁ s₂ : sem₁.S} {s' s₁' : sem₂.S}
--   -- Same input values to both semantics
--   (hinputs : sem₁.lts.Step sem₁.init (.input args) s)
--   (hinputs' : sem₂.lts.Step sem₂.init (.input args) s')

--   -- There exists a terminating trace in the sequential semantics
--   -- that output `outputVals`.
--   (htrace : sem₁.lts.TauStarN .τ k s s₁)
--   (hterm : sem₁.lts.IsFinalFor (·.isSilent) s₁)
--   (houtput : sem₁.lts.Step s₁ (.output outputVals) s₂)

--   (htrace' : sem₂.lts.TauStarN .τ k' s' s₁') :
--     ∃ s₁'' s₂' k'',
--       k = k' + k'' ∧
--       sem₂.lts.TauStarN .τ k'' s₁' s₁'' ∧
--       sem₂.lts.IsFinalFor (·.isSilent) s₁'' ∧
--       sem₂.lts.Step s₁'' (.output outputVals) s₂' ∧
--       (cast (by simp [hsem₂, Semantics.interpret]) s₁'' : _ × opInterp.S).2 =
--         (cast (by simp [hsem₁, Semantics.interpret]) s₂ : _ × opInterp.S).2
--   := sorry

end Wavelet
