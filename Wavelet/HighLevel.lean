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

/-- Final semantics of a sequential program when interpreted
with a specific operator interpretation. -/
abbrev Seq.Prog.semanticsᵢ
  {Op : Type u₁} {χ : Type u₂} {V : Type u₃}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {sigs : Sigs k}
  {opSpec : Determinacy.OpSpec Op V T}
  (prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs))
  (i : Fin k) :
    Semantics.{_, _, max u₁ u₂ u₃ w} Semantics.Empty V (sigs i).ι (sigs i).ω
  := ((prog.semantics i).guard opSpec.TrivGuard).interpret opInterp

/-- Final semantics of a dataflow program when interpreted
with a specific operator interpretation. -/
abbrev Dataflow.Proc.semanticsᵢ
  {Op : Type u₁} {χ : Type u₂} {V : Type u₃}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {opSpec : Determinacy.OpSpec Op V T}
  (proc : Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)) :
    Semantics.{_, _, max u₁ u₂ u₃ w} Semantics.Empty V m n
  := (proc.semantics.guard opSpec.TrivGuard).interpret opInterp

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
    apply sim_compile_prog (extendSigs sigs) prog ↑i (by omega) haff₁ haff₂
  simp
  sorry

theorem compile_strong_norm
  {Op V T : Type u}
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}
  (prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs))
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (haff₁ : ∀ (i : Fin k), (prog i).AffineVar)
  (haff₂ : prog.AffineInrOp)
  (i : Fin k)
  {args : Vector V (sigs i).ι}
  {outputVals : Vector V (sigs i).ω}

  {proc : Proc (WithSpec Op opSpec) (LinkName (ChanName χ)) (V ⊕ T) _ _}
  (hcomp : proc = compileProg (extendSigs sigs) prog i)

  {s s₁ s₂ : (prog.semanticsᵢ i).S}
  {s' s₁' : proc.semanticsᵢ.S}
  -- Same input values to both semantics
  (hinputs : (prog.semanticsᵢ i).lts.Step (prog.semanticsᵢ i).init (.input args) s)
  (hinputs' : proc.semanticsᵢ.lts.Step proc.semanticsᵢ.init (.input args) s')

  -- There exists a terminating trace in the sequential semantics
  -- that output `outputVals`.
  (htrace : (prog.semanticsᵢ i).lts.TauStarN .τ k s s₁)
  (hterm : (prog.semanticsᵢ i).lts.IsFinalFor (·.isSilent) s₁)
  (houtput : (prog.semanticsᵢ i).lts.Step s₁ (.output outputVals) s₂)

  (htrace' : proc.semanticsᵢ.lts.TauStarN .τ k' s' s₁') :
    ∃ (s₁'' s₂' : proc.semanticsᵢ.S) (k'' : Nat),
      k = k' + k'' ∧
      proc.semanticsᵢ.lts.TauStarN .τ k'' s₁' s₁'' ∧
      proc.semanticsᵢ.lts.IsFinalFor (·.isSilent) s₁'' ∧
      proc.semanticsᵢ.lts.Step s₁'' (.output outputVals) s₂' ∧
      s₂'.2 = s₂.2 -- Equal "memory" states
  := sorry

end Wavelet
