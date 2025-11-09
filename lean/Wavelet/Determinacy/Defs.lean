import Wavelet.Dataflow.IndexedStep
import Wavelet.Dataflow.AffineChan
import Wavelet.Semantics.Confluence

import Wavelet.Determinacy.PCM
import Wavelet.Determinacy.OpSpec

/-! Basic definitions for determinacy proofs. -/

namespace Wavelet.Dataflow

open Semantics Determinacy

/-- Converts any guard on normal labels to indexed labels. -/
inductive IndexedGuard (P : E → E' → Prop) : Nat × E → Nat × E' → Prop where
  | idx_guard : P l l' → IndexedGuard P (i, l) (i, l')

/- Some abbreviations for some proc related LTS. -/

abbrev Config.GuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := (Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.Guard ioSpec)

abbrev Config.TrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := (Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.TrivGuard ioSpec)

abbrev Config.InterpGuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := ((Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.Guard ioSpec)).InterpStep
    opInterp.lts

abbrev Config.InterpTrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := ((Dataflow.Config.Step (χ := χ)).GuardStep
    (opSpec.TrivGuard ioSpec)).InterpStep
    opInterp.lts

abbrev Config.IdxGuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := (Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.Guard ioSpec))

abbrev Config.IdxTrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := (Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.TrivGuard ioSpec))

abbrev Config.IdxInterpGuardStep
  [Arity Op] [PCM T] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := ((Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.Guard ioSpec))).IndexedInterpStep
    opInterp.lts

abbrev Config.IdxInterpTrivStep {m n}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp Op V]
  (opSpec : OpSpec Op V T)
  (ioSpec : IOSpec V T m n)
  := ((Dataflow.Config.IndexedStep (χ := χ)).GuardStep
    (IndexedGuard (opSpec.TrivGuard ioSpec))).IndexedInterpStep
    opInterp.lts

end Wavelet.Dataflow
