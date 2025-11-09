import Wavelet.Dataflow.Proc
import Wavelet.Determinacy.Defs

/-! Erasing ghost inputs/outputs to operators. -/

namespace Wavelet.Dataflow

open Semantics Determinacy

inductive EraseName (χ : Type u) where
  | base (name : χ)
  | input (name : χ)
  | output (name : χ)
  | join (name₁ : χ) (name₂ : χ)
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

/-- Translates operators with ghost tokens into the base operators. -/
def AtomicProc.eraseGhost
  [Arity Op] [instNZ : NeZeroArity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  : AtomicProc (WithSpec Op opSpec) χ V → AtomicProcs Op (EraseName χ) V
  | .op (.op ghost o) inputs outputs =>
    if h : ghost then
      let hne₁ : NeZero (Arity.ι (WithSpec.op ghost o) - 1) := by
        simp [Arity.ι, h]; infer_instance
      let hne₂ : NeZero (Arity.ω (WithSpec.op ghost o) - 1) := by
        simp [Arity.ω]; infer_instance
      let lastInput := @Vector.back _ _ hne₁ inputs.pop
      let lastOutput := @Vector.back _ _ hne₂ outputs.pop
      let inputPerm := inputs.back
      let outputPerm := outputs.back
      let inputs' := (inputs.pop.pop.map .base).push (.input lastInput)
      let outputs' := (outputs.pop.pop.map .base).push (.output lastOutput)
      [
        -- Use an order operator to wait for permission token input
        .async (.order 2) [.base lastInput, .base inputPerm] [.input lastInput],
        -- Use a fork at the end to produce permission token output
        -- TODO: fork may not have matching types here?
        .async (.fork 2) [.output lastOutput] [.base lastOutput, .base outputPerm],
        .op o
          (inputs'.cast (by
            have : Arity.ι o ≠ 0 := (instNZ.neZeroᵢ o).ne
            simp [Arity.ι, h]
            omega))
          (outputs'.cast (by
            have : Arity.ω o ≠ 0 := (instNZ.neZeroₒ o).ne
            simp [Arity.ω]
            omega))
      ]
    else
      let hne₂ : NeZero (Arity.ω (WithSpec.op ghost o) - 1) := by
        simp [Arity.ω]; infer_instance
      let lastOutput := @Vector.back _ _ hne₂ outputs.pop
      let outputPerm := outputs.back
      let outputs' := (outputs.pop.pop.map .base).push (.output lastOutput)
      [
        -- Use a fork at the end to produce permission token output
        -- TODO: fork may not have matching types here?
        .async (.fork 2) [.output lastOutput] [.base lastOutput, .base outputPerm],
        .op o
          ((inputs.map EraseName.base).cast (by simp [Arity.ι, h]))
          (outputs'.cast (by
            have : Arity.ω o ≠ 0 := (instNZ.neZeroₒ o).ne
            simp [Arity.ω]
            omega))
      ]
  | .op (WithSpec.join k l req) inputs outputs =>
    let output₁ := outputs[0]'(by simp [Arity.ω])
    let output₂ := outputs[1]'(by simp [Arity.ω])
    let joined := .join output₁ output₂
    [
      .async (.order (k + l)) (inputs.toList.map .base) [joined],
      .async (.fork 2) [joined] [.base output₁, .base output₂],
    ]
  | .async aop inputs outputs => [.async aop (inputs.map .base) (outputs.map .base)]

def AtomicProcs.eraseGhost
  [Arity Op] [NeZeroArity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  (aps : AtomicProcs (WithSpec Op opSpec) χ V) :
    AtomicProcs Op (EraseName χ) V
  := (aps.map AtomicProc.eraseGhost).flatten

def Proc.eraseGhost
  [Arity Op] [NeZeroArity Op] [PCM T]
  {opSpec : OpSpec Op V T}
  (proc : Proc (WithSpec Op opSpec) χ V m n) :
    Proc Op (EraseName χ) V m n
  := {
    inputs := proc.inputs.map EraseName.base,
    outputs := proc.outputs.map EraseName.base,
    atoms := proc.atoms.eraseGhost,
  }

end Wavelet.Dataflow
