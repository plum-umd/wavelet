import Wavelet.Op
import Wavelet.LTS
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

namespace Wavelet.Simulation.Defs

open Wavelet.Op Wavelet.LTS Wavelet.Seq Wavelet.Dataflow Wavelet.Compile

class GetState (Config : Type u) (S : Type v) where
  getState : Config → S

class FinalWithValues (Config : Type u) (V : Type v) where
  IsFinalWithValues : Config → List V → Prop

/-- Simulation that preserves the state and final values. -/
def SPSimulation
  S V
  [inst₁ : GetState C₁ S] [FinalWithValues C₁ V]
  [inst₂ : GetState C₂ S] [FinalWithValues C₂ V]
  (c₁ : C₁) (c₂ : C₂)
  (R : C₁ → C₂ → Prop)
  (Step₁ : LTS C₁ E)
  (Step₂ : LTS C₂ E) :=
  Simulation c₁ c₂ R Step₁ Step₂ ∧
  (∀ c₁ c₂, R c₁ c₂ → inst₁.getState c₁ = inst₂.getState c₂) ∧
  (∀ c₁ c₂ (vals : List V),
    R c₁ c₂ →
    FinalWithValues.IsFinalWithValues c₁ vals →
    FinalWithValues.IsFinalWithValues c₂ vals)

instance [Arity Op] : GetState (Seq.Config Op χ V S m n) S where
  getState c := c.state

instance [Arity Op] : GetState (Dataflow.Config Op χ V S m n) S where
  getState c := c.state

instance [Arity Op] : FinalWithValues (Seq.Config Op χ V S m n) V where
  IsFinalWithValues c vals :=
    ∃ vals', c.expr = .ret vals' ∧ vals'.toList = vals

instance [Arity Op] [DecidableEq χ] : FinalWithValues (Dataflow.Config Op χ V S m n) V where
  /- TODO: this currently don't enforce that the configuration is terminal. -/
  IsFinalWithValues c vals :=
    ∃ vals',
      c.chans.popVals c.proc.outputs = some (vals', c.chans) ∧
      vals'.toList = vals

/-- Specific case for a Seq config to refine a dataflow config. -/
abbrev Seq.RefinesDataflow
  [DecidableEq χ₁] [DecidableEq χ₂]
  [Arity Op] [InterpConsts V] [InterpOp Op V E S]
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  Simulation (E := E) c₁ c₂ R Config.Step Config.StepPlus

abbrev Seq.SPRefinesDataflow
  [DecidableEq χ₁] [DecidableEq χ₂]
  [Arity Op] [InterpConsts V] [InterpOp Op V E S]
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  SPSimulation (E := E) S V c₁ c₂ R Config.Step Config.StepPlus

end Wavelet.Simulation.Defs
