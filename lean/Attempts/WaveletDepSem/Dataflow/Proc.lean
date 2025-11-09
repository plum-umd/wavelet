import Mathlib.Logic.Relation

import Wavelet.Semantics.Defs
import Wavelet.Data.List

import Wavelet.Dataflow.ChanMap
import Wavelet.Dataflow.AsyncOp

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Semantics

/-- Dataflow operators in two kinds:
  - (Synchronous) operators always consume exactly one value
    from each input channel and always output exactly one value
    to each output channel.
  - Asynchronous operators can change the number of inputs/outputs
    depending on internal state or input values. -/
inductive AtomicProc (Op χ V : Type*) [Arity Op] where
  | op (op : Op) (inputs : Vector χ (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  | async (aop : AsyncOp V) (inputs : List χ) (outputs : List χ)

abbrev AtomicProcs Op χ V [Arity Op] := List (AtomicProc Op χ V)

/-- `Proc ... m n` is a process with `m` inputs and `n` outputs. -/
structure Proc Op χ V [Arity Op] (m : Nat) (n : Nat) where
  inputs : Vector χ m
  outputs : Vector χ n
  atoms : AtomicProcs Op χ V

structure Config (Op : Type u) (χ : Type v) (V : Type w) [Arity Op] m n where
  proc : Proc Op χ V m n
  chans : ChanMap χ V

/-- Initial process configuration. -/
def Config.init
  [Arity Op] [DecidableEq χ]
  (proc : Proc Op χ V m n) : Config Op χ V m n
  := { proc, chans := .empty }

/-- Main stepping relation for dataflow. -/
inductive Config.Step
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  : Lts (Config Op χ V m n) (Label Op V m n) where
  | step_init :
    Step c (.input args) { c with
      chans := c.chans.pushVals c.proc.inputs args,
    }
  | step_output :
    c.chans.popVals c.proc.outputs = some (outputVals, chans') →
    Step c (.output outputVals) { c with
      chans := chans',
    }
  | step_op {op}
    {inputs : Vector χ (Arity.ι op)}
    {outputs : Vector χ (Arity.ω op)}
    {inputVals outputVals chans'} :
    .op op inputs outputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c (.yield op inputVals outputVals) { c with
      chans := chans'.pushVals outputs outputVals,
    }
  | step_async
    {c : Config Op χ V _ _}
    {aop aop' : AsyncOp V}
    {allInputs allOutputs}
    {inputs : Vector χ k₁}
    {inputVals : Vector V k₁}
    {outputs : Vector χ k₂}
    {outputVals : Vector V k₂}
    {chans'}
    {i : Nat} :
    (_ : i < c.proc.atoms.length) →
    c.proc.atoms[i] = .async aop allInputs allOutputs →
    aop.Interp (.mk allInputs allOutputs
      inputs.toList inputVals.toList
      outputs.toList outputVals.toList) aop' →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with
      proc := { c.proc with
        atoms := c.proc.atoms.set i (.async aop' allInputs allOutputs),
      },
      chans := chans'.pushVals outputs outputVals,
    }

def Proc.semantics
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) : Semantics (Config Op χ V m n) Op V m n := {
    init := Config.init proc,
    lts := Config.Step,
  }

end Wavelet.Dataflow
