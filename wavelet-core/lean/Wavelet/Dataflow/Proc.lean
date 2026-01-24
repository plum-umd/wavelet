import Wavelet.Semantics.Defs

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
inductive AtomicProc (Op : Type u) χ V [Arity Op] where
  | op (op : Op) (inputs : Vector χ (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  | async (aop : AsyncOp V) (inputs : List χ) (outputs : List χ)
  deriving Repr

def AtomicProc.inputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ inputs _ => inputs.toList
  | .async _ inputs _ => inputs

def AtomicProc.outputs [Arity Op] : AtomicProc Op χ V → List χ
  | .op _ _ outputs => outputs.toList
  | .async _ _ outputs => outputs

/-! Built-in asynchronous operators. -/
namespace AtomicProc

def switch [Arity Op]
  (decider : χ) (inputs : Vector χ n)
  (outputs₁ : Vector χ n)
  (outputs₂ : Vector χ n) : AtomicProc Op χ V
  := .async (.switch n) (#v[decider] ++ inputs).toList (outputs₁ ++ outputs₂).toList

def steer [Arity Op]
  (flavor : Bool)
  (decider : χ) (inputs : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.steer flavor n) (#v[decider] ++ inputs).toList outputs.toList

def merge [Arity Op] [NeZero n]
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V :=
  .async (.merge .decider n) (#v[decider] ++ inputs₁ ++ inputs₂).toList outputs.toList

/-- Carry is a variant of merge that can have a different initial state. -/
def carry [Arity Op] [NeZero n]
  (state : AsyncOp.MergeState)
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.merge state n) (#v[decider] ++ inputs₁ ++ inputs₂).toList outputs.toList

def forward [Arity Op] [NeZero n]
  (inputs : Vector χ n) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.forward n) inputs.toList outputs.toList

def fork [Arity Op]
  (input : χ) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.fork n) [input] outputs.toList

def order [Arity Op] [NeZero n]
  (inputs : Vector χ n) (output : χ) : AtomicProc Op χ V
  := .async (.order n) inputs.toList [output]

def const [Arity Op]
  (c : V) (act : χ) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.const c n) [act] outputs.toList

def forwardc [Arity Op] [NeZero n]
  (inputs : Vector χ n) (consts : Vector V m)
  (outputs : Vector χ (n + m)) : AtomicProc Op χ V
  := .async (.forwardc n m consts) inputs.toList outputs.toList

def sink [Arity Op]
  (inputs : Vector χ n) : AtomicProc Op χ V
  := if h : n ≠ 0 then
    let _ : NeZero n := NeZero.mk h
    .async (.sink n) inputs.toList #v[].toList
  else
    .async (.inact 0) [] []

def inv [Arity Op]
  (flavor : Bool) (c : Option V) (decider : χ) (input : χ) (output : χ) : AtomicProc Op χ V
  := .async (.inv flavor c) [decider, input] [output]

def inact [Arity Op]
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.inact n) [] outputs.toList

end AtomicProc

abbrev AtomicProcs Op χ V [Arity Op] := List (AtomicProc Op χ V)

/-- `Proc ... m n` is a process with `m` inputs and `n` outputs. -/
structure Proc Op χ V [Arity Op] (m : Nat) (n : Nat) where
  inputs : Vector χ m
  outputs : Vector χ n
  atoms : AtomicProcs Op χ V

structure Config (Op : Type u) (χ : Type v) (V : Type w) [Arity Op] m n : Type (max u v w) where
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
  {Op : Type u} {χ : Type v} {V : Type w}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) : Semantics.{_, _, max u v w} Op V m n := {
    S := Config Op χ V m n,
    init := Config.init proc,
    lts := Config.Step,
  }

end Wavelet.Dataflow
