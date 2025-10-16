import Mathlib.Logic.Relation
import Wavelet.Semantics.Defs

import Wavelet.Dataflow.ChanMap

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Semantics

/-- Built-in asynchronous operators. -/
inductive AsyncOp Op V [Arity Op] where
  | switch (n : Nat)
  | steer (n : Nat)
  | carry (inLoop : Bool) (n : Nat)
  | merge (n : Nat)
  | forward (n : Nat)
  | fork (n : Nat)
  | const (c : V) (n : Nat)
  | forwardc (n m : Nat) (consts : Vector V m)
  | sink (n : Nat)

/-- Input arity of asynchronous operators. -/
def AsyncOp.ι [Arity Op] : AsyncOp Op V → Nat
  | .switch n => n + 1
  | .steer n => n + 1
  | .carry _ n => n + 1
  | .merge n => n + 1
  | .forward n => n
  | .fork _ => 1
  | .const _ n => n
  | .forwardc n _ _ => n
  | .sink n => n

/-- Output arity of asynchronous operators. -/
def AsyncOp.ω [Arity Op] : AsyncOp Op V → Nat
  | .switch n => n + n
  | .steer n => n
  | .carry _ n => n
  | .merge n => n
  | .forward n => n
  | .fork n => n
  | .const _ n => n
  | .forwardc n m _ => n + m
  | .sink _ => 0

-- /-- Returns the number of inputs to pop in the current state. -/
-- def AyncOp.numActiveInputs [Arity Op] : AsyncOp Op V → Nat
--   | .switch n => n + 1
--   | .steer n => n + 1
--   | .carry false n => n
--   | .carry true n => n + 1

inductive CarryState where
  | popLeft
  | popRight
  | decider

/-- Dataflow operators. -/
inductive AtomicProc (Op χ V : Type*) [Arity Op] where
  | op (op : Op) (inputs : Vector χ (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  -- | async (aop : AsyncOp Op V) (inputs : Vector χ (AsyncOp.ι aop)) (outputs : Vector χ (AsyncOp.ω aop))
  | switch (decider : χ) (inputs : Vector χ n) (outputs₁ : Vector χ n) (outputs₂ : Vector χ n)
  | steer (flavor : Bool) (decider : χ) (inputs : Vector χ n) (outputs : Vector χ n)
  | carry (state : CarryState)
    (decider : χ)
    (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
    (outputs : Vector χ n)
  | merge (decider : χ)
    (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
    (outputs : Vector χ n)
  | forward (inputs : Vector χ n) (outputs : Vector χ n)
  | fork (input : χ) (outputs : Vector χ n)
  | const (c : V) (act : χ) (outputs : Vector χ n)
  -- A combination of `forward` and `const` to wait for inputs to arrive,
  -- forward the inputs to the first `n` outputs, and then send constants
  -- to the last `m` outputs.
  | forwardc
    (inputs : Vector χ n) (consts : Vector V m) (outputs : Vector χ (n + m))
  | sink (inputs : Vector χ n)

-- def AtomicProc.switch [Arity Op]
--   (decider : χ) (inputs : Vector χ n)
--   (outputs₁ : Vector χ n)
--   (outputs₂ : Vector χ n) :
--   AtomicProc Op χ V
--   := .async (.switch n) (inputs.push decider) (outputs₁ ++ outputs₂)

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
  | step_switch
    {outputs₁ outputs₂ : Vector χ n} :
    .switch decider inputs outputs₁ outputs₂ ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    chans'.popVals inputs = some (inputVals, chans'') →
    InterpConsts.toBool deciderVal = some deciderBool →
    Step c .τ { c with
      chans :=
        let outputs := if deciderBool then outputs₁ else outputs₂
        chans''.pushVals outputs inputVals
    }
  | step_steer :
    .steer flavor decider inputs outputs ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    chans'.popVals inputs = some (inputVals, chans'') →
    InterpConsts.toBool deciderVal = some deciderBool →
    Step c .τ { c with
      chans :=
        if deciderBool = flavor then
          chans''.pushVals outputs inputVals
        else
          chans'',
    }
  | step_merge :
    .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    InterpConsts.toBool deciderVal = some deciderBool →
    chans'.popVals
      (if deciderBool then inputs₁ else inputs₂)
      = some (inputVals, chans'') →
    Step c .τ { c with chans := chans''.pushVals outputs inputVals }
  | step_carry_left :
    c.proc.atoms = ctxLeft ++ [.carry .popLeft decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVals inputs₁ = some (inputVals, chans') →
    Step c .τ { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight,
      },
      chans := chans'.pushVals outputs inputVals,
    }
  | step_carry_right :
    c.proc.atoms = ctxLeft ++ [.carry .popRight decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVals inputs₂ = some (inputVals, chans') →
    Step c .τ { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight,
      },
      chans := chans'.pushVals outputs inputVals,
    }
  | step_carry_decider :
    c.proc.atoms = ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVal decider = some (deciderVal, chans') →
    InterpConsts.toBool deciderVal = some deciderBool →
    Step c .τ { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [
          .carry (if deciderBool then .popRight else .popLeft)
            decider inputs₁ inputs₂ outputs
        ] ++ ctxRight,
      },
      chans := chans',
    }
  | step_forward :
    .forward inputs outputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs inputVals,
    }
  | step_fork :
    .fork input outputs ∈ c.proc.atoms →
    c.chans.popVal input = some (inputVal, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs (Vector.replicate _ inputVal),
    }
  | step_const :
    .const val act outputs ∈ c.proc.atoms →
    c.chans.popVal act = some (actVal, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs (Vector.replicate _ val),
    }
  | step_forwardc :
    .forwardc inputs consts outputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs (inputVals ++ consts),
    }
  | step_sink :
    .sink inputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with chans := chans' }

def Proc.semantics
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) : Semantics Op V m n := {
    S := Config Op χ V m n,
    init := Config.init proc,
    lts := Config.Step,
    yields_functional hyield := by
      intros
      cases hyield with | step_op hmem hpop =>
      exact ⟨_, .step_op hmem hpop⟩
  }

end Wavelet.Dataflow
