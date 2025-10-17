import Mathlib.Logic.Relation
import Wavelet.Semantics.Defs
import Wavelet.Data.List

import Wavelet.Dataflow.ChanMap

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Semantics

inductive CarryState where
  | popLeft
  | popRight
  | decider

/-- Built-in asynchronous operators: `AsyncOp ... m n`
is an asynchronous operator with a total of `m` inputs
ports and `n` outputs ports. -/
inductive AsyncOp V : Nat → Nat → Type u where
  | switch (n : Nat) : AsyncOp V (1 + n) (n + n)
  | steer (flavor : Bool) (n : Nat) : AsyncOp V (1 + n) n
  | carry (state : CarryState) (n : Nat) : AsyncOp V (1 + n + n) n
  | merge (n : Nat) : AsyncOp V (1 + n + n) n
  | forward (n : Nat) : AsyncOp V n n
  | fork (n : Nat) : AsyncOp V 1 n
  | const (c : V) (n : Nat) : AsyncOp V 0 n
  | forwardc (n m : Nat) (consts : Vector V m) : AsyncOp V n (n + m)
  | sink (n : Nat) : AsyncOp V n 0

/-- Dataflow operators. -/
inductive AtomicProc (Op χ V : Type*) [Arity Op] where
  | op (op : Op) (inputs : Vector χ (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  | async (aop : AsyncOp V m n) (inputs : Vector χ m) (outputs : Vector χ n)
  -- | switch (decider : χ) (inputs : Vector χ n) (outputs₁ : Vector χ n) (outputs₂ : Vector χ n)
  -- | steer (flavor : Bool) (decider : χ) (inputs : Vector χ n) (outputs : Vector χ n)
  -- | carry (state : CarryState)
  --   (decider : χ)
  --   (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  --   (outputs : Vector χ n)
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

def AtomicProc.switch [Arity Op]
  (decider : χ) (inputs : Vector χ n)
  (outputs₁ : Vector χ n)
  (outputs₂ : Vector χ n) :
  AtomicProc Op χ V
  := .async (.switch n) (#v[decider] ++ inputs) (outputs₁ ++ outputs₂)

def AtomicProc.steer [Arity Op]
  (flavor : Bool)
  (decider : χ) (inputs : Vector χ n)
  (outputs : Vector χ n) :
  AtomicProc Op χ V
  := .async (.steer flavor n) (#v[decider] ++ inputs) outputs

def AtomicProc.carry [Arity Op]
  (state : CarryState)
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) :
  AtomicProc Op χ V
  := .async (.carry state n) (#v[decider] ++ inputs₁ ++ inputs₂) outputs

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

/-- Defines the semantics of each async operator -/
inductive AsyncOp.Interp
  [InterpConsts V] :
  (aop : AsyncOp V m n) →
  (aop' : AsyncOp V m n) → -- Next operator to transition to
  Vector χ m → -- All inputs
  Vector χ n → -- All outputs
  (m' : Nat) × Vector χ m' × Vector V m' → -- A subset of inputs to read from
  (n' : Nat) × Vector χ n' × Vector V n' → -- A subset of outputs to write to
  Prop where
  | interp_switch
    {decider : χ}
    {deciderVal : V}
    {inputs : Vector χ k} :
    InterpConsts.toBool deciderVal = some deciderBool →
    Interp (.switch k) (.switch k)
      (#v[decider] ++ inputs)
      (outputs₁ ++ outputs₂)
      ⟨1 + k, #v[decider] ++ inputs, #v[deciderVal] ++ inputVals⟩
      ⟨k, if deciderBool then outputs₁ else outputs₂, inputVals⟩
  | interp_steer_true
    {decider : χ}
    {deciderVal : V}
    {inputs : Vector χ k} :
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool = flavor →
    Interp (.steer flavor k) (.steer flavor k)
      (#v[decider] ++ inputs)
      outputs
      ⟨1 + k, #v[decider] ++ inputs, #v[deciderVal] ++ inputVals⟩
      ⟨k, outputs, inputVals⟩
  | interp_steer_false
    {decider : χ}
    {deciderVal : V}
    {inputs : Vector χ k}
    {inputVals : Vector V k} :
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool ≠ flavor →
    Interp (.steer flavor k) (.steer flavor k)
      (#v[decider] ++ inputs)
      outputs
      ⟨1 + k, #v[decider] ++ inputs, #v[deciderVal] ++ inputVals⟩
      ⟨0, #v[], #v[]⟩
  | interp_carry_left
    {decider : χ}
    {inputs₁ inputs₂ : Vector χ k} :
    Interp (.carry .popLeft k) (.carry .decider k)
      (#v[decider] ++ inputs₁ ++ inputs₂)
      outputs
      ⟨k, inputs₁, inputVals⟩
      ⟨k, outputs, inputVals⟩
  | interp_carry_right
    {decider : χ}
    {inputs₁ inputs₂ : Vector χ k} :
    Interp (.carry .popRight k) (.carry .decider k)
      (#v[decider] ++ inputs₁ ++ inputs₂)
      outputs
      ⟨k, inputs₂, inputVals⟩
      ⟨k, outputs, inputVals⟩
  | interp_carry_decider
    {decider : χ}
    {deciderVal : V}
    {inputs₁ inputs₂ : Vector χ k} :
    InterpConsts.toBool deciderVal = some deciderBool →
    Interp (.carry .decider k)
      (.carry (if deciderBool then .popRight else .popLeft) k)
      (#v[decider] ++ inputs₁ ++ inputs₂)
      outputs
      ⟨1, #v[decider], #v[deciderVal]⟩
      ⟨0, #v[], #v[]⟩

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
    {k₁} {inputs : Vector χ k₁} {inputVals : Vector V k₁}
    {k₂} {outputs : Vector χ k₂} {outputVals : Vector V k₂} :
    c.proc.atoms = ctxLeft ++ .async aop allInputs allOutputs :: ctxRight →
    aop.Interp aop' allInputs allOutputs ⟨k₁, inputs, inputVals⟩ ⟨k₂, outputs, outputVals⟩ →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with
      proc := { c.proc with
        atoms := ctxLeft ++ .async aop' allInputs allOutputs :: ctxRight,
      },
      chans := chans'.pushVals outputs outputVals,
    }
  | step_merge :
    .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    InterpConsts.toBool deciderVal = some deciderBool →
    chans'.popVals
      (if deciderBool then inputs₁ else inputs₂)
      = some (inputVals, chans'') →
    Step c .τ { c with chans := chans''.pushVals outputs inputVals }
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

/-! Alternative rules for the stepping relation. -/
section AltStep

theorem Config.Step.step_switch
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {outputs₁ outputs₂ : Vector χ k}
  (hmem : .switch decider inputs outputs₁ outputs₂ ∈ c.proc.atoms)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hpop_inputs : chans'.popVals inputs = some (inputVals, chans''))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool) :
  Step c .τ { c with
    chans :=
      let outputs := if deciderBool then outputs₁ else outputs₂
      chans''.pushVals outputs inputVals
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.switch] at happ
  apply Config.Step.step_async
    (aop := .switch k)
    (aop' := .switch k)
    happ
    (.interp_switch hdecider)
    (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_steer
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs outputs : Vector χ k}
  (hmem : .steer flavor decider inputs outputs ∈ c.proc.atoms)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hpop_inputs : chans'.popVals inputs = some (inputVals, chans''))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool) :
  Step c .τ { c with
    chans :=
      if deciderBool = flavor then
        chans''.pushVals outputs inputVals
      else
        chans'',
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.steer] at happ
  by_cases h₁ : deciderBool = flavor
  · apply Config.Step.step_async
      (aop := .steer flavor k)
      (aop' := .steer flavor k)
      happ
      (.interp_steer_true hdecider h₁)
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp [h₁]
    congr 1
    exact happ.symm
  · apply Config.Step.step_async
      (aop := .steer flavor k)
      (aop' := .steer flavor k)
      happ
      (.interp_steer_false hdecider h₁)
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp [h₁, ChanMap.pushVals]
    congr 1
    exact happ.symm

theorem Config.Step.step_carry_left
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  {ctxLeft ctxRight : List (AtomicProc Op χ V)}
  (happ : c.proc.atoms =
    ctxLeft ++ [.carry .popLeft decider inputs₁ inputs₂ outputs] ++ ctxRight)
  (hpop_inputs₁ : c.chans.popVals inputs₁ = some (inputVals, chans')) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight,
    },
    chans := chans'.pushVals outputs inputVals,
  } := by
  simp at happ
  apply Config.Step.step_async
    (aop := .carry .popLeft k)
    (aop' := .carry .decider k)
    happ
    .interp_carry_left
    hpop_inputs₁
    |> Lts.Step.eq_rhs
  simp
  congr 1
  simp

theorem Config.Step.step_carry_right
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  {ctxLeft ctxRight : List (AtomicProc Op χ V)}
  (happ : c.proc.atoms =
    ctxLeft ++ [.carry .popRight decider inputs₁ inputs₂ outputs] ++ ctxRight)
  (hpop_inputs₂ : c.chans.popVals inputs₂ = some (inputVals, chans')) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight,
    },
    chans := chans'.pushVals outputs inputVals,
  } := by
  simp at happ
  apply Config.Step.step_async
    (aop := .carry .popRight k)
    (aop' := .carry .decider k)
    happ
    .interp_carry_right
    hpop_inputs₂
    |> Lts.Step.eq_rhs
  simp
  congr 1
  simp

theorem Config.Step.step_carry_decider
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  {ctxLeft ctxRight : List (AtomicProc Op χ V)}
  (happ : c.proc.atoms =
    ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ [
          .carry (if deciderBool then .popRight else .popLeft)
            decider inputs₁ inputs₂ outputs
        ] ++ ctxRight,
    },
    chans := chans',
  } := by
  simp at happ
  apply Config.Step.step_async
    (aop := .carry .decider k)
    (aop' := .carry (if deciderBool then .popRight else .popLeft) k)
    happ
    (.interp_carry_decider hdecider)
    (pop_val_to_pop_vals hpop_decider)
    |> Lts.Step.eq_rhs
  simp
  constructor
  · simp [AtomicProc.carry]
  · simp [ChanMap.pushVals]

end AltStep

end Wavelet.Dataflow
