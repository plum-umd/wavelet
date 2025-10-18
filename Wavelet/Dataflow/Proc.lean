import Mathlib.Logic.Relation

import Wavelet.Semantics.Defs
import Wavelet.Data.List

import Wavelet.Dataflow.ChanMap

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Semantics

/-! Local state of a carry gate -/
inductive CarryState where
  | popLeft
  | popRight
  | decider

/-- Built-in asynchronous operators: `AsyncOp ... m n`
is an asynchronous operator with a total of `m` inputs
ports and `n` outputs ports. -/
inductive AsyncOp V : Type u where
  | switch (n : Nat) : AsyncOp V
  | steer (flavor : Bool) (n : Nat) : AsyncOp V
  | carry (state : CarryState) (n : Nat) : AsyncOp V
  | merge (n : Nat) : AsyncOp V
  | forward (n : Nat) : AsyncOp V
  | fork (n : Nat) : AsyncOp V
  | const (c : V) (n : Nat) : AsyncOp V
  -- A combination of `forward` and `const` to wait for inputs to arrive,
  -- forward the inputs to the first `n` outputs, and then send constants
  -- to the last `m` outputs.
  | forwardc (n m : Nat) (consts : Vector V m) : AsyncOp V
  | sink (n : Nat) : AsyncOp V

/-- Dataflow operators in two kinds:
  - (Synchronous) operators always consume exactly one value
    from each input channel and always output exactly one value
    to each output channel.
  - Asynchronous operators can change the number of inputs/outputs
    depending on internal state or input values. -/
inductive AtomicProc (Op χ V : Type*) [Arity Op] where
  | op (op : Op) (inputs : Vector χ (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  | async (aop : AsyncOp V) (inputs : List χ) (outputs : List χ)

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

def carry [Arity Op]
  (state : CarryState)
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.carry state n) (#v[decider] ++ inputs₁ ++ inputs₂).toList outputs.toList

def merge [Arity Op]
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.merge n) (#v[decider] ++ inputs₁ ++ inputs₂).toList outputs.toList

def forward [Arity Op]
  (inputs : Vector χ n) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.forward n) inputs.toList outputs.toList

def fork [Arity Op]
  (input : χ) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.fork n) [input] outputs.toList

def const [Arity Op]
  (c : V) (act : χ) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.const c n) [act] outputs.toList

def forwardc [Arity Op]
  (inputs : Vector χ n) (consts : Vector V m)
  (outputs : Vector χ (n + m)) : AtomicProc Op χ V
  := .async (.forwardc n m consts) inputs.toList outputs.toList

def sink [Arity Op]
  (inputs : Vector χ n) : AtomicProc Op χ V
  := .async (.sink n) inputs.toList #v[].toList

end AtomicProc

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

structure AsyncOp.Label χ V where
  allInputs : List χ
  allOutputs : List χ
  -- A subset of inputs to read from
  inputs : List χ
  inputVals : List V
  -- A subset of outputs to write to
  outputs : List χ
  outputVals : List V

/--
Defines the semantics of each built-in async operator.

NOTE: Unlike synchronous operators, async operators's types
are left mostly non-dependent to simplify spec and type inference.
-/
inductive AsyncOp.Interp
  [InterpConsts V] : Lts (AsyncOp V) (AsyncOp.Label χ V) where
  | interp_switch :
    inputs.length = k →
    outputs.length = k + k →
    InterpConsts.toBool deciderVal = some deciderBool →
    Interp (.switch k)
      (.mk (decider :: inputs) outputs
        (decider :: inputs) (deciderVal :: inputVals)
        (if deciderBool then outputs.take k else outputs.drop k) inputVals)
      (.switch k)
  | interp_steer_true :
    inputs.length = k →
    outputs.length = k →
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool = flavor →
    Interp (.steer flavor k)
      (.mk (decider :: inputs) outputs
        (decider :: inputs) (deciderVal :: inputVals)
        outputs inputVals)
      (.steer flavor k)
  | interp_steer_false :
    inputs.length = k →
    outputs.length = k →
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool ≠ flavor →
    Interp (.steer flavor k)
      (.mk (decider :: inputs) outputs
        (decider :: inputs) (deciderVal :: inputVals)
        [] [])
      (.steer flavor k)
  | interp_carry_left :
    inputs.length = k + k →
    outputs.length = k →
    Interp (.carry .popLeft k)
      (.mk (decider :: inputs) outputs
        (inputs.take k) inputVals
        outputs inputVals)
      (.carry .decider k)
  | interp_carry_right :
    inputs.length = k + k →
    outputs.length = k →
    Interp (.carry .popRight k)
      (.mk (decider :: inputs) outputs
        (inputs.drop k) inputVals
        outputs inputVals)
      (.carry .decider k)
  | interp_carry_decider :
    inputs.length = k + k →
    outputs.length = k →
    InterpConsts.toBool deciderVal = some deciderBool →
    Interp (.carry .decider k)
      (.mk (decider :: inputs) outputs
        [decider] [deciderVal]
        [] [])
      (.carry (if deciderBool then .popRight else .popLeft) k)
  | interp_merge_true :
    inputs.length = k + k →
    outputs.length = k →
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool →
    Interp (.merge k)
      (.mk (decider :: inputs) outputs
        (decider :: inputs.take k) (deciderVal :: inputVals)
        outputs inputVals)
      (.merge k)
  | interp_merge_false :
    inputs.length = k + k →
    outputs.length = k →
    InterpConsts.toBool deciderVal = some deciderBool →
    ¬deciderBool →
    Interp (.merge k)
      (.mk (decider :: inputs) outputs
        (decider :: inputs.drop k) (deciderVal :: inputVals)
        outputs inputVals)
      (.merge k)
  | interp_forward :
    inputs.length = k →
    outputs.length = k →
    Interp (.forward k)
      (.mk inputs outputs
        inputs inputVals
        outputs inputVals)
      (.forward k)
  | interp_fork :
    outputs.length = k →
    Interp (.fork k)
      (.mk [input] outputs
        [input] [inputVal]
        outputs (.replicate k inputVal))
      (.fork k)
  | interp_const :
    outputs.length = k →
    Interp (.const c k)
      (.mk [act] outputs
        [act] [actVal]
        outputs (.replicate k c))
      (.const c k)
  | interp_forwardc :
    inputs.length = k →
    outputs.length = k + l →
    Interp (.forwardc k l consts)
      (.mk inputs outputs
        inputs inputVals
        outputs (inputVals ++ consts.toList))
      (.forwardc k l consts)
  | interp_sink :
    inputs.length = k →
    Interp (.sink k)
      (.mk inputs []
        inputs inputVals
        [] [])
      (.sink k)

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
  (proc : Proc Op χ V m n) : Semantics Op V m n := {
    S := Config Op χ V m n,
    init := Config.init proc,
    lts := Config.Step,
  }

theorem AsyncOp.Interp.eq_label
  [InterpConsts V]
  {aop aop' : AsyncOp V}
  {label₁ label₂ : AsyncOp.Label χ V}
  (hinterp₁ : aop.Interp label₁ aop')
  (heq : label₁ = label₂) : aop.Interp label₂ aop'
  := by
  simp [heq] at hinterp₁
  exact hinterp₁

/-- If two async op invocations reads the same values from the same input channels,
then the transition is deterministic. Note that this does not rule out the case
when the async operator can non-deterministically choose different inputs to read. -/
theorem async_op_interp_det_outputs
  [InterpConsts V]
  {aop aop₁' aop₂' : AsyncOp V}
  (hinterp₁ : aop.Interp (.mk allInputs allOutputs inputs₁ inputVals₁ outputs₁ outputVals₁) aop₁')
  (hinterp₂ : aop.Interp (.mk allInputs allOutputs inputs₂ inputVals₂ outputs₂ outputVals₂) aop₂')
  (heq₁ : inputs₁ = inputs₂)
  (heq₂ : inputVals₁ = inputVals₂) :
    outputs₁ = outputs₂ ∧
    outputVals₁ = outputVals₂ ∧
    aop₁' = aop₂'
  := by
  cases hinterp₁ <;> cases hinterp₂
  any_goals grind only [cases Or]

theorem async_op_interp_det_inputs_len
  [InterpConsts V]
  {aop aop₁' aop₂' : AsyncOp V}
  (hinterp₁ : aop.Interp (.mk allInputs₁ allOutputs₁ inputs₁ inputVals₁ outputs₁ outputVals₁) aop₁')
  (hinterp₂ : aop.Interp (.mk allInputs₂ allOutputs₂ inputs₂ inputVals₂ outputs₂ outputVals₂) aop₂') :
    inputs₁.length = inputs₂.length
  := by
  cases hinterp₁ <;> cases hinterp₂
  any_goals grind only [List.length_cons, = List.length_drop,
    = List.length_take, = Nat.min_def, cases Or, List.length]

/-- Inputs read in each async op is a sublist of the total input list. -/
theorem async_op_interp_input_sublist
  [InterpConsts V]
  {aop aop' : AsyncOp V}
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals)
    aop') :
  inputs.Sublist allInputs := by
  cases hinterp
  any_goals simp [List.take_sublist, List.drop_sublist]

/-- Outputs read in each async op is a sublist of the total output list. -/
theorem async_op_interp_output_sublist
  [InterpConsts V]
  {aop aop' : AsyncOp V}
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals)
    aop') :
  outputs.Sublist allOutputs := by
  cases hinterp
  any_goals simp
  case interp_switch =>
    split <;> simp [List.take_sublist, List.drop_sublist]

/-! Alternative rules for the stepping relation. -/
section AltStep

theorem Config.Step.step_async_alt
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {k₁' k₂'}
  {aop aop' : AsyncOp V}
  {ctxLeft ctxRight}
  {allInputs allOutputs}
  {inputs : Vector χ k₁'}
  {outputs : Vector χ k₂'}
  {inputVals outputVals chans'}
  (happ : c.proc.atoms = ctxLeft ++ .async aop allInputs allOutputs :: ctxRight)
  (hinterp : aop.Interp
    (.mk allInputs allOutputs inputs.toList inputVals.toList outputs.toList outputVals.toList)
    aop')
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ .async aop' allInputs allOutputs :: ctxRight,
    },
    chans := chans'.pushVals outputs outputVals,
  } := by
  have hget := List.getElem_of_append_cons happ
  apply Config.Step.step_async
    (by simp [happ])
    hget hinterp hpop_inputs
    |> Lts.Step.eq_rhs
  simp [happ]

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
  apply Config.Step.step_async_alt
    (aop := .switch k)
    (aop' := .switch k)
    (outputs := if deciderBool then outputs₁ else outputs₂)
    happ
    (by
      apply AsyncOp.Interp.interp_switch (k := k)
        (inputs := inputs.toList)
        (outputs := (outputs₁ ++ outputs₂).toList)
        (by simp)
        (by simp)
        hdecider
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      split <;> simp)
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
  · apply Config.Step.step_async_alt
      (aop := .steer flavor k)
      (aop' := .steer flavor k)
      happ
      (by
        apply AsyncOp.Interp.interp_steer_true (k := k)
          (inputs := inputs.toList)
          (outputs := outputs.toList)
          (by simp)
          (by simp)
          hdecider h₁
          |> AsyncOp.Interp.eq_label
        simp [Vector.toList]
        and_intros
        any_goals try rfl)
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp [h₁]
    congr 1
    exact happ.symm
  · apply Config.Step.step_async_alt
      (aop := .steer flavor k)
      (aop' := .steer flavor k)
      happ
      (by
        apply AsyncOp.Interp.interp_steer_false (k := k)
          (inputs := inputs.toList)
          (outputs := outputs.toList)
          (by simp)
          (by simp)
          hdecider h₁
          |> AsyncOp.Interp.eq_label
        simp [Vector.toList]
        and_intros
        any_goals try rfl
        exact #v[]
        exact #v[])
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
  apply Config.Step.step_async_alt
    (aop := .carry .popLeft k)
    (aop' := .carry .decider k)
    happ
    (by
      apply AsyncOp.Interp.interp_carry_left (k := k)
        (inputs := (inputs₁ ++ inputs₂).toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
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
  apply Config.Step.step_async_alt
    (aop := .carry .popRight k)
    (aop' := .carry .decider k)
    happ
    (by
      apply AsyncOp.Interp.interp_carry_right (k := k)
        (inputs := (inputs₁ ++ inputs₂).toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
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
  apply Config.Step.step_async_alt
    (aop := .carry .decider k)
    (aop' := .carry (if deciderBool then .popRight else .popLeft) k)
    happ
    (by
      apply AsyncOp.Interp.interp_carry_decider (k := k)
        (inputs := (inputs₁ ++ inputs₂).toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        hdecider
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      exact #v[]; exact #v[])
    (pop_val_to_pop_vals hpop_decider)
    |> Lts.Step.eq_rhs
  simp
  constructor
  · simp [AtomicProc.carry]
  · simp [ChanMap.pushVals]

theorem Config.Step.step_merge
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  (hmem : .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool)
  (hpop_inputs : chans'.popVals
    (if deciderBool then inputs₁ else inputs₂) = some (inputVals, chans'')) :
  Step c .τ { c with
    chans := chans''.pushVals outputs inputVals
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.merge] at happ
  by_cases h₁ : deciderBool <;> simp [h₁] at hpop_inputs
  · apply Config.Step.step_async_alt
      (aop := .merge k)
      (aop' := .merge k)
      happ
      (by
        apply AsyncOp.Interp.interp_merge_true (k := k)
          (inputs := (inputs₁ ++ inputs₂).toList)
          (outputs := outputs.toList)
          (by simp)
          (by simp)
          hdecider h₁
          |> AsyncOp.Interp.eq_label
        simp [Vector.toList]
        and_intros
        any_goals try rfl)
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp
    congr 1
    simp only [Vector.append_assoc] at happ
    exact happ.symm
  · apply Config.Step.step_async_alt
      (aop := .merge k)
      (aop' := .merge k)
      happ
      (by
        apply AsyncOp.Interp.interp_merge_false (k := k)
          (inputs := (inputs₁ ++ inputs₂).toList)
          (outputs := outputs.toList)
          (by simp)
          (by simp)
          hdecider h₁
          |> AsyncOp.Interp.eq_label
        simp [Vector.toList]
        and_intros
        any_goals try rfl)
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp [ChanMap.pushVals]
    congr 1
    simp only [Vector.append_assoc] at happ
    exact happ.symm

theorem Config.Step.step_forward
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs outputs : Vector χ k}
  (hmem : .forward inputs outputs ∈ c.proc.atoms)
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs inputVals,
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.forward] at happ
  apply Config.Step.step_async_alt
    (aop := .forward k)
    (aop' := .forward k)
    happ
    (.interp_forward (k := k)
      (by simp)
      (by simp))
    hpop_inputs
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_fork
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {input : χ}
  {outputs : Vector χ k}
  (hmem : .fork input outputs ∈ c.proc.atoms)
  (hpop_input : c.chans.popVal input = some (inputVal, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs (Vector.replicate _ inputVal),
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.fork] at happ
  apply Config.Step.step_async_alt
    (aop := .fork k)
    (aop' := .fork k)
    (outputVals := Vector.replicate _ inputVal)
    happ
    (by
      apply AsyncOp.Interp.interp_fork (k := k)
        (outputs := outputs.toList)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      simp)
    (pop_val_to_pop_vals hpop_input)
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_const
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {val : V}
  {act : χ}
  {outputs : Vector χ k}
  (hmem : .const val act outputs ∈ c.proc.atoms)
  (hpop_act : c.chans.popVal act = some (actVal, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs (Vector.replicate _ val),
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.const] at happ
  apply Config.Step.step_async_alt
    (aop := .const val k)
    (aop' := .const val k)
    (outputVals := Vector.replicate _ val)
    happ
    (by
      apply AsyncOp.Interp.interp_const (k := k)
        (outputs := outputs.toList)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
    (pop_val_to_pop_vals hpop_act)
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_forwardc
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs : Vector χ k}
  {consts : Vector V l}
  {outputs : Vector χ (k + l)}
  (hmem : .forwardc inputs consts outputs ∈ c.proc.atoms)
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs (inputVals ++ consts),
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.forwardc] at happ
  apply Config.Step.step_async_alt
    (aop := .forwardc k l consts)
    (aop' := .forwardc k l consts)
    (outputVals := inputVals ++ consts)
    happ
    (by
      apply AsyncOp.Interp.interp_forwardc (k := k) (l := l)
        (inputs := inputs.toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
    hpop_inputs
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_sink
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs : Vector χ k}
  (hmem : .sink inputs ∈ c.proc.atoms)
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
    Step c .τ { c with chans := chans' }
  := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.sink] at happ
  apply Config.Step.step_async_alt
    (aop := .sink k)
    (aop' := .sink k)
    happ
    (by
      apply AsyncOp.Interp.interp_sink (k := k)
        (inputs := inputs.toList)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      exact #v[]; exact #v[])
    hpop_inputs
    |> Lts.Step.eq_rhs
  simp [ChanMap.pushVals]
  congr 1
  exact happ.symm

end AltStep

end Wavelet.Dataflow
