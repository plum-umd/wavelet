import Wavelet.Semantics.Defs

/-!
Syntax and semantics of built-in asynchronous operators.

Async operators (in dataflow literature) are operators that can
  1. Choose the input channels to read from depending on their internal state, and
  2. Choose the output channels to write to depending on input values.

They are contrasted with synchronous operators, which always read a fixed
number of values (fixed to 1 in our case) from each input channel, and
push a fixed number of values to each output channel (also fixed to 1 in
our formulation).
-/

namespace Wavelet.Dataflow

open Semantics

/-! Local state of a merge gate -/
inductive AsyncOp.MergeState where
  | popLeft
  | popRight
  | decider

/-- Built-in asynchronous operators: `AsyncOp ... m n`
is an asynchronous operator with a total of `m` inputs
ports and `n` outputs ports. -/
inductive AsyncOp V where
  | switch (n : Nat) : AsyncOp V
  | steer (flavor : Bool) (n : Nat) : AsyncOp V
  | merge (state : AsyncOp.MergeState) (n : Nat) [NeZero n] : AsyncOp V
  | forward (n : Nat) [NeZero n] : AsyncOp V
  | fork (n : Nat) : AsyncOp V
  | order (n : Nat) [NeZero n] : AsyncOp V
  | const (c : V) (n : Nat) : AsyncOp V
  -- A combination of `forward` and `const` to wait for inputs to arrive,
  -- forward the inputs to the first `n` outputs, and then send constants
  -- to the last `m` outputs.
  | forwardc (n m : Nat) (consts : Vector V m) [NeZero n] : AsyncOp V
  | sink (n : Nat) [NeZero n] : AsyncOp V
  | inv (flavor : Bool) (c : Option V) : AsyncOp V
  | inact (n : Nat) : AsyncOp V

/-- Input arity of an async operator. -/
def AsyncOp.ι : AsyncOp V → Nat
  | switch n => n + 1
  | steer _ n => n + 1
  | merge _ n => n + n + 1
  | forward n => n
  | fork _ => 1
  | order n => n
  | const _ _ => 1
  | forwardc n _ _ => n
  | sink n => n
  | inv _ _ => 2
  | inact _ => 0

/-- Output arity of an async operator. -/
def AsyncOp.ω : AsyncOp V → Nat
  | switch n => n + n
  | steer _ n => n
  | merge _ n => n
  | forward n => n
  | fork n => n
  | order _ => 1
  | const _ n => n
  | forwardc n m _ => n + m
  | sink _ => 0
  | inv _ _ => 1
  | inact n => n

namespace AsyncOp

structure Label χ V where
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
inductive Interp
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
  | interp_merge_left [NeZero k] :
    inputs.length = k + k →
    outputs.length = k →
    Interp (.merge .popLeft k)
      (.mk (decider :: inputs) outputs
        (inputs.take k) inputVals
        outputs inputVals)
      (.merge .decider k)
  | interp_merge_right [NeZero k] :
    inputs.length = k + k →
    outputs.length = k →
    Interp (.merge .popRight k)
      (.mk (decider :: inputs) outputs
        (inputs.drop k) inputVals
        outputs inputVals)
      (.merge .decider k)
  | interp_merge_decider [NeZero k] :
    inputs.length = k + k →
    outputs.length = k →
    InterpConsts.toBool deciderVal = some deciderBool →
    Interp (.merge .decider k)
      (.mk (decider :: inputs) outputs
        [decider] [deciderVal]
        [] [])
      (.merge (if deciderBool then .popRight else .popLeft) k)
  | interp_forward [NeZero k] :
    inputs.length = k →
    outputs.length = k →
    Interp (.forward k)
      (.mk inputs outputs
        inputs inputVals
        outputs inputVals)
      (.forward k)
  | interp_fork :
    outputs.length = k →
    -- This is to dynamically forbid cloning, e.g., permission tokens.
    InterpConsts.isClonable inputVal →
    Interp (.fork k)
      (.mk [input] outputs
        [input] [inputVal]
        outputs (.replicate k inputVal))
      (.fork k)
  | interp_order [NeZero k] :
    inputs.length = k →
    (h : inputVals.length = k) →
    Interp (.order k)
      (.mk inputs [output]
        inputs inputVals
        [output] [inputVals[0]'(by have := NeZero.ne k; omega)])
      (.order k)
  | interp_const :
    outputs.length = k →
    Interp (.const c k)
      (.mk [act] outputs
        [act] [actVal]
        outputs (.replicate k c))
      (.const c k)
  | interp_forwardc [NeZero k] :
    inputs.length = k →
    outputs.length = k + l →
    Interp (.forwardc k l consts)
      (.mk inputs outputs
        inputs inputVals
        outputs (inputVals ++ consts.toList))
      (.forwardc k l consts)
  | interp_sink [NeZero k] :
    inputs.length = k →
    Interp (.sink k)
      (.mk inputs []
        inputs inputVals
        [] [])
      (.sink k)
  -- An invariant waiting for the initial input
  | interp_inv_init :
    inputs.length = 1 →
    outputs.length = 1 →
    InterpConsts.isClonable inputVal →
    Interp (.inv flavor none)
      (.mk (decider :: inputs) outputs
        inputs [inputVal]
        outputs [inputVal])
      (.inv flavor (some inputVal))
  -- An invariant reading a true decider
  | interp_inv_true :
    inputs.length = 1 →
    outputs.length = 1 →
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool = flavor →
    Interp (.inv flavor (some val))
      (.mk (decider :: inputs) outputs
        [decider] [deciderVal]
        outputs [val])
      (.inv flavor (some val))
  -- An invariant reading a false decider and restoring to the initial state
  | interp_inv_false :
    inputs.length = 1 →
    outputs.length = 1 →
    InterpConsts.toBool deciderVal = some deciderBool →
    deciderBool ≠ flavor →
    Interp (.inv flavor (some val))
      (.mk (decider :: inputs) outputs
        [decider] [deciderVal]
        [] [])
      (.inv flavor none)

theorem Interp.eq_label
  [InterpConsts V]
  {aop aop' : AsyncOp V}
  {label₁ label₂ : AsyncOp.Label χ V}
  (hinterp₁ : aop.Interp label₁ aop')
  (heq : label₁ = label₂) : aop.Interp label₂ aop'
  := by
  simp [heq] at hinterp₁
  exact hinterp₁

/-- In every state, an async operator always deterministically chooses the input channels to read. -/
theorem Interp.det_inputs
  [InterpConsts V]
  {aop aop₁' aop₂' : AsyncOp V}
  (hinterp₁ : aop.Interp (.mk allInputs allOutputs₁ inputs₁ inputVals₁ outputs₁ outputVals₁) aop₁')
  (hinterp₂ : aop.Interp (.mk allInputs allOutputs₂ inputs₂ inputVals₂ outputs₂ outputVals₂) aop₂') :
    inputs₁ = inputs₂
  := by
  cases hinterp₁ <;> cases hinterp₂
  all_goals rfl

/-- If the input values are the same, every async operator has deterministic outputs. -/
theorem Interp.det_outputs
  [InterpConsts V]
  {aop aop₁' aop₂' : AsyncOp V}
  (hinterp₁ : aop.Interp (.mk allInputs allOutputs inputs₁ inputVals₁ outputs₁ outputVals₁) aop₁')
  (hinterp₂ : aop.Interp (.mk allInputs allOutputs inputs₂ inputVals₂ outputs₂ outputVals₂) aop₂')
  (heq : inputVals₁ = inputVals₂) :
    inputs₁ = inputs₂ ∧
    outputs₁ = outputs₂ ∧
    outputVals₁ = outputVals₂ ∧
    aop₁' = aop₂'
  := by
  cases hinterp₁ <;> cases hinterp₂
  any_goals grind only [cases Or]

/-- Inputs read in each async op is a sublist of the total input list. -/
theorem Interp.input_sublist
  [InterpConsts V]
  {aop aop' : AsyncOp V}
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals)
    aop') :
  inputs.Sublist allInputs := by
  cases hinterp
  any_goals simp [List.take_sublist, List.drop_sublist]

/-- Outputs read in each async op is a sublist of the total output list. -/
theorem Interp.output_sublist
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

end AsyncOp

end Wavelet.Dataflow
