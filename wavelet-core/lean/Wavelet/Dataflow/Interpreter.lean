import Wavelet.Data.Basic
import Wavelet.Dataflow.Proc
import Wavelet.Semantics.OpInterp

/-! A simple executable interpreter for `Proc`. -/

namespace Wavelet.Dataflow

open Semantics

/-- Marks some operators as "trivial" for more realistic cycle counts and graph sizes. -/
def AtomicProc.isTrivial [Arity Op] : AtomicProc Op χ V → Bool
  | .async (AsyncOp.fork ..) ..
  | .async (AsyncOp.forward ..) ..
  | .async (AsyncOp.forwardc ..) ..
  | .async (AsyncOp.inact ..) ..
  | .async (AsyncOp.const ..) ..
  | .async (AsyncOp.sink ..) .. => true
  | _ => false

/-- More performant replacement for `ChanMap` only for the interpreter. -/
private abbrev ChanMapImpl χ V [DecidableEq χ] [Hashable χ] := Std.HashMap χ (List V)

/-- More performant replacement for `Config`. -/
private structure ConfigImpl Op χ V m n [Arity Op] [DecidableEq χ] [Hashable χ] where
  inputs: Vector χ m
  outputs: Vector χ n
  atoms: Array (AtomicProc Op χ V)
  chans: ChanMapImpl χ V

namespace ChanMapImpl

variable {χ V : Type} [DecidableEq χ] [Hashable χ]

private def pushVal (name : χ) (val : V) (map : ChanMapImpl χ V) : ChanMapImpl χ V :=
  map.insert name (map.getD name [] ++ [val])

private def pushVals (names : Vector χ n) (vals : Vector V n) (map : ChanMapImpl χ V) : ChanMapImpl χ V :=
  (names.zip vals).foldl (λ map (n, v) => pushVal n v map) map

private def popVal (name : χ) (map : ChanMapImpl χ V) : Option (V × ChanMapImpl χ V) :=
  match map.getD name [] with
  | [] => none
  | v :: vs => some (v, map.insert name vs)

private def popVals (names : Vector χ n) (map : ChanMapImpl χ V) : Option (Vector V n × ChanMapImpl χ V) :=
  match n with
  | 0 => some (#v[], map)
  | _ + 1 => do
    let (vals', map') ← popVals names.pop map
    let (val, map'') ← popVal names.back map'
    return (vals'.push val, map'')

end ChanMapImpl

variable {Op χ V : Type} {M : Type → Type} {m n : Nat}
variable [Arity Op] [InterpConsts V] [OpInterpM Op V M] [Monad M]
variable [DecidableEq χ] [Hashable χ]

namespace ConfigImpl

private def assume (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then pure ⟨h⟩ else failure

/-- Convert a `Config` to a `ConfigImpl`. -/
private def fromConfig (c : Config Op χ V m n) : ConfigImpl Op χ V m n :=
  let chans := allNames.foldl (init := .emptyWithCapacity) λ map name =>
    if map.contains name then map
    else map.insert name (c.chans name)
  { inputs := c.proc.inputs
    outputs := c.proc.outputs
    atoms := c.proc.atoms.toArray
    chans := chans }
  where
    allNames : List χ :=
      let fromAtoms := c.proc.atoms.foldl (init := []) λ acc ap =>
        acc ++ ap.inputs ++ ap.outputs
      c.proc.inputs.toList ++ c.proc.outputs.toList ++ fromAtoms

/-- Convert a `ConfigImpl` back to a `Config`. -/
private def toConfig (c : ConfigImpl Op χ V m n) : Config Op χ V m n :=
  { proc := { inputs := c.inputs
              outputs := c.outputs
              atoms := c.atoms.toList }
    chans := λ name => c.chans.getD name [] }

/-- Attempts to step the specified atomic process using array indexing. -/
private def stepAtom (idx : Nat) (c : ConfigImpl Op χ V m n)
  : Option (M (Label Op V m n × ConfigImpl Op χ V m n))
  := do
  let ⟨_⟩ ← assume (idx < c.atoms.size)
  let ap := c.atoms[idx]
  match ap with
  | .op o inputs outputs => do
    let (inputVals, chans') ← c.chans.popVals inputs
    return OpInterpM.interp o inputVals >>= λ outputVals => do
      let chans'' := chans'.pushVals outputs outputVals
      return (.yield o inputVals outputVals, { c with chans := chans'' })
  | .async (.switch k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k + k)
    let (deciderVal, chans₁) ← c.chans.popVal decider
    let (inputVals, chans₂) ← chans₁.popVals inputs.toVector
    let deciderBool ← InterpConsts.toBool deciderVal
    let outputs' := if deciderBool then outputs.take k else outputs.drop k
    return pure (.τ, {
      c with
      chans := chans₂.pushVals outputs'.toVector (inputVals.cast (by grind)),
    })
  | .async (.steer flavor k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k)
    let (deciderVal, chans₁) ← c.chans.popVal decider
    let (inputVals, chans₂) ← chans₁.popVals inputs.toVector
    let deciderBool ← InterpConsts.toBool deciderVal
    return pure (.τ, {
      c with
      chans :=
        if deciderBool = flavor then
          chans₂.pushVals outputs.toVector (inputVals.cast (by grind))
        else chans₂,
    })
  | .async (AsyncOp.merge .decider k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k + k ∧ outputs.length = k)
    let (deciderVal, chans') ← c.chans.popVal decider
    let deciderBool ← InterpConsts.toBool deciderVal
    return pure (.τ, {
      c with
      atoms := c.atoms.set idx
        (.async (AsyncOp.merge (if deciderBool then .popRight else .popLeft) k)
          (decider :: inputs) outputs),
      chans := chans',
    })
  | .async (AsyncOp.merge .popLeft k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k + k ∧ outputs.length = k)
    let (inputVals, chans') ← c.chans.popVals (inputs.take k).toVector
    return pure (.τ, {
      c with
      atoms := c.atoms.set idx
        (.async (AsyncOp.merge .decider k) (decider :: inputs) outputs),
      chans := chans'.pushVals outputs.toVector (inputVals.cast (by grind)),
    })
  | .async (AsyncOp.merge .popRight k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k + k ∧ outputs.length = k)
    let (inputVals, chans') ← c.chans.popVals (inputs.drop k).toVector
    return pure (.τ, {
      c with
      atoms := c.atoms.set idx
        (.async (AsyncOp.merge .decider k) (decider :: inputs) outputs),
      chans := chans'.pushVals outputs.toVector (inputVals.cast (by grind)),
    })
  | .async (AsyncOp.forward k) inputs outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k)
    let (inputVals, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      c with
      chans := chans'.pushVals outputs.toVector (inputVals.cast (by grind)),
    })
  | .async (.fork k) [input] outputs => do
    let ⟨h⟩ ← assume (outputs.length = k)
    let (inputVal, chans') ← c.chans.popVal input
    let outputVals := Vector.replicate k inputVal
    return pure (.τ, {
      c with
      chans := chans'.pushVals outputs.toVector (outputVals.cast (by grind)),
    })
  | .async (AsyncOp.order k) inputs [output] => do
    let ⟨h⟩ ← assume (inputs.length = k)
    let (inputVals, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      c with
      chans := chans'.pushVal output (inputVals[0]'(by
        rename NeZero _ => h';
        have h' := h'.ne; omega)),
    })
  | .async (.const v k) [act] outputs => do
    let ⟨h⟩ ← assume (outputs.length = k)
    let (_, chans') ← c.chans.popVal act
    let outputVals := Vector.replicate k v
    return pure (.τ, {
      c with
      chans := chans'.pushVals outputs.toVector (outputVals.cast (by grind)),
    })
  | .async (AsyncOp.forwardc k l consts) inputs outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k + l)
    let (inputVals, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      c with
      chans := chans'.pushVals outputs.toVector ((inputVals ++ consts).cast (by grind)),
    })
  | .async (AsyncOp.sink k) inputs [] => do
    let ⟨h⟩ ← assume (inputs.length = k)
    let (_, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      c with
      chans := chans',
    })
  | .async (AsyncOp.inv flavor none) [decider, input] [output] => do
    let (inputVal, chans') ← c.chans.popVal input
    if ¬ InterpConsts.isClonable inputVal then
      failure
    return pure (.τ, {
      c with
      atoms := c.atoms.set idx
        (.async (AsyncOp.inv flavor (some inputVal)) [decider, input] [output]),
      chans := chans'.pushVal output inputVal,
    })
  | .async (AsyncOp.inv flavor (some invVal)) [decider, input] [output] => do
    let (deciderVal, chans') ← c.chans.popVal decider
    let deciderBool ← InterpConsts.toBool deciderVal
    if deciderBool = flavor then
      return pure (.τ, {
        c with
        chans := chans'.pushVal output invVal,
      })
    else
      return pure (.τ, {
        c with
        atoms := c.atoms.set idx
          (.async (AsyncOp.inv flavor none) [decider, input] [output]),
        chans := chans',
      })
  | _ => failure

private def eagerStep
  (c : ConfigImpl Op χ V m n)
  (filter : AtomicProc Op χ V → Bool := λ _ => true) :
    M (Array (Nat × Label Op V m n) × ConfigImpl Op χ V m n)
  :=
  let fireable := (Array.finRange c.atoms.size).filter
    λ idx : Fin _ =>
      filter c.atoms[idx] &&
      (c.stepAtom (M := M) idx).isSome
  fireable.foldlM
    (init := (#[], c))
    λ (trace, c) (idx : Fin _) =>
      match c.stepAtom (M := M) idx with
      | some m => do let (label, c') ← m; return (trace.push (idx, label), c')
      | none => pure (trace, c)

private partial def eagerNonTrivialStep
  (c : ConfigImpl Op χ V m n) :
    M (Array (Nat × Label Op V m n) × ConfigImpl Op χ V m n)
  := do
  let (tr, c') ← eagerStep c
  fireAllTrivialStep tr c'
  where
    fireAllTrivialStep tr c := do
      let (tr', c') ← eagerStep c (·.isTrivial)
      if tr'.isEmpty then
        return (tr, c)
      else
        fireAllTrivialStep (tr ++ tr') c'

/-- Performs at most `bound` eager steps or until termination. -/
private partial def eagerSteps
  (bound : Option Nat := none)
  (c : ConfigImpl Op χ V m n) :
    M (List (List (Nat × Label Op V m n)) × ConfigImpl Op χ V m n) := do
  if let some 0 := bound then
    return ([], c)
  let (tr, c') ← c.eagerStep (M := M)
  if tr.isEmpty then
    return ([], c)
  let (tail, c'') ← eagerSteps (Nat.pred <$> bound) c'
  return (tr.toList :: tail, c'')

/-- Performs at most `bound` eager steps or until termination,
at each step, trivial operators like fork/const are fired repeatedly
until no trivial operators are fireable any more. -/
private partial def eagerNonTrivialSteps
  (bound : Option Nat := none)
  (c : ConfigImpl Op χ V m n) :
    M (List (List (Nat × Label Op V m n)) × ConfigImpl Op χ V m n) := do
  if let some 0 := bound then
    return ([], c)
  let (tr, c') ← c.eagerNonTrivialStep (M := M)
  if tr.isEmpty then
    return ([], c)
  let (tail, c'') ← eagerNonTrivialSteps (Nat.pred <$> bound) c'
  return (tr.toList :: tail, c'')

end ConfigImpl

def Config.pushInputs
  (c : Config Op χ V m n) (inputVals : Vector V m) :
    Config Op χ V m n :=
  { c with chans := c.chans.pushVals c.proc.inputs inputVals }

def Config.popOutputs
  (c : Config Op χ V m n) :
    Option (Vector V n × Config Op χ V m n) := do
  let (outputVals, chans') ← c.chans.popVals c.proc.outputs
  return (outputVals, { c with chans := chans' })

/-- Fires all fireable operators at once, and returns the
list of fired operators and the resulting config. -/
def Config.eagerStep (c : Config Op χ V m n)
  : M (List (Nat × Label Op V m n) × Config Op χ V m n) := do
  let (trace, c') ← (ConfigImpl.fromConfig c).eagerStep (M := M)
  return (trace.toList, c'.toConfig)

/-- Performs at most `bound` eager steps or until termination,
and returns the trace as a list of (non-empty) sets of operators
fired at each step. -/
def Config.eagerSteps
  (bound : Option Nat := none)
  (c : Config Op χ V m n) :
    M (List (List (Nat × Label Op V m n)) × Config Op χ V m n) := do
  let (trace, c') ← (ConfigImpl.fromConfig c).eagerSteps (M := M) bound
  return (trace, c'.toConfig)

/-- Similar to `Config.eagerSteps`, but one step is considered to include
firing of all available operators *followed by* any trivial operators. -/
def Config.eagerNonTrivialSteps
  (bound : Option Nat := none)
  (c : Config Op χ V m n) :
    M (List (List (Nat × Label Op V m n)) × Config Op χ V m n) := do
  let (trace, c') ← (ConfigImpl.fromConfig c).eagerNonTrivialSteps (M := M) bound
  return (trace, c'.toConfig)

end Wavelet.Dataflow
