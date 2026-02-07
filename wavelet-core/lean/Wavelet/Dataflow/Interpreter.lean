import Wavelet.Data.Basic
import Wavelet.Dataflow.Proc
import Wavelet.Semantics.OpInterp

/-! A simple executable interpreter for `Proc`. -/

namespace Wavelet.Dataflow

open Semantics

variable {Op χ V : Type} {M : Type → Type}
variable [Arity Op] [InterpConsts V] [OpInterpM Op V M] [Monad M] [DecidableEq χ]

private def assume (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then pure ⟨h⟩ else failure

def Config.pushInputs [DecidableEq χ]
  (c : Config Op χ V m n) (inputVals : Vector V m) :
    Config Op χ V m n :=
  { c with
    chans := c.chans.pushVals c.proc.inputs inputVals }

def Config.popOutputs [DecidableEq χ]
  (c : Config Op χ V m n) :
    Option (Vector V n × Config Op χ V m n) := do
  let (outputVals, chans') ← c.chans.popVals c.proc.outputs
  return (outputVals, { c with chans := chans' })

/-- Attempts to step the specified atomic process, and if succeeds,
returns the monad interpretation of the atomic process. -/
def Config.stepAtom (idx : Nat) (c : Config Op χ V m n)
  : Option (M (Label Op V m n × Config Op χ V m n))
  := do
  let ap ← c.proc.atoms[idx]?
  match ap with
  | .op o inputs outputs => do
    let (inputVals, chans') ← c.chans.popVals inputs
    return OpInterpM.interp o inputVals >>= λ outputVals => do
      let chans'' := chans'.pushVals outputs outputVals
      return (.yield o inputVals outputVals, { proc := c.proc, chans := chans'' })
  | .async (.switch k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k + k)
    let (deciderVal, chans₁) ← c.chans.popVal decider
    let (inputVals, chans₂) ← chans₁.popVals inputs.toVector
    let deciderBool ← InterpConsts.toBool deciderVal
    let outputs' := if deciderBool then outputs.take k else outputs.drop k
    return pure (.τ, {
      proc := c.proc,
      chans := chans₂.pushVals outputs'.toVector (inputVals.cast (by grind)),
    })
  | .async (.steer flavor k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k)
    let (deciderVal, chans₁) ← c.chans.popVal decider
    let (inputVals, chans₂) ← chans₁.popVals inputs.toVector
    let deciderBool ← InterpConsts.toBool deciderVal
    return pure (.τ, {
      proc := c.proc,
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
      proc := { c.proc with
        atoms := c.proc.atoms.set idx
          (.async (AsyncOp.merge (if deciderBool then .popRight else .popLeft) k)
            (decider :: inputs) outputs)
      },
      chans := chans',
    })
  | .async (AsyncOp.merge .popLeft k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k + k ∧ outputs.length = k)
    let (inputVals, chans') ← c.chans.popVals (inputs.take k).toVector
    return pure (.τ, {
      proc := { c.proc with
        atoms := c.proc.atoms.set idx
          (.async (AsyncOp.merge .decider k) (decider :: inputs) outputs)
      },
      chans := chans'.pushVals outputs.toVector (inputVals.cast (by grind)),
    })
  | .async (AsyncOp.merge .popRight k) (decider :: inputs) outputs => do
    let ⟨h⟩ ← assume (inputs.length = k + k ∧ outputs.length = k)
    let (inputVals, chans') ← c.chans.popVals (inputs.drop k).toVector
    return pure (.τ, {
      proc := { c.proc with
        atoms := c.proc.atoms.set idx
          (.async (AsyncOp.merge .decider k) (decider :: inputs) outputs)
      },
      chans := chans'.pushVals outputs.toVector (inputVals.cast (by grind)),
    })
  | .async (AsyncOp.forward k) inputs outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k)
    let (inputVals, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      proc := c.proc,
      chans := chans'.pushVals outputs.toVector (inputVals.cast (by grind)),
    })
  | .async (.fork k) [input] outputs => do
    let ⟨h⟩ ← assume (outputs.length = k)
    let (inputVal, chans') ← c.chans.popVal input
    let outputVals := Vector.replicate k inputVal
    return pure (.τ, {
      proc := c.proc,
      chans := chans'.pushVals outputs.toVector (outputVals.cast (by grind)),
    })
  | .async (AsyncOp.order k) inputs [output] => do
    let ⟨h⟩ ← assume (inputs.length = k)
    let (inputVals, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      proc := c.proc,
      chans := chans'.pushVal output (inputVals[0]'(by
        rename NeZero _ => h';
        have h' := h'.ne; omega)),
    })
  | .async (.const v k) [act] outputs => do
    let ⟨h⟩ ← assume (outputs.length = k)
    let (_, chans') ← c.chans.popVal act
    let outputVals := Vector.replicate k v
    return pure (.τ, {
      proc := c.proc,
      chans := chans'.pushVals outputs.toVector (outputVals.cast (by grind)),
    })
  | .async (AsyncOp.forwardc k l consts) inputs outputs => do
    let ⟨h⟩ ← assume (inputs.length = k ∧ outputs.length = k + l)
    let (inputVals, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      proc := c.proc,
      chans := chans'.pushVals outputs.toVector ((inputVals ++ consts).cast (by grind)),
    })
  | .async (AsyncOp.sink k) inputs [] => do
    let ⟨h⟩ ← assume (inputs.length = k)
    let (_, chans') ← c.chans.popVals inputs.toVector
    return pure (.τ, {
      proc := c.proc,
      chans := chans',
    })
  | .async (AsyncOp.inv flavor none) [decider, input] [output] => do
    let (inputVal, chans') ← c.chans.popVal input
    if ¬ InterpConsts.isClonable inputVal then
      failure
    return pure (.τ, {
      proc := { c.proc with
        atoms := c.proc.atoms.set idx
          (.async (AsyncOp.inv flavor (some inputVal)) [decider, input] [output])
      },
      chans := chans'.pushVal output inputVal,
    })
  | .async (AsyncOp.inv flavor (some invVal)) [decider, input] [output] => do
    let (deciderVal, chans') ← c.chans.popVal decider
    let deciderBool ← InterpConsts.toBool deciderVal
    if deciderBool = flavor then
      return pure (.τ, {
        proc := c.proc,
        chans := chans'.pushVal output invVal,
      })
    else
      return pure (.τ, {
        proc := { c.proc with
          atoms := c.proc.atoms.set idx
            (.async (AsyncOp.inv flavor none) [decider, input] [output])
        },
        chans := chans',
      })
  | _ => failure

/-- An executable stepping relation that returns the current list of
fireable operators and their monadic interpretations. -/
def Config.step (c : Config Op χ V m n)
  : List (Nat × M (Label Op V m n × Config Op χ V m n)) := do
  let idx ← List.range c.proc.atoms.length
  (c.stepAtom idx).toList.map (idx, ·)

/-- An eager stepping relation that fires all fireable operator once. -/
def Config.eagerStep (c : Config Op χ V m n)
  : M (List (Nat × Label Op V m n) × Config Op χ V m n) :=
  (List.range c.proc.atoms.length)
    |>.filter (λ idx => (c.stepAtom (M := M) idx).isSome)
    |>.foldlM
      (init := ([], c))
      λ (trace, c) idx => do
        match c.stepAtom idx with
        | some m =>
          let (label, c') ← m
          return (trace ++ [(idx, label)], c')
        | none => pure (trace, c)

end Wavelet.Dataflow
