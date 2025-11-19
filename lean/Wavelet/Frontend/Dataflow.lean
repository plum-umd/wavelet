import Wavelet.Data.Basic
import Wavelet.Dataflow.Proc

/-! A JSON format for dataflow graphs (`Proc`). -/

namespace Wavelet.Frontend

open Semantics Dataflow

inductive RawMergeState where
  | popLeft
  | popRight
  | decider
  deriving Repr, Lean.ToJson, Lean.FromJson

inductive RawAsyncOp V where
  | switch (n : Nat) : RawAsyncOp V
  | steer (flavor : Bool) (n : Nat) : RawAsyncOp V
  | merge (state : RawMergeState) (n : Nat) : RawAsyncOp V
  | forward (n : Nat) : RawAsyncOp V
  | fork (n : Nat) : RawAsyncOp V
  | order (n : Nat) : RawAsyncOp V
  | const (c : V) (n : Nat) : RawAsyncOp V
  | forwardc (n m : Nat) (consts : List V) : RawAsyncOp V
  | sink (n : Nat) : RawAsyncOp V
  | inv (flavor : Bool) (c : Option V) : RawAsyncOp V
  | inact (n : Nat) : RawAsyncOp V
  deriving Repr, Lean.ToJson, Lean.FromJson

inductive RawAtomicProc (Op : Type u) χ V where
  | op (op : Op) (inputs : List χ) (outputs : List χ) : RawAtomicProc Op χ V
  | async (op : RawAsyncOp V) (inputs : List χ) (outputs : List χ) : RawAtomicProc Op χ V
  deriving Repr, Lean.ToJson, Lean.FromJson

structure RawProc (Op : Type u) (χ : Type v) (V : Type w) where
  inputs : List χ
  outputs : List χ
  atoms : List (RawAtomicProc Op χ V)
  deriving Repr, Lean.ToJson, Lean.FromJson

instance : Coe AsyncOp.MergeState RawMergeState where
  coe | .popLeft => .popLeft
      | .popRight => .popRight
      | .decider => .decider

instance : Coe RawMergeState AsyncOp.MergeState where
  coe | .popLeft => .popLeft
      | .popRight => .popRight
      | .decider => .decider

instance : Coe (AsyncOp V) (RawAsyncOp V) where
  coe
    | AsyncOp.switch n => .switch n
    | AsyncOp.steer flavor n => .steer flavor n
    | AsyncOp.merge state n => .merge ↑state n
    | AsyncOp.forward n => .forward n
    | AsyncOp.fork n => .fork n
    | AsyncOp.order n => .order n
    | AsyncOp.const c n => .const c n
    | AsyncOp.forwardc n m consts => .forwardc n m consts.toList
    | AsyncOp.sink n => .sink n
    | AsyncOp.inv flavor c => .inv flavor c
    | AsyncOp.inact n => .inact n

instance [Arity Op] : Coe (AtomicProc Op χ V) (RawAtomicProc Op χ V) where
  coe
    | AtomicProc.op op inputs outputs => .op op inputs.toList outputs.toList
    | AtomicProc.async op inputs outputs => .async ↑op inputs outputs

def RawProc.fromProc [Arity Op] (proc : Proc Op χ V m n) : RawProc Op χ V :=
  {
    inputs := proc.inputs.toList,
    outputs := proc.outputs.toList,
    atoms := proc.atoms.map (↑·),
  }

def RawAsyncOp.toAsyncOp : RawAsyncOp V → Except String (AsyncOp V)
  | switch n => return .switch n
  | steer flavor n => return .steer flavor n
  | merge state (n + 1) => return .merge ↑state (n + 1)
  | merge _ 0 => throw "merge operator must have at least one output"
  | forward (n + 1) => return .forward (n + 1)
  | forward 0 => throw "forward operator must have at least one output"
  | fork n => return .fork n
  | order (n + 1) => return .order (n + 1)
  | order 0 => throw "order operator must have at least one output"
  | const c n => return .const c n
  | forwardc (n + 1) m consts =>
    if consts.length ≠ m then
      throw s!"forwardc operator consts length mismatch: expected {m}, got {consts.length}"
    else
      return .forwardc (n + 1) consts.length consts.toVector
  | forwardc 0 _ _ => throw "forwardc operator must have at least one output"
  | sink (n + 1) => return .sink (n + 1)
  | sink 0 => throw "sink operator must have at least one output"
  | inv flavor c => return .inv flavor c
  | inact n => return .inact n

def RawAtomicProc.toAtomicProc [Arity Op] [Repr Op] [Repr χ] [Repr V] :
  RawAtomicProc Op χ V → Except String (AtomicProc Op χ V)
  | op o inputs outputs => do
    if h₁ : inputs.length = Arity.ι o then
      if h₂ : outputs.length = Arity.ω o then
        return .op o
          (inputs.toVector.cast (by simp [h₁]))
          (outputs.toVector.cast (by simp [h₂]))
      else
        throw s!"output arity mismatch for op `{repr o}`: expected {Arity.ω o}, got {outputs.length}"
    else
      throw s!"input arity mismatch for op `{repr o}`: expected {Arity.ι o}, got {inputs.length}"
  | ap@(async aop inputs outputs) => do
    let aop' ← aop.toAsyncOp
      |>.mapError (λ err => s!"when parsing atomic proc: `{repr ap}`")
    if h₁ : inputs.length = aop'.ι then
      if h₂ : outputs.length = aop'.ω then
        return .async aop' inputs outputs
      else
        throw s!"output arity mismatch for async op `{repr aop}`: expected {aop'.ω}, got {outputs.length}"
    else
      throw s!"input arity mismatch for async op `{repr aop}`: expected {aop'.ι}, got {inputs.length}"

/-- Converts a `RawProc` to `Proc` with some dynamic arity checks. -/
def RawProc.toProc [Arity Op] [Repr Op] [Repr χ] [Repr V] (raw : RawProc Op χ V) :
  Except String (Proc Op χ V raw.inputs.length raw.outputs.length) :=
  return {
    inputs := raw.inputs.toVector,
    outputs := raw.outputs.toVector,
    atoms := ← raw.atoms.mapM RawAtomicProc.toAtomicProc,
  }

section Examples

-- #eval Lean.ToJson.toJson (RawAsyncOp.switch 3 : RawAsyncOp Nat)
-- #eval Lean.ToJson.toJson (RawAsyncOp.inact : RawAsyncOp Nat)
-- #eval Lean.ToJson.toJson ({
--     inputs := ["decider", "a", "b"],
--     outputs := ["d"],
--     atoms := [
--       .async (RawAsyncOp.steer true 1) ["decider", "a", "b"] ["c"],
--       .op "id" ["c"] ["d"],
--     ]
--   } : RawProc String String Nat)

end Examples

end Wavelet.Frontend
