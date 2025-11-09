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
