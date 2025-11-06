import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.Plot
import Wavelet.Semantics.OpInterp
import Wavelet.Determinacy.OpSpec
import Wavelet.Compile.Rewrite.Defs

import Wavelet.Frontend.Seq

/-! A formalization of the operator set of RipTide (https://ieeexplore.ieee.org/document/9923793). -/

namespace Wavelet.Frontend.RipTide

open Semantics Determinacy Compile

-- TODO: Using Int for now since `Int32` doesn't implement ToJson/FromJson
abbrev Value := Int

/-- Synchronous operators in RipTide, parametrized by a type of location/array symbols. -/
inductive SyncOp (Loc : Type u) : Type u where
  | add | sub | mul | div
  | shl | ashr | lshr
  | eq | lt | le
  | and
  | load (_ : Loc) | store (_ : Loc) | sel
  | const (_ : Value)
  | copy (_ : Nat)
  deriving Repr, Lean.ToJson, Lean.FromJson

instance : Arity (SyncOp Loc) where
  ι | .add => 2 | .sub => 2 | .mul => 2 | .div => 2
    | .shl => 2 | .ashr => 2 | .lshr => 2
    | .eq => 2 | .lt => 2 | .le => 2
    | .and => 2
    | .load _ => 1 | .store _ => 2 | .sel => 3
    | .const _ => 1 | .copy _ => 1
  ω | .add => 1 | .sub => 1 | .mul => 1 | .div => 1
    | .shl => 1 | .ashr => 1 | .lshr => 1
    | .eq => 1 | .lt => 1 | .le => 1
    | .and => 1
    | .load _ => 1 | .store _ => 1 | .sel => 1
    | .const _ => 1
    -- NOTE: `copy n` outputs `n + 1` values
    | .copy n => n + 1

instance : NeZeroArity (SyncOp Loc) where
  neZeroᵢ op := by cases op <;> infer_instance
  neZeroₒ op := by cases op <;> infer_instance

/-- Some constants used for compilation. -/
instance : InterpConsts Value where
  junkVal := -1
  toBool | 0 => some false
         | 1 => some true
         | _ => none
  fromBool b := if b then 1 else 0
  unique_fromBool_toBool b := by cases b <;> simp
  unique_toBool_fromBool b v h := by
    split at h <;> simp at h <;> subst h <;> decide
  isClonable _ := true
  bool_clonable := by simp

structure State (Loc : Type u) : Type u where
  memory : Loc → Value → Value

def State.init : State Loc := { memory := λ _ _ => 0 }

def State.load (s : State Loc) (loc : Loc) (addr : Value) : Value :=
  s.memory loc addr

def State.store [DecidableEq Loc]
  (s : State Loc) (loc : Loc) (addr : Value) (val : Value) : State Loc :=
  { s with
    memory := Function.update s.memory loc
      (Function.update (s.memory loc) addr val) }

inductive InterpOp [DecidableEq Loc] : Lts (State Loc) (RespLabel (SyncOp Loc) Value) where
  | interp_add
    {inputs : Vector Value 2}
    {outputs : Vector Value 1} :
    outputs[0] = inputs[0] + inputs[1] →
    InterpOp s (.respond .add inputs outputs) s
  -- TODO: other pure operators
  | interp_load
    {inputs : Vector Value 1}
    {outputs : Vector Value 1} :
    outputs[0] = s.memory loc inputs[0] →
    InterpOp s (.respond (SyncOp.load loc) inputs outputs) s
  | interp_store
    {inputs : Vector Value 2} :
    InterpOp s (.respond (SyncOp.store loc) inputs #v[0])
      (s.store loc inputs[0] inputs[1])

def opInterp [DecidableEq Loc] :
  OpInterp (SyncOp Loc) Value := {
    S := State Loc,
    init := State.init,
    lts := InterpOp,
  }

/-- TODO: Actually define the pre/post conditions. -/
def opSpec : OpSpec (SyncOp Loc) Value (PCM.FractionPerm Loc) :=
  {
    pre | _, _ => PCM.zero,
    post | _, _, _ => PCM.zero,
  }

instance [Lean.FromJson Loc] : Lean.FromJson (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) where
  fromJson? json :=
    (do
      let obj ← json.getObjVal? "op_ghost"
      return .op true (← Lean.FromJson.fromJson? obj)) <|>
    (do
      let obj ← json.getObjVal? "op"
      return .op false (← Lean.FromJson.fromJson? obj)) <|>
    (do
      let obj ← json.getObjVal? "join"
      let k ← obj.getObjValAs? Nat "toks"
      let l ← obj.getObjValAs? Nat "deps"
      if h : k = 0 then
        throw "the join operator requires at least one token argument"
      else
        let : NeZero k := .mk h
        -- TODO: currently not parsing permission annotations
        return .join k l (λ _ => PCM.zero)) <|>
    (.error s!"failed to parse RipTide operator {json}")

instance [Lean.ToJson Loc] : Lean.ToJson (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) where
  toJson
    | WithSpec.op true op =>
      json% { "op_ghost": $(op) }
    | WithSpec.op false op =>
      json% { "op": $(op) }
    | WithSpec.join k l _ =>
      json% { "join": { "toks": $(k), "deps": $(l) } }

section Examples

def prog₁ :
    RawProg
      (WithCall (WithSpec (RipTide.SyncOp String) RipTide.opSpec) String)
      String
  := ⟨[
    {
      name := "sum",
      params := ["sum", "i", "n", "t₀"],
      outputs := 2,
      body :=
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₀"] ["t₁", "t₂"] <|
        .op (.op (.op false (.copy 3))) ["i"] ["i₁", "i₂", "i₃", "i₄", "dummy₁"] <|
        .op (.op (.op false (.copy 1))) ["n"] ["n₁", "n₂", "dummy₂"] <|
        .op (.op (.op false .lt)) ["i₁", "n₁"] ["c", "dummy₃"] <|
        .br "c"
          (.op (.op (.op true (.load "A"))) ["i₂", "t₁"] ["x", "t₁'"] <|
           .op (.op (.op false .add)) ["sum", "x"] ["sum'", "dummy₄"] <|
           .op (.op (.op false (.const 1))) ["i₃"] ["one", "dummy₅"] <|
           .op (.op (.op false .add)) ["i₄", "one"] ["i'", "dummy₆"] <|
            .tail ["sum'", "i'", "n₂", "t₂"])
          (.ret ["sum", "t₂"]),
    }
  ]⟩

-- #eval (prog₁.toProg (V := Nat)).map (λ _ => ())
-- #eval Lean.ToJson.toJson prog₁

end Examples

instance [ToString Loc] : Dataflow.DotName (SyncOp Loc) where
  dotName
    | .add => "\"+\""
    | .sub => "\"-\""
    | .mul => "\"*\""
    | .div => "\"/\""
    | .shl => "\"<<\""
    | .ashr => "\"a>>\""
    | .lshr => "\"l>>\""
    | .eq => "\"=\""
    | .lt => "\"<\""
    | .le => "\"<=\""
    | .and => "\"&&\""
    | .load loc => s!"<LD<sub>{loc}</sub>>"
    | .store loc => s!"<ST<sub>{loc}</sub>>"
    | .sel => "\"SEL\""
    | .const v => s!"\"{v}\""
    | .copy .. => s!"\"CP\""

instance : Dataflow.DotName Value where
  dotName v := s!"\"{v}\""

/-- Custom rewrites for RipTide. -/
def operatorSel [DecidableEq χ] : Rewrite (RipTide.SyncOp Loc) χ Value :=
  .choose λ
  -- Lower `copy` to `fork`
  | .op (.copy n) inputs outputs =>
    return [.fork (inputs[0]'(by simp [Arity.ι])) outputs]
  -- Lower `const` to the built-in `const`
  | .op (.const v) inputs outputs =>
    return [.const v (inputs[0]'(by simp [Arity.ι])) outputs]
  -- Lower `switch` to two `steer`s
  -- This is optional but may enable more rewrites
  | .async (.switch 1) inputs outputs =>
    if h : inputs.length = 2 ∧ outputs.length = 2 then
      let decider := inputs[0]'(by omega)
      let input := inputs[1]'(by omega)
      let output₁ := outputs[0]'(by omega)
      let output₂ := outputs[1]'(by omega)
      return [
        .fork input #v[.rename 0 input, .rename 1 input],
        .fork decider #v[.rename 0 decider, .rename 1 decider],
        .steer true (.rename 0 decider) #v[.rename 0 input] #v[output₁],
        .steer false (.rename 1 decider) #v[.rename 1 input] #v[output₂],
      ]
    else failure
  | _ => failure

end Wavelet.Frontend.RipTide
