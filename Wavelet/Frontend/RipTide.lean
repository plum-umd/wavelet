import Wavelet.Dataflow.Proc
import Wavelet.Semantics.OpInterp
import Wavelet.Determinacy.OpSpec

import Wavelet.Frontend.Seq

/-! A formalization of the operator set of RipTide (https://ieeexplore.ieee.org/document/9923793). -/

namespace Wavelet.Frontend.RipTide

open Semantics Determinacy

-- TODO: Using Int for now since `Int32` doesn't implement ToJson/FromJson
abbrev Value := Int

/-- Synchronous operators in RipTide, parametrized by a type of location/array symbols. -/
inductive SyncOp (Loc : Type u) : Type u where
  | add | sub | mul | div
  | shl | ashr | lshr
  | eq | lt
  | load (loc : Loc) | store (loc : Loc) | sel
  | const (v : Value)
  | fork (n : Nat)
  deriving Repr, Lean.ToJson, Lean.FromJson

instance : Arity (SyncOp Loc) where
  ι | .add => 2 | .sub => 2 | .mul => 2 | .div => 2
    | .shl => 2 | .ashr => 2 | .lshr => 2
    | .eq => 2 | .lt => 2
    | .load _ => 1 | .store _ => 2 | .sel => 3
    | .const _ => 1 | .fork _ => 1
  ω | .add => 1 | .sub => 1 | .mul => 1 | .div => 1
    | .shl => 1 | .ashr => 1 | .lshr => 1
    | .eq => 1 | .lt => 1
    | .load _ => 1 | .store _ => 0 | .sel => 1
    | .const _ => 1 | .fork n => n

instance : NeZeroArity (SyncOp Loc) where
  neZeroᵢ op := by cases op <;> infer_instance

/-- Some constants used for compilation. -/
instance : InterpConsts Value where
  junkVal := 0
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
    InterpOp s (.respond (SyncOp.store loc) inputs #v[])
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
    (return .op (← Lean.FromJson.fromJson? json)) <|>
    (do
      let obj ← json.getObjVal? "join"
      let k ← obj.getObjValAs? Nat "toks"
      let l ← obj.getObjValAs? Nat "deps"
      if h : k = 0 then
        throw "the join operator requires at least one token argument"
      else
        let : NeZero k := .mk h
        -- TODO: currently not parsing permission annotations
        return .join k l (λ _ => PCM.zero))

instance [Lean.ToJson Loc] : Lean.ToJson (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) where
  toJson
    | WithSpec.op op => Lean.ToJson.toJson op
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
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₁"] ["t₃", "t₄"] <|
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₂"] ["t₅", "t₆"] <|
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₃"] ["t₇", "t₈"] <|
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₄"] ["t₉", "t₁₀"] <|
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₅"] ["t₁₁", "t₁₂"] <|
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₆"] ["t₁₃", "t₁₄"] <|
        .op (.op (.op (.fork 4))) ["i", "t₇"] ["i₁", "i₂", "i₃", "i₄", "t₇'"] <|
        .op (.op (.op (.fork 2))) ["n", "t₈"] ["n₁", "n₂", "t₈'"] <|
        .op (.op (.op .lt)) ["i₁", "n₁", "t₉"] ["c", "t₉'"] <|
        .br "c"
          (.op (.op (.op (.load "A"))) ["i₂", "t₁₀"] ["x", "t₁₀'"] <|
           .op (.op (.op .add)) ["sum", "x", "t₁₁"] ["sum'", "t₁₁'"] <|
           .op (.op (.op (.const 1))) ["i₃", "t₁₂"] ["one", "t₁₂'"] <|
           .op (.op (.op .add)) ["i₄", "one", "t₁₃"] ["i'", "t₁₃'"] <|
            .tail ["sum'", "i'", "n₂", "t₁₄"])
          (.ret ["sum", "t₁₄"]),
    }
  ]⟩

#eval (prog₁.toProg (V := Nat)).map (λ _ => ())
#eval Lean.ToJson.toJson prog₁

end Examples

end Wavelet.Frontend.RipTide
