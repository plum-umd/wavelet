import Wavelet.Data.Except
import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.Plot
import Wavelet.Dataflow.Interpreter
import Wavelet.Semantics.OpInterp
import Wavelet.Determinacy.OpSpec
import Wavelet.Compile.Rewrite.Defs

import Wavelet.Frontend.Dataflow

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
  | eq | lt | le | neq
  | and
  | bitand
  | load (_ : Loc) | store (_ : Loc) | sel
  | const (_ : Value)
  | copy (_ : Nat)
  deriving Repr, Lean.ToJson, Lean.FromJson

instance : Arity (SyncOp Loc) where
  ι | .add => 2 | .sub => 2 | .mul => 2 | .div => 2
    | .shl => 2 | .ashr => 2 | .lshr => 2
    | .eq => 2 | .lt => 2 | .le => 2 | .neq => 2
    | .and => 2
    | .bitand => 2
    | .load _ => 1 | .store _ => 2 | .sel => 3
    | .const _ => 1 | .copy _ => 1
  ω | .add => 1 | .sub => 1 | .mul => 1 | .div => 1
    | .shl => 1 | .ashr => 1 | .lshr => 1
    | .eq => 1 | .lt => 1 | .le => 1 | .neq => 1
    | .and => 1
    | .bitand => 1
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

structure State (Loc : Type u) [DecidableEq Loc] [Hashable Loc] : Type u where
  -- memory : Loc → Value → Option Value
  memory : Std.HashMap Loc (Std.HashMap Value Value)

def State.init [DecidableEq Loc] [Hashable Loc] : State Loc
  := { memory := .emptyWithCapacity }

def State.load [DecidableEq Loc] [Hashable Loc]
  (s : State Loc) (loc : Loc) (addr : Value) : Option Value :=
  s.memory.get? loc >>= (·.get? addr)

def State.store [DecidableEq Loc] [Hashable Loc]
  (s : State Loc) (loc : Loc) (addr : Value) (val : Value) : State Loc :=
  { s with
    memory := s.memory.insert loc
      ((s.memory.getD loc .emptyWithCapacity).insert addr val) }

instance instOpInterpM [DecidableEq Loc] [Hashable Loc] :
  OpInterpM (SyncOp Loc) Value (StateT (State Loc) Option) where
  interp
    | .add, (inputs : Vector Value 2) => return #v[inputs[0] + inputs[1]]
    | .mul, (inputs : Vector Value 2) => return #v[inputs[0] * inputs[1]]
    | .lt, (inputs : Vector Value 2) => return #v[if inputs[0] < inputs[1] then 1 else 0]
    | .and, (inputs : Vector Value 2) => do
      let a ← InterpConsts.toBool inputs[0]
      let b ← InterpConsts.toBool inputs[1]
      return #v[InterpConsts.fromBool (a && b)]
    | .ashr, (inputs : Vector Value 2) =>
      let a : Int32 := inputs[0].toInt32
      let b : Int32 := inputs[1].toInt32
      let c := a >>> b
      return #v[c.toInt]
    | .load loc, (inputs : Vector Value 1) => return #v[← (← get).load loc inputs[0]]
    | .sel, (inputs : Vector Value 3) => do
      let cond ← InterpConsts.toBool inputs[0]
      let v₁ := inputs[1]
      let v₂ := inputs[2]
      return #v[if cond then v₁ else v₂]
    | .store loc, (inputs : Vector Value 2) => do
      modify (λ s => s.store loc inputs[0] inputs[1])
      return #v[0]
    -- TODO: other pure operators
    | _, _ => failure

/-- Converts the monadic interpretation to a relation. -/
inductive SyncOp.Step [DecidableEq Loc] [Hashable Loc] :
  Lts (State Loc) (RespLabel (SyncOp Loc) Value) where
  | step :
    (instOpInterpM.interp op inputVals).run s = some (outputVals, s') →
    Step s (.respond op inputVals outputVals) s'

def opInterp [DecidableEq Loc] [Hashable Loc] :
  OpInterp (SyncOp Loc) Value := {
    S := State Loc,
    init := State.init,
    lts := SyncOp.Step,
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

instance : Lean.FromJson Value where
  fromJson? json := json.getInt?

instance : Lean.ToJson Value where
  toJson v := Lean.Json.num v

instance [DecidableEq Loc] [Hashable Loc] [Lean.FromJson Loc] : Lean.FromJson (State Loc) where
  fromJson? json := do
    (← json.getArr?).foldlM (λ state entry => do
      let loc ← entry.getObjValAs? Loc "loc"
      let vals ← entry.getObjValAs? (List (Value × Value)) "values"
      return vals.foldl (λ state (addr, val) => state.store loc addr val) state)
      ⟨.emptyWithCapacity⟩

instance [DecidableEq Loc] [Hashable Loc] [Lean.ToJson Loc] : Lean.ToJson (State Loc) where
  toJson s :=
    Lean.ToJson.toJson <| s.memory.toArray.map (λ (loc, vals) =>
      let values := vals.toArray.map (λ item : Value × Value =>
        json% [ $(item.1), $(item.2) ])
      json% {
        "loc": $(loc),
        "values": $(values)
      })

/-- Test inputs. -/
structure TestVector Loc [DecidableEq Loc] [Hashable Loc] where
  inputs : List Value
  state : State Loc
  deriving Lean.FromJson, Lean.ToJson

/-- Run the test vector on the given process until termination. -/
partial def TestVector.run
  [DecidableEq χ] [Repr χ] [DecidableEq Loc] [Hashable Loc] [Repr Loc]
  [Lean.ToJson Loc] [Lean.ToJson χ]
  (tv : TestVector Loc)
  (proc : Dataflow.Proc (SyncOp Loc) χ Value m n) :
    Except String (
      List (Nat × Label (SyncOp Loc) Value m n) × -- Execution trace
      List Value × -- Output values
      State Loc -- Final state
    ) := do
  let c := Dataflow.Config.init proc
  let st := tv.state
  let inputs ← (tv.inputs.toVectorDyn m : Option _).toExcept
    s!"test vector has incorrect number of inputs: expected {m}, got {tv.inputs.length}"
  let c := c.pushInputs inputs
  let inst₁ : OpInterpM (SyncOp Loc) Value (StateT (State Loc) Option) := instOpInterpM
  let inst₂ : Monad (StateT (State Loc) Option) := by infer_instance
  let rec loop (tr : List (Nat × Label (SyncOp Loc) Value m n)) c st : Except String
    (
      List (Nat × Label (SyncOp Loc) Value m n) ×
      Dataflow.Config (SyncOp Loc) χ Value m n ×
      State Loc
    ) := do
    let nextSteps := @Dataflow.Config.step _ χ _ _ _ _ inst₁ inst₂ _ _ _ c
    match nextSteps with
    | [] => pure (tr, c, st)
    | (idx, m) :: _ =>
      let atom ← (c.proc.atoms[idx]?).toExcept s!"invalid operator index {idx}"
      let rawAtom : RawAtomicProc (SyncOp Loc) χ Value := ↑atom
      let ((lbl, c'), st') ← (m.run st).toExcept
        s!"execution encountered a runtime error at operator index {idx} : {Lean.ToJson.toJson rawAtom}"
      -- dbg_trace s!"### step {tr.length + 1} ###\n  operator index {idx}\n  atom: {Lean.ToJson.toJson rawAtom}\n  label: {repr lbl}"
      let tr' := tr ++ [(idx, lbl)]
      loop tr' c' st'
  let (tr, c, st) ← loop [] c st
  -- dbg_trace s!"trace: {repr tr}"
  let (outputs, c) ← c.popOutputs.toExcept
    s!"output channels not ready at termination"

  -- Checks if all channels are empty
  for atom in c.proc.atoms do
    let rawAtom : RawAtomicProc (SyncOp Loc) χ Value := ↑atom
    for name in atom.inputs do
      let buf := c.chans name
      if ¬ buf.isEmpty then
        dbg_trace s!"channel {repr name} (input of {Lean.ToJson.toJson rawAtom}) not empty at termination: {buf}"
    for name in atom.outputs do
      let buf := c.chans name
      if ¬ buf.isEmpty then
        dbg_trace s!"channel {repr name} (output of {Lean.ToJson.toJson rawAtom}) not empty at termination: {buf}"

  return (tr, outputs.toList, st)

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
    | .neq => "\"!=\""
    | .and => "\"&&\""
    | .bitand => "\"&\""
    | .load loc => s!"<LD<sub>{loc}</sub>>"
    | .store loc => s!"<ST<sub>{loc}</sub>>"
    | .sel => "\"SEL\""
    | .const v => s!"\"{v}\""
    | .copy .. => s!"\"CP\""

instance : Dataflow.DotName Value where
  dotName v := s!"\"{v}\""

/-- Custom rewrites for RipTide. -/
def operatorSel [DecidableEq χ] [Hashable χ] : Rewrite (RipTide.SyncOp Loc) χ Value :=
  .choose λ
  -- Lower `copy` to `fork`
  | .op (.copy n) inputs outputs =>
    return .mk "riptide-copy" [.fork (inputs[0]'(by simp [Arity.ι])) outputs]
  -- Lower `const` to the built-in `const`
  | .op (.const v) inputs outputs =>
    return .mk "riptide-const" [.const v (inputs[0]'(by simp [Arity.ι])) outputs]
  -- Select with equal inputs can be rewritten to a forward
  | .op .sel (inputs : Vector _ 3) (outputs : Vector _ 1) => do
    let cond := inputs[0]
    let input₁ := inputs[1]
    let input₂ := inputs[2]
    let output := outputs[0]
    .assumeFromSameFork input₁ input₂
    return .mk "riptide-sel-eq" [
      .forward #v[input₁] #v[output],
      .sink #v[cond, input₂],
    ]
  -- Lower `switch` to two `steer`s
  -- This is optional but may enable more rewrites
  | .async (.switch 1) inputs outputs =>
    if h : inputs.length = 2 ∧ outputs.length = 2 then
      let decider := inputs[0]'(by omega)
      let input := inputs[1]'(by omega)
      let output₁ := outputs[0]'(by omega)
      let output₂ := outputs[1]'(by omega)
      return .mk "riptide-switch" [
        .fork input #v[.rename 0 input, .rename 1 input],
        .fork decider #v[.rename 0 decider, .rename 1 decider],
        .steer true (.rename 0 decider) #v[.rename 0 input] #v[output₁],
        .steer false (.rename 1 decider) #v[.rename 1 input] #v[output₂],
      ]
    else failure
  -- Merging opposite steers with the same decider
  -- is equivalent to a select operator
  | .async (.merge .decider 1) inputs outputs =>
    .assume (inputs.length = 3 ∧ outputs.length = 1) λ h => do
    let decider := inputs[0]'(by omega)
    let inputL := inputs[1]'(by omega)
    let inputR := inputs[2]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .async (.steer flavor₁ 1) inputs₁ outputs₁ =>
      .assume (inputs₁.length = 2 ∧ outputs₁.length = 1) λ h₁ => do
      let decider₁ := inputs₁[0]'(by omega)
      let input₁ := inputs₁[1]'(by omega)
      let output₁ := outputs₁[0]'(by omega)
      .assumeFromSameFork decider decider₁
      .chooseWithNames (inputs ++ outputs) λ
      | .async (.steer flavor₂ 1) inputs₂ outputs₂ =>
        .assume (inputs₂.length = 2 ∧ outputs₂.length = 1) λ h₂ => do
        let decider₂ := inputs₂[0]'(by omega)
        let input₂ := inputs₂[1]'(by omega)
        let output₂ := outputs₂[0]'(by omega)
        .assumeFromSameFork decider decider₂
        if flavor₁ = false ∧ flavor₂ = true ∧ output₁ = inputL ∧ output₂ = inputR then
          return .mk "riptide-merge-steer-steer-to-sel" [
            .op .sel #v[decider, input₂, input₁] #v[output],
            .sink #v[decider₁, decider₂],
          ]
        else failure
      | _ => failure
    | _ => failure
  -- A pure synchronous operator can be merged into a non-first input
  -- of an order operator.
  | .async (Dataflow.AsyncOp.order n) inputs outputs =>
    .assume (n > 0 ∧ inputs.length = n ∧ outputs.length = 1) λ h => do
    let input₁ := inputs[0]'(by omega)
    let output := outputs[0]'(by omega)
    .chooseWithNames (inputs ++ outputs) λ
    | .op op inputs' outputs' =>
      match op with
      | .load .. | .store .. => failure
      | op =>
        if input₁ ∉ outputs' ∧ outputs'.toList ⊆ inputs then
          have : NeZero (inputs.removeAll outputs'.toList ++ inputs'.toList).length := by
            constructor
            simp
            intros h₁ h₂
            have : NeZero (Arity.ι op) := by infer_instance
            have := this.ne
            omega
          return .mk "riptide-order-sync" [
            .order ((inputs.removeAll outputs'.toList) ++ inputs'.toList).toVector output,
          ]
        else failure
    | _ => failure
  | _ => failure

end Wavelet.Frontend.RipTide
