import Wavelet.Data.Basic
import Wavelet.Seq.AffineVar
import Wavelet.Dataflow.Proc
import Wavelet.Dataflow.Plot
import Wavelet.Dataflow.Interpreter
import Wavelet.Dataflow.AffineChan
import Wavelet.Semantics.OpInterp
import Wavelet.Determinacy.OpSpec
import Wavelet.Compile

import Wavelet.Frontend.Dataflow
import Wavelet.Frontend.Seq

/-! A formalization of the operator set of RipTide (https://ieeexplore.ieee.org/document/9923793). -/

namespace Wavelet.Frontend.RipTide

open Semantics Determinacy Compile

section Syntax

/-- A memory location name. -/
abbrev Loc := String

/-- A function name. -/
abbrev FnName := String

inductive Value where
  | int (w : Nat) (val : BitVec w)
  | junk
  deriving BEq, DecidableEq, Hashable, Repr

/-- A special value for control signals. -/
def Value.unit : Value := .int 0 0

def Value.bool (b : Bool) : Value :=
  if b then .int 1 1 else .int 1 0

instance : Lean.ToJson Value where
  toJson
    | .int w val => json% { "int": { "width": $(w), "value": $(val.toNat) } }
    | .junk => json% "junk"

instance : Lean.FromJson Value where
  fromJson? json :=
  (do
    let obj ← json.getObjVal? "int"
    let w ← obj.getObjValAs? Nat "width"
    let v ← obj.getObjValAs? Nat "value"
    return .int w (BitVec.ofNat w v)) <|>
  if let .ok s := json.getStr? then
    if s = "junk" then
      return .junk
    else
      .error "failed to parse Value"
  else
    .error "failed to parse Value"

/-- Synchronous operators in RipTide, parametrized by a type of location/array symbols. -/
inductive SyncOp where
  | add | sub | mul | sdiv | udiv
  | shl | ashr | lshr
  | eq | neq | slt | sle | ult | ule
  | and
  | bitand
  | load (_ : Loc) | store (_ : Loc) | sel
  | const (_ : Value)
  | copy (_ : NzNat)
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

instance : Arity SyncOp where
  ι | .add => 2 | .sub => 2 | .mul => 2
    | .sdiv => 2 | .udiv => 2
    | .shl => 2 | .ashr => 2 | .lshr => 2
    | .eq => 2 | .neq => 2
    | .slt => 2 | .sle => 2
    | .ult => 2 | .ule => 2
    | .and => 2
    | .bitand => 2
    | .load _ => 1 | .store _ => 2 | .sel => 3
    | .const _ => 1 | .copy _ => 1
  ω | .add => 1 | .sub => 1 | .mul => 1
    | .sdiv => 1 | .udiv => 1
    | .shl => 1 | .ashr => 1 | .lshr => 1
    | .eq => 1 | .neq => 1
    | .slt => 1 | .sle => 1
    | .ult => 1 | .ule => 1
    | .and => 1
    | .bitand => 1
    | .load _ => 1 | .store _ => 1 | .sel => 1
    | .const _ => 1
    | .copy n => n

instance : NeZeroArity SyncOp where
  neZeroᵢ op := by cases op <;> infer_instance
  neZeroₒ op := by
    cases op with
    | copy n =>
      have := n.property
      constructor
      dsimp [Arity.ω]
      omega
    | _ => infer_instance

/-- Some constants used for compilation. -/
instance : InterpConsts Value where
  junkVal := .junk
  toBool | .int 1 0 => some false
         | .int 1 1 => some true
         | _ => none
  fromBool b := if b then .int 1 1 else .int 1 0
  unique_fromBool_toBool b := by cases b <;> simp
  unique_toBool_fromBool b v h := by
    split at h <;> simp at h <;> subst h <;> simp
  isClonable _ := true
  bool_clonable := by simp

end Syntax

/-! Executable semantics. -/
section Semantics

structure State where
  memory : Std.HashMap Loc (Std.HashMap Value Value)

def State.init : State
  := { memory := .emptyWithCapacity }

def State.load (s : State) (loc : Loc) (addr : Value) : Option Value :=
  s.memory.get? loc >>= (·.get? addr)

def State.store (s : State) (loc : Loc) (addr : Value) (val : Value) : State :=
  { s with
    memory := s.memory.insert loc
      ((s.memory.getD loc .emptyWithCapacity).insert addr val) }

abbrev SemM := StateT State (Except String)

private def applyBitVecBinOp
  (name : String)
  (f : ∀ {w : Nat}, BitVec w → BitVec w → BitVec w) :
    Value → Value → SemM (Vector Value 1)
  | .int w₁ v₁, .int w₂ v₂ =>
    if h : w₁ = w₂ then
      let v := f v₁ (v₂.cast h.symm)
      return #v[.int w₁ v]
    else
      throw s!"bitvector width mismatch for {name}"
  | _, _ => throw s!"type mismatch for operator {name}"

private def applyBitVecBinPred
  (name : String)
  (f : ∀ {w : Nat}, BitVec w → BitVec w → Bool) :
    Value → Value → SemM (Vector Value 1)
  | .int w₁ v₁, .int w₂ v₂ =>
    if h : w₁ = w₂ then
      let b := f v₁ (v₂.cast h.symm)
      return #v[InterpConsts.fromBool b]
    else
      throw s!"bitvector width mismatch for {name}"
  | _, _ => throw s!"type mismatch for operator {name}"

instance instOpInterpM : OpInterpM SyncOp Value SemM where
  interp
    | .add, (inputs : Vector Value 2) => applyBitVecBinOp "add" BitVec.add inputs[0] inputs[1]
    | .sub, (inputs : Vector Value 2) => applyBitVecBinOp "sub" BitVec.sub inputs[0] inputs[1]
    | .mul, (inputs : Vector Value 2) => applyBitVecBinOp "mul" BitVec.mul inputs[0] inputs[1]
    | .eq, (inputs : Vector Value 2) => applyBitVecBinPred "eq" (· == ·) inputs[0] inputs[1]
    | .neq, (inputs : Vector Value 2) => applyBitVecBinPred "neq" (· != ·) inputs[0] inputs[1]
    | .slt, (inputs : Vector Value 2) => applyBitVecBinPred "slt" BitVec.slt inputs[0] inputs[1]
    | .sle, (inputs : Vector Value 2) => applyBitVecBinPred "sle" BitVec.sle inputs[0] inputs[1]
    | .ult, (inputs : Vector Value 2) => applyBitVecBinPred "ult" BitVec.ult inputs[0] inputs[1]
    | .ule, (inputs : Vector Value 2) => applyBitVecBinPred "ule" BitVec.ule inputs[0] inputs[1]
    | .and, (inputs : Vector Value 2) => applyBitVecBinOp "and" BitVec.and inputs[0] inputs[1]
    | .bitand, (inputs : Vector Value 2) => applyBitVecBinOp "bitand" BitVec.and inputs[0] inputs[1]
    | .shl, (inputs : Vector Value 2) =>
      match inputs[0], inputs[1] with
      | .int w v, .int _ shift => return #v[.int w (BitVec.shiftLeft v shift.toNat)]
      | _, _ => throw s!"type mismatch for operator shl"
    | .ashr, (inputs : Vector Value 2) =>
      match inputs[0], inputs[1] with
      | .int w v, .int _ shift => return #v[.int w (BitVec.sshiftRight v shift.toNat)]
      | _, _ => throw s!"type mismatch for operator ashr"
    | .lshr, (inputs : Vector Value 2) =>
      match inputs[0], inputs[1] with
      | .int w v, .int _ shift => return #v[.int w (BitVec.ushiftRight v shift.toNat)]
      | _, _ => throw s!"type mismatch for operator lshr"
    | .load loc, (inputs : Vector Value 1) => do
      match (← get).load loc inputs[0] with
      | some val => return #v[val]
      | none => throw s!"loading uninitialized memory address {loc}[{repr inputs[0]}]"
    | .store loc, (inputs : Vector Value 2) => do
      modify (λ s => s.store loc inputs[0] inputs[1])
      return #v[.unit]
    | .sel, (inputs : Vector Value 3) => do
      let cond ← InterpConsts.toBool inputs[0] |>.toExcept
        "select condition is not a boolean"
      let v₁ := inputs[1]
      let v₂ := inputs[2]
      return #v[if cond then v₁ else v₂]
    -- TODO: other pure operators
    | op, _ => throw s!"unsupported operator or wrong number of arguments: {repr op}"

/-- Converts the monadic interpretation to a relation. -/
inductive SyncOp.Step : Lts State (RespLabel SyncOp Value) where
  | step :
    (instOpInterpM.interp op inputVals).run s = .ok (outputVals, s') →
    Step s (.respond op inputVals outputVals) s'

def opInterp : OpInterp SyncOp Value := {
    S := State,
    init := State.init,
    lts := SyncOp.Step,
  }

/-- TODO: Actually define the pre/post conditions. -/
def opSpec : OpSpec SyncOp Value PCM.Triv :=
  {
    pre | _, _ => PCM.zero,
    post | _, _, _ => PCM.zero,
  }

end Semantics

section Json

instance : Lean.FromJson (WithSpec SyncOp RipTide.opSpec) where
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

instance : Lean.ToJson (WithSpec RipTide.SyncOp RipTide.opSpec) where
  toJson
    | WithSpec.op true op =>
      json% { "op_ghost": $(op) }
    | WithSpec.op false op =>
      json% { "op": $(op) }
    | WithSpec.join k l _ =>
      json% { "join": { "toks": $(k), "deps": $(l) } }

instance : Lean.FromJson State where
  fromJson? json := do
    (← json.getArr?).foldlM (λ state entry => do
      let loc ← entry.getObjValAs? Loc "loc"
      let vals ← entry.getObjValAs? (List (Value × Value)) "values"
      return vals.foldl (λ state (addr, val) => state.store loc addr val) state)
      ⟨.emptyWithCapacity⟩

instance : Lean.ToJson State where
  toJson s :=
    Lean.ToJson.toJson <| s.memory.toArray.map (λ (loc, vals) =>
      let values := vals.toArray.map (λ item : Value × Value =>
        json% [ $(item.1), $(item.2) ])
      json% {
        "loc": $(loc),
        "values": $(values)
      })

end Json

section Examples

def prog₁ :
    RawProg
      (WithCall (WithSpec RipTide.SyncOp RipTide.opSpec) String)
      String
  := ⟨[
    {
      name := "sum",
      params := ["sum", "i", "n", "t₀"],
      rets := ["a", "b"],
      body :=
        .op (.op (.join 1 0 (λ _ => PCM.zero))) ["t₀"] ["t₁", "t₂"] <|
        .op (.op (.op false (.copy ⟨3, by simp⟩))) ["i"] ["i₁", "i₂", "i₃", "i₄", "dummy₁"] <|
        .op (.op (.op false (.copy ⟨1, by simp⟩))) ["n"] ["n₁", "n₂", "dummy₂"] <|
        .op (.op (.op false .slt)) ["i₁", "n₁"] ["c", "dummy₃"] <|
        .br "c"
          (.op (.op (.op true (.load "A"))) ["i₂", "t₁"] ["x", "t₁'"] <|
           .op (.op (.op false .add)) ["sum", "x"] ["sum'", "dummy₄"] <|
           .op (.op (.op false (.const (.int 32 1)))) ["i₃"] ["one", "dummy₅"] <|
           .op (.op (.op false .add)) ["i₄", "one"] ["i'", "dummy₆"] <|
            .tail ["sum'", "i'", "n₂", "t₂"])
          (.ret ["sum", "t₂"]),
    }
  ]⟩

-- #eval (prog₁.toProg (V := Nat)).map (λ _ => ())
-- #eval Lean.ToJson.toJson prog₁

end Examples

section ToString

instance : ToString Value where
  toString
    | .int 0 _ => "()"
    | .int 1 0 => "f"
    | .int 1 1 => "t"
    | .int _ val => s!"{val.toInt}"
    | .junk => "?"

instance [ToString Loc] : Dataflow.DotName SyncOp where
  dotName
    | .add => "\"+\""
    | .sub => "\"-\""
    | .mul => "\"*\""
    | .sdiv => "\"s/\""
    | .udiv => "\"u/\""
    | .shl => "\"<<\""
    | .ashr => "\"a>>\""
    | .lshr => "\"l>>\""
    | .eq => "\"=\""
    | .neq => "\"!=\""
    | .slt => "\"s<\""
    | .sle => "\"s<=\""
    | .ult => "\"u<\""
    | .ule => "\"u<=\""
    | .and => "\"&&\""
    | .bitand => "\"&\""
    | .load loc => s!"<LD<sub>{loc}</sub>>"
    | .store loc => s!"<ST<sub>{loc}</sub>>"
    | .sel => "\"SEL\""
    | .const v => s!"\"{v}\""
    | .copy .. => s!"\"CP\""

instance : Dataflow.DotName Value where
  dotName v := s!"\"{v}\""

end ToString

/-! Instances of various compilation passes to RipTide. -/
section Passes

open Seq Dataflow

inductive PrimType where
  | int (_ : Nat)
  | unknown
  deriving BEq, DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson

def PrimType.unit : PrimType := .int 0
def PrimType.bool : PrimType := .int 1

structure VarName (α : Type u) where
  name : α
  ty : PrimType
  deriving BEq, DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson

/-- Global array/memory declaration. -/
structure ArrayDecl where
  loc : Loc
  elem : PrimType
  size : Option Nat
  external : Bool
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Raw program format used for encoding/decoding。 -/
structure RawProg where
  arrays : List ArrayDecl
  inner : Frontend.RawProg (WithCall (WithSpec SyncOp RipTide.opSpec) FnName) (VarName String)
  deriving Repr

/-- Raw process format used for encoding/decoding. -/
structure RawProc where
  arrays : List ArrayDecl
  inner : Frontend.RawProc SyncOp (VarName Nat) RipTide.Value
  deriving Repr

instance : Lean.FromJson RawProg where
  fromJson? json :=
    return {
      arrays := ← Lean.FromJson.fromJson? (← json.getObjVal? "arrays"),
      inner := ← Lean.FromJson.fromJson? json,
    }

instance : Lean.ToJson RawProg where
  toJson raw :=
    let base := Lean.ToJson.toJson raw.inner
    base.setObjVal! "arrays" (Lean.ToJson.toJson raw.arrays)


instance : Lean.FromJson RawProc where
  fromJson? json :=
    return {
      arrays := ← Lean.FromJson.fromJson? (← json.getObjVal? "arrays"),
      inner := ← Lean.FromJson.fromJson? json,
    }

instance : Lean.ToJson RawProc where
  toJson raw :=
    let base := Lean.ToJson.toJson raw.inner
    base.setObjVal! "arrays" (Lean.ToJson.toJson raw.arrays)

structure Prog where
  arrays : List ArrayDecl
  inner : Frontend.EncapProg (WithSpec SyncOp RipTide.opSpec) (VarName String) RipTide.Value

structure Proc where
  arrays : List ArrayDecl
  inner : Frontend.EncapProc SyncOp (VarName Nat) RipTide.Value

def RawProg.toProg (raw : RawProg) : Except String RipTide.Prog :=
  return {
    arrays := raw.arrays,
    inner := ← raw.inner.toProg,
  }

/-- Checks if there are duplicate declarations, etc. -/
def ArrayDecl.validate (arrays : List ArrayDecl) : Except String Unit := do
  let noDup := arrays.map (·.loc) |>.removeDup
  if noDup.length ≠ arrays.length then
    throw "duplicate array declarations"
  else
    return ()

def RawProc.toProc (raw : RawProc) : Except String RipTide.Proc := do
  ArrayDecl.validate raw.arrays
  return {
    arrays := raw.arrays,
    inner := .fromProc (← raw.inner.toProc),
  }

def RawProc.fromProc (proc : RipTide.Proc) : RawProc :=
  {
    arrays := proc.arrays,
    inner := Frontend.RawProc.fromProc proc.inner.proc,
  }

/-- Validates static properties of a `Prog`. -/
def Prog.validate (prog : RipTide.Prog) : Except String Unit := do
  for i in List.finRange prog.inner.numFns do
    let name := prog.inner.names[i]? |>.getD s!"unknown"
    (prog.inner.prog i).checkAffineVar.resolve.context s!"function {i} ({name})"

/-- Validates static properties of a `Proc`. -/
def Proc.validate (proc : RipTide.Proc) : Except String Unit := do
  proc.inner.proc.checkAffineChan

/-- TODO: On certain (currently) unreachable cases
(e.g., `.dest i` with `i` exceeding the number of
return values), this function will return `.unknown`.
Ideally we want to fail early instead of silently
passing types of `.unknown` around. -/
private def typeOfChanName
  [Arity Op]
  (fn : Fn Op (VarName β) V m n)
  : ChanName (VarName α) → PrimType
  | .input name
  | .var name _ => name.ty
  | .switch_cond _
  | .merge_cond _
  | .tail_cond _
  | .tail_cond_carry
  | .tail_cond_steer_dests
  | .tail_cond_steer_tail_args => .bool
  | .dest i _
  | .final_dest i =>
    if h : i < n then
      (fn.rets[i]'h).ty
    else
      .unknown
  | .tail_arg i _
  | .final_tail_arg i =>
    if h : i < m then
      (fn.params[i]'h).ty
    else
      .unknown

private def typeOfLinkChanName
  (prog : RipTide.Prog)
  (curIdx : Nat)
  : LinkName (ChanName (VarName α)) → PrimType
  | .base name =>
    if h : curIdx < prog.inner.numFns then
      typeOfChanName (prog.inner.prog ⟨curIdx, h⟩) name
    else
      .unknown
  | .main name => typeOfLinkChanName prog curIdx name
  | .dep idx name => typeOfLinkChanName prog idx name

private def typeOfEraseName
  : EraseName (VarName α) → PrimType
  | .base name
  | .input name
  | .output name
  | .join name _
  | .op_finish name => name.ty

private def typeOfRewriteName
  : RewriteName (VarName α) → PrimType
  | .base name => name.ty
  | .rw name => typeOfRewriteName name
  | .rename _ name => typeOfRewriteName name

/-- Renames a variable/channel name after linking and compilation,
but preserves the type annotation. -/
private def renameLinkChanName
  (prog : RipTide.Prog)
  (idx : Nat) (name : LinkName (ChanName (VarName α))) : VarName Nat
  := { name := idx, ty := typeOfLinkChanName prog (prog.inner.numFns - 1) name }

/-- Renames a variable after ghost erasure. -/
private def renameEraseName (idx : Nat) (name : EraseName (VarName α)) : VarName Nat
  := { name := idx, ty := typeOfEraseName name }

/-- Renames a variable after rewriting. -/
private def renameRewriteName (idx : Nat) (name : RewriteName (VarName α)) : VarName Nat
  := { name := idx, ty := typeOfRewriteName name }

/-- Converts the last function of the given program to a dataflow process.
This compiles all imperative control-flow to dataflow, and also lowers all
ghost operators/inputs/outputs to concrete order operators. -/
def Prog.lowerControlFlow (prog : RipTide.Prog) : Except String RipTide.Proc := do
  if h : prog.inner.numFns > 0 then
    let : NeZeroSigs prog.inner.sigs := prog.inner.neZero
    let last : Fin prog.inner.numFns := ⟨prog.inner.numFns - 1, by omega⟩
    -- Compile and link
    let proc := compileProg prog.inner.prog last
    let proc := proc.renameChans (renameLinkChanName prog)
    -- Erase ghost tokens
    let proc := proc.eraseGhost
    let proc := proc.renameChans renameEraseName
    return {
      arrays := prog.arrays,
      inner := .fromProc proc,
    }
  else
    .error "compiling empty program"

/-- Connects the last `n` output channels of the process to `sink`s.
This is useful in avoiding unnecessary outputs (like for ghost permissions)
and reducing the size of the dataflow graph. -/
def Proc.sinkLastNOutputs (n : Nat) (proc : RipTide.Proc) : RipTide.Proc :=
  let rem := proc.inner.numOuts - n
  {
    proc with
    inner := .fromProc {
      proc.inner.proc with
      outputs := proc.inner.proc.outputs.take rem,
      atoms := .sink (proc.inner.proc.outputs.drop rem) :: proc.inner.proc.atoms
    }
  }

/-- Generates a fresh variable name not appearing in the given process. -/
private def Proc.freshName (ty : PrimType) (proc : RipTide.Proc) (offset := 1) : VarName Nat :=
  let used := proc.inner.proc.atoms.map (λ atom =>
      atom.inputs.map (·.name) ++ atom.outputs.map (·.name)) |>.flatten
  let used := used ++
    proc.inner.proc.inputs.toList.map (·.name) ++
    proc.inner.proc.outputs.toList.map (·.name)
  let fresh := offset + used.foldl Nat.max 0
  { name := fresh, ty }

/--
Trims the inputs (outputs) of the process so that:
- If there is a non-unit input (output), all other unit inputs (outputs) are removed
  (with suitable forks/orders added);
- If all inputs (outputs) are units, only one is kept.

TODO: Maybe a bit too complicated than necessary.
-/
def Proc.trimUnitIO (proc : RipTide.Proc) : RipTide.Proc :=
  trimOutputs <| trimInputs proc
  where
    trimInputs proc :=
      let unitInputs :=
        proc.inner.proc.inputs.toList.filter (·.ty = PrimType.unit)
      let nonUnitInputs :=
        proc.inner.proc.inputs.toList.filter (·.ty ≠ PrimType.unit)
      if let firstNonUnit :: restNonUnit := nonUnitInputs then
        -- Some non-unit inputs, remove all unit inputs
        let newInput := proc.freshName firstNonUnit.ty 1
        let newInputFork := proc.freshName firstNonUnit.ty 2
        {
          proc with
          inner := .fromProc {
            proc.inner.proc with
            inputs := (newInput :: restNonUnit).toVector,
            atoms :=
              .fork newInput #v[newInputFork, firstNonUnit] ::
              .const Value.unit newInputFork unitInputs.toVector ::
              proc.inner.proc.atoms
          }
        }
      else
        -- All inputs are units, join them to one
        if proc.inner.numIns > 1 then
          let newInput := proc.freshName .unit 1
          {
            proc with
            inner := .fromProc {
              proc.inner.proc with
              inputs := #v[newInput],
              atoms :=
                .fork newInput proc.inner.proc.inputs :: proc.inner.proc.atoms
            }
          }
        else
          -- Only one input, do nothing
          proc
    trimOutputs proc :=
      let unitOuputs :=
        proc.inner.proc.outputs.toList.filter (·.ty = PrimType.unit)
      let nonUnitOutputs :=
        proc.inner.proc.outputs.toList.filter (·.ty ≠ PrimType.unit)
      if let firstNonUnit :: restNonUnit := nonUnitOutputs then
        -- Some non-unit outputs, remove all unit outputs
        let newOutput := proc.freshName firstNonUnit.ty 1
        let newOutputFork := proc.freshName firstNonUnit.ty 2
        let : NeZero (firstNonUnit :: unitOuputs).length := ⟨by simp⟩
        {
          proc with
          inner := .fromProc {
            proc.inner.proc with
            outputs := (newOutput :: restNonUnit).toVector,
            atoms :=
              .order (firstNonUnit :: unitOuputs).toVector newOutput ::
              proc.inner.proc.atoms
          }
        }
      else
        -- All outputs are units, join them to one with a order
        if h : proc.inner.numOuts > 1 then
          let newOutput := proc.freshName .unit 1
          let : NeZero proc.inner.numOuts := ⟨by omega⟩
          {
            proc with
            inner := .fromProc {
              proc.inner.proc with
              outputs := #v[newOutput],
              atoms :=
                .order proc.inner.proc.outputs newOutput ::
                proc.inner.proc.atoms
            }
          }
        else
          -- Only one output, do nothing
          proc

/-- Rewrites the given dataflow process using the given rules. -/
def Proc.rewriteProc
  (rules : Rewrite SyncOp (VarName Nat) RipTide.Value)
  (proc : RipTide.Proc)
  (disabledRules : List String := []) :
  Nat × RewriteStats × RipTide.Proc :=
  let (numRws, stats, rewritten) := Rewrite.applyUntilFail
    renameRewriteName rules proc.inner.proc disabledRules
  (numRws, stats, { proc with inner := .fromProc rewritten })

/-- Custom rewrites for RipTide. -/
def operatorSel [DecidableEq χ] [Hashable χ] : Rewrite SyncOp χ Value :=
  .choose λ
  -- Lower `copy` to `fork`
  | .op (.copy n) inputs outputs =>
    .apply "riptide-copy" [.fork (inputs[0]'(by simp [Arity.ι])) outputs]
  -- Lower `const` to the built-in `const`
  | .op (.const v) inputs outputs =>
    .apply "riptide-const" [.const v (inputs[0]'(by simp [Arity.ι])) outputs]
  -- Select with equal inputs can be rewritten to a forward
  | .op .sel (inputs : Vector _ 3) (outputs : Vector _ 1) => do
    let cond := inputs[0]
    let input₁ := inputs[1]
    let input₂ := inputs[2]
    let output := outputs[0]
    .assumeFromSameFork input₁ input₂
    .apply "riptide-sel-eq" [
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
      .apply "riptide-switch" [
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
          .apply "riptide-merge-steer-steer-to-sel" [
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
          .apply "riptide-order-sync" [
            .order ((inputs.removeAll outputs'.toList) ++ inputs'.toList).toVector output,
          ]
        else failure
    | _ => failure
  | _ => failure

end Passes

/-! Testing utilities. -/
section Testbench

/-- A simply-typed wrapper around a semantic label. -/
structure Label where
  numIns : Nat
  numOuts : Nat
  idx : Nat
  inner : Semantics.Label SyncOp Value numIns numOuts

/-- A simply-typed wrapper around dataflow config and the memory state. -/
structure Config where
  proc : RipTide.Proc
  config :
    Dataflow.Config SyncOp (VarName Nat) Value
      proc.inner.numIns proc.inner.numOuts
  state : State

/-- Initial configuration of a RipTide process (including memory state). -/
def Config.init (proc : RipTide.Proc) : Config :=
  {
    proc := proc,
    config := Dataflow.Config.init proc.inner.proc,
    state := State.init,
  }

/-- Checks if the given configuration is in its initial state (except for the memory). -/
def Config.checkInit (c : Config) : Except String Unit := do
  if c.config.proc ≠ c.proc.inner.proc then
    throw "atom local state not in initial state"
  -- For each channel, check if the input/output buffers are empty
  for ap in c.proc.inner.proc.atoms do
    for chan in ap.inputs do
      if c.config.chans.getBuf chan ≠ [] then
        throw s!"input buffer for channel {repr chan} not empty"
    for chan in ap.outputs do
      if c.config.chans.getBuf chan ≠ [] then
        throw s!"output buffer for channel {repr chan} not empty"

def Config.storeMem (loc : Loc) (addr : Value) (val : Value)
  (c : Config) : Config :=
  { c with state := c.state.store loc addr val }

def Config.loadMem (loc : Loc) (addr : Value)
  (c : Config) : Option Value :=
  c.state.load loc addr

def Config.memAddrs (loc : Loc)
  (c : Config) : List Value :=
  match c.state.memory.get? loc with
  | some mem => mem.keys
  | none => []

def Config.memNames (c : Config) : List Loc := c.state.memory.keys

/-- Pushes one value to each input channel. -/
def Config.pushInputs
  (inputs : List Value)
  (c : Config) : Except String Config := do
  let inputs ← (inputs.toVectorDyn c.proc.inner.numIns : Option _).toExcept <|
    s!"incorrect number of inputs: expected {c.proc.inner.numIns}, got {inputs.length}"
  return { c with config := c.config.pushInputs inputs }

/-- Pops one value from each output channel. -/
def Config.popOutputs
  (c : Config) : Except String (List Value × Config) := do
  let (outputs, config') ← c.config.popOutputs.toExcept
    s!"some output channels are empty"
  return (outputs.toList, { c with config := config' })

/-- Eagerly fires all fireable operators for `bound` steps (if specified),
or until termination. -/
def Config.eagerSteps
  (bound : Option Nat := none)
  (c : Config) :
    Except String (List (List Label) × Config) := do
  let ((tr, config'), state') ← (c.config.eagerSteps (M := SemM) bound).run c.state
  let tr := tr.map (λ labels => labels.map λ (idx, label) => .mk _ _ idx label)
  return (tr, { c with config := config', state := state' })

def Config.eagerNonTrivialSteps
  (bound : Option Nat := none)
  (c : Config) :
    Except String (List (List Label) × Config) := do
  let ((tr, config'), state') ← (c.config.eagerNonTrivialSteps (M := SemM) bound).run c.state
  let tr := tr.map (λ labels => labels.map λ (idx, label) => .mk _ _ idx label)
  return (tr, { c with config := config', state := state' })

end Testbench

end Wavelet.Frontend.RipTide
