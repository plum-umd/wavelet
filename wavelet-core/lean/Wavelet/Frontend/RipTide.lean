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
import Wavelet.Backend.Handshake

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
  | copy (_ : Nat)
  deriving Repr, Lean.ToJson, Lean.FromJson

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
    -- NOTE: `copy n` outputs `n + 1` values
    | .copy n => n + 1

instance : NeZeroArity SyncOp where
  neZeroᵢ op := by cases op <;> infer_instance
  neZeroₒ op := by cases op <;> infer_instance

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

section Semantics

structure State where
  -- memory : Loc → Value → Option Value
  memory : Std.HashMap Loc (Std.HashMap Value Value)

def State.init : State
  := { memory := .emptyWithCapacity }

def State.load (s : State) (loc : Loc) (addr : Value) : Option Value :=
  s.memory.get? loc >>= (·.get? addr)

def State.store (s : State) (loc : Loc) (addr : Value) (val : Value) : State :=
  { s with
    memory := s.memory.insert loc
      ((s.memory.getD loc .emptyWithCapacity).insert addr val) }

private def applyBitVecBinOp
  (f : ∀ {w : Nat}, BitVec w → BitVec w → BitVec w) :
    Value → Value → StateT State Option (Vector Value 1)
  | .int w₁ v₁, .int w₂ v₂ =>
    if h : w₁ = w₂ then
      let v := f v₁ (v₂.cast h.symm)
      return #v[.int w₁ v]
    else
      failure
  | _, _ => failure

private def applyBitVecBinPred
  (f : ∀ {w : Nat}, BitVec w → BitVec w → Bool) :
    Value → Value → StateT State Option (Vector Value 1)
  | .int w₁ v₁, .int w₂ v₂ =>
    if h : w₁ = w₂ then
      let b := f v₁ (v₂.cast h.symm)
      return #v[InterpConsts.fromBool b]
    else
      failure
  | _, _ => failure

instance instOpInterpM : OpInterpM SyncOp Value (StateT State Option) where
  interp
    | .add, (inputs : Vector Value 2) => applyBitVecBinOp BitVec.add inputs[0] inputs[1]
    | .mul, (inputs : Vector Value 2) => applyBitVecBinOp BitVec.mul inputs[0] inputs[1]
    | .eq, (inputs : Vector Value 2) => applyBitVecBinPred (· == ·) inputs[0] inputs[1]
    | .neq, (inputs : Vector Value 2) => applyBitVecBinPred (· != ·) inputs[0] inputs[1]
    | .slt, (inputs : Vector Value 2) => applyBitVecBinPred BitVec.slt inputs[0] inputs[1]
    | .sle, (inputs : Vector Value 2) => applyBitVecBinPred BitVec.sle inputs[0] inputs[1]
    | .and, (inputs : Vector Value 2) => applyBitVecBinOp BitVec.and inputs[0] inputs[1]
    | .ashr, (inputs : Vector Value 2) =>
      match inputs[0], inputs[1] with
      | .int w v, .int _ shift => return #v[.int w (BitVec.sshiftRight v shift.toNat)]
      | _, _ => failure
    | .load loc, (inputs : Vector Value 1) => return #v[← (← get).load loc inputs[0]]
    | .store loc, (inputs : Vector Value 2) => do
      modify (λ s => s.store loc inputs[0] inputs[1])
      return #v[.unit]
    | .sel, (inputs : Vector Value 3) => do
      let cond ← InterpConsts.toBool inputs[0]
      let v₁ := inputs[1]
      let v₂ := inputs[2]
      return #v[if cond then v₁ else v₂]
    -- TODO: other pure operators
    | _, _ => failure

/-- Converts the monadic interpretation to a relation. -/
inductive SyncOp.Step : Lts State (RespLabel SyncOp Value) where
  | step :
    (instOpInterpM.interp op inputVals).run s = some (outputVals, s') →
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

section Testbench

/-- Test inputs. -/
structure Testbench where
  inputs : List Value
  state : State
  deriving Lean.FromJson, Lean.ToJson

/-- Run the test vector on the given process until termination. -/
partial def Testbench.run
  [DecidableEq χ] [Repr χ] [Lean.ToJson χ]
  (tv : Testbench)
  (proc : Dataflow.Proc SyncOp χ Value m n) :
    Except String (
      List (Nat × Label SyncOp Value m n) × -- Execution trace
      List Value × -- Output values
      State -- Final state
    ) := do
  let c := Dataflow.Config.init proc
  let st := tv.state
  let inputs ← (tv.inputs.toVectorDyn m : Option _).toExcept
    s!"test vector has incorrect number of inputs: expected {m}, got {tv.inputs.length}"
  let c := c.pushInputs inputs
  let inst₁ : OpInterpM SyncOp Value (StateT State Option) := instOpInterpM
  let inst₂ : Monad (StateT State Option) := by infer_instance
  let rec loop (tr : List (Nat × Label SyncOp Value m n)) c st : Except String
    (
      List (Nat × Label SyncOp Value m n) ×
      Dataflow.Config SyncOp χ Value m n ×
      State
    ) := do
    let nextSteps := @Dataflow.Config.step _ χ _ _ _ _ inst₁ inst₂ _ _ _ c
    match nextSteps with
    | [] => pure (tr, c, st)
    | (idx, m) :: _ =>
      let atom ← (c.proc.atoms[idx]?).toExcept s!"invalid operator index {idx}"
      let rawAtom : RawAtomicProc SyncOp χ Value := ↑atom
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
    let rawAtom : RawAtomicProc SyncOp χ Value := ↑atom
    for name in atom.inputs do
      let buf := c.chans name
      if ¬ buf.isEmpty then
        dbg_trace s!"channel {repr name} (input of {Lean.ToJson.toJson rawAtom}) not empty at termination: {repr buf}"
    for name in atom.outputs do
      let buf := c.chans name
      if ¬ buf.isEmpty then
        dbg_trace s!"channel {repr name} (output of {Lean.ToJson.toJson rawAtom}) not empty at termination: {repr buf}"

  return (tr, outputs.toList, st)

end Testbench

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
        .op (.op (.op false (.copy 3))) ["i"] ["i₁", "i₂", "i₃", "i₄", "dummy₁"] <|
        .op (.op (.op false (.copy 1))) ["n"] ["n₁", "n₂", "dummy₂"] <|
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
    | .int w val => s!"{val.toInt}i{w}"
    | .junk => "junk"

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
  size : Nat
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

/-- Rewrites the given dataflow process using the given rules. -/
def Proc.rewriteProc
  (rules : Rewrite SyncOp (VarName Nat) RipTide.Value)
  (proc : RipTide.Proc)
  (disabledRules : List String := []) :
  Nat × RewriteStats × RipTide.Proc :=
  let (numRws, stats, rewritten) := Rewrite.applyUntilFailNat
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

/-! Emitting CIRCT Handshake operation(s) for each operator.
TODO: Move this section to `Wavelet.Backend`? -/
section Handshake

open Backend Handshake

instance : EmitType PrimType where
  emit
    | .int 0 => return Handshake.PrimType.none
    | .int w => return Handshake.PrimType.int w
    | .unknown => .error "cannot emit unknown primitive type"

instance [Repr α] : EmitType (VarName α) where
  emit v := EmitType.emit v.ty

instance [ToString α] : EmitVar (VarName α) where
  emit v := return s!"%v{v.name}"

instance : EmitType RipTide.Value where
  emit
    | .int 0 _ => return Handshake.PrimType.none
    | .int w _ => return Handshake.PrimType.int w
    | .junk => .error "cannot emit type for junk value"

instance : EmitConst Value where
  emit
    | .int w val =>
      if w = 0 then
        .error "cannot emit constant of type none"
      else
        return s!"{val.toNat}"
    | .junk => .error "cannot emit constant of type junk"

private inductive MemAccess where | load | store
  deriving DecidableEq, Repr

/-- Each memory access is assigned a port to
send the actual values and signals. -/
private structure MemPort where
  loc : Loc
  access : MemAccess
  addrTy : Handshake.PrimType
  valTy : Handshake.PrimType

/-- Records required memory ports for all accesses. -/
private structure EmitState where
  arrays : List ArrayDecl
  ports : List MemPort

def EmitState.init (proc : RipTide.Proc) : EmitState :=
  { arrays := proc.arrays, ports := [] }

def EmitState.loadPortAddr (loc : Loc) (idx : Nat) : String := s!"%mem.{loc}.load.addr.{idx}"
def EmitState.loadPortVal (loc : Loc) (idx : Nat) : String := s!"%mem.{loc}.load.val.{idx}"

def EmitState.storePortAddr (loc : Loc) (idx : Nat) : String := s!"%mem.{loc}.store.addr.{idx}"
def EmitState.storePortVal (loc : Loc) (idx : Nat) : String := s!"%mem.{loc}.store.val.{idx}"
def EmitState.storePortDone (loc : Loc) (idx : Nat) : String := s!"%mem.{loc}.store.done.{idx}"

/-- Registers a new memory port and returns its index for generating unique variables. -/
def EmitState.addPort (port : MemPort) : EmitM EmitState Nat := do
  let s ← .get
  let idx := s.ports.length
  -- Check if the location is declared and matches the element type
  if let .some arr := s.arrays.find? (·.loc = port.loc) then
    let elemTy ← EmitType.emit arr.elem
    if elemTy ≠ port.valTy then
      throw s!"conflicting value type for memory `{port.loc}`: \
        declared {elemTy}, accessed {port.valTy}"
  else
    throw s!"undeclared memory location `{port.loc}`"
  -- Check that previous accesses to the same location
  -- have the same address and value types
  for prevPort in s.ports do
    if prevPort.loc = port.loc then
      if prevPort.addrTy ≠ port.addrTy then
        throw s!"conflicting address types for memory `{port.loc}`: \
          previous {prevPort.addrTy}, new {port.addrTy}"
      if prevPort.valTy ≠ port.valTy then
        throw s!"conflicting value types for memory `{port.loc}`: \
          previous {prevPort.valTy}, new {port.valTy}"
  .set { s with ports := s.ports.concat port }
  return idx

/-- Some simple ops that have a direct correspondence with an `arith` operation. -/
private def SyncOp.emitArith : SyncOp → Option String
  | .add => some "arith.addi"
  | .sub => some "arith.subi"
  | .mul => some "arith.muli"
  | .sdiv => some "arith.divsi"
  | .udiv => some "arith.divsi"
  | .shl => some "arith.shli"
  | .ashr => some "arith.shrsi"
  | .lshr => some "arith.shrui"
  | .eq => some "arith.cmpi eq,"
  | .neq => some "arith.cmpi ne,"
  | .slt => some "arith.cmpi slt,"
  | .sle => some "arith.cmpi sle,"
  | .ult => some "arith.cmpi ult,"
  | .ule => some "arith.cmpi ule,"
  | .and => some "arith.andi"
  | .bitand => some "arith.andi"
  | _ => none

/-- TODO: Check types. -/
instance [Repr α] [ToString α] : EmitOp EmitState SyncOp (VarName α) where
  emit
  | .load loc, inputs, outputs => do
    let addr := inputs[0]'(by simp [Arity.ι])
    let val := outputs[0]'(by simp [Arity.ω])
    let addrTy ← EmitType.emit addr
    let valTy ← EmitType.emit val
    let port := { loc, access := .load, addrTy, valTy : MemPort }
    let idx ← EmitState.addPort port
    let ctrl ← .freshVar
    let portAddr := EmitState.loadPortAddr loc idx
    let portVal := EmitState.loadPortVal loc idx
    -- Wait for the address input to arrive, interact with the memory port
    -- and then forward the loaded value.
    let addrCopy1 ← .freshVar
    let addrCopy2 ← .freshVar
    .writeLn s!"{addrCopy1}, {addrCopy2} = handshake.fork [2] {← EmitVar.emit addr} : {addrTy}"
    .writeLn s!"{ctrl} = handshake.join {addrCopy1} : {addrTy}"
    .writeLn s!"{← EmitVar.emit val}, {portAddr} = handshake.load [{addrCopy2}] {portVal}, {ctrl} : {addrTy}, {valTy}"
  -- The `done` signal of a store operator has the `unit`/`none` type.
  | .store loc, inputs, outputs => do
    let addr := inputs[0]'(by simp [Arity.ι])
    let val := inputs[1]'(by simp [Arity.ι])
    let done := outputs[0]'(by simp [Arity.ω])
    let addrTy ← EmitType.emit addr
    let valTy ← EmitType.emit val
    let port := { loc, access := .store, addrTy, valTy : MemPort }
    let idx ← EmitState.addPort port
    let ctrl ← .freshVar
    let portAddr := EmitState.storePortAddr loc idx
    let portVal := EmitState.storePortVal loc idx
    let portDone := EmitState.storePortDone loc idx
    -- Wait for all inputs to arrive, interact with the memory port
    -- and then forward the done signal.
    let addrCopy1 ← .freshVar
    let addrCopy2 ← .freshVar
    let valCopy1 ← .freshVar
    let valCopy2 ← .freshVar
    .writeLn s!"{addrCopy1}, {addrCopy2} = handshake.fork [2] {← EmitVar.emit addr} : {addrTy}"
    .writeLn s!"{valCopy1}, {valCopy2} = handshake.fork [2] {← EmitVar.emit val} : {valTy}"
    .writeLn s!"{ctrl} = handshake.join {addrCopy1}, {valCopy1} : {addrTy}, {valTy}"
    .writeLn s!"{portVal}, {portAddr} = handshake.store [{addrCopy2}] {valCopy2}, {ctrl} : \
      {addrTy}, {valTy}"
    .writeLn <| s!"{← EmitVar.emit done} = handshake.br {portDone} : {Handshake.PrimType.none}"
  -- | .const v, inputs, outputs
  -- | .copy n, inputs, outputs
  | .sel, inputs, outputs => do
    -- Similar to the cases below, but the type needs
    -- to be taken from one of the data inputs
    let inputVars ← inputs.toList.mapM λ v => EmitVar.emit v
    let ty ← EmitType.emit inputs[1]
    .writeLn s!"{← EmitVar.emit outputs[0]} = \
        arith.select {", ".intercalate inputVars} : {ty}"
  | op, inputs, outputs => do
    if let some arithOp := op.emitArith then
      -- Simple arithmetic operators
      let firstIn := inputs[0]'(by cases op <;> simp [Arity.ι])
      let inputTy ← EmitType.emit firstIn
      let inputVars ← inputs.toList.mapM λ v => EmitVar.emit v
      let outputVars ← outputs.toList.mapM λ v => EmitVar.emit v
      .writeLn s!"{", ".intercalate outputVars} = \
        {arithOp} {", ".intercalate inputVars} : {inputTy}"
    else throw s!"operator {repr op} not yet implemented"

  /-
  Generates templates for actual memory definitions (`handshake.memory`).
  TODO:
    - `handshake.memory` or `handshake.extmemory`?
    - User input for memory sizes
  -/
  finalize := do
    let s ← .get
    -- Generate one `handshake.memory` op for each declared array
    for (locIdx, arr) in s.arrays.mapIdx Prod.mk do
      let ports := s.ports.mapIdx Prod.mk |>.filter (·.snd.loc = arr.loc)
      if let some (_, firstPort) := ports.head? then
        let addrTy := firstPort.addrTy
        let valTy := firstPort.valTy
        -- See <https://circt.llvm.org/docs/Dialects/Handshake/#handshakememory-circthandshakememoryop>
        -- for the order of inputs and outputs.
        let loads := ports.filter (·.snd.access = .load)
        let stores := ports.filter (·.snd.access = .store)
        let inputs :=
          (stores.map λ (idx, _) =>
            [
              EmitState.storePortVal arr.loc idx,
              EmitState.storePortAddr arr.loc idx,
            ]).flatten ++
          (loads.map λ (idx, _) =>
            EmitState.loadPortAddr arr.loc idx)
        let inputTys :=
          (stores.map λ _ => [valTy, addrTy]).flatten ++
          (loads.map λ _ => addrTy)
        let inputTys := inputTys.map ToString.toString
        let outputs :=
          (loads.map λ (idx, _) =>
            EmitState.loadPortVal arr.loc idx) ++
          (stores.map λ (idx, _) =>
            EmitState.storePortDone arr.loc idx) ++
          -- Dummy outputs for unused load "done" signals
          (← loads.mapM λ _ => .freshVar)
        let outputTys :=
          (loads.map λ _ => valTy) ++
          (stores.map λ _ => Handshake.PrimType.none) ++
          -- Dummy outputs for unused load "done" signals
          (loads.map λ _ => Handshake.PrimType.none)
        let outputTys := outputTys.map ToString.toString
        let attr := "{id = " ++ s!"{locIdx}" ++ " : i32, lsq = false}"
        IndentWriterT.writeLn s!"{", ".intercalate outputs} = \
          handshake.memory [ld = {loads.length}, st = {stores.length}] \
          ({", ".intercalate inputs}) {attr} : \
          memref<{arr.size}x{valTy}>, \
          ({", ".intercalate inputTys}) -> ({", ".intercalate outputTys})"

/-- Compiles the given RipTide process to CIRCT/Handshake. -/
def Proc.emitHandshake
  (proc : RipTide.Proc) : Except String String := do
  let (res, _) ← (emitProc proc.inner.proc).run (EmitState.init proc)
  return res

end Handshake

end Wavelet.Frontend.RipTide
