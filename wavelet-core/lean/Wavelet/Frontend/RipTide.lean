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

inductive Value where
  | int (w : Nat) (val : BitVec w)
  deriving BEq, DecidableEq, Hashable, Repr

/-- A special value for control signals. -/
def Value.unit : Value := .int 0 0

instance : Lean.ToJson Value where
  toJson
    | .int w val => json% { "int": { "width": $(w), "value": $(val.toNat) } }

instance : Lean.FromJson Value where
  fromJson? json :=
  (do
    let obj ← json.getObjVal? "int"
    let w ← obj.getObjValAs? Nat "width"
    let v ← obj.getObjValAs? Nat "value"
    return .int w (BitVec.ofNat w v)) <|>
  .error "failed to parse Value"

instance : ToString Value where
  toString
    | .int w val => s!"{val.toInt}i{w}"

/-- Synchronous operators in RipTide, parametrized by a type of location/array symbols. -/
inductive SyncOp (Loc : Type u) : Type u where
  | add | sub | mul | sdiv | udiv
  | shl | ashr | lshr
  | eq | neq | slt | sle | ult | ule
  | and
  | bitand
  | load (_ : Loc) | store (_ : Loc) | sel
  | const (_ : Value)
  | copy (_ : Nat)
  deriving Repr, Lean.ToJson, Lean.FromJson

instance : Arity (SyncOp Loc) where
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

instance : NeZeroArity (SyncOp Loc) where
  neZeroᵢ op := by cases op <;> infer_instance
  neZeroₒ op := by cases op <;> infer_instance

/-- Some constants used for compilation. -/
instance : InterpConsts Value where
  junkVal := .int 0 0
  toBool | .int 1 0 => some false
         | .int 1 1 => some true
         | _ => none
  fromBool b := if b then .int 1 1 else .int 1 0
  unique_fromBool_toBool b := by cases b <;> simp
  unique_toBool_fromBool b v h := by
    split at h <;> simp at h <;> subst h <;> simp
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

private def applyBitVecBinOp
  [DecidableEq Loc] [Hashable Loc]
  (f : ∀ {w : Nat}, BitVec w → BitVec w → BitVec w) :
    Value → Value → StateT (State Loc) Option (Vector Value 1)
  | .int w₁ v₁, .int w₂ v₂ =>
    if h : w₁ = w₂ then
      let v := f v₁ (v₂.cast h.symm)
      return #v[.int w₁ v]
    else
      failure

private def applyBitVecBinPred
  [DecidableEq Loc] [Hashable Loc]
  (f : ∀ {w : Nat}, BitVec w → BitVec w → Bool) :
    Value → Value → StateT (State Loc) Option (Vector Value 1)
  | .int w₁ v₁, .int w₂ v₂ =>
    if h : w₁ = w₂ then
      let b := f v₁ (v₂.cast h.symm)
      return #v[InterpConsts.fromBool b]
    else
      failure

instance instOpInterpM [DecidableEq Loc] [Hashable Loc] :
  OpInterpM (SyncOp Loc) Value (StateT (State Loc) Option) where
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
def opSpec : OpSpec (SyncOp Loc) Value PCM.Triv :=
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
structure Testbench Loc [DecidableEq Loc] [Hashable Loc] where
  inputs : List Value
  state : State Loc
  deriving Lean.FromJson, Lean.ToJson

/-- Run the test vector on the given process until termination. -/
partial def Testbench.run
  [DecidableEq χ] [Repr χ] [DecidableEq Loc] [Hashable Loc] [Repr Loc]
  [Lean.ToJson Loc] [Lean.ToJson χ]
  (tv : Testbench Loc)
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

instance [ToString Loc] : Dataflow.DotName (SyncOp Loc) where
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

/-- Custom rewrites for RipTide. -/
def operatorSel [DecidableEq χ] [Hashable χ] : Rewrite (RipTide.SyncOp Loc) χ Value :=
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

/-! Instances of various compilation passes to RipTide. -/
section Passes

open Compile Determinacy Seq Dataflow Semantics

private abbrev Loc := String
private abbrev FnName := String

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

-- Raw program and process formats used for encoding/decoding
abbrev RawProg := Frontend.RawProg (WithCall (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) FnName) (VarName String)
abbrev RawProc := Frontend.RawProc (RipTide.SyncOp Loc) (VarName Nat) RipTide.Value

-- Actual program and process formats used for compilation
abbrev EncapProg := Frontend.EncapProg (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) (VarName String) RipTide.Value
abbrev EncapProc := Frontend.EncapProc (RipTide.SyncOp Loc) (VarName Nat) RipTide.Value

/-- Validates static properties of a `Prog`. -/
def EncapProg.validate (prog : RipTide.EncapProg) : Except String Unit := do
  for i in List.finRange prog.numFns do
    let name := prog.names[i]? |>.getD s!"unknown"
    (prog.prog i).checkAffineVar.resolve.context s!"function {i} ({name})"

/-- Validates static properties of a `Proc`. -/
def EncapProc.validate (proc : RipTide.EncapProc) : Except String Unit := do
  proc.proc.checkAffineChan

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
  (prog : EncapProg)
  (curIdx : Nat)
  : LinkName (ChanName (VarName α)) → PrimType
  | .base name =>
    if h : curIdx < prog.numFns then
      typeOfChanName (prog.prog ⟨curIdx, h⟩) name
    else
      .unknown
  | .main name => typeOfLinkChanName prog curIdx name
  | .dep idx name => typeOfLinkChanName prog idx name

private def typeOfEraseName
  : EraseName (VarName α) → PrimType
  | .base name => name.ty
  | .input name => name.ty
  | .output name => name.ty
  | .join name _ => name.ty

private def typeOfRewriteName
  : RewriteName (VarName α) → PrimType
  | .base name => name.ty
  | .rw name => typeOfRewriteName name
  | .rename _ name => typeOfRewriteName name

/-- Renames a variable/channel name after linking and compilation,
but preserves the type annotation. -/
private def renameLinkChanName
  (prog : EncapProg)
  (idx : Nat) (name : LinkName (ChanName (VarName α))) : VarName Nat
  := { name := idx, ty := typeOfLinkChanName prog (prog.numFns - 1) name }

/-- Renames a variable after ghost erasure. -/
private def renameEraseName (idx : Nat) (name : EraseName (VarName α)) : VarName Nat
  := { name := idx, ty := typeOfEraseName name }

/-- Renames a variable after rewriting. -/
private def renameRewriteName (idx : Nat) (name : RewriteName (VarName α)) : VarName Nat
  := { name := idx, ty := typeOfRewriteName name }

/-- Converts the last function of the given program to a dataflow process.
This compiles all imperative control-flow to dataflow, and also lowers all
ghost operators/inputs/outputs to concrete order operators. -/
def EncapProg.lowerControlFlow (prog : RipTide.EncapProg) : Except String RipTide.EncapProc := do
  if h : prog.numFns > 0 then
    let : NeZeroSigs prog.sigs := prog.neZero
    let last : Fin prog.numFns := ⟨prog.numFns - 1, by omega⟩
    -- Compile and link
    let proc := compileProg prog.prog last
    let proc := proc.renameChans (renameLinkChanName prog)
    -- Erase ghost tokens
    let proc := proc.eraseGhost
    let proc := proc.renameChans renameEraseName
    return .fromProc proc
  else
    .error "compiling empty program"

/-- Connects the last `n` output channels of the process to `sink`s.
This is useful in avoiding unnecessary outputs (like for ghost permissions)
and reducing the size of the dataflow graph. -/
def EncapProc.sinkLastNOutputs (n : Nat) (proc : RipTide.EncapProc) : RipTide.EncapProc :=
  let rem := proc.numOuts - n
  EncapProc.fromProc {
    proc.proc with
    outputs := proc.proc.outputs.take rem,
    atoms := .sink (proc.proc.outputs.drop rem) :: proc.proc.atoms
  }

/-- Rewrites the given dataflow process using the given rules. -/
def EncapProc.rewriteProc
  (rules : Rewrite (RipTide.SyncOp Loc) (VarName Nat) RipTide.Value)
  (proc : RipTide.EncapProc)
  (disabledRules : List String := []) :
  Nat × RewriteStats × RipTide.EncapProc :=
  let (numRws, stats, proc) := Rewrite.applyUntilFailNat
    renameRewriteName rules proc.proc disabledRules
  (numRws, stats, EncapProc.fromProc proc)

end Passes

/-! Emitting CIRCT Handshake operation(s) for each operator.
TODO: Move this section to `Wavelet.Backend`? -/
section Handshake

open Backend Handshake

instance [Repr α] : EmitType (VarName α) where
  emit v := match v.ty with
    | .int 0 => return Handshake.PrimType.none
    | .int w => return Handshake.PrimType.int w
    | .unknown => .error s!"cannot emit unknown type for variable {repr v}"

instance [ToString α] : EmitVar (VarName α) where
  emit v := return s!"%v{v.name}"

instance : EmitType RipTide.Value where
  emit
    | .int 0 _ => return Handshake.PrimType.none
    | .int w _ => return Handshake.PrimType.int w

instance : EmitConst Value where
  emit | .int _ val => return ToString.toString val

private structure EmitState where

/-- Some simple ops that have a direct correspondence with an `arith` operation. -/
private def SyncOp.emitArith : RipTide.SyncOp Loc → Option String
  | .add => some "arith.addi"
  | .sub => some "arith.subi"
  | .mul => some "arith.muli"
  | .sdiv => some "arith.divsi"
  | .udiv => some "arith.divsi"
  | .shl => some "arith.shli"
  | .ashr => some "arith.shrsi"
  | .lshr => some "arith.shrui"
  | .eq => some "arith.cmpi eq"
  | .neq => some "arith.cmpi ne"
  | .slt => some "arith.cmpi slt"
  | .sle => some "arith.cmpi sle"
  | .ult => some "arith.cmpi ult"
  | .ule => some "arith.cmpi ule"
  | .and => some "arith.andi"
  | .bitand => some "arith.andi"
  | _ => none

/-- TODO: Check types. -/
instance [Repr α] [ToString α] : EmitOp EmitState (RipTide.SyncOp Loc) (VarName α) where
  emit
  -- TODO: Memory
  -- | .load loc, inputs, outputs => sorry
  -- | .store loc, inputs, outputs => sorry
  -- `const` and `copy` should be already lowered to the built-in versions
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

  finalize := return

/-- Compiles the given RipTide process to CIRCT/Handshake. -/
def EncapProc.emitHandshake
  (proc : RipTide.EncapProc) : Except String String := do
  let (res, _) ← (emitProc proc.proc).run EmitState.mk
  return res

end Handshake

end Wavelet.Frontend.RipTide
