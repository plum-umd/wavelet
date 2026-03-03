import Wavelet.Data.IndentWriter
import Wavelet.Dataflow.Proc
import Wavelet.Frontend.RipTide

/-!
A (unverified) backend that compiles dataflow graphs
to a dataflow circuit in the CIRCT Handshake dialect.
-/

namespace Wavelet.Backend.Handshake

open Semantics Dataflow

/-- CIRCT/Handshake primitive types. -/
inductive PrimType where
  | none
  | int (w : Nat)
  | index
  | memref (n : Nat) (elem : PrimType)
  deriving DecidableEq, Repr

private def PrimType.toString : PrimType → String
  | .none => "none"
  | .int w => s!"i{w}"
  | .index => "index"
  | .memref n elem => s!"memref<{n} x {elem.toString}>"

instance : ToString PrimType where
  toString := PrimType.toString

private def PrimType.defaultValue : PrimType → Except String String
  | .int _ => return "0"
  | ty => .error s!"no default value for type `{ty}`"

private structure EmitState (σ : Type u) where
  freshCounter : Nat
  userState : σ

abbrev EmitM σ := IndentWriterT (EmitState σ) String

def EmitM.freshVar : EmitM σ String := do
  let s ← .get
  .modify λ s => { s with freshCounter := s.freshCounter + 1 }
  return s!"%_{s.freshCounter}"

def EmitM.get : EmitM σ σ := (·.userState) <$> IndentWriterT.get

def EmitM.set (x : σ) : EmitM σ Unit := do
  IndentWriterT.modify λ s => { s with userState := x }

def EmitM.modify (f : σ → σ) : EmitM σ Unit := do
  EmitM.set (f (← EmitM.get))

def EmitM.run (m : EmitM σ Unit) (init : σ) : Except String (String × σ) := do
  let (v, s) ← IndentWriterT.run m { freshCounter := 0, userState := init }
  return ⟨v, s.userState⟩

def EmitM.context (m : EmitM σ α) (ctx : String) : EmitM σ α := do
  match StateT.run m (← StateT.get) with
  | .ok (v, s) => StateT.set s; return v
  | .error err => throw (s!"{ctx}: {err}")

class EmitType (χ : Type u) where
  emit : χ → Except String PrimType

class EmitVar (χ : Type u) where
  emit : χ → Except String String

class EmitConst (V : Type u) where
  emit : V → Except String String

/-- External port is an input or output of the top-level circuit. -/
structure ExternalPort where
  /-- Name when used as an MLIR variable. -/
  name : String
  /-- External name used in Verilog. -/
  extName : String
  ty : PrimType

/-- User-defined operators are emitted via a custom state monad. -/
class EmitOp σ (Op : Type u) (χ : Type v) [Arity Op] where
  emit : (op : Op)
    → Vector χ (Arity.ι op)
    → Vector χ (Arity.ω op)
    → EmitM σ Unit

  /-- Declares additional inputs/arguments, called before the body compilation. -/
  additionalInputs : EmitM σ (List ExternalPort)

  /-- Declares additional outputs, called before the body compilation. -/
  additionalOutputs : EmitM σ (List ExternalPort)

  /-- Generates initializing operations. -/
  init : EmitM σ Unit

  /-- Generates finalizing operations. -/
  finalize : EmitM σ Unit

section Emit

variable {Op χ V σ}
variable [Repr Op] [Repr χ] [Repr V]
variable [Arity Op] [InterpConsts V] [DecidableEq V]
variable [instEmitOp : EmitOp σ Op χ] [EmitType χ] [EmitVar χ]
variable [EmitType V] [EmitConst V]

/-- Translates the given atomic process to an CIRCT/Handshake operation. -/
def emitAtomicProc : AtomicProc Op χ V → EmitM σ Unit
  -- User-defined operators
  | .op o inputs outputs => EmitOp.emit o inputs outputs
  -- `switch` maps to `handshake.cond_br`
  | .async (.switch 1) [decider, input] [output₁, output₂] => do
    let deciderTy ← EmitType.emit decider
    let inputTy ← EmitType.emit input
    let outputTy₁ ← EmitType.emit output₁
    let outputTy₂ ← EmitType.emit output₂
    if deciderTy ≠ .int 1 then
      throw s!"decider should have type {PrimType.int 1}, but got {deciderTy}"
    if outputTy₁ ≠ inputTy then
      throw s!"output type should match input type {inputTy}, but got {outputTy₁}"
    if outputTy₂ ≠ inputTy then
      throw s!"output type should match input type {inputTy}, but got {outputTy₂}"
    .writeLn s!"{← EmitVar.emit output₁}, {← EmitVar.emit output₂} = \
      cond_br {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
  -- `steer` maps to `handshake.cond_br` with one output
  | .async (.steer flavor 1) [decider, input] [output] => do
    let deciderTy ← EmitType.emit decider
    let inputTy ← EmitType.emit input
    let outputTy ← EmitType.emit output
    if deciderTy ≠ .int 1 then
      throw s!"decider should have type {PrimType.int 1}, but got {deciderTy}"
    if outputTy ≠ inputTy then
      throw s!"output type should match input type {inputTy}, but got {outputTy}"
    let dummy ← .freshVar
    if flavor then
      .writeLn s!"{← EmitVar.emit output}, {dummy} = \
        cond_br {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
    else
      .writeLn s!"{dummy}, {← EmitVar.emit output} = \
        cond_br {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
  -- `merge` maps to `handshake.mux`
  | .async (.merge state 1) [decider, input₁, input₂] [output] => do
    let deciderTy ← EmitType.emit decider
    let inputTy₁ ← EmitType.emit input₁
    let inputTy₂ ← EmitType.emit input₂
    let outputTy ← EmitType.emit output
    if deciderTy ≠ .int 1 then
      throw s!"decider should have type {PrimType.int 1}, but got {deciderTy}"
    if inputTy₁ ≠ outputTy then
      throw s!"input type should match output type {outputTy}, but got {inputTy₁}"
    if inputTy₂ ≠ outputTy then
      throw s!"input type should match output type {outputTy}, but got {inputTy₂}"
    match state with
    -- Normal mux
    | .decider =>
      .writeLn s!"{← EmitVar.emit output} = \
        mux {← EmitVar.emit decider} [{← EmitVar.emit input₁}, {← EmitVar.emit input₂}] \
          : {PrimType.int 1}, {outputTy}"
    -- Carry requires an initial false/true decider token
    | .popLeft | .popRight =>
      let buf ← .freshVar
      let attr := if state = .popLeft then "{initValues = [0]}" else "{initValues = [1]}"
      .writeLn s!"{buf} = buffer [1] seq {← EmitVar.emit decider} {attr} : {PrimType.int 1}"
      .writeLn s!"{← EmitVar.emit output} = \
        mux {buf} [{← EmitVar.emit input₁}, {← EmitVar.emit input₂}] : {PrimType.int 1}, {outputTy}"
  -- `forward` maps to `handshake.br`
  | .async (.forward 1) [input] [output] => do
    let inputTy ← EmitType.emit input
    let outputTy ← EmitType.emit output
    if inputTy ≠ outputTy then
      throw s!"input type should match output type {outputTy}, but got {inputTy}"
    .writeLn s!"{← EmitVar.emit output} = br {← EmitVar.emit input} : {inputTy}"
  -- `fork` maps to `handshake.fork`
  | .async (.fork n) [input] outputs => do
    let inputTy ← EmitType.emit input
    for output in outputs do
      let outputTy ← EmitType.emit output
      if inputTy ≠ outputTy then
        throw s!"input type should match output type {outputTy}, but got {inputTy}"
    let forkOuts ← outputs.mapM λ o => EmitVar.emit o
    .writeLn s!"{", ".intercalate forkOuts} = fork [{n}] {← EmitVar.emit input} : {inputTy}"
  -- `order` maps to `handshake.sync` with rest of the outputs ignored
  | .async (AsyncOp.order _) (first :: rest) [output] => do
    let outputTy ← EmitType.emit output
    let firstTy ← EmitType.emit first
    if outputTy ≠ firstTy then
      throw s!"output type should match input type {firstTy}, but got {outputTy}"
    let ins := ", ".intercalate <| (← EmitVar.emit first) :: (← rest.mapM λ r => EmitVar.emit r)
    let inTys := ", ".intercalate <| ToString.toString firstTy ::
      ((← rest.mapM λ r => EmitType.emit r).map toString)
    if outputTy = .none then
      -- If the output is `none`, we directly use `handshake.join`
      -- to avoid a `handshake.sync` issue when all inputs/outputs are `none`.
      .writeLn s!"{← EmitVar.emit output} = join {ins} : {inTys}"
    else
      let dummyOuts ← rest.mapM λ _ => .freshVar
      let outs := ", ".intercalate <| (← EmitVar.emit output) :: dummyOuts
      .writeLn s!"{outs} = sync {ins} : {inTys}"
  -- `const` maps to `handshake.constant` (but we need to convert the activation
  -- signal to `none` if it is not already one)
  | .async (AsyncOp.const const 1) [act] [output] => do
    let actTy ← EmitType.emit act
    let outputTy ← EmitType.emit output

    -- Since we cannot create a `none` constant in MLIR,
    -- we have to handle four cases here.
    -- TODO: Check if this is actually the case.
    if outputTy = .none then
      if actTy = .none then
        .writeLn s!"{← EmitVar.emit output} = br {← EmitVar.emit act} : {outputTy}"
      else
        .writeLn s!"{← EmitVar.emit output} = join {← EmitVar.emit act} : {actTy}"
    else
      -- In the special case when `const` is `junkVal`, we
      -- emit the default constant of the output type.
      let attr ← if const = InterpConsts.junkVal then
        pure <| "{value = " ++ s!"{← outputTy.defaultValue} : {outputTy}" ++ "}"
      else
        let constTy ← EmitType.emit const
        if constTy ≠ outputTy then
          throw s!"constant type should match output type {outputTy}, but got {constTy}"
        pure <| "{value = " ++ s!"{← EmitConst.emit const} : {outputTy}" ++ "}"
      if actTy = .none then
        .writeLn s!"{← EmitVar.emit output} = \
          constant {← EmitVar.emit act} {attr} : {outputTy}"
      else
        -- Convert `act` to `none` first, then call `constant`
        let act' ← .freshVar
        .writeLn s!"{act'} = join {← EmitVar.emit act} : {actTy}"
        .writeLn s!"{← EmitVar.emit output} = \
          constant {act'} {attr} : {outputTy}"
  -- `sink` maps to `handshake.sink`
  | .async (AsyncOp.sink 1) [input] [] => do
    .writeLn s!"sink {← EmitVar.emit input} : {← EmitType.emit input}"
  -- `inact` maps to `handshake.never`
  | .async (AsyncOp.inact 1) [] [output] => do
    .writeLn s!"{← EmitVar.emit output} = never : {← EmitType.emit output}"
  | ap =>
    throw s!"unsupported atomic process: {repr ap}"

def emitAtomicProcs (aps : AtomicProcs Op χ V) : EmitM σ Unit :=
  aps.forM λ ap =>
    emitAtomicProc ap |>.context s!"when emitting atomic process {repr ap}"

/-- Generates handshake function header. -/
def emitHeader
  (proc : Proc Op χ V m n)
  (additionalIns : List ExternalPort)
  (additionalOuts : List ExternalPort) : EmitM σ Unit := do
  -- Arguments and their external names.
  let args ← proc.inputs.toList.mapM λ v => do
    return s!"{← EmitVar.emit v}.tmp: {← EmitType.emit v}"
  let args := args ++ additionalIns.map λ i => s!"{i.name}.tmp: {i.ty}"
  let argNames := proc.inputs.toList.mapIdx λ i _ => s!"\"in{i}\""
  let argNames := argNames ++ additionalIns.map λ i => s!"\"{i.extName}\""
  -- Return (types) and their external names.
  let retTys ← proc.outputs.toList.mapM λ v => ToString.toString <$> EmitType.emit v
  let retTys := retTys ++ additionalOuts.map (ToString.toString ·.ty)
  let retNames := proc.outputs.toList.mapIdx λ i _ => s!"\"out{i}\""
  let retNames := retNames ++ additionalOuts.map λ o => s!"\"{o.extName}\""
  -- Generate the final header
  let attrs := s!"argNames = [{", ".intercalate argNames}], \
    resNames = [{", ".intercalate retNames}]"
  let attrs := "{" ++ attrs ++ "}"
  .writeLn <| s!"handshake.func @top({", ".intercalate args}) \
    -> ({", ".intercalate retTys}) attributes {attrs}" ++ " {"
  -- Generate buffers for each input
  -- TODO: Figure out why this is needed
  .indentBy 2
  for v in proc.inputs.toList do
    let var ← EmitVar.emit v
    let ty ← EmitType.emit v
    IndentWriterT.writeLn s!"{var} = buffer [1] seq {var}.tmp : {ty}"
  for i in additionalIns do
    IndentWriterT.writeLn s!"{i.name} = buffer [1] seq {i.name}.tmp : {i.ty}"

/-- Emits the final return operation. -/
def emitReturn (proc : Proc Op χ V m n) (additionalOuts : List ExternalPort) : EmitM σ Unit := do
  let retVars ← proc.outputs.toList.mapM λ v => EmitVar.emit v
  let retVars := retVars ++ additionalOuts.map (·.name)
  let retTys ← proc.outputs.toList.mapM λ v => ToString.toString <$> EmitType.emit v
  let retTys := retTys ++ additionalOuts.map (ToString.toString ·.ty)
  .writeLn s!"return {", ".intercalate retVars} : {", ".intercalate retTys}"

def emitProc (proc : Proc Op χ V m n) : EmitM σ Unit := do
  let additionalIns ← instEmitOp.additionalInputs
  let additionalOuts ← instEmitOp.additionalOutputs
  emitHeader proc additionalIns additionalOuts
  instEmitOp.init
  emitAtomicProcs proc.atoms
  instEmitOp.finalize
  emitReturn proc additionalOuts
  .dedentBy 2
  .writeLn "}"

end Emit

/-! Handshake backend for RipTide. -/
namespace RipTide

open Frontend

instance : EmitType RipTide.PrimType where
  emit
    | .int 0 => return Handshake.PrimType.none
    | .int w => return Handshake.PrimType.int w
    | .unknown => .error "cannot emit unknown primitive type"

instance [Repr α] : EmitType (RipTide.VarName α) where
  emit v := EmitType.emit v.ty

instance [ToString α] : EmitVar (RipTide.VarName α) where
  emit v := return s!"%v{v.name}"

instance : EmitType RipTide.Value where
  emit
    | .int 0 _ => return Handshake.PrimType.none
    | .int w _ => return Handshake.PrimType.int w
    | .junk => .error "cannot emit type for junk value"

instance : EmitConst RipTide.Value where
  emit
    | .int w val =>
      if w = 0 then
        .error "cannot emit constant of type none"
      else
        return s!"{val.toNat}"
    | .junk => .error "cannot emit constant of type junk"

private inductive MemAccess where | load | store
  deriving DecidableEq, Repr

instance : ToString MemAccess where
  toString
    | .load => "load"
    | .store => "store"

/-- Each memory access is assigned a port to send the actual
values and addresses. The value of `MemPort` should be unique
for each memory access. -/
private structure MemPort where
  loc : RipTide.Loc
  access : MemAccess
  idx : Nat
  deriving DecidableEq, Repr

/- MLIR variable names of a memory port. -/
def MemPort.addrVar (port : MemPort) : String := s!"%mem.{port.loc}.{port.access}{port.idx}.addr"
def MemPort.dataVar (port : MemPort) : String := s!"%mem.{port.loc}.{port.access}{port.idx}.data"
def MemPort.doneVar (port : MemPort) : String := s!"%mem.{port.loc}.{port.access}{port.idx}.done"

/-- Records required memory ports for all accesses. -/
private structure EmitState where
  proc : RipTide.Proc
  ports : List MemPort

def EmitState.init (proc : RipTide.Proc) : EmitState :=
  { proc, ports := initPorts }
  where
    /-- Iterates through all atomic processes and assigns
    unique ports to all memory accesses. -/
    initPorts : List MemPort :=
      proc.inner.proc.atoms.foldl
        (λ acc ap =>
          match ap with
          | .op (RipTide.SyncOp.load loc) _ _ =>
            let idx := acc.countP λ p => p.loc = loc ∧ p.access = .load
            acc.concat { loc, access := .load, idx }
          | .op (RipTide.SyncOp.store loc) _ _ =>
            let idx := acc.countP λ p => p.loc = loc ∧ p.access = .store
            acc.concat { loc, access := .store, idx }
          | _ => acc)
        []

/--
Generates a list of input/output variables for a particular array `arr`,
in the same order as required by `handshake.memory`.

See <https://circt.llvm.org/docs/Dialects/Handshake/#handshakememory-circthandshakememoryop>
for the order of inputs and outputs.
-/
def EmitState.getMemIO (arr : RipTide.ArrayDecl) : EmitM EmitState (List ExternalPort × List ExternalPort) := do
  let s ← .get
  let ports := s.ports.filter (·.loc = arr.loc)
  let valTy ← EmitType.emit arr.elem
  let loads := ports.filter (·.access = .load)
  let stores := ports.filter (·.access = .store)
  let inputs :=
    (stores.map λ port => [
      { name := port.dataVar,
        extName := s!"mem.{arr.loc}.store{port.idx}.data",
        ty := valTy },
      { name := port.addrVar,
        extName := s!"mem.{arr.loc}.store{port.idx}.addr",
        ty := .index }
    ]).flatten ++
    (loads.map λ port => {
      name := port.addrVar,
      extName := s!"mem.{arr.loc}.load{port.idx}.addr",
      ty := .index
    })
  let outputs :=
    (loads.map λ port => {
      name := port.dataVar,
      extName := s!"mem.{arr.loc}.load{port.idx}.data",
      ty := valTy
    }) ++
    (stores.map λ port => {
      name := port.doneVar,
      extName := s!"mem.{arr.loc}.store{port.idx}.done",
      ty := Handshake.PrimType.none
    }) ++
    (loads.map λ port => {
      name := port.doneVar,
      extName := s!"mem.{arr.loc}.load{port.idx}.done",
      ty := Handshake.PrimType.none
    })
  return (inputs, outputs)

/-- Checks if the given memory is external. -/
def EmitState.isExternal (loc : RipTide.Loc) : EmitM EmitState  Bool := do
  let s ← .get
  return s.proc.arrays.any (λ arr => arr.loc = loc ∧ arr.external)

/-- Finds and removes the next available port for loading/storing to `loc`. -/
def EmitState.useNextPort (loc : RipTide.Loc) (access : MemAccess) : EmitM EmitState MemPort := do
  let s ← .get
  match s.ports.find? λ p => p.loc = loc ∧ p.access = access with
  | .some port =>
    .set { s with ports := s.ports.erase port }
    return port
  | .none =>
    -- NOTE: This is likely a bug.
    throw s!"no available port for {access} at memory `{loc}`"

/-- Some simple ops that have a direct correspondence with an `arith` operation. -/
private def emitArithOp : RipTide.SyncOp → Option String
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

instance [Repr α] [ToString α]
  : EmitOp EmitState RipTide.SyncOp (RipTide.VarName α) where
  emit
  | .load loc, inputs, outputs => do
    let addr := inputs[0]'(by simp [Arity.ι])
    let val := outputs[0]'(by simp [Arity.ω])
    let addrTy ← EmitType.emit addr
    -- Cast the address to `index` type.
    -- This is not required with `handshake.memory`,
    -- but it seems to be the case for `handshake.extmemory`.
    let addr ← if addrTy ≠ .index then
      let addr' ← .freshVar
      .writeLn s!"{addr'} = arith.index_cast {← EmitVar.emit addr} : {addrTy} to index"
      pure addr'
    else
      EmitVar.emit addr
    let addrTy := PrimType.index
    let valTy ← EmitType.emit val
    let port ← EmitState.useNextPort loc .load
    let ctrl ← .freshVar
    -- Wait for the address input to arrive, interact with the memory port
    -- and then forward the loaded value.
    let addrCopy1 ← .freshVar
    let addrCopy2 ← .freshVar
    .writeLn s!"{addrCopy1}, {addrCopy2} = fork [2] {addr} : {addrTy}"
    .writeLn s!"{ctrl} = join {addrCopy1} : {addrTy}"
    .writeLn s!"{← EmitVar.emit val}, {port.addrVar} = load [{addrCopy2}] {port.dataVar}, {ctrl} : {addrTy}, {valTy}"
  -- The `done` signal of a store operator has the `unit`/`none` type.
  | .store loc, inputs, outputs => do
    let addr := inputs[0]'(by simp [Arity.ι])
    let val := inputs[1]'(by simp [Arity.ι])
    let done := outputs[0]'(by simp [Arity.ω])
    let addrTy ← EmitType.emit addr
    -- Cast to `index` type
    let addr ← if addrTy ≠ .index then
      let addr' ← .freshVar
      .writeLn s!"{addr'} = arith.index_cast {← EmitVar.emit addr} : {addrTy} to index"
      pure addr'
    else
      EmitVar.emit addr
    let addrTy := PrimType.index
    let valTy ← EmitType.emit val
    let port ← EmitState.useNextPort loc .store
    let ctrl ← .freshVar
    -- For external memory, we need to conservatively insert
    -- additional buffers to avoid deadlocks.
    -- TODO: Figure out a better solution.
    let (portAddr, portVal, portDone) ← if ← EmitState.isExternal loc then
      let portAddrBuf ← .freshVar
      let portValBuf ← .freshVar
      let portDoneBuf ← .freshVar
      .writeLn s!"{port.addrVar} = buffer [1] seq {portAddrBuf} : {addrTy}"
      .writeLn s!"{port.dataVar} = buffer [1] seq {portValBuf} : {valTy}"
      .writeLn s!"{portDoneBuf} = buffer [1] seq {port.doneVar} : {Handshake.PrimType.none}"
      pure (portAddrBuf, portValBuf, port.doneVar)
    else
      pure (port.addrVar, port.dataVar, port.doneVar)
    -- Wait for all inputs to arrive, interact with the memory port
    -- and then forward the done signal.
    let addrCopy1 ← .freshVar
    let addrCopy2 ← .freshVar
    let valCopy1 ← .freshVar
    let valCopy2 ← .freshVar
    .writeLn s!"{addrCopy1}, {addrCopy2} = fork [2] {addr} : {addrTy}"
    .writeLn s!"{valCopy1}, {valCopy2} = fork [2] {← EmitVar.emit val} : {valTy}"
    .writeLn s!"{ctrl} = join {addrCopy1}, {valCopy1} : {addrTy}, {valTy}"
    .writeLn s!"{portVal}, {portAddr} = store [{addrCopy2}] {valCopy2}, {ctrl} : \
      {addrTy}, {valTy}"
    .writeLn <| s!"{← EmitVar.emit done} = br {portDone} : {Handshake.PrimType.none}"
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
    if let some arithOp := emitArithOp op then
      -- Simple arithmetic operators
      let firstIn := inputs[0]'(by cases op <;> simp [Arity.ι])
      let inputTy ← EmitType.emit firstIn
      let inputVars ← inputs.toList.mapM λ v => EmitVar.emit v
      let outputVars ← outputs.toList.mapM λ v => EmitVar.emit v
      .writeLn s!"{", ".intercalate outputVars} = \
        {arithOp} {", ".intercalate inputVars} : {inputTy}"
    else throw s!"operator {repr op} not yet implemented"

  /- External memories have extra parameters. Note that here,
  the inputs to the top-level circuit is the output of a
  `handshake.memory` operation. -/
  additionalInputs := do
    let s ← .get
    let outputs ← s.proc.arrays.mapM λ arr => do
      if arr.external then
        let (_, outputs) ← EmitState.getMemIO arr
        return outputs
      else
        return []
    return outputs.flatten

  /- External memories have additional outputs. -/
  additionalOutputs := do
    let s ← .get
    let inputs ← s.proc.arrays.mapM λ arr => do
      if arr.external then
        let (inputs, _) ← EmitState.getMemIO arr
        return inputs
      else
        return []
    return inputs.flatten

  /- Generates concrete memory definitions (`handshake.memory` and `handshake.extmemory`). -/
  init := do
    let s ← .get
    -- Generate one `handshake.memory` op for each declared array
    for (locIdx, arr) in s.proc.arrays.mapIdx Prod.mk do
      if ¬ arr.external then
        -- External memories do not have an internal `handshake.memory` definition
        let valTy ← EmitType.emit arr.elem
        let numLoads := s.ports.countP λ p => p.loc = arr.loc ∧ p.access = .load
        let numStores := s.ports.countP λ p => p.loc = arr.loc ∧ p.access = .store
        let (inputs, outputs) ← EmitState.getMemIO arr
        let inputVars := inputs.map (·.name)
        let inputTys := inputs.map (ToString.toString ·.ty)
        let outputVars := outputs.map (·.name)
        let outputTys := outputs.map (ToString.toString ·.ty)
        let attr := "{id = " ++ s!"{locIdx}" ++ " : i32, lsq = false}"
        let size ← if let .some s := arr.size then pure s else
          throw s!"cannot emit internal memory of unknown size for array `{arr.loc}`"
        -- Generates an internal memory definition
        IndentWriterT.writeLn s!"{", ".intercalate outputVars} = \
          memory [ld = {numLoads}, st = {numStores}] \
          ({", ".intercalate inputVars}) {attr} : \
          memref<{size}x{valTy}>, \
          ({", ".intercalate inputTys}) -> ({", ".intercalate outputTys})"

  finalize := pure ()

/-- Compiles the given RipTide process to CIRCT/Handshake. -/
def emitProc
  (proc : RipTide.Proc) : Except String String := do
  let (res, _) ← (Handshake.emitProc proc.inner.proc).run (EmitState.init proc)
  return res

end RipTide

end Wavelet.Backend.Handshake
