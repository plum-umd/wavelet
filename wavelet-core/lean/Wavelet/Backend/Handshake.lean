import Wavelet.Data.IndentWriter
import Wavelet.Dataflow.Proc

/-!
A (unverified) backend that compiles dataflow graphs
to a dataflow circuit in the CIRCT Handshake dialect.
-/

namespace Wavelet.Backend.Handshake

open Semantics Dataflow

/-- CIRCT/Handshake primitive types. -/
inductive PrimType where
  | int (w : Nat)
  | none
  deriving DecidableEq, Repr

instance : ToString PrimType where
  toString
    | .int w => s!"i{w}"
    | .none => "none"

private def PrimType.defaultValue : PrimType → Except String String
  | .int _ => return "0"
  | .none => .error "no default value for type none"

private structure EmitState (σ : Type u) where
  freshCounter : Nat
  userState : σ

abbrev EmitM σ := IndentWriterT (EmitState σ) String

def EmitM.freshVar : EmitM σ String := do
  let s ← .get
  .modify λ s => { s with freshCounter := s.freshCounter + 1 }
  return s!"%_.{s.freshCounter}"

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

/-- User-defined operators are emitted via a custom state monad. -/
class EmitOp σ (Op : Type u) (χ : Type v) [Arity Op] where
  emit : (op : Op)
    → Vector χ (Arity.ι op)
    → Vector χ (Arity.ω op)
    → EmitM σ Unit

  /-- There might be some finalizing operators to call. -/
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
      handshake.cond_br {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
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
        handshake.cond_br {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
    else
      .writeLn s!"{dummy}, {← EmitVar.emit output} = \
        handshake.cond_br {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
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
        handshake.mux {← EmitVar.emit decider} [{← EmitVar.emit input₁}, {← EmitVar.emit input₂}] \
          : {PrimType.int 1}, {outputTy}"
    -- Carry requires an initial false/true decider token
    | .popLeft | .popRight =>
      let buf ← .freshVar
      let attr := if state = .popLeft then "{initValues = [0]}" else "{initValues = [1]}"
      .writeLn s!"{buf} = handshake.buffer [1] seq {← EmitVar.emit decider} {attr} : {PrimType.int 1}"
      .writeLn s!"{← EmitVar.emit output} = \
        handshake.mux {buf} [{← EmitVar.emit input₁}, {← EmitVar.emit input₂}] : {PrimType.int 1}, {outputTy}"
  -- `forward` maps to `handshake.br`
  | .async (.forward 1) [input] [output] => do
    let inputTy ← EmitType.emit input
    let outputTy ← EmitType.emit output
    if inputTy ≠ outputTy then
      throw s!"input type should match output type {outputTy}, but got {inputTy}"
    .writeLn s!"{← EmitVar.emit output} = handshake.br {← EmitVar.emit input} : {inputTy}"
  -- `fork` maps to `handshake.fork`
  | .async (.fork n) [input] outputs => do
    let inputTy ← EmitType.emit input
    for output in outputs do
      let outputTy ← EmitType.emit output
      if inputTy ≠ outputTy then
        throw s!"input type should match output type {outputTy}, but got {inputTy}"
    let forkOuts ← .freshVar
    .writeLn s!"{forkOuts}:{n} = handshake.fork [{n}] {← EmitVar.emit input} : {inputTy}"
    -- Destruct fork results
    (outputs.mapIdx Prod.mk).forM λ ⟨i, output⟩ => do
      .writeLn s!"{← EmitVar.emit output} = handshake.br {forkOuts}#{i} : {inputTy}"
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
      .writeLn s!"{← EmitVar.emit output} = handshake.join {ins} : {inTys}"
    else
      let dummyOuts ← rest.mapM λ _ => .freshVar
      let outs := ", ".intercalate <| (← EmitVar.emit output) :: dummyOuts
      .writeLn s!"{outs} = handshake.sync {ins} : {inTys}"
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
        .writeLn s!"{← EmitVar.emit output} = handshake.br {← EmitVar.emit act} : {outputTy}"
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
          handshake.constant {← EmitVar.emit act} {attr} : {outputTy}"
      else
        -- Convert `act` to `none` first, then call `constant`
        let act' ← .freshVar
        .writeLn s!"{act'} = join {← EmitVar.emit act} : {actTy}"
        .writeLn s!"{← EmitVar.emit output} = \
          handshake.constant {act'} {attr} : {outputTy}"
  -- `sink` maps to `handshake.sink`
  | .async (AsyncOp.sink 1) [input] [] => do
    .writeLn s!"handshake.sink {← EmitVar.emit input} : {← EmitType.emit input}"
  -- `inact` maps to `handshake.never`
  | .async (AsyncOp.inact 1) [] [output] => do
    .writeLn s!"{← EmitVar.emit output} = handshake.never : {← EmitType.emit output}"
  | ap =>
    throw s!"unsupported atomic process: {repr ap}"

def emitAtomicProcs (aps : AtomicProcs Op χ V) : EmitM σ Unit :=
  aps.forM λ ap =>
    emitAtomicProc ap |>.context s!"when emitting atomic process {repr ap}"

def emitProc (proc : Proc Op χ V m n) : EmitM σ Unit := do
  -- Emit function header
  let args ← proc.inputs.toList.mapM λ v => do
    return s!"{← EmitVar.emit v}: {← EmitType.emit v}"
  let retTys ← proc.outputs.toList.mapM λ v => ToString.toString <$> EmitType.emit v
  let argNames := proc.inputs.toList.mapIdx λ i _ => s!"\"in{i}\""
  let retNames := proc.outputs.toList.mapIdx λ i _ => s!"\"out{i}\""
  let attrs := s!"argNames = [{", ".intercalate argNames}], \
    resNames = [{", ".intercalate retNames}]"
  let attrs := "{" ++ attrs ++ "}"
  .writeLn <| s!"handshake.func @top({", ".intercalate args}) \
    -> ({", ".intercalate retTys}) attributes {attrs}" ++ " {"
  .indentBy 2
  -- Emit body
  emitAtomicProcs proc.atoms
  -- Finalize
  instEmitOp.finalize
  -- Emit return operation
  let retVars ← proc.outputs.toList.mapM λ v => EmitVar.emit v
  let retTys ← proc.outputs.toList.mapM λ v => ToString.toString <$> EmitType.emit v
  .writeLn s!"return {", ".intercalate retVars} : {", ".intercalate retTys}"
  .dedentBy 2
  .writeLn "}"

end Emit

end Wavelet.Backend.Handshake
