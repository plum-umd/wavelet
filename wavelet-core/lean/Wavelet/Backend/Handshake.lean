import Wavelet.Data.IndentWriter
import Wavelet.Frontend.RipTide

/-!
A (unverified) backend that compiles dataflow graphs
to a dataflow circuit in the CIRCT Handshake dialect.
-/

namespace Wavelet.Backend.Handshake

open Frontend Semantics Dataflow

/-- MLIR/Handshake primitive types. -/
inductive PrimType where
  | int (w : Nat)
  | none
  deriving DecidableEq, Repr

instance : ToString PrimType where
  toString
    | .int w => s!"i{w}"
    | .none => "none"

class EmitType (χ : Type u) where
  emit : χ → Except String PrimType

class EmitVar (χ : Type u) where
  emit : χ → Except String String

class EmitConst (V : Type u) where
  emit : V → Except String String

class EmitOp (Op : Type u) (χ : Type v) [Arity Op] where
  emit : (op : Op) → Vector χ (Arity.ι op) → Vector χ (Arity.ω op) → Except String String

structure EmitState where
  freshCounter : Nat

abbrev EmitM := IndentWriterT EmitState String

def EmitM.freshVar : EmitM String := do
  let s ← .get
  .modify λ s => { s with freshCounter := s.freshCounter + 1 }
  return s!"%_.{s.freshCounter}"

/-- Translates the given atomic process to an MLIR/Handshake operation. -/
def emitAtomicProc
  [Repr Op] [Repr χ] [Repr V]
  [Arity Op] [EmitOp Op χ]
  [EmitType χ] [EmitVar χ] [EmitType V] [EmitConst V]
  : AtomicProc Op χ V → EmitM Unit
  -- User-defined operators
  | .op o inputs outputs => do
    .writeLn (← EmitOp.emit o inputs outputs)
  -- `switch` maps to `handshake.conditional_branch`
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
      handshake.conditional_branch {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
  -- `steer` maps to `handshake.conditional_branch` with one output
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
        handshake.conditional_branch {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
    else
      .writeLn s!"{dummy}, {← EmitVar.emit output} = \
        handshake.conditional_branch {← EmitVar.emit decider}, {← EmitVar.emit input} : {inputTy}"
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
      let attr := if state = .popLeft then "{initValues = [1]}" else "{initValues = [0]}"
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
      .writeLn s!"{← EmitVar.emit output} = handshake.br {forkOuts}:{i} : {inputTy}"
  -- `order` maps to `handshake.sync` with rest of the outputs ignored
  | .async (AsyncOp.order _) (first :: rest) [output] => do
    let outputTy ← EmitType.emit output
    let firstTy ← EmitType.emit first
    if outputTy ≠ firstTy then
      throw s!"output type should match input type {firstTy}, but got {outputTy}"
    let dummyOuts ← rest.mapM λ _ => .freshVar
    let outs := ", ".intercalate <| (← EmitVar.emit output) :: dummyOuts
    let ins := ", ".intercalate <| (← EmitVar.emit first) :: (← rest.mapM λ r => EmitVar.emit r)
    let inTys := ", ".intercalate <| ToString.toString firstTy ::
      ((← rest.mapM λ r => EmitType.emit r).map toString)
    .writeLn s!"{outs} = handshake.sync {ins} : {inTys}"
  -- `const` maps to `handshake.constant` (but we need to convert the activation
  -- signal to `none` if it is not already one)
  | .async (AsyncOp.const const 1) [act] [output] => do
    let constTy ← EmitType.emit const
    let actTy ← EmitType.emit act
    let outputTy ← EmitType.emit output
    if constTy ≠ outputTy then
      throw s!"constant type should match output type {outputTy}, but got {constTy}"

    let attr := "{value = " ++ s!"{← EmitConst.emit const} : {constTy}" ++ "}"
    if actTy = .none then
      .writeLn s!"{← EmitVar.emit output} = \
        handshake.constant {← EmitVar.emit act} {attr} : {constTy}"
    else
      -- Convert `act` to `none` first, then call `constant`
      let act' ← .freshVar
      .writeLn s!"{act'} = join {← EmitVar.emit act} : {actTy}"
      .writeLn s!"{← EmitVar.emit output} = \
        handshake.constant {act'} {attr} : {constTy}"
  -- `sink` maps to `handshake.sink`
  | .async (AsyncOp.sink 1) [input] [] => do
    .writeLn s!"handshake.sink {← EmitVar.emit input} : {← EmitType.emit input}"
  -- `inact` maps to `handshake.never`
  | .async (AsyncOp.inact 1) [] [output] => do
    .writeLn s!"{← EmitVar.emit output} = handshake.never : {← EmitType.emit output}"
  | ap =>
    throw s!"unsupported atomic process: {repr ap}"

end Wavelet.Backend.Handshake
