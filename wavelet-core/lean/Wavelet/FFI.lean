import Wavelet.Data.Basic
import Wavelet.Frontend
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Foreign interfaces for using Wavelet as a library. -/

namespace Wavelet.FFI

inductive Result (T : Type u) where
  | ok (val : T)
  | error (msg : String)
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Converts a function with JSON-serializable inputs/outputs to
a `String → String` function to be used as FFI. -/
unsafe def runIO [Lean.FromJson A] [Lean.ToJson B]
  (f : A → IO B) (name : String) : String → String :=
  λ input =>
    let m : IO B := do
      let json ← Lean.Json.parse input
        |>.unwrapIO s!"failed to parse JSON input for {name}"
      let args : A ← Lean.FromJson.fromJson? json
        |>.unwrapIO s!"failed to decode JSON input as the argument for {name}"
      f args
    let output : Result _ := match unsafeIO m with
      | .ok val => .ok val
      | .error err => .error err.toString
    (Lean.ToJson.toJson output).compress

end Wavelet.FFI

/-! Compiler for RipTide. -/
namespace Wavelet.FFI.RipTide

open Wavelet.Frontend Wavelet.Compile Wavelet.Determinacy Wavelet.Seq Wavelet.Dataflow

abbrev Loc := String
abbrev FnName := String
abbrev Var := String

abbrev RawProg := Frontend.RawProg (WithCall (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) FnName) Var
abbrev RawProc := Frontend.RawProc (RipTide.SyncOp Loc) Nat RipTide.Value

abbrev EncapProg := Frontend.EncapProg (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) Var RipTide.Value

abbrev Proc := Dataflow.Proc (RipTide.SyncOp Loc) Nat RipTide.Value
abbrev EncapProc := Frontend.EncapProc (RipTide.SyncOp Loc) Nat RipTide.Value

structure CompileArgs where
  prog : RawProg
  enablePermOut : Bool
  enableSinkAllOut : Bool
  enableStats : Bool
  deriving Repr, Lean.ToJson, Lean.FromJson

structure CompileOutput where
  unopt : RawProc
  final : RawProc
  deriving Repr, Lean.ToJson, Lean.FromJson

def compile (args : CompileArgs) : IO CompileOutput := do
  let prog : RipTide.EncapProg ← args.prog.toProg.unwrapIO "failed to convert RawProg to Prog"

  if h : prog.numFns > 0 then
    let : NeZeroSigs prog.sigs := prog.neZero
    let last : Fin prog.numFns := ⟨prog.numFns - 1, by omega⟩

    -- Check some static properties
    for i in List.finRange prog.numFns do
      let name := args.prog.fns[i]?.map (·.name) |>.getD s!"unknown"
      (prog.prog i).checkAffineVar.resolve
        |>.unwrapIO s!"function {i} ({name})"

    -- Compile and link
    let proc := compileProg prog.prog last
    let proc := proc.renameChans
    trace s!"compiled {prog.numFns} function(s). graph size: {proc.atoms.length} ops"
    proc.checkAffineChan.unwrapIO "dfg invariant error"

    -- Erase ghost tokens
    let proc := proc.eraseGhost
    let proc := proc.renameChans
    trace s!"erased ghost tokens. graph size: {proc.atoms.length} ops"
    proc.checkAffineChan.unwrapIO "dfg invariant error"

    -- Save unoptimized proc for output
    let unoptProc := proc

    -- If enabled, sink the global permission output (the last output) or all outputs
    let proc : RipTide.EncapProc :=
      if ¬ args.enablePermOut then
        if args.enableSinkAllOut then
          -- If we enable the more aggressive no-output mode,
          -- sink all outputs of the dataflow graph
          EncapProc.fromProc { proc with
            outputs := #v[],
            atoms := .sink proc.outputs :: proc.atoms }
        else
          -- If we don't need output permission from the entire graph,
          -- the last output (which assumed to be a ghost permission output)
          -- can be replaced with a sink to enable more optimizations.
          EncapProc.fromProc { proc with
            outputs := proc.outputs.pop,
            atoms := .sink #v[proc.outputs.back] :: proc.atoms }
      else EncapProc.fromProc proc

    -- Apply some graph rewrites
    trace s!"applying op selection and optimizations..."
    let (numRws, stats, proc) := Rewrite.applyUntilFailNat
      (naryLowering <|> deadCodeElim <|> RipTide.operatorSel)
      proc.proc
    trace s!"{numRws} rewrites. graph size: {proc.atoms.length} ops"

    -- Print stats if enabled
    if args.enableStats then
      trace "rewrite rule stats:"
      for (rwName, count) in stats.toList do
        trace s!"  {rwName}: {count}"

      let numNonTrivial :=
        proc.atoms
        |>.filter (λ
          | .async (AsyncOp.fork ..) ..
          | .async (AsyncOp.forward ..) ..
          | .async (AsyncOp.forwardc ..) ..
          | .async (AsyncOp.inact ..) ..
          | .async (AsyncOp.const ..) ..
          | .async (AsyncOp.sink ..) .. => false
          | _ => true)
        |>.length
      trace s!"non-trivial operators: {numNonTrivial}"

    return {
      unopt := RawProc.fromProc unoptProc,
      final := RawProc.fromProc proc,
    }
  else
    throw <| IO.userError "compiling empty program"

@[export wavelet_riptide_compile]
unsafe def compileFFI := runIO compile "Wavelet.FFI.RipTide.compile"

end Wavelet.FFI.RipTide
