import Cli
import Wavelet

open Cli
open Wavelet.Frontend Wavelet.Compile Wavelet.Determinacy Wavelet.Seq Wavelet.Dataflow

def Except.unwrapIO {ε α} (e : Except ε α) (msg : String) [ToString ε] : IO α :=
  match e with
  | .ok x => pure x
  | .error err => throw <| IO.userError s!"{msg}: {toString err}"

def Option.unwrapIO {α} (o : Option α) (msg : String) : IO α :=
  match o with
  | some x => pure x
  | none => throw <| IO.userError msg

def trace (msg : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn s!"[trace] {msg}"

/-! Some specialized types for RipTide. -/
namespace Wavelet.Frontend.RipTide

abbrev Loc := String
abbrev FnName := String
abbrev Var := String

abbrev RawProg := Frontend.RawProg (WithCall (WithSpec (SyncOp Loc) opSpec) FnName) Var
abbrev RawProc := Frontend.RawProc (SyncOp Loc) Nat Value

abbrev EncapProg := Frontend.EncapProg (WithSpec (SyncOp Loc) opSpec) Var Value
abbrev Proc := Dataflow.Proc (SyncOp Loc) Nat Value

end Wavelet.Frontend.RipTide

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  -- CLI option parsing
  let inputPath := p.positionalArg! "input" |>.as! String
  let outputPath? := p.flag? "output" |>.map (·.as! String)
  let enablePermOut := p.hasFlag "perm-out"
  let enableNoOut := p.hasFlag "no-out"
  let enableStats := p.hasFlag "stats"
  let omitForks := p.hasFlag "omit-forks"
  let writeOutput (content : String) : IO Unit :=
    match outputPath? with
    | some path => IO.FS.writeFile path content
    | none      => IO.getStdout >>= (·.putStrLn content)

  let input ← IO.FS.readFile inputPath
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"

  let Loc := String
  let FnName := String
  let Var := String

  let rawProg : RipTide.RawProg ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProg"
  let prog : RipTide.EncapProg ← rawProg.toProg.unwrapIO "failed to convert RawProg to Prog"

  if h : prog.numFns > 0 then
    -- Some abbreviations
    let : NeZeroSigs prog.sigs := prog.neZero
    let last : Fin prog.numFns := ⟨prog.numFns - 1, by omega⟩

    -- Check some static properties
    for i in List.finRange prog.numFns do
      let name := rawProg.fns[i]?.map (·.name) |>.getD s!"unknown"
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

    -- Some optimizations
    let Proc := RipTide.Proc (prog.sigs last).ι
      (if ¬ enablePermOut then
        if enableNoOut then 0 else
        (prog.sigs last).ω - 1
      else (prog.sigs last).ω)
    let proc : Proc :=
      if h₁ : ¬ enablePermOut then
        if h₂ : enableNoOut then
          -- If we enable the more aggressive no-output mode,
          -- sink all outputs of the dataflow graph
          { proc with
            outputs := #v[].cast (by simp [h₁, h₂]),
            atoms := .sink proc.outputs :: proc.atoms }
        else
          -- If we don't need output permission from the entire graph,
          -- the last output (which assumed to be a ghost permission output)
          -- can be replaced with a sink to enable more optimizations.
          { proc with
            outputs := proc.outputs.pop.cast (by simp [h₁, h₂]),
            atoms := .sink #v[proc.outputs.back] :: proc.atoms }
      else cast (by simp [Proc, h₁]) proc

    trace s!"applying op selection and optimizations..."
    let (numRws, stats, proc) := Rewrite.applyUntilFailNat
      -- (naryLowering <|> RipTide.operatorSel)
      (naryLowering <|> deadCodeElim <|> RipTide.operatorSel)
      proc
    trace s!"{numRws} rewrites. graph size: {proc.atoms.length} ops"

    if enableStats then
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

    -- Dump graph as JSON
    let rawProc := RawProc.fromProc proc
    let output := Lean.ToJson.toJson rawProc
    writeOutput (Lean.Json.pretty output)
    return 0
  else
    trace "no function provided"
    return 0

def runPlotCmd (p : Cli.Parsed) : IO UInt32 := do
  let inputPath := p.positionalArg! "input" |>.as! String
  let omitForks := p.hasFlag "omit-forks"
  let input ← IO.FS.readFile inputPath
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"
  let rawProc : RipTide.RawProc ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProc"
  let proc : RipTide.Proc _ _ ← rawProc.toProc.unwrapIO "failed to convert RawProc to Proc"
  let plot ← (proc.plot (omitForks := omitForks)).run.unwrapIO "failed to generate DOT plot"
  IO.getStdout >>= (·.putStrLn plot)
  return 0

def runTestCmd (p : Cli.Parsed) : IO UInt32 := do
  let inputPath := p.positionalArg! "input" |>.as! String
  let testbenchPath := p.positionalArg! "testbench" |>.as! String
  let input ← IO.FS.readFile inputPath
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"
  let rawProc : RipTide.RawProc ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProc"
  let proc : RipTide.Proc _ _ ← rawProc.toProc.unwrapIO "failed to convert RawProc to Proc"

  trace s!"running tests from {testbenchPath}..."
  let tbsInput ← IO.FS.readFile testbenchPath
  let tbsJson ← (Lean.Json.parse tbsInput).unwrapIO s!"failed to parse JSON from {testbenchPath}"
  let tbs : List (RipTide.Testbench RipTide.Loc) ←
    (Lean.FromJson.fromJson? tbsJson).unwrapIO s!"failed to parse test vectors from {testbenchPath}"
  trace s!"loaded {tbs.length} test vector(s)"

  let mut numFailed := 0
  for (i, tb) in tbs.mapIdx (·, ·) do
    trace s!"  running test vector {i}..."
    match tb.run proc with
    | .ok (tr, outputs, st) =>
      trace s!"    steps: {tr.length}, outputs: {outputs}, final state:\n{Lean.ToJson.toJson st}"
    | .error err =>
      trace s!"    failed: {err}"
      numFailed := numFailed + 1

  trace s!"summary: {tbs.length - numFailed} passed, {numFailed} failed."
  if numFailed = 0 then
    return 1
  else
    return 0

def runMainCmd (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 1

def compileCmd := `[Cli|
    compile VIA runCompileCmd;
    "Compiles sequential programs to dataflow graphs."

    FLAGS:
      o, output    : String ; "Path to output final dataflow graph (Default: stdout)"
      "perm-out"            ; "Enable permission output which might increase graph size"
      "no-out"              ; "Disable all outputs for a smaller graph"
      stats                 ; "Print various statistics"

    ARGS:
      input        : String ; "Input sequential program in JSON"
  ]

def plotCmd := `[Cli|
    plot VIA runPlotCmd;
    "Converts a dataflow graph to DOT format."

    FLAGS:
      "omit-forks"          ; "Omit fork operators in the DOT graph"

    ARGS:
      input        : String ; "Input dataflow graph in JSON"
  ]

def testCmd := `[Cli|
    test VIA runTestCmd;
    "Run testbenches on a dataflow graph."

    FLAGS:

    ARGS:
      input        : String ; "Input dataflow graph in JSON"
      testbench    : String ; "Input testbench in JSON"
  ]

def mainCmd := `[Cli|
    wavelet VIA runMainCmd; ["0.0.1"]
    "A verified dataflow compiler."
    SUBCOMMANDS: compileCmd; plotCmd; testCmd
  ]

def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
