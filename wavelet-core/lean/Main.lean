import Cli
import Wavelet

open Wavelet.Frontend Wavelet.Compile Wavelet.Determinacy
  Wavelet.Seq Wavelet.Dataflow Wavelet.FFI

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let inputPath := p.positionalArg! "input" |>.as! String
  let outputPath? := p.flag? "output" |>.map (·.as! String)
  let enablePermOut := p.hasFlag "perm-out"
  let enableSinkAllOut := p.hasFlag "sink-all-out"
  let enableDot := p.hasFlag "dot"
  let enableUnopt := p.hasFlag "unopt"
  let enableStats := p.hasFlag "stats"

  let outputPrefix ← inputPath.dropSuffix? ".json" |>.unwrapIO "input must be a .json file"
  let unoptPath := s!"{outputPrefix}.unopt.dfg.json"
  let dotPath := s!"{outputPrefix}.dot"
  let finalOutputPath := outputPath?.getD s!"{outputPrefix}.dfg.json"

  let input ← IO.FS.readFile inputPath
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"

  let rawProg : RipTide.RawProg ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProg"
  let compiled ← RipTide.compile {
    prog := rawProg,
    enablePermOut := enablePermOut,
    enableSinkAllOut := enableSinkAllOut,
    enableStats := enableStats,
  }

  if enableUnopt then
    trace s!"writing unoptimized dfg to {unoptPath}..."
    let output := Lean.ToJson.toJson compiled.unopt
    IO.FS.writeFile unoptPath (Lean.Json.pretty output)

  if enableDot then
    trace s!"writing DOT graph to {dotPath}..."
    let proc : RipTide.Proc _ _ ← compiled.final.toProc.unwrapIO "failed to convert RawProc to Proc"
    let plot ← proc.plot.run.unwrapIO "failed to generate DOT plot"
    IO.FS.writeFile dotPath plot

  -- Dump graph as JSON
  trace s!"writing final dfg to {finalOutputPath}..."
  let output := Lean.ToJson.toJson compiled.final
  IO.FS.writeFile finalOutputPath (Lean.Json.pretty output)
  return 0

def compileCmd := `[Cli|
    compile VIA runCompileCmd;
    "Compiles sequential programs to dataflow graphs."

    FLAGS:
      o, output    : String ; "Path to output final dataflow graph (Default: <input>.dfg.json)"
      "perm-out"            ; "Enable permission output which might increase graph size"
      "sink-all-out"        ; "Sink all dataflow outputs for a smaller graph"
      dot                   ; "Output a DOT graph along with the final dfg"
      unopt                 ; "Output the unoptimized dfg along with the final dfg"
      stats                 ; "Print various statistics"

    ARGS:
      input        : String ; "Input sequential program in JSON"
  ]

def runPlotCmd (p : Cli.Parsed) : IO UInt32 := do
  let inputPath := p.positionalArg! "input" |>.as! String
  let omitForks := p.hasFlag "omit-forks"
  let outputPrefix ← inputPath.dropSuffix? ".json" |>.unwrapIO "input must be a .json file"
  let input ← IO.FS.readFile inputPath
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"
  let rawProc : RipTide.RawProc ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProc"
  let proc : RipTide.Proc _ _ ← rawProc.toProc.unwrapIO "failed to convert RawProc to Proc"
  let plot ← (proc.plot (omitForks := omitForks)).run.unwrapIO "failed to generate DOT plot"
  trace s!"writing DOT graph to {outputPrefix}.dot..."
  IO.FS.writeFile s!"{outputPrefix}.dot" plot
  return 0

def plotCmd := `[Cli|
    plot VIA runPlotCmd;
    "Converts a dataflow graph to DOT format."

    FLAGS:
      "omit-forks"          ; "Omit fork operators in the DOT graph"

    ARGS:
      input        : String ; "Input dataflow graph in JSON"
  ]

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

def testCmd := `[Cli|
    test VIA runTestCmd;
    "Run testbenches on a dataflow graph."

    FLAGS:

    ARGS:
      input        : String ; "Input dataflow graph in JSON"
      testbench    : String ; "Input testbench in JSON"
  ]

def runMainCmd (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 1

def mainCmd := `[Cli|
    wavelet VIA runMainCmd; ["0.0.1"]
    "A verified dataflow compiler."
    SUBCOMMANDS: compileCmd; plotCmd; testCmd
  ]

def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
