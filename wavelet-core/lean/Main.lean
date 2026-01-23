import Cli
import Wavelet

open Wavelet.Frontend Wavelet.Compile Wavelet.Determinacy Wavelet.Seq Wavelet.Dataflow

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

  let rawProg : RipTide.RawProg ← Lean.Json.decodeFile inputPath
  let prog : RipTide.EncapProg ← rawProg.toProg.unwrapIO "failed to convert RawProg to Prog"

  prog.validate |>.unwrapIO "input program validation failed"
  let proc ← prog.lowerControlFlow |>.unwrapIO "control-flow lowering failed"
  proc.validate |>.unwrapIO "invalid proc after control-flow lowering"

  if enableUnopt then
    dbg_trace s!"writing unoptimized dfg to {unoptPath}..."
    Lean.Json.encodeToFilePretty unoptPath (RawProc.fromProc proc.proc)

  -- Trim some unused outputs as needed
  let proc := if ¬ enablePermOut then
      if enableSinkAllOut then
        -- If we enable the more aggressive no-output mode,
        -- sink all outputs of the dataflow graph
        proc.sinkLastNOutputs proc.numOuts
      else
        -- If we don't need output permission from the entire graph,
        -- the last output (which assumed to be a ghost permission output)
        -- can be replaced with a sink to enable more optimizations.
        proc.sinkLastNOutputs 1
    else proc

  -- Legalizations and optimizations
  let (numRws, stats, proc) := proc.rewriteProc
    (naryLowering <|> deadCodeElim <|> RipTide.operatorSel)
  proc.validate |>.unwrapIO "invalid proc after rewrites"
  dbg_trace s!"{numRws} rewrites. graph size: {proc.proc.atoms.length} ops"

  -- Print stats if enabled
  if enableStats then
    dbg_trace "rewrite rule stats:"
    for (rwName, count) in stats.toList do
      dbg_trace s!"  {rwName}: {count}"
    let numNonTrivial :=
      proc.proc.atoms
      |>.filter (λ
        | .async (AsyncOp.fork ..) ..
        | .async (AsyncOp.forward ..) ..
        | .async (AsyncOp.forwardc ..) ..
        | .async (AsyncOp.inact ..) ..
        | .async (AsyncOp.const ..) ..
        | .async (AsyncOp.sink ..) .. => false
        | _ => true)
      |>.length
    dbg_trace s!"non-trivial operators: {numNonTrivial}"

  if enableDot then
    dbg_trace s!"writing DOT graph to {dotPath}..."
    let plot ← proc.proc.plot.run.unwrapIO "failed to generate DOT plot"
    IO.FS.writeFile dotPath plot

  -- Dump graph as JSON
  dbg_trace s!"writing final dfg to {finalOutputPath}..."
  Lean.Json.encodeToFilePretty finalOutputPath (RawProc.fromProc proc.proc)
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
  let rawProc : RipTide.RawProc ← Lean.Json.decodeFile inputPath
  let proc ← rawProc.toProc.unwrapIO "failed to convert RawProc to Proc"
  let plot ← (proc.plot (omitForks := omitForks)).run.unwrapIO "failed to generate DOT plot"
  dbg_trace s!"writing DOT graph to {outputPrefix}.dot..."
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
  let rawProc : RipTide.RawProc ← Lean.Json.decodeFile inputPath
  let proc ← rawProc.toProc.unwrapIO "failed to convert RawProc to Proc"

  let tbs : List (RipTide.Testbench _) ← Lean.Json.decodeFile testbenchPath
  dbg_trace s!"running {tbs.length} tests from {testbenchPath}..."

  let mut numFailed := 0
  for (i, tb) in tbs.mapIdx (·, ·) do
    dbg_trace s!"  running test vector {i}..."
    match tb.run proc with
    | .ok (tr, outputs, st) =>
      dbg_trace s!"    steps: {tr.length}, outputs: {outputs}, final state:\n{Lean.Json.encodePretty st}"
    | .error err =>
      dbg_trace s!"    failed: {err}"
      numFailed := numFailed + 1

  dbg_trace s!"summary: {tbs.length - numFailed} passed, {numFailed} failed."
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
