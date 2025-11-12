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

inductive OutputFormat where
  | json
  | dot
  | none
  deriving Repr

def trace (msg : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn s!"[trace] {msg}"

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  -- CLI option parsing
  let inputPath := p.positionalArg! "input" |>.as! String
  let outputPath? := p.flag? "output" |>.map (·.as! String)
  let testsPath? := p.flag? "tests" |>.map (·.as! String)
  let format ← match p.flag! "format" |>.as! String with
    | "json" => pure OutputFormat.json
    | "dot"  => pure OutputFormat.dot
    | "none" => pure OutputFormat.none
    | fmt    => throw <| IO.userError s!"unknown output format: {fmt}"
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

  let RawT := RawProg
    (WithCall (WithSpec (RipTide.SyncOp Loc) RipTide.opSpec) FnName) Var
  let rawProg : RawT ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProg"
  let prog ← (rawProg.toProg (V := RipTide.Value)).unwrapIO "failed to convert RawProg to Prog"

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
    let P χ := Proc
      (RipTide.SyncOp Loc) χ RipTide.Value
      (prog.sigs last).ι
      (if ¬ enablePermOut then
        if enableNoOut then 0 else
        (prog.sigs last).ω - 1
      else (prog.sigs last).ω)
    let proc : P Nat :=
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
      else cast (by simp [P, h₁]) proc

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

    -- If a test file is specified, read and run the tests
    if let some testsPath := testsPath? then
      trace s!"running tests from {testsPath}..."
      let testsInput ← IO.FS.readFile testsPath
      let testsJson ← (Lean.Json.parse testsInput).unwrapIO s!"failed to parse JSON from {testsPath}"
      let testVecs : List (RipTide.TestVector Loc) ←
        (Lean.FromJson.fromJson? testsJson).unwrapIO s!"failed to parse test vectors from {testsPath}"
      trace s!"loaded {testVecs.length} test vector(s)"
      for (i, testVec) in testVecs.mapIdx (·, ·) do
        trace s!"  running test vector {i}..."
        match testVec.run proc with
        | .ok (tr, outputs, st) =>
          trace s!"    steps: {tr.length}, outputs: {outputs}, final state:\n{Lean.ToJson.toJson st}"
        | .error err =>
          trace s!"    failed: {err}"

    match format with
    | .dot =>
      -- Dump graph as DOT
      let plot ← (proc.plot (omitForks := omitForks)).run.unwrapIO "failed to generate DOT plot"
      writeOutput plot
    | .json =>
      -- Dump graph as JSON
      let rawProc := RawProc.fromProc proc
      let output := Lean.ToJson.toJson rawProc
      writeOutput (Lean.Json.pretty output)
    | .none =>
      trace "no output format selected"
    return 0
  else
    trace "no function provided"
    return 0

def compileCmd := `[Cli|
    compileCmd VIA runCompileCmd; ["0.0.1"]
    "Wavelet compiler (Lean backend)"

    FLAGS:
      o, output    : String ; "Path to output final dataflow graph in JSON (Default: stdout)"
      f, format    : String ; "Output format [json|dot|none]"
      "perm-out"            ; "Enable permission output which might increase graph size"
      "no-out"              ; "Disable all outputs for a smaller graph"
      stats                 ; "Print various statistics"
      "omit-forks"          ; "Omit fork operators in the DOT graph"
      "tests"      : String ; "A JSON file including test vectors for the final dataflow graph"

    ARGS:
      input        : String ; "Input sequential program in JSON"

    EXTENSIONS:
      defaultValues! #[("format", "json")]
  ]

def main (args : List String) : IO UInt32 :=
  compileCmd.validate args
