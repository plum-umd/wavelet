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
  deriving Repr

def trace (msg : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn s!"[trace] {msg}"

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  -- CLI option parsing
  let inputPath := p.positionalArg! "input" |>.as! String
  let outputPath? := p.flag? "output" |>.map (·.as! String)
  let format ← match p.flag! "format" |>.as! String with
    | "json" => pure OutputFormat.json
    | "dot"  => pure OutputFormat.dot
    | fmt    => throw <| IO.userError s!"unknown output format: {fmt}"
  let writeOutput (content : String) : IO Unit :=
    match outputPath? with
    | some path => IO.FS.writeFile path content
    | none      => IO.getStdout >>= (·.putStrLn content)

  let input ← IO.FS.readFile inputPath
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"

  let RawT := RawProg
    (WithCall (WithSpec (RipTide.SyncOp String) RipTide.opSpec) String)
    String
  let rawProg : RawT ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProg"
  let prog ← (rawProg.toProg (V := RipTide.Value)).unwrapIO "failed to convert RawProg to Prog"

  if h : prog.numFns > 0 then
    -- Some abbreviations
    let : NeZeroSigs prog.sigs := prog.neZero
    let last : Fin prog.numFns := ⟨prog.numFns - 1, by omega⟩
    let P χ := Proc
      (RipTide.SyncOp String) χ RipTide.Value
      (prog.sigs last).ι (prog.sigs last).ω

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
    let proc : P Nat := proc.renameChans
    trace s!"erased ghost tokens. graph size: {proc.atoms.length} ops"
    proc.checkAffineChan.unwrapIO "dfg invariant error"

    -- Some optimizations
    let applyRewrites (descr : String) (rw : Rewrite _ _ _) (proc : P Nat) : IO (P Nat) := do
      -- let proc : P (RewriteName Nat) := proc.mapChans RewriteName.base
      let (numRws, proc) := Rewrite.applyUntilFailNat rw proc
      proc.checkAffineChan.unwrapIO "dfg invariant error"
      trace s!"{descr}: {numRws} rewrites. graph size: {proc.atoms.length} ops"
      return proc

    -- let proc ← applyRewrites "lowering n-ary ops" naryLowering proc
    -- let proc ← applyRewrites "operator selection" RipTide.operatorSel proc
    -- let proc ← applyRewrites "dead code elimination" deadCodeElim proc

    let proc ← applyRewrites "operator selection and optimization"
      (naryLowering <|> deadCodeElim <|> RipTide.operatorSel) proc

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

    match format with
    | .dot =>
      -- Dump graph as DOT
      let plot ← proc.plot.run.unwrapIO "failed to generate DOT plot"
      writeOutput plot
    | .json =>
      -- Dump graph as JSON
      let rawProc := RawProc.fromProc proc
      let output := Lean.ToJson.toJson rawProc
      writeOutput (Lean.Json.pretty output)
    return 0
  else
    trace "no function provided"
    return 0

def compileCmd := `[Cli|
    compileCmd VIA runCompileCmd; ["0.0.1"]
    "Wavelet compiler (Lean backend)"

    FLAGS:
      o, output : String; "Path to output final dataflow graph in JSON (Default: stdout)"
      f, format : String; "Output format [json|dot]"

    ARGS:
      input : String; "Input sequential program in JSON"

    EXTENSIONS:
      defaultValues! #[("format", "json")]
  ]

def main (args : List String) : IO UInt32 :=
  compileCmd.validate args
