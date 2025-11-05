import Wavelet

open Wavelet.Frontend Wavelet.Compile Wavelet.Determinacy Wavelet.Seq Wavelet.Dataflow

def Except.unwrapIO {ε α} (e : Except ε α) (msg : String) [ToString ε] : IO α :=
  match e with
  | .ok x => pure x
  | .error err => throw <| IO.userError s!"{msg}: {toString err}"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stderr ← IO.getStderr
  let stdout ← IO.getStdout
  let input ← stdin.readToEnd
  let json ← (Lean.Json.parse input).unwrapIO "failed to parse JSON input"
  let T := RawProg
    (WithCall (WithSpec (RipTide.SyncOp String) RipTide.opSpec) String)
    String
  let rawProg : T ← (Lean.FromJson.fromJson? json).unwrapIO "failed to decode JSON input as RawProg"
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
      if ¬ (prog.prog i).AffineVar then
        let name := rawProg.fns[i]?.map (·.name) |>.getD s!"unknown"
        throw <| IO.userError s!"function {i} ({name}) does not satisfy affine variable usage"

    -- Compile and link
    let proc := compileProg prog.prog last
    let proc := proc.renameChans
    stderr.putStrLn s!"compiled {prog.numFns} function(s). graph size: {proc.atoms.length} ops"
    proc.checkAffineChan.unwrapIO "dfg invariant error"

    -- Erase ghost tokens
    let proc := proc.eraseGhost
    stderr.putStrLn s!"erased ghost tokens. graph size: {proc.atoms.length} ops"
    proc.checkAffineChan.unwrapIO "dfg invariant error"

    -- Some optimizations
    let applyRewrites {k} (descr : String) (rw : Rewrite _ _ _ k) (proc : P Nat) : IO (P Nat) := do
      stderr.putStr s!"{descr} ..."
      let proc : P (RewriteName Nat) := proc.mapChans RewriteName.base
      let (numRws, atoms) := Rewrite.applyUntilFail rw proc.atoms
      let proc : P Nat := { proc with atoms }.renameChans
      proc.checkAffineChan.unwrapIO "dfg invariant error"
      stderr.putStrLn s!" {numRws} rewrites. graph size: {proc.atoms.length} ops"
      return proc

    let proc : P Nat := proc.renameChans
    let proc ← applyRewrites "lowering n-ary ops" naryLowering proc
    let proc ← applyRewrites "dead code elimination" deadCodeElim proc

    -- Dump graph as DOT
    let plot ← proc.plot.run.unwrapIO "failed to generate DOT plot"
    stderr.putStrLn plot

    -- Dump graph as JSON
    let rawProc := RawProc.fromProc proc
    let output := Lean.ToJson.toJson rawProc
    stdout.putStrLn (Lean.Json.pretty output)
  else
    stderr.putStrLn "no function provided"
