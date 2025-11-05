import Wavelet

open Wavelet.Frontend Wavelet.Compile Wavelet.Determinacy Wavelet.Seq Wavelet.Dataflow

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stderr ← IO.getStderr
  let stdout ← IO.getStdout
  let input ← stdin.readToEnd
  let json ← match Lean.Json.parse input with
    | .ok x => pure x
    | .error err => throw <| IO.userError s!"failed to parse JSON input: {err}"
  let T := RawProg
    (WithCall (WithSpec (RipTide.SyncOp String) RipTide.opSpec) String)
    String

  let rawProg ← match Lean.FromJson.fromJson? json with
    | .ok (x : T) => pure x
    | .error err => throw <| IO.userError s!"failed to decode JSON input as RawProg: {err}"
  let prog ← match rawProg.toProg (V := RipTide.Value) with
    | .ok p => pure p
    | .error err => throw <| IO.userError s!"failed to convert RawProg to Prog: {err}"
  if h : prog.numFns > 0 then
    -- Some abbreviations
    let : NeZeroSigs prog.sigs := prog.neZero
    let last : Fin prog.numFns := ⟨prog.numFns - 1, by omega⟩
    let P χ := Proc
      (WithSpec (RipTide.SyncOp String) RipTide.opSpec) χ RipTide.Value
      (prog.sigs last).ι (prog.sigs last).ω

    -- Compile and link
    let proc := compileProg prog.prog last
    let proc := proc.renameChans

    -- Some graph rewrites
    stderr.putStrLn s!"compiled {prog.numFns} function(s). graph size: {proc.atoms.length} ops"

    -- Rename channels to `Nat`
    let proc : P Nat := proc.renameChans

    stderr.putStr s!"lowering n-ary ops ..."
    let proc : P (RewriteName Nat) := proc.mapChans RewriteName.base
    let (numRws, atoms) := Rewrite.applyUntilFail naryLowering proc.atoms
    let proc : P Nat := { proc with atoms }.renameChans
    stderr.putStrLn s!" {numRws} rewrites. graph size: {proc.atoms.length} ops"

    stderr.putStr s!"folding forwards ..."
    let proc : P (RewriteName Nat) := proc.mapChans RewriteName.base
    let (numRws, atoms) := Rewrite.applyUntilFail forwardElim proc.atoms
    let proc : P Nat := { proc with atoms }.renameChans
    stderr.putStrLn s!" {numRws} rewrites. graph size: {proc.atoms.length} ops"

    -- Dump graph as JSON
    let rawProc := RawProc.fromProc proc
    let output := Lean.ToJson.toJson rawProc
    stdout.putStrLn (Lean.Json.pretty output)
  else
    stderr.putStrLn "no function provided, exiting"
