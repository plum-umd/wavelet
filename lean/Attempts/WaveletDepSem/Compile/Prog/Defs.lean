import Wavelet.Seq.Prog

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.MapChans

/-! Compiler from `Prog` to dataflow `Proc`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

/-- Channel name prefixes to disambiguate names during linking. -/
inductive LinkName (χ : Type u) where
  | base (name : χ)
  | main (name : LinkName χ)
  | dep (op : Nat) (name : LinkName χ)
  deriving DecidableEq

def linkAtomicProc
  [Arity Op]
  (sigs : Sigs k)
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  (atom : AtomicProc (Op ⊕ (SigOps sigs k')) (LinkName χ) V)
  : AtomicProcs Op (LinkName χ) V :=
  match atom with
  | .op (.inl o) inputs outputs =>
    [.op o (inputs.map .main) (outputs.map .main)]
  | .op (.inr op) inputs outputs =>
    [.forward (inputs.map .main) ((procs op.toFin').inputs.map (LinkName.dep op.toFin))] ++
    (procs op.toFin').atoms.mapChans (LinkName.dep op.toFin) ++
    [.forward ((procs op.toFin').outputs.map (LinkName.dep op.toFin)) (outputs.map .main)]
  | .async aop inputs outputs =>
    [.async aop (inputs.map .main) (outputs.map .main)]

/--
Inline calls to the given `k` processes while preserving a forward simulation.

This procedure is a bit more subtle than one might expect.
In order to preserve simulation (e.g., see `sim_link_procs`),
we have to assume one of the following properties about the dependent processes:
1. Either that no dependent process is called twice, or
2. The depdenent processes are "good-behaving" in the sense that
   if they emit the `.output` label, then they can always continue
   to a state identical to the initial state.

They are required because if the main process makes two separate calls
to the same dependent process, we have to make sure there is a schedule
where one call does not interfere with the other.

Property 1 is harder to prove without determinancy. Because we have
to prove that for **any trace** that produces the `.output` label at
the end, something good happens. But determinancy might be dependent
on, e.g., lack of data races.

Therefore, in the theorems below, we assume property 1.
-/
def linkProcs
  [Arity Op]
  (sigs : Sigs k)
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  (main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n)
  : Proc Op (LinkName χ) V m n := {
    inputs := main.inputs.map LinkName.main,
    outputs := main.outputs.map LinkName.main,
    atoms := (main.atoms.map (linkAtomicProc sigs k' procs)).flatten,
  }

/-- Given a program (a list of functions that non-recursively call each other),
compile the `i`-th function to a process without any dependencies. -/
def compileProg
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (sigs : Sigs k)
  (prog : Prog Op χ V sigs)
  (i : Fin k) : Proc Op (LinkName (ChanName χ)) V (sigs i).ι (sigs i).ω :=
  -- Compile the current function
  let proc : Proc (Op ⊕ SigOps sigs i.castSucc) (LinkName (ChanName χ)) V _ _ :=
    compileFn (prog i) |>.mapChans LinkName.base
  -- Compile dependencies
  let deps : (j : Fin i) →
    Proc Op (LinkName (ChanName χ)) V
      (sigs (j.castLT (by omega))).ι
      (sigs (j.castLT (by omega))).ω :=
    λ j => compileProg sigs prog (j.castLT (by omega))
  -- Link everything into one dataflow graph
  linkProcs sigs i.castSucc deps proc

end Wavelet.Compile
