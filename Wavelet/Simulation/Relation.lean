import Mathlib.Logic.Relation

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

namespace Wavelet.Simulation.Relation

open Op Seq Dataflow Compile

/-- Defines refinement of two transition systems in general. -/
def Refines
  {T : Type v} {S : Type w}
  (c₁ : T) (c₂ : S)
  (R : T → S → Prop)
  (Step₁ : T → T → Prop)
  (Step₂ : S → S → Prop) :=
  R c₁ c₂ ∧
  (∀ c₁ c₂ c₁',
    R c₁ c₂ →
    Step₁ c₁ c₁' →
    ∃ c₂', Step₂ c₂ c₂' ∧ R c₁' c₂')

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

/-- Specific case for a Seq config to refine a dataflow config. -/
def SeqRefinesDataflow
  [DecidableEq χ₁] [DecidableEq χ₂]
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  Refines c₁ c₂ R (Config.Step Op χ₁ V S) (Config.StepPlus Op χ₂ V S)

def SimR.varsToChans
  (ec : Seq.Config Op χ V S m n) : ChanMap (ChanName χ) V :=
  λ name =>
    match name with
    | .var v pathConds =>
      if pathConds = ec.pathConds then
        if let some val := ec.vars.getVar _ _ v then
          [val]
        else []
      else []
    | .merge_cond v =>
      if (true, v) ∈ ec.pathConds then
        [instInterp.fromBool true]
      else if (false, v) ∈ ec.pathConds then
        [instInterp.fromBool false]
      else []
    | .final_dest i =>
      -- Corresponding final return values
      if let .ret vals := ec.expr then
        if _ : i < n then [vals[i]]
        else []
      else []
    | _ => []

def SimR.HasMerges
  (m n : Nat)
  (atoms : AtomicProcs Op (ChanName χ) V) :
  List (Bool × ChanName χ) → Prop
  | [] => True
  | (_, chan) :: rest =>
    (compileExpr.brMerge _ _ _ m n chan rest ∈ atoms) ∧
    SimR.HasMerges m n atoms rest

def SimR
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.state = pc.state ∧
  -- Some invariants about the correspondence between variables and channels
  pc.chans = SimR.varsToChans _ _ _ _ ec ∧
  ec.definedVars.Nodup ∧
  (∀ var, var ∈ ec.definedVars ↔ ∃ val, ec.vars.getVar _ _ var = some val) ∧
  (∀ b var pathConds, (b, .var var pathConds) ∈ ec.pathConds →
    pathConds.length < ec.pathConds.length) ∧
  -- No path condition are pushed twice
  (ec.pathConds.map Prod.snd).Nodup ∧
  -- Some invariants about the "shape" of the processes
  SimR.HasMerges _ _ _ m n pc.proc.atoms ec.pathConds ∧
  ec.fn.WellFormed ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    pc.proc.atoms = compileFn.initCarry _ _ _ ec.fn carryInLoop :: rest ∧
    (compileFn Op χ V S hnz ec.fn).atoms = compileFn.initCarry _ _ _ ec.fn false :: rest ∧
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    (∀ vals, ec.expr = .ret vals → ¬ carryInLoop ∧ ctxCurrent = [] ∧ ctxRight = []) ∧
    (∀ expr, ec.expr = .cont expr → carryInLoop ∧
      expr.WellFormed _ _ ec.definedVars ∧
      compileExpr Op χ V S hnz ec.definedVars ec.pathConds expr = ctxCurrent)

end Wavelet.Simulation.Relation
