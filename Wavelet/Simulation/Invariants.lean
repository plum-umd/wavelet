import Mathlib.Logic.Relation

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Simulation invariants for the compilation from `Seq` to `Dataflow`. -/

namespace Wavelet.Simulation.Invariants

open Op Seq Dataflow Compile

def varsToChans
  [Arity Op] [instInterp : Interp Op V S]
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

@[grind]
def HasMerges
  [Arity Op]
  (m n : Nat)
  (atoms : AtomicProcs Op (ChanName χ) V) :
  List (Bool × ChanName χ) → Prop
  | [] => True
  | (_, chan) :: rest =>
    (compileExpr.brMerge _ _ _ m n chan rest ∈ atoms) ∧
    HasMerges m n atoms rest

@[grind]
def OrderedPathConds (pathConds : List (Bool × ChanName χ)) : Prop :=
  (∀ b var pathConds', (b, ChanName.var var pathConds') ∈ pathConds →
    pathConds'.length < pathConds.length)

/-- Invariants that the processes should correspond
to the compiled expressions/fns. -/
@[grind]
def HasCompiledProcs
  [Arity Op] [Interp Op V S] [DecidableEq χ]
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    pc.proc.atoms = compileFn.initCarry _ _ _ ec.fn carryInLoop :: rest ∧
    (compileFn Op χ V S hnz ec.fn).atoms = compileFn.initCarry _ _ _ ec.fn false :: rest ∧
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    (∀ vals, ec.expr = .ret vals → ¬ carryInLoop ∧
      ctxCurrent = [] ∧
      ctxRight = [] ∧
      ec.definedVars = [] ∧
      ec.pathConds = []) ∧
    (∀ expr, ec.expr = .cont expr → carryInLoop ∧
      expr.WellFormed _ _ ec.definedVars ∧
      compileExpr Op χ V S hnz ec.definedVars ec.pathConds expr = ctxCurrent)

@[grind]
def SimRel
  [Arity Op] [Interp Op V S] [DecidableEq χ]
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.state = pc.state ∧
  -- Some invariants about the correspondence between variables and channels
  pc.chans = varsToChans ec ∧
  ec.definedVars.Nodup ∧
  (∀ var, var ∈ ec.definedVars ↔ ∃ val, ec.vars.getVar _ _ var = some val) ∧
  OrderedPathConds ec.pathConds ∧
  -- No path condition are pushed twice
  (ec.pathConds.map Prod.snd).Nodup ∧
  -- Some invariants about the "shape" of the processes
  HasMerges m n pc.proc.atoms ec.pathConds ∧
  ec.fn.WellFormed ∧
  HasCompiledProcs hnz ec pc

/-! Utility functions to extract facts from the simulation relation. -/
section Utilities

variable {Op χ V S}
variable [Arity Op] [Interp Op V S] [DecidableEq χ]
variable {ec : Seq.Config Op χ V S m n}
variable {pc : Dataflow.Config Op (ChanName χ) V S m n}
variable {hnz : m > 0 ∧ n > 0}
variable (hsim : SimRel hnz ec pc)

def SimRel.eq_state : ec.state = pc.state := hsim.1

def SimRel.vars_to_chans : pc.chans = varsToChans ec := hsim.2.1

def SimRel.wf_fn : ec.fn.WellFormed := by
  have ⟨_, _, _, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.defined_vars_nodup : ec.definedVars.Nodup := hsim.2.2.1

def SimRel.defined_vars_to_get_var :
  var ∈ ec.definedVars → ∃ val, ec.vars.getVar _ _ var = some val := by
  have ⟨_, _, _, h, _⟩ := hsim
  apply (h var).mp

def SimRel.get_var_to_defined_vars :
  (∃ val, ec.vars.getVar _ _ var = some val) → var ∈ ec.definedVars := by
  have ⟨_, _, _, h, _⟩ := hsim
  apply (h var).mpr

def SimRel.defined_vars_iff_get_var
  : var ∈ ec.definedVars ↔ ∃ val, ec.vars.getVar _ _ var = some val := by
  have ⟨_, _, _, h, _⟩ := hsim
  exact h var

def SimRel.path_conds_nodup : (ec.pathConds.map Prod.snd).Nodup := by
  have ⟨_, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.path_conds_acyclic : (b, .var v ec.pathConds) ∉ ec.pathConds := by
  intros h'
  have ⟨_, _, _, _, h, _⟩ := hsim
  have := h _ _ _ h'
  simp at this

def SimRel.has_merges : HasMerges m n pc.proc.atoms ec.pathConds := by
  have ⟨_, _, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.has_compiled_procs : HasCompiledProcs hnz ec pc := by
  have ⟨_, _, _, _, _, _, _, _, h⟩ := hsim
  exact h

def SimRel.final_config_empty_defined_vars
  (h : ec.expr = .ret vals) : ec.definedVars = [] := by
  have ⟨_, _, _, _, _, _, _, _, hret, _⟩ := hsim.has_compiled_procs
  have ⟨_, _, _, h, _⟩ := hret _ h
  exact h

def SimRel.final_config_empty_path_conds
  (h : ec.expr = .ret vals) : ec.pathConds = [] := by
  have ⟨_, _, _, _, _, _, _, _, hret, _⟩ := hsim.has_compiled_procs
  have ⟨_, _, _, _, h⟩ := hret _ h
  exact h

end Utilities

end Wavelet.Simulation.Invariants
