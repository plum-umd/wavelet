import Mathlib.Logic.Relation

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.AffineVar

/-! Simulation relation for `compileFn`. -/

namespace Wavelet.Compile.Fn

open Semantics Seq Dataflow Compile

/-! Ghost state used for simulation that keeps track of
the defined variables and path conditions on the `Seq` side. -/
structure GhostState χ where
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

@[simp, grind]
def GhostState.empty : GhostState χ := ⟨[], []⟩

@[simp, grind]
def GhostState.init (params : List χ) : GhostState χ := ⟨params, []⟩

@[simp, grind]
def GhostState.useThenDefine [DecidableEq χ]
  (gs : GhostState χ)
  (usedVars : List χ)
  (newVars : List χ) : GhostState χ :=
  ⟨gs.definedVars.removeAll usedVars ++ newVars, gs.pathConds⟩

@[simp, grind]
def GhostState.useThenBranch [DecidableEq χ]
  (gs : GhostState χ)
  (condVar : χ)
  (condVal : Bool) : GhostState χ :=
  ⟨
    gs.definedVars.removeAll [condVar],
    (condVal, .var condVar gs.pathConds) :: gs.pathConds,
  ⟩

def varsToChans
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (gs : GhostState χ)
  (ec : Seq.Config Op χ V m n) : ChanMap (ChanName χ) V :=
  λ name =>
    match name with
    | .var v pathConds =>
      if pathConds = gs.pathConds then
        if let some val := ec.vars.getVar v then
          [val]
        else []
      else []
    | .merge_cond v =>
      if (true, v) ∈ gs.pathConds then
        [InterpConsts.fromBool true]
      else if (false, v) ∈ gs.pathConds then
        [InterpConsts.fromBool false]
      else []
    | .final_dest _ => []
    | _ => []

@[grind]
def HasMerges
  [Arity Op]
  (m n : Nat)
  (atoms : AtomicProcs Op (ChanName χ) V) :
  List (Bool × ChanName χ) → Prop
  | [] => True
  | (_, chan) :: rest =>
    (compileExpr.branchMerge m n chan rest ∈ atoms) ∧
    HasMerges m n atoms rest

@[grind]
def OrderedPathConds (pathConds : List (Bool × ChanName χ)) : Prop :=
  (∀ b var pathConds', (b, ChanName.var var pathConds') ∈ pathConds →
    pathConds'.length < pathConds.length)

/-- Invariants that the processes should correspond
to the compiled expressions/fns. -/
@[grind]
def HasCompiledProcs
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (ec : Seq.Config Op χ V m n)
  (pc : Dataflow.Config Op (ChanName χ) V m n)
  (gs : GhostState χ) : Prop :=
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (mergeState : AsyncOp.MergeState)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    pc.proc.atoms = compileFn.initCarry ec.fn mergeState :: rest ∧
    (compileFn ec.fn).atoms = compileFn.initCarry ec.fn .popLeft :: rest ∧
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    (ec.cont = .init →
      mergeState = .popLeft ∧
      ctxCurrent = [] ∧
      ctxRight = [] ∧
      gs.definedVars = [] ∧
      gs.pathConds = []) ∧
    (∀ expr, ec.cont = .expr expr →
      mergeState = .decider ∧
      expr.AffineVar gs.definedVars ∧
      compileExpr gs.definedVars gs.pathConds expr = ctxCurrent)

@[grind]
def SimRel
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (gs : GhostState χ)
  (ec : Seq.Config Op χ V m n)
  (pc : Dataflow.Config Op (ChanName χ) V m n) : Prop :=
  -- Some invariants about the correspondence between variables and channels
  pc.chans = varsToChans gs ec ∧
  gs.definedVars.Nodup ∧
  (∀ var, var ∈ gs.definedVars ↔ ∃ val, ec.vars.getVar var = some val) ∧
  OrderedPathConds gs.pathConds ∧
  -- No path condition are pushed twice
  (gs.pathConds.map Prod.snd).Nodup ∧
  -- Some invariants about the "shape" of the processes
  HasMerges m n pc.proc.atoms gs.pathConds ∧
  ec.fn.AffineVar ∧
  pc.proc.inputs = ec.fn.params.map .input ∧
  pc.proc.outputs = (Vector.range n).map .final_dest ∧
  HasCompiledProcs ec pc gs

/-! Utility functions to extract facts from the simulation relation. -/
section Utilities

variable {Op χ V S : Type*}
variable [Arity Op] [DecidableEq χ] [InterpConsts V]
variable {ec : Seq.Config Op χ V m n}
variable {pc : Dataflow.Config Op (ChanName χ) V m n}
variable {gs : GhostState χ}
variable {hnz : m > 0 ∧ n > 0}
variable (hsim : SimRel gs ec pc)

def SimRel.vars_to_chans : pc.chans = varsToChans gs ec := hsim.1

def SimRel.wf_fn : ec.fn.AffineVar := by
  have ⟨_, _, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.defined_vars_nodup : gs.definedVars.Nodup := hsim.2.1

def SimRel.defined_vars_to_get_var :
  var ∈ gs.definedVars → ∃ val, ec.vars.getVar var = some val := by
  have ⟨_, _, h, _⟩ := hsim
  apply (h var).mp

def SimRel.get_var_to_defined_vars :
  (∃ val, ec.vars.getVar var = some val) → var ∈ gs.definedVars := by
  have ⟨_, _, h, _⟩ := hsim
  apply (h var).mpr

def SimRel.defined_vars_iff_get_var
  : var ∈ gs.definedVars ↔ ∃ val, ec.vars.getVar var = some val := by
  have ⟨_, _, h, _⟩ := hsim
  exact h var

def SimRel.path_conds_nodup : (gs.pathConds.map Prod.snd).Nodup := by
  have ⟨_, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.path_conds_acyclic : (b, .var v gs.pathConds) ∉ gs.pathConds := by
  intros h'
  have ⟨_, _, _, h, _⟩ := hsim
  have := h _ _ _ h'
  simp at this

def SimRel.has_merges : HasMerges m n pc.proc.atoms gs.pathConds := by
  have ⟨_, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.inputs : pc.proc.inputs = ec.fn.params.map .input := by
  have ⟨_, _, _, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.outputs : pc.proc.outputs = (Vector.range n).map .final_dest := by
  have ⟨_, _, _, _, _, _, _, _, h, _⟩ := hsim
  exact h

def SimRel.has_compiled_procs : HasCompiledProcs ec pc gs := by
  have ⟨_, _, _, _, _, _, _, _, _, h⟩ := hsim
  exact h

def SimRel.final_config_empty_defined_vars
  (h : ec.cont = .init) : gs.definedVars = [] := by
  have ⟨_, _, _, _, _, _, _, _, hret, _⟩ := hsim.has_compiled_procs
  have ⟨_, _, _, h, _⟩ := hret h
  exact h

def SimRel.final_config_empty_path_conds
  (h : ec.cont = .init) : gs.pathConds = [] := by
  have ⟨_, _, _, _, _, _, _, _, hret, _⟩ := hsim.has_compiled_procs
  have ⟨_, _, _, _, h⟩ := hret h
  exact h

end Utilities

end Wavelet.Compile.Fn
