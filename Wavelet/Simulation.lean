import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

open Wavelet.Op

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

/-! Simulation proofs. -/

/-! Some utilities for the simulation invariants. -/
namespace Wavelet.Seq

/-- Checks if the channel name is a variable and it has
a different suffix than the given path condition. -/
def ChanName.HasDiffPathSuffix (pathConds : List (Bool × ChanName χ)) (name : ChanName χ) : Prop :=
  match name with
  | .var _ _ pathConds' => ∀ ext, ext ++ pathConds ≠ pathConds'
  | _ => True

end Wavelet.Seq

/-! Some utilities for the simulation invariants. -/
namespace Wavelet.Dataflow

open Wavelet.Seq

def AtomicProc.HasInput (ap : AtomicProc Op χ V) (v : χ) : Prop :=
  ∃ inp ∈ ap.inputs, inp.1 = v

def AtomicProc.HasInputWithBuf (ap : AtomicProc Op χ V) (v : χ) (buf : List V) : Prop :=
  ∃ inp ∈ ap.inputs, inp = (v, buf)

def AtomicProc.HasEmptyInputs (ap : AtomicProc Op χ V) : Prop :=
  ∀ inp ∈ ap.inputs, inp.2 = []

def ChanBuf.MatchModBuffer (buf₁ buf₂ : ChanBuf χ V) : Prop := buf₁.1 = buf₂.1

def AtomicProc.MatchModBuffers : AtomicProc Op χ V → AtomicProc Op χ V → Prop
  | .op o₁ inputs₁ outputs₁, .op o₂ inputs₂ outputs₂ =>
    o₁ = o₂ ∧
    List.Forall₂ MatchBuf inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .steer flavor₁ decider₁ inputs₁ outputs₁, .steer flavor₂ decider₂ inputs₂ outputs₂ =>
    flavor₁ = flavor₂ ∧
    decider₁.1 = decider₂.1 ∧
    List.Forall₂ MatchBuf inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .carry inLoop₁ decider₁ inputs₁₁ inputs₁₂ outputs₁,
    .carry inLoop₂ decider₂ inputs₂₁ inputs₂₂ outputs₂ =>
    inLoop₁ = inLoop₂ ∧
    decider₁.1 = decider₂.1 ∧
    List.Forall₂ MatchBuf inputs₁₁.toList inputs₂₁.toList ∧
    List.Forall₂ MatchBuf inputs₁₂.toList inputs₂₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .merge decider₁ inputs₁₁ inputs₁₂ outputs₁,
    .merge decider₂ inputs₂₁ inputs₂₂ outputs₂ =>
    decider₁.1 = decider₂.1 ∧
    List.Forall₂ MatchBuf inputs₁₁.toList inputs₂₁.toList ∧
    List.Forall₂ MatchBuf inputs₁₂.toList inputs₂₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .forward inputs₁ outputs₁, .forward inputs₂ outputs₂ =>
    List.Forall₂ MatchBuf inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | .const c₁ act₁ outputs₁, .const c₂ act₂ outputs₂ =>
    c₁ = c₂ ∧ act₁.1 = act₂.1 ∧
    outputs₁.toList = outputs₂.toList
  | _, _ => False
  where
    @[simp]
    MatchBuf := ChanBuf.MatchModBuffer _ _

def AtomicProcs.MatchModBuffers (aps₁ aps₂ : AtomicProcs Op χ V) : Prop :=
  List.Forall₂ (AtomicProc.MatchModBuffers Op χ V) aps₁ aps₂

def AtomicProcs.IsDAG (aps : AtomicProcs Op χ V) : Prop :=
  ∀ i j, (hi : i < aps.length) → (hj : j ≤ i) →
    ∀ output ∈ aps[i].outputs, ¬ aps[j].HasInput Op χ V output

def AtomicProcs.HasEmptyInputs (aps : AtomicProcs Op χ V) : Prop :=
  ∀ ap ∈ aps, ap.HasEmptyInputs Op χ V

def AtomicProc.HasDiffPathSuffix (pathConds : List (Bool × ChanName χ)) (ap : AtomicProc Op (ChanName χ) V) : Prop :=
  ∀ inp ∈ ap.inputs, inp.1.HasDiffPathSuffix _ pathConds

def AtomicProcs.HasDiffPathSuffix (pathConds : List (Bool × ChanName χ)) (aps : AtomicProcs Op (ChanName χ) V) : Prop :=
  ∀ ap ∈ aps, ap.HasDiffPathSuffix _ _ _ pathConds

end Wavelet.Dataflow

namespace Wavelet.Simulation

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

/-- Specific case for a Seq config to refine a dataflow config. -/
def SeqRefinesDataflow
  [DecidableEq χ₁] [DecidableEq χ₂]
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  Refines c₁ c₂ R (Config.Step Op χ₁ V S) (Config.StepPlus Op χ₂ V S)

/-- The main invariant for proving forward simulation of compilation. -/
def SimR (ec : Seq.Config Op χ V S m n) (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.estate.state = pc.state ∧
  -- The process matches the compiled function in shape
  AtomicProcs.MatchModBuffers _ _ _ pc.proc.atoms (compileFn Op χ V S ec.estate.fn).atoms ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (carryDecider : ChanBuf (ChanName χ) V)
    (carryInputs₁ carryInputs₂ : Vector (ChanBuf (ChanName χ) V) m)
    (carryOutputs : Vector (ChanName χ) m)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    -- The processes form a DAG if we remove the first carry operator
    pc.proc.atoms = (.carry carryInLoop carryDecider carryInputs₁ carryInputs₂ carryOutputs) :: rest ∧
    rest.IsDAG _ _ _ ∧
    -- States of the first carry gate
    (¬ carryInLoop → ∀ input ∈ carryInputs₁, ∃ var val, input = (.var var 0 [], [val])) ∧
    (carryInLoop → ∀ input ∈ carryInputs₁, input.2 = []) ∧
    -- The processes can be split into three fragments
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    ctxLeft.HasEmptyInputs _ _ _ ∧
    -- If we have reached the end of execution, nothing else should be executable
    (∀ vals, ec.expr = .ret vals →
      ctxCurrent = [] ∧
      ctxRight = [] ∧
      -- Same return value in the proc side
      List.Forall₂ (λ v (_, buf) => buf = [v])
        vals.toList pc.proc.outputs.toList) ∧
    -- If we still have a continuation
    (∀ expr, ec.expr = .cont expr →
      expr.WellFormed ∧
      -- The current fragment corresponds to the compilation results
      AtomicProcs.MatchModBuffers _ _ _
        ctxCurrent
        (compileExpr Op χ V S ec.estate.fn.NonEmptyIO ec.estate.definedVars ec.estate.pathConds expr) ∧
      -- Some constraints about live variables
      (∀ ap ∈ ctxCurrent, ∀ inp ∈ ap.inputs,
        -- Check if the channel name corresponds to a live variable
        -- in the current branch
        let IsLiveVar (name : ChanName χ) val := ∃ var,
          ec.estate.vars var = some val ∧
          name = .var var (ec.estate.definedVars.count var) ec.estate.pathConds
        -- If it's a live var, the channel buffer should have the corresponding value
        (∀ val, IsLiveVar inp.1 val → inp.2 = [val]) ∧
        -- Otherwise it's empty.
        ((∀ val, ¬ IsLiveVar inp.1 val) → inp.2 = [])) ∧
      -- The remaining processes in `ctxRight` should be of the form
      --
      --   `p₁ ... pₘ || merge || p'₁ ... p'ₖ || merge || ...`
      --
      -- i.e., a sequence of processes interspersed with consecutive
      -- chunks of n merge nodes.
      -- Furthermore, all processes other than these merges should
      -- have empty input buffers, and the merges will have exactly
      -- one Boolean in the decider buffers corresponding to the
      -- branching decision.
      (∃ (chunks : List (AtomicProcs Op (ChanName χ) V × AtomicProc Op (ChanName χ) V))
        (tail : AtomicProcs Op (ChanName χ) V),
        ctxRight = (joinM (chunks.map (λ (l, r) => l ++ [r]))) ++ tail ∧
        -- The first half chunks and the tail have empty inputs
        (∀ chunk₁ chunk₂, (chunk₁, chunk₂) ∈ chunks →
          chunk₁.HasEmptyInputs _ _ _ ∧
          chunk₁.HasDiffPathSuffix _ _ _ ec.estate.pathConds) ∧
        tail.HasEmptyInputs _ _ _ ∧
        tail.HasDiffPathSuffix _ _ _ ec.estate.pathConds ∧
        -- The second half chunk corresponds exactly to the merge nodes
        -- generated along the branches marked in the current `pathConds`.
        List.Forall₂
          (λ (_, merge) i =>
            let (b, cond) := ec.estate.pathConds[i]
            let prevPathConds := ec.estate.pathConds.drop (i + 1)
            ∃ v,
              Interp.asBool Op S v = b ∧
              -- Same as the original merge gate, except with the corresponding
              -- branching decision in the decider buffer.
              merge = compileExpr.brMerge Op _ _ m n cond [v] prevPathConds)
          chunks
          (Vector.finRange ec.estate.pathConds.length).toList))

theorem aps_match_mod_bufs_refl :
  AtomicProcs.MatchModBuffers Op χ V aps aps := sorry

theorem aps_match_symmetric
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps aps') :
  AtomicProcs.MatchModBuffers Op χ V aps' aps := sorry

theorem aps_push_preserves_shape :
  AtomicProcs.MatchModBuffers Op χ V (aps.push Op χ V updates) aps := sorry

theorem aps_push_preserves_dag
  (hdag : AtomicProcs.IsDAG Op _ V aps) :
  AtomicProcs.IsDAG Op _ V (aps.push Op χ V updates) := sorry

theorem aps_push_commutes_tail
  {aps : AtomicProcs Op χ V} :
  (aps.push Op χ V updates).tail
    = AtomicProcs.push Op χ V updates aps.tail := sorry

theorem aps_push_commutes_append :
  (AtomicProcs.push Op χ V updates (aps₁ ++ aps₂))
    = (AtomicProcs.push Op χ V updates aps₁) ++
      (AtomicProcs.push Op χ V updates aps₂) := sorry

/-- The result of compilation should be a DAG except for the first carry process. -/
theorem fn_compile_dag :
  AtomicProcs.IsDAG Op _ V ((compileFn Op χ V S fn).atoms.tail) := sorry

theorem aps_match_cons_implies_exists_ap_match
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps (ap' :: rest')) :
  ∃ ap rest,
    aps = ap :: rest ∧
    AtomicProc.MatchModBuffers _ _ _ ap ap' ∧
    AtomicProcs.MatchModBuffers _ _ _ rest rest'
  := sorry

/-- Initial configs satisfy the simulation relation. -/
theorem sim_init_config
  (f : Fn Op χ m n)
  (p : Proc Op (ChanName χ) V m n)
  (hcomp : compileFn Op χ V S f = p)
  (s : S)
  (args : Vector V m) :
  SimR _ _ _ _
    (Seq.Config.init _ _ _ _ f s args)
    (Dataflow.Config.init _ _ _ _ p s args) := by
  simp only [← hcomp]
  and_intros
  · rfl
  · apply aps_push_preserves_shape
  · generalize hinitUpdates : ((compileFn Op χ V S f).inputs.zip args).toList = initUpdates
    exists
      (Proc.push Op _ _ initUpdates p).atoms.tail,
      false,
      (.empty _ (.tail_cond [])),
      (f.params.map λ v => (ChanBuf.empty _ (.var v 0 [])).push _ initUpdates),
      ((Vector.range m).map λ i => .empty _ (.final_tail_arg i)),
      (f.params.map λ v => .var v 1 []),
      [],
      AtomicProcs.push Op _ _ initUpdates (compileFn.bodyComp Op χ V S f),
      AtomicProcs.push Op _ _ initUpdates (compileFn.resultSteers Op χ V m n)
    and_intros
    · simp [Dataflow.Config.init, Proc.push, ← hcomp]
      cases h : (compileFn Op χ V S f).atoms with
      | nil => simp [compileFn] at h
      | cons carry rest =>
        simp [AtomicProcs.push, List.tail, hinitUpdates]
        -- TODO: Reason about carry substitution
        simp [compileFn, compileFn.initCarry] at h
        simp only [← h.1, AtomicProc.push, AtomicProc.push.pushOne]
        congr 1
        · sorry
        · sorry
        · sorry
    · simp [Proc.push, ← hcomp]
      apply aps_push_preserves_dag
      apply fn_compile_dag
    · simp
      -- Some facts about push
      sorry
    · simp
    · simp [Proc.push, ← hcomp, compileFn, aps_push_commutes_tail, aps_push_commutes_append]
    · simp [AtomicProcs.HasEmptyInputs]
    · simp [Seq.Config.init]
    · intros expr hexpr
      simp [Seq.Config.init] at hexpr
      simp only [← hexpr]
      and_intros
      · exact f.WellFormedBody
      · simp only [compileFn.bodyComp, Seq.Config.init, ExprState.init]
        apply aps_push_preserves_shape
      · intros ap hap inp hinp
        constructor
        · intros val hval
          have ⟨var, hvar_lookup, hvar_name⟩ := hval
          simp [Seq.Config.init, ExprState.init] at hvar_lookup
          sorry
        · sorry
      · exists [], AtomicProcs.push Op _ _ initUpdates (compileFn.resultSteers Op χ V m n)
        simp [joinM]
        and_intros
        · -- TODO: reason about steer pushes
          sorry
        · -- TODO: reason about HasDiffPathSuffix
          sorry
        · constructor

theorem sim_step
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ ec pc)
  (hstep : Config.Step Op χ V S ec ec') :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ ec' pc' := by
  have ⟨
    heq_state,
    hmatch_fn,
    ⟨
      rest,
      carryInLoop,
      carryDecider,
      carryInputs₁,
      carryInputs₂,
      carryOutputs,
      ctxLeft,
      ctxCurrent,
      ctxRight,
      hatoms,
      hdag,
      hcarry_false,
      hcarry_true,
      hrest,
      hempty_ctxLeft,
      hret,
      hcont,
    ⟩,
  ⟩ := hsim
  generalize hcarry :
    @AtomicProc.carry Op _ _ V m
      carryInLoop carryDecider
      carryInputs₁ carryInputs₂
      carryOutputs = carry
  simp only [hcarry] at hatoms
  cases hstep with
  | step_op hinputs hop hexpr =>
    rename_i o inputVals outputVals state' args rets cont
    have ⟨
      hwf_expr,
      hmatch,
      hlive_vars,
      hctxRight,
    ⟩ := hcont _ hexpr
    simp [compileExpr] at hmatch
    have ⟨
      ap, ctxRest,
      hctxCurrent,
      hmatch_ap,
      hmatch_ctxRest,
    ⟩ := aps_match_cons_implies_exists_ap_match _ _ _ hmatch
    simp [AtomicProc.MatchModBuffers] at hmatch_ap
    cases ap <;> simp at hmatch_ap
    rename_i o' inputs outputs
    have ⟨heq_o, hap_match_inputs, hap_match_outputs⟩ := hmatch_ap
    replace heq_o := heq_o.symm
    subst heq_o
    have hatoms' : pc.proc.atoms = ([carry] ++ ctxLeft) ++ [AtomicProc.op o inputs outputs] ++ (ctxRest ++ ctxRight) := by
      grind
    have ⟨inputs', hinputs'⟩ : ∃ inputs', inputs.pop _ = some (inputVals, inputs') :=
      sorry
    simp only [heq_state] at hop
    have : Dataflow.Config.StepPlus _ _ _ _ pc _ := .single (.step_op hinputs' hop hatoms')
    simp only at this
    constructor
    constructor
    · exact this
    · and_intros
      · rfl
      · simp
        sorry
      · sorry

theorem compile_refines
  (f : Fn Op χ m n)
  (p : Proc Op (ChanName χ) V m n)
  (hcomp : compileFn Op χ V S f = p)
  (s : S)
  (args : Vector V m) :
  Refines
    (Config.init _ _ _ _ f s args)
    (Config.init _ _ _ _ p s args)
    (SimR _ _ _ _)
    (Config.Step Op χ V S)
    (Config.StepPlus Op (ChanName χ) V S) := by
  constructor
  · apply sim_init_config
    exact hcomp
  · intros ec pc ec' hstep
    apply sim_step _ _ _ _ ec ec'
    exact hstep

end Wavelet.Simulation
