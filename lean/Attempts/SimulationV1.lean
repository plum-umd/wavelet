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
  | .var _ pathConds' => ∀ ext, ext ++ pathConds ≠ pathConds'
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
    (¬ carryInLoop → ∀ input ∈ carryInputs₁, ∃ var val, input = (.input var, [val])) ∧
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
      expr.WellFormed _ _ ec.estate.definedVars ∧
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
          name = .var var ec.estate.pathConds
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

theorem aps_match_refl :
  AtomicProcs.MatchModBuffers Op χ V aps aps := sorry

theorem aps_match_symm
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps aps') :
  AtomicProcs.MatchModBuffers Op χ V aps' aps := sorry

theorem aps_match_trans
  (h₁ : AtomicProcs.MatchModBuffers Op χ V aps₁ aps₂)
  (h₂ : AtomicProcs.MatchModBuffers Op χ V aps₂ aps₃) :
  AtomicProcs.MatchModBuffers Op χ V aps₁ aps₃ := sorry

theorem aps_push_preserves_shape :
  AtomicProcs.MatchModBuffers Op χ V (aps.push Op χ V vars vals) aps := sorry

theorem aps_push_preserves_dag
  (hdag : AtomicProcs.IsDAG Op _ V aps) :
  AtomicProcs.IsDAG Op _ V (aps.push Op χ V vars vals) := sorry

theorem aps_push_commutes_tail
  {aps : AtomicProcs Op χ V} :
  (aps.push Op χ V vars vals).tail
    = AtomicProcs.push Op χ V vars vals aps.tail := sorry

theorem aps_push_commutes_append :
  (AtomicProcs.push Op χ V vars vals (aps₁ ++ aps₂))
    = (AtomicProcs.push Op χ V vars vals aps₁) ++
      (AtomicProcs.push Op χ V vars vals aps₂) := sorry

/-- The result of compilation should be a DAG except for the first carry process. -/
theorem fn_compile_dag :
  AtomicProcs.IsDAG Op _ V ((compileFn Op χ V S fn).atoms.tail) := sorry

theorem expr_compile_dag
  (hwf : m > 0 ∧ n > 0) :
  AtomicProcs.IsDAG Op _ V (compileExpr Op χ V S hwf definedVars pathConds expr) := sorry

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
  · generalize hcompInputs : (compileFn Op χ V S f).inputs = compInputs
    exists
      (Proc.push Op _ _ compInputs args p).atoms.tail,
      false,
      (.empty _ (.tail_cond [])),
      (f.params.map λ v => (ChanBuf.empty _ (.input v)).push _ compInputs args),
      ((Vector.range m).map λ i => .empty _ (.final_tail_arg i)),
      (f.params.map λ v => .var v []),
      [],
      AtomicProcs.push Op _ _ compInputs args (compileFn.bodyComp Op χ V S f),
      AtomicProcs.push Op _ _ compInputs args (compileFn.resultSteers Op χ V m n)
    and_intros
    · simp [Dataflow.Config.init, Proc.push, ← hcomp]
      cases h : (compileFn Op χ V S f).atoms with
      | nil => simp [compileFn] at h
      | cons carry rest =>
        simp [List.tail, hcompInputs]
        -- TODO: Reason about carry substitution
        simp [compileFn, compileFn.initCarry] at h
        simp only [← h.1]
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
      · exists [], AtomicProcs.push Op _ _ compInputs args (compileFn.resultSteers Op χ V m n)
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
  | step_op hexpr hinputs hop =>
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
    have : Dataflow.Config.StepPlus _ _ _ _ pc _ := .single (.step_op hatoms' hinputs' hop)
    simp only at this
    constructor
    constructor
    · exact this
    · -- Prove the simulation relation after the step
      and_intros
      · rfl
      · simp
        apply aps_match_trans
        · sorry -- apply aps_push_preserves_shape
        · apply aps_match_trans _ _ _ _ hmatch_fn
          -- simp [hatoms']
          -- TODO: prove AtomicProcs.MatchModBuffers
          all_goals sorry
        all_goals sorry
      · exists
          AtomicProcs.push Op (ChanName χ) V outputs outputVals
            (ctxLeft ++ [AtomicProc.op o inputs' outputs] ++ (ctxRest ++ ctxRight)),
          carryInLoop,
          carryDecider,
          carryInputs₁,
          carryInputs₂,
          carryOutputs,
          ctxLeft ++ [AtomicProc.op o inputs' outputs],
          AtomicProcs.push Op (ChanName χ) V outputs outputVals ctxRest,
          ctxRight
        and_intros
        · simp
          -- TODO: need to prove that the push does not affect
          -- carry, ctxLeft, the current .op, and ctxRight
          sorry
        · apply aps_push_preserves_dag
          -- TODO: prove that poping preserves DAG.
          sorry
        · grind
        · grind
        · sorry
        · -- TODO: prove that input' have empty buffers
          sorry
        · simp
        · intros expr' hexpr'
          simp at hexpr'
          subst hexpr'
          and_intros
          · cases hwf_expr
            assumption
          · simp
            sorry
          · simp
            -- TODO: variable mapping
            sorry
          · -- TODO: invariants about tail
            sorry
  | _ => sorry

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

/-- Converts a local map to channel pushes to the continuation process. -/
def localToInputs
  (locals : VarMap χ V)
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ)) :
  Option (Vector (ChanName χ × V) definedVars.eraseDups.length) :=
  let uniq := definedVars.eraseDups.toArray.toVector
  uniq.mapM λ var =>
    return (ChanName.var var pathConds, ← locals.getVar χ V var)

theorem bufs_forall₂_implies_pop_some
  {bufs bufs' : ChanBufs χ V n}
  (hvals : List.Forall₂ (λ buf val => ∃ rest, buf.2 = val :: rest) bufs.toList vals.toList)
  (hbufs : List.Forall₂ (λ buf buf' => buf.1 = buf'.1 ∧ ∃ val, buf.2 = val :: buf.2) bufs.toList bufs'.toList) :
  bufs.pop _ = some (vals, bufs') := sorry

@[simp]
theorem buf_pop_singleton :
  (ChanBuf.singleton _ var val).pop _ = some (val, ChanBuf.empty _ var) := sorry

@[simp]
theorem bufs_pop_singleton :
  (ChanBufs.singleton _ vars vals).pop _ = some (vals, ChanBufs.empty _ vars) := sorry

@[simp]
theorem buf_push_tail_args_to_empty_var :
  ChanBuf.push (ChanName χ)
    (compileExpr.tailArgs χ pathConds) vals
    (ChanBuf.empty (ChanName χ) (compileExpr.varName χ pathConds var))
  = ChanBuf.empty (ChanName χ) (compileExpr.varName χ pathConds var) := sorry

@[simp]
theorem buf_push_tail_args_to_singleton_var :
  ChanBuf.push (ChanName χ)
    (compileExpr.tailArgs χ pathConds) vals
    (ChanBuf.singleton (ChanName χ) (compileExpr.varName χ pathConds var) val)
  = ChanBuf.singleton (ChanName χ) (compileExpr.varName χ pathConds var) val := sorry

@[simp]
theorem buf_push_ret_chans_to_singleton_var :
  ChanBuf.push (ChanName χ)
    (compileExpr.retChans χ pathConds) vals
    (ChanBuf.singleton (ChanName χ) (compileExpr.varName χ pathConds var) val)
  = ChanBuf.singleton (ChanName χ) (compileExpr.varName χ pathConds var) val := sorry

@[simp]
theorem buf_push_tail_cond_to_empty_vars :
  ChanBuf.push (ChanName χ)
    #v[ChanName.tail_cond pathConds] #v[val]
    (ChanBuf.empty (ChanName χ) (compileExpr.varName χ pathConds var))
  = ChanBuf.empty (ChanName χ) (compileExpr.varName χ pathConds var) := sorry

@[simp]
theorem bufs_push_tail_args_to_empty_vars :
  ChanBufs.push (ChanName χ)
    (compileExpr.tailArgs χ pathConds) vals
    (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds vars))
  = ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds vars) := sorry

@[simp]
theorem bufs_push_tail_cond_to_empty_vars :
  ChanBufs.push (ChanName χ)
    #v[ChanName.tail_cond pathConds] #v[val]
    (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds vars))
  = ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds vars) := sorry

@[simp]
theorem bufs_push_ret_chans_to_empty_var :
  ChanBufs.push (ChanName χ)
    (compileExpr.retChans χ pathConds) vals
    (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds vars))
  = ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds vars) := sorry

/-- Appends additional atoms on the left as long as the resulting process is a DAG. -/
theorem step_plus_frame_left
  (frame : AtomicProcs Op (ChanName χ) V)
  (hstep : Dataflow.Config.StepPlus Op (ChanName χ) V S pc pc')
  (hdag : AtomicProcs.IsDAG Op _ V (frame ++ pc.proc.atoms)) :
  Dataflow.Config.StepPlus Op (ChanName χ) V S
    { pc with proc := { pc.proc with atoms := frame ++ pc.proc.atoms } }
    { pc' with proc := { pc'.proc with atoms := frame ++ pc'.proc.atoms } } := sorry

theorem eval_refines
  (expr : Expr Op χ m n)
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  (state : S)
  (locals : VarMap χ V)
  (proc : Proc _ _ _ definedVars.length (1 + n + m))
  (args : Vector V definedVars.length)

  (hwf_mn : m > 0 ∧ n > 0)
  (hdisj : definedVars.Nodup)
  (hwf_expr : expr.WellFormed _ _ definedVars)
  (hcomp : proc = compileExprAsProc Op χ V S hwf definedVars pathConds expr)
  (heval : (expr.eval _ _ _ _ locals).run state = some (.ret vals, state'))
  (hlocals : ∀ var, var ∈ definedVars ↔ locals.getVar χ V var ≠ none)
  : Dataflow.Config.StepPlus Op (ChanName χ) V S
    (Dataflow.Config.init _ _ _ _ proc state args)
    { proc := { proc with
        outputs := .singleton _ (compileExpr.exprOutputs _ m n pathConds)
          (
            #v[(Interp.trueVal Op S : V)] ++
            vals ++
            Vector.replicate m (Interp.junkVal Op S : V)
          ),
      },
      state := state' }
  := by
  cases expr with
  | ret vars =>
    -- Simplify evals
    simp [Expr.eval, bind, liftM, monadLift, MonadLift.monadLift] at heval
    cases hvals : VarMap.getVars χ V vars locals <;> simp [hvals] at heval
    · contradiction
    rename_i vals
    simp [StateT.bind, StateT.lift, StateT.run, Option.bind, pure, StateT.pure] at heval
    -- Simplify pushes
    simp [compileExprAsProc, compileExpr] at hcomp
    simp [hcomp]
    -- Some facts about push
    generalize hallVars : compileExpr.allDefinedVars χ definedVars pathConds = allVars
    have houtputsNoChange :
      ChanBufs.push (ChanName χ) allVars args
        (ChanBufs.empty (ChanName χ) (compileExpr.exprOutputs χ m n pathConds))
      = ChanBufs.empty (ChanName χ) (compileExpr.exprOutputs χ m n pathConds) := sorry
    simp only [houtputsNoChange]
    have hpush₁ :
      ChanBufs.push (ChanName χ)
        allVars args
        (.empty _ (compileExpr.varNames χ pathConds vars))
      = .singleton _
        (compileExpr.varNames χ pathConds vars) vals := sorry
    simp only [hpush₁]
    have hpush₂ :
      ChanBuf.push (ChanName χ) allVars args
        (ChanBufs.empty (ChanName χ)
          (compileExpr.varNames χ pathConds vars))[0]
      = ChanBuf.singleton _
        (compileExpr.varName χ pathConds vars[0])
        vals[0] := sorry
    simp only [hpush₂]
    -- Step 1: run forward
    apply Relation.TransGen.head
    · apply step_forward_alt₁ _ _ _ _ []
        vals -- inputVals
        (.empty _ (compileExpr.varNames χ pathConds vars)) -- inputs after pop
      · rfl
      · simp
    simp
    -- Step 2: run const
    apply Relation.TransGen.head
    · apply step_const_alt₁ _ _ _ _ [_]
      · rfl
      · simp
        constructor <;> rfl
    simp
    -- Step 3: run second const
    apply Relation.TransGen.single
    apply step_eq
    · apply step_const_alt₁ _ _ _ _ [_, _]
      · rfl
      · simp
        constructor <;> rfl
    simp
    and_intros
    · -- TODO: pushes at the final output
      sorry
    · simp [ChanBufs.empty, compileExpr.varNames]
    · exact heval.2
  | op o opArgs bind cont =>
    -- Extract well-formedness of `cont`
    cases hwf_expr with | wf_op hbind_nodup hbind_disj hwf_cont =>
    -- Simplify evals
    simp [Expr.eval] at heval
    cases hargVals : VarMap.getVars χ V opArgs locals <;> simp [hargVals] at heval
    rename_i argVals
    simp [Option.bind] at heval
    split at heval
    · contradiction
    rename_i outputAndState' houtputAndState'
    rcases outputAndState' with ⟨outputVals, state''⟩
    simp at heval
    -- Simplify comp
    have hcomp_dag : AtomicProcs.IsDAG Op _ V proc.atoms := by
      simp only [hcomp, compileExprAsProc]
      apply expr_compile_dag
    simp [compileExprAsProc, compileExpr] at hcomp
    have hlocals' :
      ∀ var, var ∈ definedVars ++ bind.toList
        ↔ (VarMap.insertVars χ V bind outputVals locals).getVar χ V var ≠ none := sorry
    have hlen : definedVars.length + Arity.ω o = (definedVars ++ bind.toList).length :=
      sorry
    have args' : Vector V (definedVars.length + Arity.ω o) := args ++ outputVals
    have hbind_nodup : (definedVars ++ bind.toList).Nodup := sorry
    simp only [hlen] at args'
    have hstep_cont := eval_refines cont
      (definedVars ++ bind.toList)
      pathConds
      state''
      (VarMap.insertVars χ V bind outputVals locals)
      (compileExprAsProc Op χ V S hwf (definedVars ++ bind.toList) pathConds cont)
      args'
      hwf_mn
      hbind_nodup
      hwf_cont
      (Eq.refl _)
      heval
      hlocals'
    simp only [compileExprAsProc] at hstep_cont

    have :
      Dataflow.Config.StepPlus Op (ChanName χ) V S
      {
        proc :=
          Proc.push Op (ChanName χ) V (compileExpr.allDefinedVars χ (definedVars ++ bind.toList) pathConds) args'
            { inputs := compileExpr.allDefinedVars χ (definedVars ++ bind.toList) pathConds,
              outputs := ChanBufs.empty (ChanName χ) (compileExpr.exprOutputs χ m n pathConds),
              atoms := compileExpr Op χ V S hwf (definedVars ++ bind.toList) pathConds cont },
        state := state'' }
      {
        proc :=
          { inputs := compileExpr.allDefinedVars χ (definedVars ++ bind.toList) pathConds,
            outputs :=
              ChanBufs.singleton (ChanName χ) (compileExpr.exprOutputs χ m n pathConds)
                (#v[Interp.trueVal Op S] ++ vals ++ Vector.replicate m (Interp.junkVal Op S)),
            atoms := compileExpr Op χ V S hwf (definedVars ++ bind.toList) pathConds cont },
        state := state' }
      := sorry

    -- Append the additional operator on the left

    simp only [hcomp] at hcomp_dag
    have :
      AtomicProcs.IsDAG Op (ChanName χ) V
        ([AtomicProc.op o (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds opArgs))
          (compileExpr.varNames χ pathConds bind)] ++
          (Dataflow.Config.init Op (ChanName χ) V S
            (compileExprAsProc Op χ V S hwf (definedVars ++ bind.toList) pathConds cont) state'' args').proc.atoms) :=
      sorry
    have := step_plus_frame_left _ _ _ _
      [AtomicProc.op o
        (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ pathConds opArgs))
        (compileExpr.varNames χ pathConds bind)]
      hstep_cont
      this
    simp [compileExprAsProc] at this

    sorry
  | _ => sorry

end Wavelet.Simulation
