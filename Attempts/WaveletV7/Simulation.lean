import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Lemmas

open Wavelet.Op

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

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
  where MatchBuf := ChanBuf.MatchModBuffer _ _

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

def SimR.Basic
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.estate.state = pc.state ∧
  -- The process matches the compiled function in shape
  AtomicProcs.MatchModBuffers _ _ _
    pc.proc.atoms (compileFn Op χ V S hnz ec.estate.fn).atoms

/-- Invariants for the current continuation expression. -/
def SimR.CtxCurrent
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (cont : Expr Op χ m n)
  (ctxCurrent : AtomicProcs Op (ChanName χ) V) : Prop :=
  cont.WellFormed _ _ ec.definedVars.toList ∧
  ctxCurrent = AtomicProcs.push _ _ _
    ec.definedVarsAsNames ec.definedVals
    (compileExpr Op χ V S hnz ec.definedVars ec.estate.pathConds cont)

/--
The remaining processes in `ctxRight` should be of the form

  `p₁ ... pₘ || merge || p'₁ ... p'ₖ || merge || ...`

i.e., a sequence of processes interspersed with consecutive
chunks of n merge nodes.
Furthermore, all processes other than these merges should
have empty input buffers, and the merges will have exactly
one Boolean in the decider buffers corresponding to the
branching decision.
-/
def SimR.CtxRight
  (ec : Seq.Config Op χ V S m n)
  (ctxRight : AtomicProcs Op (ChanName χ) V) : Prop :=
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
      (Vector.finRange ec.estate.pathConds.length).toList)

/-- The main invariant for proving forward simulation of compilation. -/
def SimR
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  SimR.Basic _ _ _ _ hnz ec pc ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    -- The processes form a DAG if we remove the first carry operator
    pc.proc.atoms = compileFn.initCarry _ _ _ ec.estate.fn carryInLoop :: rest ∧
    rest.IsDAG _ _ _ ∧
    -- The processes can be split into three fragments
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    ctxLeft.HasEmptyInputs _ _ _ ∧
    -- If we have reached the end of execution, nothing else should be executable
    (∀ vals, ec.expr = .ret vals →
      ¬ carryInLoop ∧
      ctxCurrent = [] ∧
      ctxRight = [] ∧
      -- Same return value in the proc side
      List.Forall₂ (λ v (_, buf) => buf = [v])
        vals.toList pc.proc.outputs.toList) ∧
    -- If we still have a continuation
    (∀ expr, ec.expr = .cont expr →
      carryInLoop ∧
      SimR.CtxCurrent _ _ _ _ hnz ec expr ctxCurrent ∧
      SimR.CtxRight _ _ _ _ ec ctxRight)

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
  AtomicProcs.IsDAG Op _ V ((compileFn Op χ V S hnz fn).atoms.tail) := sorry

theorem expr_compile_dag
  (hwf : m > 0 ∧ n > 0) :
  AtomicProcs.IsDAG Op _ V (compileExpr Op χ V S hwf definedVars pathConds expr) := sorry

theorem aps_match_commutes_with_cons
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps (ap' :: rest')) :
  ∃ ap rest,
    aps = ap :: rest ∧
    AtomicProc.MatchModBuffers _ _ _ ap ap' ∧
    AtomicProcs.MatchModBuffers _ _ _ rest rest'
  := sorry

theorem aps_match_commutes_with_append
  left' right'
  (hmatch : AtomicProcs.MatchModBuffers Op χ V aps (left' ++ right')) :
  ∃ left right,
    aps = left ++ right ∧
    AtomicProcs.MatchModBuffers _ _ _ left left' ∧
    AtomicProcs.MatchModBuffers _ _ _ right right'
  := sorry

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

theorem ap_match_steer_destruct
  (hmatch : AtomicProc.MatchModBuffers Op χ V ap
    (AtomicProc.steer flavor
      (ChanBuf.empty χ deciderName)
      (ChanBufs.empty χ inputNames)
      outputNames)) :
  ∃ deciderBuf inputBufs,
    ap = AtomicProc.steer flavor
      (ChanBuf.withBuf _ deciderBuf deciderName)
      (ChanBufs.withBufs _ inputBufs inputNames)
      outputNames := sorry

theorem sim_step_br
  {cond}
  (hnz : m > 0 ∧ n > 0)
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hbr : ec.expr = .cont (.br cond left right)) :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ hnz ec' pc' := by
  have ⟨
    ⟨heq_states, hmatch_global⟩,
    ⟨
      rest,
      carryInLoop,
      ctxLeft,
      ctxCurrent,
      ctxRight,
      hatoms,
      hdag,
      hrest,
      hleft_empty,
      _,
      hcont,
    ⟩
  ⟩ := hsim
  have ⟨
    hcarry_inLoop,
    hcurrent,
    hright,
  ⟩ := hcont (.br cond left right) hbr
  replace ⟨hwf, hcurrent⟩ := hcurrent
  simp [compileExpr, AtomicProcs.push, compileExpr.brMerge] at hcurrent
  -- Short-hands for some complex terms
  generalize hcarry :
    compileFn.initCarry Op χ V ec.estate.fn carryInLoop = carry
  simp only [hcarry] at hatoms
  generalize hleftConds :
    (true, (ChanBuf.empty (ChanName χ) (V := V) (compileExpr.varName χ ec.estate.pathConds cond)).fst) ::
    ec.estate.pathConds = leftConds
  generalize hrightConds :
    (false, (ChanBuf.empty (ChanName χ) (V := V) (compileExpr.varName χ ec.estate.pathConds cond)).fst) ::
    ec.estate.pathConds = rightConds
  generalize hallVars : compileExpr.allVars χ (Config.definedVars Op χ V S ec) ec.estate.pathConds = allVars
  generalize hallVarsLeft : compileExpr.allVars χ (Config.definedVars Op χ V S ec) leftConds = allVarsLeft
  generalize hallVarsRight : compileExpr.allVars χ (Config.definedVars Op χ V S ec) rightConds = allVarsRight
  generalize hcondName : compileExpr.varName χ ec.estate.pathConds cond = condName
  simp only [hleftConds, hrightConds, hallVars,
    hallVarsLeft, hallVarsRight] at hcurrent
  simp only [hcondName] at hcurrent
  simp [AtomicProc.push] at hcurrent
  generalize hsteer₁ :
    AtomicProc.steer (instArity := instArity) true
      (ChanBuf.push _ ec.definedVarsAsNames ec.definedVals
        (ChanBuf.empty _ condName))
      (ChanBufs.push _ ec.definedVarsAsNames ec.definedVals
        (ChanBufs.empty _ allVars))
      allVarsLeft
    = steer₁
  generalize hsteer₂ :
    AtomicProc.steer (instArity := instArity) false
      (ChanBuf.push _ ec.definedVarsAsNames ec.definedVals
        (ChanBuf.empty _ condName))
      (ChanBufs.push _ ec.definedVarsAsNames ec.definedVals
        (ChanBufs.empty _ allVars))
      allVarsRight
    = steer₂
  generalize hforward :
    AtomicProc.forward (instArity := instArity)
      (.push _ ec.definedVarsAsNames ec.definedVals
        #v[.empty _ condName])
      #v[(ChanBuf.empty (V := V) _ condName).fst.merge_cond]
    = forward
  generalize hleftComp :
    List.map
      (AtomicProc.push Op (ChanName χ) V ec.definedVarsAsNames ec.definedVals)
      (compileExpr Op χ V S hnz (Config.definedVars Op χ V S ec) leftConds left)
    = leftComp
  generalize hrightComp :
    List.map
      (AtomicProc.push Op (ChanName χ) V ec.definedVarsAsNames ec.definedVals)
      (compileExpr Op χ V S hnz (Config.definedVars Op χ V S ec) rightConds right)
    = rightComp
  generalize hmerge :
    AtomicProc.merge (instArity := instArity)
      (ChanBuf.push (ChanName χ) ec.definedVarsAsNames ec.definedVals
        ((ChanBuf.empty (V := V) (ChanName χ) condName).fst.merge_cond, []))
      (ChanBufs.push (ChanName χ) ec.definedVarsAsNames ec.definedVals
        (ChanBufs.empty (V := V) (ChanName χ) (compileExpr.exprOutputs χ m n leftConds)))
      (ChanBufs.push (ChanName χ) ec.definedVarsAsNames ec.definedVals
        (ChanBufs.empty (V := V) (ChanName χ) (compileExpr.exprOutputs χ m n rightConds)))
      (compileExpr.exprOutputs χ m n ec.estate.pathConds)
    = merge
  simp only [hsteer₁, hsteer₂, hforward, hleftComp, hrightComp, hmerge] at hcurrent
  simp only [ChanBuf.empty] at hforward
  -- Simplify some pushes
  have hpush_allVars :
    ChanBufs.push _
      ec.definedVarsAsNames ec.definedVals
      (ChanBufs.empty _ allVars)
    = ChanBufs.singleton _ allVars ec.definedVals
  := sorry
  simp only [hpush_allVars] at hsteer₁ hsteer₂
  cases hstep with
  | step_ret hexpr => simp [hbr] at hexpr
  | step_tail hexpr => simp [hbr] at hexpr
  | step_op hexpr => simp [hbr] at hexpr
  | step_br hexpr hcond =>
    rename_i condVal _ _ cond'
    simp [hbr] at hexpr
    have heq_cond' := hexpr.1
    subst heq_cond'
    have hpush_cond :
      ChanBuf.push _
        ec.definedVarsAsNames ec.definedVals
        (.empty _ condName)
      = ChanBuf.singleton _ condName condVal
    := sorry
    simp only [hpush_cond] at hsteer₁ hsteer₂
    simp only [hcurrent] at hrest
    simp only [hrest] at hatoms
    -- generalize hctxLeft₁ :
    --   compileFn.initCarry Op χ V ec.estate.fn carryInLoop :: ctxLeft = ctxLeft₁
    if hcondVal : Interp.asBool Op S condVal then
      generalize hpc₁ :
        { pc with
          proc := { pc.proc with
            outputs := pc.proc.outputs,
            atoms :=
              (carry :: ctxLeft) ++ [
                AtomicProc.steer true
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsLeft
              ] ++ (
                steer₂ :: forward ::
                (AtomicProcs.push _ _ _ allVarsLeft ec.definedVals leftComp) ++
                rightComp ++
                [merge] ++
                ctxRight
              ),
          } } = pc₁
      have hstep₁ : Dataflow.Config.Step _ _ _ _ pc pc₁
      := by
        simp only [← hpc₁]
        apply step_eq
        apply Dataflow.Config.Step.step_steer (instInterp := instInterp)
          (ctxLeft := carry :: ctxLeft)
          (ctxRight := steer₂ :: forward :: leftComp ++ rightComp ++ [merge] ++ ctxRight)
          (steer := steer₁)
          (by grind)
          hsteer₁.symm
          (buf_pop_singleton (var := condName) (val := condVal))
          (bufs_pop_singleton (vars := allVars) (vals := ec.definedVals))
        simp [AtomicProcs.push, hcondVal]
        and_intros
        · sorry
        · sorry
        · sorry
      -- Make one step with the second steer...
      generalize hpc₂ :
        {
          pc with
          proc := { pc.proc with
            outputs := pc.proc.outputs,
            atoms :=
              (carry :: ctxLeft) ++ [
                AtomicProc.steer true
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsLeft
              ] ++ (
                AtomicProc.steer false
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsRight ::
                forward ::
                (AtomicProcs.push _ _ _ allVarsLeft ec.definedVals leftComp) ++
                rightComp ++
                [merge] ++
                ctxRight
              ),
          }
        } = pc₂
      have hstep₂ : Dataflow.Config.Step _ _ _ _ pc₁ pc₂
      := by
        simp only [← hpc₁, ← hpc₂]
        apply step_eq
        apply Dataflow.Config.Step.step_steer (instInterp := instInterp)
          (ctxLeft := carry :: ctxLeft ++ [
                AtomicProc.steer true
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsLeft
              ])
          (ctxRight := forward ::
                (AtomicProcs.push _ _ _ allVarsLeft ec.definedVals leftComp) ++
                rightComp ++
                [merge] ++
                ctxRight)
          (steer := steer₂)
          (by grind)
          hsteer₂.symm
          (buf_pop_singleton (var := condName) (val := condVal))
          (bufs_pop_singleton (vars := allVars) (vals := ec.definedVals))
        simp [AtomicProcs.push, hcondVal]
      -- Third step with the forward!
      generalize hpc₃ :
        {
          pc with
          proc := { pc.proc with
            outputs := pc.proc.outputs,
            atoms :=
              (carry :: ctxLeft) ++ [
                AtomicProc.steer true
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsLeft
              ] ++ (
                AtomicProc.steer false
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsRight ::
                AtomicProc.forward (instArity := instArity)
                  #v[.empty _ condName]
                  #v[condName.merge_cond] ::
                (AtomicProcs.push _ _ _ allVarsLeft ec.definedVals leftComp) ++
                rightComp ++
                [AtomicProc.push _ _ _ #v[condName.merge_cond] #v[condVal] merge] ++
                ctxRight
              ),
          }
        } = pc₃
      have hstep₃ : Dataflow.Config.Step _ _ _ _ pc₂ pc₃
      := by
        simp only [← hpc₂, ← hpc₃]
        apply step_eq
        have hpush :
          (ChanBufs.push (ChanName χ) (Config.definedVarsAsNames Op χ V S ec) (Config.definedVals Op χ V S ec)
            #v[(condName, [])])
          = ChanBufs.singleton _ #v[condName] #v[condVal] := sorry
        simp only [hpush] at hforward
        apply Dataflow.Config.Step.step_forward (instInterp := instInterp)
          (ctxLeft := (carry :: ctxLeft) ++ [
                AtomicProc.steer true
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsLeft
              ] ++ [
                AtomicProc.steer false
                  (ChanBuf.empty (ChanName χ) condName)
                  (ChanBufs.empty (ChanName χ) allVars)
                  allVarsRight])
          (ctxRight := (AtomicProcs.push _ _ _ allVarsLeft ec.definedVals leftComp) ++
            rightComp ++
            [merge] ++
            ctxRight)
          (forward := forward)
          (by grind)
          hforward.symm
          (bufs_pop_singleton (vars := #v[condName]) (vals := #v[condVal]))
        simp [AtomicProcs.push]
        and_intros
        · sorry
        · sorry
        · sorry
      -- Connect the previous steps
      have hsteps : Dataflow.Config.StepPlus _ _ _ _ pc pc₃
      := by
        apply Relation.TransGen.trans
        apply Relation.TransGen.single hstep₁
        apply Relation.TransGen.trans
        apply Relation.TransGen.single hstep₂
        apply Relation.TransGen.single hstep₃
      -- Prove that invariants hold...
      exists pc₃
      simp [hsteps]
      and_intros
      · simp [← hpc₃, heq_states]
      · simp [← hpc₃]
        sorry
      · sorry
    else
      sorry

theorem sim_step
  (hnz : m > 0 ∧ n > 0)
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec') :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ hnz ec' pc' := by
  sorry

end Wavelet.Simulation
