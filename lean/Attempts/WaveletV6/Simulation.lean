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

-- /-- An attempt to define a computable version of a subset of the simulation relation. -/
-- def simR
--   (ec : Seq.Config Op χ V S m n)
--   (hnz : m > 0 ∧ n > 0)
--   (definedVars : List χ)
--   (pathConds : List (Bool × ChanName χ))
--   : Expr Op χ m n → AtomicProcs Op (ChanName χ) V
--   | .ret vars =>
--     let chans := chanBufs (varNames vars)
--     let act := chans[0] -- Use the first return value as an activation signal
--     [
--       .forward chans retChans,
--       -- No tail recursion, so we send junk values for the tail arguments
--       -- and send `false` on the tail condition channel.
--       .const (Interp.junkVal Op S) act tailArgs,
--       .const (Interp.falseVal Op S) act #v[.tail_cond pathConds]
--     ]
--   | .tail vars =>
--     let chans := chanBufs (varNames vars)
--     let act := chans[0]
--     [
--       .const (Interp.junkVal Op S) act retChans,
--       .forward chans tailArgs,
--       .const (Interp.trueVal Op S) act #v[.tail_cond pathConds]
--     ]
--   | .op o args rets cont =>
--     let inputChans := chanBufs (varNames args)
--     (.op o inputChans (newVarNames rets)) ::
--       simR ec hnz (definedVars ++ rets.toList) pathConds cont
--   | .br cond left right =>
--     let condChan := chanBuf (varName cond)
--     let leftConds := (true, condChan.1) :: pathConds
--     let rightConds := (false, condChan.1) :: pathConds
--     let leftComp := simR ec hnz definedVars leftConds left
--     let rightComp := simR ec hnz definedVars rightConds right
--     [
--       -- Steer all live variables
--       .steer true condChan
--         (chanBufs (allDefinedVars pathConds))
--         (allDefinedVars leftConds),
--       .steer false condChan
--         (chanBufs (allDefinedVars pathConds))
--         (allDefinedVars rightConds),
--       -- Forward the condition again to the merge
--       -- (extra forward for a simpler simulation relation)
--       .forward #v[condChan] #v[.merge_cond condChan.1],
--     ] ++ leftComp ++ rightComp ++ [
--       -- Merge tail call conditions, return values and tail call arguments
--       -- from both branches. This is done at the end so that we can keep
--       -- the graph as "acyclic" as possible.
--       brMerge m n condChan.1 [] pathConds
--     ]
--   where
--     chanBuf name :=
--       match name with
--       | .var v count pathConds' =>
--         if count = ec.estate.definedVars.count v ∧
--            pathConds' = ec.estate.pathConds then
--           ChanBuf.withBuf _ (ec.estate.vars v).toList name
--         else
--           .empty _ name
--       | _ => .empty _ name
--     chanBufs {n} names := names.map chanBuf
--     -- Current variable names
--     varName v := .var v (definedVars.count v) pathConds
--     varNames {n} (vars : Vector χ n) := vars.map varName
--     -- New variable names after shadowing
--     newVarName v := .var v (definedVars.count v + 1) pathConds
--     newVarNames {n} (vars : Vector χ n) := vars.map newVarName
--     retChans := (Vector.range n).map λ i => .dest i pathConds
--     tailArgs := (Vector.range m).map λ i => .tail_arg i pathConds
--     allDefinedVars pathConds : Vector (ChanName χ) definedVars.eraseDups.length :=
--       definedVars.eraseDups.toArray.toVector.map λ v =>
--         .var v (definedVars.count v) pathConds
--     exprOutputs m n pathConds := #v[ChanName.tail_cond pathConds] ++
--       ((Vector.range n).map λ i => ChanName.dest i pathConds) ++
--       ((Vector.range m).map λ i => ChanName.tail_arg i pathConds)
--     brMerge m n condName condBuf pathConds :=
--       let leftConds := (true, condName) :: pathConds
--       let rightConds := (false, condName) :: pathConds
--       .merge (.merge_cond condName, condBuf)
--         (chanBufs (exprOutputs m n leftConds))
--         (chanBufs (exprOutputs m n rightConds))
--         (exprOutputs m n pathConds)

def SimR.Basic
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.estate.state = pc.state ∧
  -- The process matches the compiled function in shape
  AtomicProcs.MatchModBuffers _ _ _
    pc.proc.atoms (compileFn Op χ V S ec.estate.fn).atoms ∧
  -- Support of `ec.estate.vars` is exactly `ec.estate.definedVars`
  (∀ var, var ∈ ec.estate.definedVars ↔ ∃ val, ec.estate.vars var = some val)

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

def SimR.CtxCurrent
  (ec : Seq.Config Op χ V S m n)
  (cont : Expr Op χ m n)
  (ctxCurrent : AtomicProcs Op (ChanName χ) V) : Prop :=
  cont.WellFormed _ _ -- ∧
  -- AtomicProcs.push _ _ _
  --   ec.estate.definedVars.eraseDups.toArray.toVector
  --   (compileExpr Op χ V S ec.estate.fn.NonEmptyIO ec.estate.definedVars ec.estate.pathConds cont)
  -- -- The current fragment corresponds to the compilation results
  -- AtomicProcs.MatchModBuffers _ _ _
  --   ctxCurrent
  --   (compileExpr Op χ V S ec.estate.fn.NonEmptyIO ec.estate.definedVars ec.estate.pathConds cont) ∧
  -- -- Some constraints about live variables
  -- (∀ ap ∈ ctxCurrent, ∀ inp ∈ ap.inputs,
  --   -- Non-variable channels are empty
  --   (¬ inp.1.isVar → inp.2 = []) ∧
  --   -- Variable channels, if defined, are non-empty
  --   (∀ var ∈ ec.estate.definedVars,
  --     inp.1 = .var var (ec.estate.definedVars.count var) ec.estate.pathConds →
  --     ∃ val, ec.estate.vars var = some val ∧ inp.2 = [val]))

/-- The main invariant for proving forward simulation of compilation. -/
def SimR (ec : Seq.Config Op χ V S m n) (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  SimR.Basic _ _ _ _ ec pc ∧
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
      SimR.CtxCurrent _ _ _ _ ec expr ctxCurrent ∧
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
  AtomicProcs.IsDAG Op _ V ((compileFn Op χ V S fn).atoms.tail) := sorry

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
    (ChanBuf.empty (ChanName χ) (compileExpr.varName χ definedVars pathConds var))
  = ChanBuf.empty (ChanName χ) (compileExpr.varName χ definedVars pathConds var) := sorry

@[simp]
theorem buf_push_tail_args_to_singleton_var :
  ChanBuf.push (ChanName χ)
    (compileExpr.tailArgs χ pathConds) vals
    (ChanBuf.singleton (ChanName χ) (compileExpr.varName χ definedVars pathConds var) val)
  = ChanBuf.singleton (ChanName χ) (compileExpr.varName χ definedVars pathConds var) val := sorry

@[simp]
theorem buf_push_ret_chans_to_singleton_var :
  ChanBuf.push (ChanName χ)
    (compileExpr.retChans χ pathConds) vals
    (ChanBuf.singleton (ChanName χ) (compileExpr.varName χ definedVars pathConds var) val)
  = ChanBuf.singleton (ChanName χ) (compileExpr.varName χ definedVars pathConds var) val := sorry

@[simp]
theorem buf_push_tail_cond_to_empty_vars :
  ChanBuf.push (ChanName χ)
    #v[ChanName.tail_cond pathConds] #v[val]
    (ChanBuf.empty (ChanName χ) (compileExpr.varName χ definedVars pathConds var))
  = ChanBuf.empty (ChanName χ) (compileExpr.varName χ definedVars pathConds var) := sorry

@[simp]
theorem bufs_push_tail_args_to_empty_vars :
  ChanBufs.push (ChanName χ)
    (compileExpr.tailArgs χ pathConds) vals
    (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ definedVars pathConds vars))
  = ChanBufs.empty (ChanName χ) (compileExpr.varNames χ definedVars pathConds vars) := sorry

@[simp]
theorem bufs_push_tail_cond_to_empty_vars :
  ChanBufs.push (ChanName χ)
    #v[ChanName.tail_cond pathConds] #v[val]
    (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ definedVars pathConds vars))
  = ChanBufs.empty (ChanName χ) (compileExpr.varNames χ definedVars pathConds vars) := sorry

@[simp]
theorem bufs_push_ret_chans_to_empty_var :
  ChanBufs.push (ChanName χ)
    (compileExpr.retChans χ pathConds) vals
    (ChanBufs.empty (ChanName χ) (compileExpr.varNames χ definedVars pathConds vars))
  = ChanBufs.empty (ChanName χ) (compileExpr.varNames χ definedVars pathConds vars) := sorry

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
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hbr : ec.expr = .cont (.br cond left right)) :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ ec' pc' := by
  have ⟨
    ⟨heq_states, hmatch_global, hdefined_vars⟩,
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
  have ⟨hwf, hmatch, hlive_vars⟩ := hcurrent
  simp only [compileExpr] at hmatch
  -- Deduce the structure of `ctxCurrent` from `hmatch`
  have ⟨steer₁, ctxCurrent₁, hctxCurrent₁, hmatch_steer₁, hmatch_ctxCurrent₁⟩ :=
    aps_match_commutes_with_cons _ _ _ hmatch
  have ⟨steer₂, ctxCurrent₂, hctxCurrent₂, hmatch_steer₂, hmatch_ctxCurrent₂⟩ :=
    aps_match_commutes_with_cons _ _ _ hmatch_ctxCurrent₁
  have ⟨forward, ctxCurrent₃, hctxCurrent₃, hmatch_forward, hmatch_ctxCurrent₃⟩ :=
    aps_match_commutes_with_cons _ _ _ hmatch_ctxCurrent₂
  have ⟨ctxCurrent₄, merge, hctxCurrent₄, hmatch_ctxCurrent₄, hmatch_merge⟩ := aps_match_commutes_with_append _ _ _ _ [_] hmatch_ctxCurrent₃
  simp at hmatch_ctxCurrent₄
  have ⟨leftBr, rightBr, hctxCurrent₅, hleftBr, hrightBr⟩ := aps_match_commutes_with_append _ _ _ _ _ hmatch_ctxCurrent₄
  -- Deduce some facts from `hstep`
  cases hstep with
  | step_ret hexpr => simp [hbr] at hexpr
  | step_tail hexpr => simp [hbr] at hexpr
  | step_op hexpr => simp [hbr] at hexpr
  | step_br hexpr hcond =>
    rename_i condVal _ _ cond'
    simp [hbr] at hexpr
    have heq_cond' := hexpr.1
    subst heq_cond'
    simp [VarMap.getVar] at hcond
    have hcond_defined : cond ∈ ec.estate.definedVars := by
      apply (hdefined_vars cond).mpr
      simp [hcond]
    if hcondVal : Interp.asBool Op S condVal then
      -- Run the first steer
      simp [AtomicProc.MatchModBuffers] at hmatch_steer₁
      have ⟨deciderBuf, inputBufs, hsteer₁⟩ := ap_match_steer_destruct _ _ _ hmatch_steer₁
      -- Reorder stuff to single out steer₁
      have hatom' : pc.proc.atoms =
        (compileFn.initCarry _ _ _ ec.estate.fn carryInLoop :: ctxLeft) ++
        [steer₁] ++
        ([steer₂, forward] ++ leftBr ++ rightBr ++ merge ++ ctxRight) := by grind
      -- Deduce the value of `deciderBuf`
      have hdeciderBuf : deciderBuf = [condVal] := by
        have : steer₁ ∈ ctxCurrent := by grind
        have := hlive_vars steer₁ this
          (ChanBuf.withBuf (ChanName χ) deciderBuf
            (compileExpr.varName χ ec.estate.definedVars ec.estate.pathConds cond))
        simp [hsteer₁] at this
        have := this.2 cond hcond_defined
        simp [ChanBuf.withBuf, compileExpr.varName, hcond] at this
        exact this
      -- Deduce the values of `inputBufs`
      have ⟨inputVals, hinputVals⟩ :
        ∃ inputVals : Vector V ec.estate.definedVars.eraseDups.length,
          ec.estate.definedVars.eraseDups.mapM ec.estate.vars
          = some inputVals.toList
      := sorry
      have hinputBufs :
        ChanBufs.withBufs (ChanName χ) inputBufs (compileExpr.allDefinedVars χ ec.estate.definedVars ec.estate.pathConds)
        = ChanBufs.singleton (ChanName χ)
            (compileExpr.allDefinedVars χ ec.estate.definedVars ec.estate.pathConds)
            inputVals
      := sorry
      simp only [hinputBufs] at hsteer₁
      have hdeciderBufPop :
        ChanBuf.pop _
          (ChanBuf.withBuf (ChanName χ) deciderBuf (compileExpr.varName χ ec.estate.definedVars ec.estate.pathConds cond))
        = some (condVal, ChanBuf.empty (ChanName χ) (compileExpr.varName χ ec.estate.definedVars ec.estate.pathConds cond))
      := sorry
      have hinputBufsPop :
        ChanBufs.pop _
          (ChanBufs.singleton (ChanName χ) (compileExpr.allDefinedVars χ ec.estate.definedVars ec.estate.pathConds) inputVals)
        = some (inputVals, ChanBufs.empty (ChanName χ) (compileExpr.allDefinedVars χ ec.estate.definedVars ec.estate.pathConds))
      := sorry
      -- split at hmatch_steer₁
      -- any_goals contradiction
      simp only [hsteer₁] at hatom'
      -- Do the step
      have := @Config.Step.step_steer Op (ChanName χ) _ _ _ _ instInterp _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hatom' hdeciderBufPop hinputBufsPop
      simp only [compileFn.initCarry, hcondVal] at this
      sorry
    else
      sorry

theorem sim_step
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ ec pc)
  (hstep : Config.Step Op χ V S ec ec') :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ ec' pc' := by
  sorry

end Wavelet.Simulation
