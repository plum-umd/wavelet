import Wavelet.Seq.Prog
import Wavelet.Dataflow.Proc

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Prog.Defs
import Wavelet.Compile.MapChans

namespace Wavelet.Seq

open Semantics

/-- Usage of a subset of operators is affine. -/
inductive Expr.AffineInrOp
  [Arity Op₁] [Arity Op₂]
  : List Op₂ → Expr (Op₁ ⊕ Op₂) χ m n → Prop where
  | aff_ret : AffineInrOp [] (.ret vars)
  | aff_tail : AffineInrOp [] (.tail vars)
  | aff_op_inl
      {op : Op₁}
      {args : Vector χ (Arity.ι op)}
      {rets : Vector χ (Arity.ω op)}
      {cont : Expr (Op₁ ⊕ Op₂) χ m n} :
      AffineInrOp used cont →
      AffineInrOp used (.op (.inl op) args rets cont)
  | aff_op_inr
      {op : Op₂}
      {args : Vector χ (Arity.ι op)}
      {rets : Vector χ (Arity.ω op)}
      {cont : Expr (Op₁ ⊕ Op₂) χ m n} :
      op ∉ used →
      AffineInrOp used cont →
      AffineInrOp (op :: used) (.op (.inr op) args rets cont)
  | aff_br :
      AffineInrOp used₁ left →
      AffineInrOp used₂ right →
      used₁.Disjoint used₂ →
      AffineInrOp (used₁ ++ used₂) (.br c left right)

def Fn.AffineInrOp [Arity Op₁] [Arity Op₂]
  (fn : Fn (Op₁ ⊕ Op₂) χ V m n) : Prop :=
  ∃ used, fn.body.AffineInrOp used

def Prog.AffineInrOp [Arity Op]
  (prog : Prog Op χ V sigs) : Prop := ∀ i, (prog i).AffineInrOp

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics

def AtomicProcs.AffineInrOp
  [Arity Op₁] [Arity Op₂]
  (aps : AtomicProcs (Op₁ ⊕ Op₂) χ V)
  (usedOps : List Op₂) : Prop
  :=
    (∀ {depOp inputs outputs},
      .op (.inr depOp) inputs outputs ∈ aps → depOp ∈ usedOps) ∧
    (∀ {i j : Nat} {depOp inputs outputs depOp' inputs' outputs'},
      i ≠ j →
      (_ : i < aps.length) →
      (_ : j < aps.length) →
      aps[i] = .op (.inr depOp) inputs outputs →
      aps[j] = .op (.inr depOp') inputs' outputs' →
      depOp ≠ depOp')

/-- Usage of a subset of operators is affine. -/
def Proc.AffineInrOp
  [Arity Op₁] [Arity Op₂]
  (proc : Proc (Op₁ ⊕ Op₂) χ V m n) : Prop
  := ∀ {i j : Nat} {depOp inputs outputs depOp' inputs' outputs'},
    i ≠ j →
    (_ : i < proc.atoms.length) →
    (_ : j < proc.atoms.length) →
    proc.atoms[i] = .op (.inr depOp) inputs outputs →
    proc.atoms[j] = .op (.inr depOp') inputs' outputs' →
    depOp ≠ depOp'

theorem Proc.AffineInrOp.of_mem
  [Arity Op₁] [Arity Op₂]
  {depOp inputs inputs' outputs outputs'}
  {proc : Proc (Op₁ ⊕ Op₂) χ V m n}
  (haff : proc.AffineInrOp)
  (hmem₁ : .op (.inr depOp) inputs outputs ∈ proc.atoms)
  (hmem₂ : .op (.inr depOp) inputs' outputs' ∈ proc.atoms) :
    inputs = inputs' ∧ outputs = outputs'
  := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem₁
  have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem₂
  by_cases hne : i = j
  · subst hne
    simp [hget_i] at hget_j
    exact hget_j
  · have := haff hne hi hj hget_i hget_j
    simp at this

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow Fn

/- TODO: Fix proof performance -/
set_option maxHeartbeats 500000

/--
`compileExpr` preserves `AffineInrOp`.
-/
theorem compile_expr_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  [DecidableEq χ]
  [InterpConsts V]
  [NeZero m] [NeZero n]
  {expr : Expr (Op₁ ⊕ Op₂) χ m n}
  (haff : expr.AffineInrOp usedOps) :
    (compileExpr (V := V) definedVars pathConds expr).AffineInrOp usedOps
  := by
  -- induction expr generalizing definedVars pathConds usedOps with
  cases expr with
  | ret =>
    simp [compileExpr, AtomicProcs.AffineInrOp,
      AtomicProc.forwardc, AtomicProc.sink]
    grind only [= Vector.toArray_map, = List.getElem_cons, = Vector.toArray_empty,
      → Array.eq_empty_of_map_eq_empty, =_ Vector.toList_toArray, = List.length_nil,
      = List.length_cons, cases Or]
  | tail =>
    simp [compileExpr, AtomicProcs.AffineInrOp,
      AtomicProc.forwardc, AtomicProc.sink]
    grind only [= Vector.toArray_map, = List.getElem_cons, = Vector.toArray_empty,
      → Array.eq_empty_of_map_eq_empty, =_ Vector.toList_toArray, = List.length_nil,
      = List.length_cons, cases Or]
  | op o args rets cont =>
    cases o with
    | inl op₁ =>
      cases haff with | aff_op_inl haff =>
      simp [compileExpr]
      have ih := compile_expr_preserves_aff_op
        (V := V) (expr := cont)
        (definedVars := definedVars.removeAll args.toList ++ rets.toList)
        (pathConds := pathConds)
        haff
      grind only [= List.getElem_cons, = List.mem_cons, =_ Vector.toList_toArray,
        = List.length_cons, AtomicProcs.AffineInrOp, usr List.length_pos_of_mem,
        usr List.getElem_mem, usr List.eq_or_mem_of_mem_cons, cases Or]
    | inr op₂ =>
      cases haff with | aff_op_inr hnot_mem haff =>
      have ih := compile_expr_preserves_aff_op
        (V := V) (expr := cont)
        (definedVars := definedVars.removeAll args.toList ++ rets.toList)
        (pathConds := pathConds)
        haff
      simp [compileExpr]
      grind only [= List.getElem_cons, = List.mem_cons, = List.getElem_cons_zero,
        =_ Vector.toList_toArray, = List.length_cons, AtomicProcs.AffineInrOp,
        usr List.length_pos_of_mem, usr List.getElem_mem, usr List.eq_or_mem_of_mem_cons, cases Or]
  | br c left right =>
    cases haff with | aff_br haff₁ haff₂ hdisj
    simp [compileExpr, AtomicProcs.AffineInrOp, compileExpr.branchMerge]
    have ih₁ := compile_expr_preserves_aff_op
      (V := V) (expr := left)
      (definedVars := definedVars.removeAll [c])
      (pathConds := (true, .var c pathConds) :: pathConds)
      haff₁
    have ih₂ := compile_expr_preserves_aff_op
      (V := V) (expr := right)
      (definedVars := definedVars.removeAll [c])
      (pathConds := (false, .var c pathConds) :: pathConds)
      haff₂
    constructor
    · intros _ _ _ hop
      grind only [usr List.length_filter_le, = List.removeAll_nil, = List.removeAll_cons,
        =_ List.countP_eq_length_filter, = Vector.length_toList, =_ Vector.toList_toArray,
        AtomicProc.switch, = Vector.append_assoc_symm, = Vector.toArray_cast, = List.length_cons,
        = Vector.toList_mk, AtomicProcs.AffineInrOp, AtomicProc.fork, usr List.length_pos_of_mem,
        = List.size_toArray, = Vector.toArray_append, = Vector.append_assoc, AtomicProc.merge]
    · intros i j depOp inputs outputs depOp' inputs' outputs'
        hne hi hj hget_i hget_j
      simp [List.getElem_cons, List.getElem_append] at hget_i hget_j hi hj
      split_ifs at hget_i
      any_goals simp [AtomicProc.switch, AtomicProc.merge, AtomicProc.fork] at hget_i
      any_goals omega
      all_goals
        split_ifs at hget_j
        any_goals simp [AtomicProc.switch, AtomicProc.merge, AtomicProc.fork] at hget_j
        any_goals omega
      · exact ih₁.2 (by omega) (by omega) (by omega) hget_i hget_j
      · intros h; subst h
        have h₁ := ih₁.1 (List.mem_of_getElem hget_i)
        have h₂ := ih₂.1 (List.mem_of_getElem hget_j)
        exact False.elim (hdisj h₁ h₂)
      · intros h; subst h
        have h₁ := ih₁.1 (List.mem_of_getElem hget_j)
        have h₂ := ih₂.1 (List.mem_of_getElem hget_i)
        exact False.elim (hdisj h₁ h₂)
      · exact ih₂.2 (by omega) (by omega) (by omega) hget_i hget_j

/-- `compileFn` preserves `AffineInrOp`. -/
theorem compile_fn_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  [DecidableEq χ]
  [InterpConsts V]
  [NeZero m] [NeZero n]
  {fn : Fn (Op₁ ⊕ Op₂) χ V m n}
  (haff : fn.AffineInrOp) :
    (compileFn fn).AffineInrOp
  := by
  have ⟨used, haff_body⟩ := haff
  have ⟨_, haff_body⟩ : (compileFn.bodyComp fn).AffineInrOp used
    := compile_expr_preserves_aff_op haff_body
  simp [compileFn, compileFn.initCarry, compileFn.resultSteers,
    Proc.AffineInrOp]
  intros i j depOp inputs outputs depOp' inputs' outputs'
    hne hi hj hget_i hget_j
  simp [compileFn.bodyComp, List.getElem_cons, List.getElem_append] at hget_i hget_j hi hj
  split_ifs at hget_i
  any_goals simp [AtomicProc.carry, AtomicProc.fork, AtomicProc.steer] at hget_i
  all_goals
    split_ifs at hget_j
    any_goals simp [AtomicProc.carry, AtomicProc.fork, AtomicProc.steer] at hget_j
  any_goals omega
  grind only [=_ Vector.toList_toArray, usr List.length_pos_of_mem, usr List.getElem_mem, cases Or]

theorem map_chans_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  {f : χ → χ'}
  {proc : Proc (Op₁ ⊕ Op₂) χ V m n}
  (haff : proc.AffineInrOp) : (proc.mapChans f).AffineInrOp
  := by
  simp [Proc.mapChans, Proc.AffineInrOp]
  intros i j depOp inputs outputs depOp' inputs' outputs'
    hne hi hj hget_i hget_j
  simp [AtomicProcs.mapChans] at hi hj hget_i hget_j
  cases h₁ : proc.atoms[i] <;> cases h₂ : proc.atoms[j]
  case op.op =>
    rename_i op₁ inputs₁ outputs₁ op₂ inputs₂ outputs₂
    cases op₁ <;> cases op₂
      <;> simp [h₁, AtomicProc.mapChans] at hget_i
      <;> simp [h₂, AtomicProc.mapChans] at hget_j
    have := haff hne hi hj h₁ h₂
    simp [← hget_i.1, ← hget_j.1, this]
  any_goals simp [h₁, AtomicProc.mapChans] at hget_i
  any_goals simp [h₂, AtomicProc.mapChans] at hget_j

end Wavelet.Compile
