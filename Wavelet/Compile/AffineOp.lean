import Wavelet.Seq
import Wavelet.Dataflow

import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Prog.Defs
import Wavelet.Compile.MapChans

namespace Wavelet.Seq

open Semantics

/-- Usage of a subset of operators is affine. -/
inductive Expr.AffineInrOp [Arity Op₁] [Arity Op₂]
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
      AffineInrOp (used₁ ++ used₂) (.br cond left right)

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
  := ∀ {depOp inputs inputs' outputs outputs'},
    .op (.inr depOp) inputs outputs ∈ aps →
    .op (.inr depOp) inputs' outputs' ∈ aps →
    inputs = inputs' ∧ outputs = outputs' ∧ depOp ∈ usedOps

/-- Usage of a subset of operators is affine. -/
def Proc.AffineInrOp
  [Arity Op₁] [Arity Op₂]
  (proc : Proc (Op₁ ⊕ Op₂) χ V m n) : Prop
  := ∀ {depOp inputs inputs' outputs outputs'},
    .op (.inr depOp) inputs outputs ∈ proc.atoms →
    .op (.inr depOp) inputs' outputs' ∈ proc.atoms →
    inputs = inputs' ∧ outputs = outputs'

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow Fn

/-- `compileExpr` preserves `AffineInrOp`. -/
theorem compile_expr_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  [DecidableEq χ]
  [InterpConsts V]
  {expr : Expr (Op₁ ⊕ Op₂) χ m n}
  (haff : expr.AffineInrOp usedOps)
  : (compileExpr (V := V) hnz definedVars pathConds expr).AffineInrOp usedOps
  := by
  induction expr generalizing definedVars pathConds usedOps with
  | ret => simp [compileExpr, AtomicProcs.AffineInrOp]
  | tail => simp [compileExpr, AtomicProcs.AffineInrOp]
  | op o args rets cont ih =>
    cases o with
    | inl op₁ =>
      cases haff with | aff_op_inl haff =>
      simp [compileExpr, AtomicProcs.AffineInrOp]
      intros
      rename_i hmem₁ hmem₂
      exact ih (hnz := hnz) haff hmem₁ hmem₂
    | inr op₂ =>
      cases haff with | aff_op_inr hnot_mem haff =>
      simp [compileExpr, AtomicProcs.AffineInrOp]
      intros depOp
      intros
      rename_i hmem₁ hmem₂
      cases hmem₁ <;> cases hmem₂
      · rename_i hmem₁ hmem₂
        have ⟨h₁, h₂, h₃⟩ := hmem₁
        have ⟨_, h₂', h₃'⟩ := hmem₂
        simp [← h₁] at hnot_mem
        simp [hnot_mem]
        have := HEq.trans h₂ h₂'.symm
        simp at this
        simp [this]
        have := HEq.trans h₃ h₃'.symm
        simp at this
        simp [this]
        assumption
      · rename_i hmem₁ hmem₂
        have := ih (hnz := hnz) haff hmem₂ hmem₂
        simp [hmem₁.1] at this
        exact False.elim (hnot_mem this)
      · rename_i hmem₁ hmem₂
        have := ih (hnz := hnz) haff hmem₁ hmem₁
        simp [hmem₂.1] at this
        exact False.elim (hnot_mem this)
      · rename_i hmem₁ hmem₂
        simp [ih (hnz := hnz) haff hmem₁ hmem₂]
  | br cond left right ih₁ ih₂ =>
    cases haff with | aff_br haff₁ haff₂ hdisj
    simp [compileExpr, AtomicProcs.AffineInrOp, compileExpr.branchMerge]
    intros
    rename_i hmem₁ hmem₂
    cases hmem₁ <;> cases hmem₂
    any_goals
      rename_i hmem₁ hmem₂
      simp [AtomicProc.switch] at hmem₁ hmem₂
    cases hmem₁ <;> cases hmem₂
    · rename_i hmem₁ hmem₂
      simp [ih₁ (hnz := hnz) haff₁ hmem₁ hmem₂]
    · rename_i hmem₁ hmem₂
      have ⟨_, _, h₁⟩ := ih₁ (hnz := hnz) haff₁ hmem₁ hmem₁
      have ⟨_, _, h₂⟩ := ih₂ (hnz := hnz) haff₂ hmem₂ hmem₂
      exact False.elim (hdisj h₁ h₂)
    · rename_i hmem₂ hmem₁
      have ⟨_, _, h₁⟩ := ih₁ (hnz := hnz) haff₁ hmem₁ hmem₁
      have ⟨_, _, h₂⟩ := ih₂ (hnz := hnz) haff₂ hmem₂ hmem₂
      exact False.elim (hdisj h₁ h₂)
    · rename_i hmem₁ hmem₂
      have := ih₂ (hnz := hnz) haff₂ hmem₁ hmem₂
      simp [ih₂ (hnz := hnz) haff₂ hmem₁ hmem₂]

/-- `compileFn` preserves `AffineInrOp`. -/
theorem compile_fn_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  [DecidableEq χ]
  [InterpConsts V]
  {fn : Fn (Op₁ ⊕ Op₂) χ V m n}
  (haff : fn.AffineInrOp)
  : (compileFn hnz fn).AffineInrOp
  := by
  have ⟨used, haff_body⟩ := haff
  have : (compileFn.bodyComp hnz fn).AffineInrOp used
    := compile_expr_preserves_aff_op haff_body
  simp [compileFn, compileFn.initCarry, compileFn.resultSteers,
    Proc.AffineInrOp]
  simp [AtomicProcs.AffineInrOp] at this
  simp [AtomicProc.carry, AtomicProc.steer]
  grind only

theorem map_chans_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  {f : χ → χ'}
  {proc : Proc (Op₁ ⊕ Op₂) χ V m n}
  (haff : proc.AffineInrOp) : (proc.mapChans f).AffineInrOp
  := by
  simp [Proc.mapChans, Proc.AffineInrOp]
  intros depOp inputs inputs' outputs outputs' hmem hmem'
  simp [AtomicProcs.mapChans] at hmem hmem'
  have ⟨ap, hmem_ap, hmap_ap⟩ := hmem
  have ⟨ap', hmem_ap', hmap_ap'⟩ := hmem'
  cases ap <;> simp [AtomicProc.mapChans] at hmap_ap
  cases ap' <;> simp [AtomicProc.mapChans] at hmap_ap'
  have ⟨h₁, h₂, h₃⟩ := hmap_ap
  subst h₁
  have ⟨h₁', h₂', h₃'⟩ := hmap_ap'
  subst h₁'
  simp at h₂ h₃ h₂' h₃'
  subst h₂ h₃ h₂' h₃'
  simp [haff hmem_ap hmem_ap']

end Wavelet.Compile
