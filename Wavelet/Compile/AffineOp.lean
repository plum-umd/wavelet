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
  | aff_ret : AffineInrOp used (.ret vars)
  | aff_tail : AffineInrOp used (.tail vars)
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
      AffineInrOp used left →
      AffineInrOp used right →
      AffineInrOp used (.br cond left right)

def Fn.AffineInrOp [Arity Op₁] [Arity Op₂]
  (fn : Fn (Op₁ ⊕ Op₂) χ V m n) : Prop := fn.body.AffineInrOp []

def Prog.AffineInrOp [Arity Op]
  (prog : Prog Op χ V sigs) : Prop := ∀ i, (prog i).AffineInrOp

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics

/-- Usage of a subset of operators is affine. -/
def Proc.AffineInrOp
  [Arity Op₁] [Arity Op₂]
  (proc : Proc (Op₁ ⊕ Op₂) χ V m n) : Prop
  := ∀ depOp inputs inputs' outputs outputs',
    .op (.inr depOp) inputs outputs ∈ proc.atoms →
    .op (.inr depOp) inputs' outputs' ∈ proc.atoms →
    inputs = inputs' ∧ outputs = outputs'

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow Fn

/-- `compileFn` preserves `AffineInrOp`. -/
theorem compile_fn_preserves_aff_op
  [Arity Op₁] [Arity Op₂]
  [DecidableEq χ]
  [InterpConsts V]
  {fn : Fn (Op₁ ⊕ Op₂) χ V m n}
  (haff : fn.AffineInrOp)
  : (compileFn hnz fn).AffineInrOp
  := sorry

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
  simp [haff _ _ _ _ _ hmem_ap hmem_ap']

end Wavelet.Compile
