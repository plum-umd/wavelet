import Wavelet.Seq.Prog

/-! Some useful invariants of the sequential semantics. -/

namespace Wavelet.Seq

open Semantics

theorem Fn.inv_const_fn
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {fn : Fn Op χ V m n} :
    fn.semantics.IsInvariant (λ s => s.fn = fn)
  := by
  apply Lts.IsInvariantAt.by_induction
  · simp [Fn.semantics, Config.init]
  · intros s₁ s₂ l hinv hstep
    cases hstep <;> simp [hinv]

/-- Unfolded version of `Prog.InvConstProg`. -/
def Prog.InvConstProg'
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} : ((prog i).semantics.link (Prog.semantics prog ·.toFin)).S → Prop
  := LinkInv
    (λ s => s.fn = prog i)
    (λ op s => Prog.InvConstProg' (Prog.unfoldState s))

def Prog.InvConstProg
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} : (prog.semantics i).S → Prop
  := Prog.InvConstProg' ∘ Prog.unfoldState

theorem Prog.inv_const_prog
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  (prog : Prog Op χ V sigs)
  (i : Fin k) :
    (prog.semantics i).IsInvariant Prog.InvConstProg
  := by
  apply Prog.unfold_is_invariant
  exact Lts.IsInvariantAt.imp
    (by
      intros s hinv
      simp [InvConstProg] at hinv ⊢
      rw [InvConstProg']
      exact hinv)
    (link_inv
      (main := (prog i).semantics)
      (deps := (Prog.semantics prog ·.toFin))
      (mainInv := λ s => s.fn = prog i)
      (depInvs := λ op => Prog.InvConstProg)
      Fn.inv_const_fn
      (by
        intros depOp
        apply Prog.inv_const_prog))

end Wavelet.Seq
