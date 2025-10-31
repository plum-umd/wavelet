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

theorem Prog.step_star_unfold
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {tr : Trace (Label Op V (sigs i).ι (sigs i).ω)}
  {s : (prog.semantics i).S}
  (hsteps : (prog.semantics i).lts.Star (prog.semantics i).init tr s) :
    ((prog i).semantics.link (Prog.semantics prog ·.toFin)).lts.Star
      (LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin))
      tr (Prog.unfoldState s)
  := by

  sorry

theorem Prog.is_invariant_unfold
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {Inv : (prog.semantics i).S → Prop}
  (h : ((prog i).semantics.link (Prog.semantics prog ·.toFin)).IsInvariant (Inv ∘ Prog.foldState)) :
    (prog.semantics i).IsInvariant Inv
  := by
  intros s tr hsteps
  rw [← Prog.state_fold_unfold_eq s] at hsteps ⊢
  replace hsteps := Prog.step_star_unfold hsteps
  have := h hsteps
  simp at this
  simp [this]

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
  {prog : Prog Op χ V sigs}
  (i : Fin k) :
    (prog.semantics i).IsInvariant Prog.InvConstProg
  := by
  apply Prog.is_invariant_unfold
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
  -- apply link_inv
  -- · sorry
  -- -- simp [IsInvariant, IsInvariantAt, Lts.IsInvariantAt]
  -- -- simp [Prog.InvConstProg'.heq]
  -- -- rw [Prog.semantics]
  -- sorry

-- theorem Prog.inv_const_prog
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {sigs : Sigs k}
--   {prog : Prog Op χ V sigs}
--   (i : Fin k) :
--     (Semantics.link (prog i).semantics (Prog.semantics prog ·.toFin)).IsInvariant
--       (LinkInv (λ s => s.fn = prog i) (λ depOp s => (Prog.castState s).mainState.fn = prog (depOp.toFin)))
--   := by
--   -- apply Prog.semantics_induction (motive := λ i sem => sem.IsInvariant Prog.InvConstProg)
--   -- -- have := Prog.semantics_induction (motive := λ i sem => True)
--   -- induction i using Prog.semantics_induction with
--   -- | _ =>
--   --   sorry
--   -- apply link_inv
--   -- · exact Fn.inv_const_fn
--   -- · intros op
--   --   apply Prog.inv_const_prog
--   --   sorry

--   rcases i with ⟨i, hlt⟩
--   induction i using Nat.strong_induction_on with
--   | _ i ih =>
--     apply link_inv
--     · exact Fn.inv_const_fn
--     · intros depOp
--       have : IsInvariantAt _ _ _ := ih depOp.toFin (by simp) (by omega)

--       have : (Semantics.link (prog depOp.toFin).semantics (Prog.semantics prog ·.toFin)).IsInvariant
--         fun s => s.mainState.fn = prog depOp.toFin
--         := sorry

--       sorry

--   --   sorry
--     -- apply Lts.IsInvariantAt.by_induction
--     -- · simp [Prog.InvConstProg]
--     --   constructor
--     --   · rw [Prog.semantics_init, LinkState.init]
--     --     simp [Fn.semantics, Config.init]
--     --   · intros depOp
--     --     rw [Prog.semantics_init, LinkState.init]
--     --     simp [Fn.semantics, Config.init]
--     --     have : Semantics.IsInvariant _ _ := ih depOp.toFin (by simp) (by omega)
--     --     have := this.base.1
--     --     exact this
--     -- · intros s₁ s₂ l hinv hstep
--     --   -- generalize hsem : prog.semantics ⟨i, hlt⟩ = sem
--     --   -- rw [← hsem] at hstep
--     --   rw [Prog.semantics]
--     --   sorry

end Wavelet.Seq
