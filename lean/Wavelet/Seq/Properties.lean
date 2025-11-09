import Wavelet.Seq.Prog

/-! Some useful properties and invariants of the sequential semantics. -/

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

/-- Unfolded version of `Prog.InvInitDeps`. -/
def Prog.InvInitDeps'
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} : ((prog i).semantics.link (Prog.semantics prog ·.toFin)).S → Prop
  := λ s => ∀ depOp,
    (s.curSem = none ∨ s.curSem ≠ some depOp) →
    s.depStates depOp = (Prog.semantics prog (depOp.toFin)).init

def Prog.InvInitDeps
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} : (prog.semantics i).S → Prop
  := Prog.InvInitDeps' ∘ Prog.unfoldState

theorem Fn.semantics_output_init
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {fn : Fn Op χ V m n}
  {outputVals : Vector V n}
  {s s' : fn.semantics.S}
  (hstep : Config.Step s (.output outputVals) s')
  (hfn : s.fn = fn) :
    s' = Seq.Config.init fn
  := by
  cases hstep
  simp [Seq.Config.init, hfn]

/-- When the main function is executing, all other
dependencies are in their initial states. -/
theorem Prog.inv_init_deps
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  (prog : Prog Op χ V sigs)
  (i : Fin k) :
    (prog.semantics i).IsInvariant Prog.InvInitDeps
  := by
  apply Prog.unfold_is_invariant
  apply Lts.IsInvariantAt.by_strong_induction
  · simp [InvInitDeps, InvInitDeps', link, LinkState.init]
  · intros s₁ s₂ l tr hpref hinv hstep
    simp [InvInitDeps, InvInitDeps', link, LinkState.init] at hinv ⊢
    simp [link] at hstep
    cases hstep with
    | step_main => exact hinv
    | step_dep hcur_sem =>
      simp [hcur_sem]
      intros depOp' hne
      simp [Ne.symm hne]
      apply hinv
      right
      simp [hcur_sem, hne]
    | step_dep_spawn hcur_sem =>
      simp
      intros depOp' hne
      simp [Ne.symm hne]
      apply hinv
      simp [hcur_sem]
    | step_dep_ret hcur_sem hstep_dep hstep_main =>
      rename SigOps sigs _ => depOp
      rename (prog.semantics depOp.toFin).S => depState'
      simp
      intros depOp'
      by_cases heq : depOp' = depOp
      · -- After the last `output` step, the state of `depOp`
        -- should be reset to init by `Fn.semantics_output_init`
        subst heq
        simp
        have hstep_dep' := Prog.unfold_step hstep_dep
        generalize hs' : unfoldState (s₁.depStates depOp') = s'
        generalize hs'' : unfoldState depState' = s''
        rw [hs', hs''] at hstep_dep'
        cases hstep_dep' with
        | step_main hcur_sem hpass hstep_dep'' =>
          cases hpass
          simp [Fn.semantics] at hstep_dep''
          -- Obtain `heq_prog` from another invariant above (`Prog.inv_const_prog`)
          have ⟨_, hpref'⟩ := link_star_to_dep_star hpref depOp'
          have hconst_prog : IsInvariant _ _ := Prog.inv_const_prog prog depOp'.toFin
          specialize hconst_prog hpref'
          have heq_prog : s'.mainState.fn = prog depOp'.toFin := by
            rw [InvConstProg] at hconst_prog
            simp only [SigOps.toFin, Fin.coe_castSucc, Fin.coe_castLT,
              Function.comp_apply] at hconst_prog
            rw [hs'] at hconst_prog
            rw [InvConstProg', LinkInv] at hconst_prog
            have ⟨h₁, _⟩ := hconst_prog
            exact h₁.base
          -- Since the last step is an output step in the dependency (depOp)
          -- we know that by the `Fn` semantics, the resulting state must
          -- be an initial state.
          have := Fn.semantics_output_init hstep_dep'' heq_prog
          rw [← Prog.state_fold_unfold_eq depState']
          rw [hs'', this, hcur_sem]
          rw [← Prog.fold_init]
          congr 1
          simp [LinkState.init, Fn.semantics]
          -- Call IH to prove that `depOp`'s own dependencies are
          -- also in their initial states.
          have ih : IsInvariant _ _ := Prog.inv_init_deps prog depOp'.toFin
          specialize ih hpref'
          simp only [InvInitDeps, SigOps.toFin, Fin.coe_castSucc, Fin.coe_castLT,
            Function.comp_apply, InvInitDeps', ne_eq] at ih
          rw [hs', hcur_sem] at ih
          simp at ih
          funext depOp''
          apply ih
        | step_dep _ hpass => cases hpass
      · simp [heq]
        apply hinv
        right
        simp [hcur_sem, Ne.symm heq]

/-- As a consequence of the invariants above (`inv_const_prog`
and `inv_init_deps`), if a program semantics makes an output step,
the resulting state is going to be identical to the initial state. -/
theorem Prog.output_init
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {outputVals : Vector V (sigs i).ω}
  {sem : Semantics Op V (sigs i).ι (sigs i).ω}
  (hsem : sem = prog.semantics i)
  {s s' : sem.S}
  {tr : Trace (Label Op V (sigs i).ι (sigs i).ω)}
  (hinit : sem.lts.Star sem.init tr s)
  (hstep : sem.lts.Step s (.output outputVals) s') :
    s' = sem.init
  := by
  unfold Prog.semantics at hsem
  subst hsem
  have heq_fn : s.mainState.fn = prog i := by
    have hinv : IsInvariant _ _ := Prog.inv_const_prog prog i
    rw [← Prog.state_unfold_fold_eq s] at hinit
    have := Prog.fold_star hinit
    have := hinv this
    simp [Prog.InvConstProg] at this
    rw [Prog.InvConstProg', LinkInv] at this
    have ⟨h₁, _⟩ := this
    exact h₁.base
  have hinit_deps :
    s.curSem = none →
    ∀ depOp,
      s.depStates depOp = (prog.semantics depOp.toFin).init := by
    have hinv : IsInvariant _ _ := Prog.inv_init_deps prog i
    rw [← Prog.state_unfold_fold_eq s] at hinit
    have := Prog.fold_star hinit
    have := hinv this
    simp [Prog.InvInitDeps] at this
    rw [Prog.InvInitDeps'] at this
    intros hcur_sem
    simp [hcur_sem] at this
    exact this
  rcases i with ⟨i, hlt⟩
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases hstep with
    | step_main hcur_sem hpass hstep =>
      cases hpass
      have := Fn.semantics_output_init hstep heq_fn
      simp [hcur_sem, this, link, LinkState.init, Fn.semantics]
      funext depOp
      simp [hinit_deps hcur_sem]
    | step_dep _ hpass => cases hpass

end Wavelet.Seq
