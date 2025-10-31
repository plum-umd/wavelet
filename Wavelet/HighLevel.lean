import Wavelet.Determinacy
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Typing

/-! Some high-level theorems and plans. -/

namespace Wavelet

open Semantics Determinacy Seq Dataflow Compile

/-- TODO -/
def ProgWithSpec.WellPermTyped
  [Arity Op] [PCM T]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  (progSpec : ProgSpec Op V T sigs)
  (prog : ProgWithSpec χ sigs opSpec) : Prop := sorry

/-- Well-typing induces a simulation between unguarded
and guarded semantics of `Prog`. -/
theorem sim_wt_prog
  [Arity Op]
  [InterpConsts V]
  [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ[PreservesInit] (prog.semantics i).guard (opSpec.Guard (progSpec i))
  := by sorry

/-- Final semantics of a sequential program when interpreted
with a specific operator interpretation. -/
abbrev Seq.Prog.semanticsᵢ
  {Op : Type u₁} {χ : Type u₂} {V : Type u₃}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {sigs : Sigs k}
  {opSpec : Determinacy.OpSpec Op V T}
  (prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs))
  (i : Fin k) :
    Semantics.{_, _, max u₁ u₂ u₃ w} Semantics.Empty V (sigs i).ι (sigs i).ω
  := ((prog.semantics i).guard opSpec.TrivGuard).interpret opInterp

/-- Final semantics of a dataflow program when interpreted
with a specific operator interpretation. -/
abbrev Dataflow.Proc.semanticsᵢ
  {Op : Type u₁} {χ : Type u₂} {V : Type u₃}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {opSpec : Determinacy.OpSpec Op V T}
  (proc : Proc (WithSpec Op opSpec) χ (V ⊕ T) (m + 1) (n + 1)) :
    Semantics.{_, _, max u₁ u₂ u₃ w} Semantics.Empty V m n
  := (proc.semantics.guard opSpec.TrivGuard).interpret opInterp

theorem compile_forward_sim_guarded
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (haff₁ : ∀ i, (prog i).AffineVar)
  (haff₂ : prog.AffineInrOp)
  (i : Fin k) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ[PreservesInit] (compileProg prog i).semantics.guard (opSpec.Guard (progSpec i))
  := by
  apply IORestrictedSimilaritySt.trans_preserves_init
  · exact sim_wt_prog prog hwt
  · apply sim_guard
    apply sim_compile_prog_preserves_init prog i haff₁ haff₂

theorem sim_guarded_unguarded
  [Arity Op] [PCM T]
  [InterpConsts V]
  {opSpec : OpSpec Op V T}
  {ioSpec : IOSpec V T m n}
  {sem : Semantics (WithSpec Op opSpec) (V ⊕ T) (m + 1) (n + 1)} :
    sem.guard (opSpec.Guard ioSpec) ≲ᵣ sem.guard opSpec.TrivGuard
  := by
  apply Lts.Similarity.refl_single
  intros s₁ l s₂ hstep
  apply Lts.IORestrictedStep.single
  simp [Semantics.guard]
  apply Lts.GuardStep.map_guard _ hstep
  exact opSpec.spec_guard_implies_triv_guard

theorem compile_forward_sim
  [Arity Op] [PCM T] [PCM.Lawful T]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}
  (prog : ProgWithSpec χ sigs opSpec)
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (haff₁ : ∀ i, (prog i).AffineVar)
  (haff₂ : prog.AffineInrOp)
  (i : Fin k) :
    (prog.semantics i).guard opSpec.TrivGuard
      ≲ᵣ (compileProg prog i).semantics.guard opSpec.TrivGuard
  := by
  apply IORestrictedSimilarity.trans
  · apply (compile_forward_sim_guarded prog hwt haff₁ haff₂ i).weaken (by simp)
  · apply sim_guarded_unguarded

theorem prog_semantics_output_init
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

theorem prog_semanticsᵢ_star_to_semantics_star
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {opSpec : OpSpec Op V T}
  {sigs : Sigs k}
  {prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs)}
  {i : Fin k}
  {s s' : (prog.semanticsᵢ i).S}
  {tr : Trace (Label Semantics.Empty V (sigs i).ι (sigs i).ω)}
  (hsteps : (prog.semanticsᵢ i).lts.Star s tr s') :
    ∃ tr', (prog.semantics i).lts.Star s.1 tr' s'.1
  := by
  simp [Prog.semanticsᵢ] at hsteps
  have ⟨_, hsteps⟩ := Lts.InterpStep.star_to_base_star hsteps
  have := Lts.GuardStep.star_to_base_star hsteps
  exact this

/-- After an output step, the program configuration becomes the initial configuration -/
theorem prog_semanticsᵢ_output_init
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {opSpec : OpSpec Op V T}
  {sigs : Sigs k}
  {prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs)}
  {i : Fin k}
  {s s' : (prog.semanticsᵢ i).S}
  {tr : Trace (Label Semantics.Empty V (sigs i).ι (sigs i).ω)}
  (hinit : (prog.semanticsᵢ i).lts.Star (prog.semanticsᵢ i).init tr s)
  {outputVals : Vector V (sigs i).ω}
  (hstep : (prog.semanticsᵢ i).lts.Step s (.output outputVals) s') :
    s'.1 = (prog.semanticsᵢ i).init.1
  := by
  simp [Semantics.interpret, Semantics.guard] at hstep ⊢
  cases hstep with | step_output hstep =>
  cases hstep with | step hguard hstep =>
  cases hguard
  have ⟨_, hinit'⟩ := prog_semanticsᵢ_star_to_semantics_star hinit
  exact prog_semantics_output_init rfl hinit' hstep

theorem compile_strong_norm
  {Op V T : Type u}
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}
  -- Required properties on the operator interpretation
  (hconfl : opSpec.Confluent opInterp)
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)
  -- Program with well-formedness and typing properties
  (prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs))
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (haff₁ : ∀ (i : Fin k), (prog i).AffineVar)
  (haff₂ : prog.AffineInrOp)
  (i : Fin k)
  -- Same inputs and outputs
  {args : Vector V (sigs i).ι}
  {outputVals : Vector V (sigs i).ω}
  -- Compiled dataflow graph
  {proc : Proc (WithSpec Op opSpec) (LinkName (ChanName χ)) (V ⊕ T) _ _}
  (hcomp : proc = compileProg prog i)
  {s s₁ s₂ : (prog.semanticsᵢ i).S}
  {s' : proc.semanticsᵢ.S}
  -- There exists a terminating trace in the sequential semantics
  (hinputs : (prog.semanticsᵢ i).lts.Step (prog.semanticsᵢ i).init (.input args) s)
  (htrace : (prog.semanticsᵢ i).lts.TauStarN .τ k s s₁)
  (hterm : (prog.semanticsᵢ i).lts.IsFinalFor (·.isSilent) s₁)
  (houtput : (prog.semanticsᵢ i).lts.Step s₁ (.output outputVals) s₂)
  -- Initial setup in the dataflow graph
  (hinputs' : proc.semanticsᵢ.lts.Step proc.semanticsᵢ.init (.input args) s') :
    ∃ (bound : Nat), -- Uniform bound on any dataflow trace length
      -- For any trace in the compiled dataflow graph
      ∀ {s₁' : proc.semanticsᵢ.S},
        proc.semanticsᵢ.lts.TauStarN .τ k' s' s₁' →
        ∃ (s₁'' s₂' : proc.semanticsᵢ.S) (k'' : Nat),
          bound = k' + k'' ∧
          proc.semanticsᵢ.lts.TauStarN .τ k'' s₁' s₁'' ∧
          proc.semanticsᵢ.lts.Step s₁'' (.output outputVals) s₂' ∧
          s₂'.1 ≈ (proc.semanticsᵢ).init.1 ∧ -- Back to initial dataflow state
          s₂'.2 = s₂.2 -- Equal operator states
  := by
  /- Sketch
  Notations:
    - →ι : input step
    - →τ : silent step
    - →ω : output step
    - ∼ : suitable simulation relation

  We have:
    `Seq`: init →ι s →τ* s₁ →ω s₂, (s₁ final wrt to τ)
    `Proc`: init →ι s' →τ* s₁'

  By simulation, we get
    `Proc`: init →ι s'' →τ* s''', with s''' ∼ s₁
    `Proc`: s''' →τ* s₁'', with s₁'' ∼ s₁
    `Proc`: s₁'' →τ* s₁''' →ω s₂'', with s₂'' ∼ s₂
    In other words:
      init →ι s'' →τ* s₁''' →ω s₂'', with s₂'' ∼ s₂

  TODO
  -/
  subst hcomp
  have hsim₁ := compile_forward_sim_guarded prog hwt haff₁ haff₂ i
  replace hsim₁ := sim_interp hsim₁
  -- Carry the first input step over
  have ⟨s''', hinputs'', hsim_s'''⟩ := hsim₁.sim_step _ _ _ _ hsim₁.sim_init hinputs
  cases hinputs'' with | step_input hinputs'' htau₁ =>
  rename_i s''
  have heq₁ := proc_interp_guarded_unguarded_det_input_mod hinputs'' hinputs'
  -- Carry the middle τ* steps over
  have ⟨s₁'', hstep_s₁'', hsim_s₁''⟩ := hsim₁.map_tau_star hsim_s''' htrace.without_length
  -- Carry the final output step over
  have ⟨s₂'', houtput', hsim_s₂''⟩ := hsim₁.sim_step _ _ _ _ hsim_s₁'' houtput
  cases houtput' with | step_output htau₂ houtput' =>
  rename_i s₁'''
  -- Concatenate the middle steps in guarded proc semantics
  have hmiddle := (htau₁.trans hstep_s₁'').trans htau₂
  replace ⟨bound, hmiddle⟩ := hmiddle.with_length
  -- Now we have a uniform bound on any dataflow trace
  exists bound
  intros s₁' htrace'
  -- Carry the silent steps after the first input steps
  have := congr_eq_mod_ghost_proc_interp_unguarded_tau_star_n htrace'
    (by
      constructor
      · exact IsSymm.symm _ _ heq₁.1
      · exact heq₁.2.symm)
  have ⟨_, htrace'', heq₂⟩ := this
  -- By `PreservesInit`, `s₂''` is an initial state
  -- and as a result, the previous step before output
  -- should be final wrt. τ and yield
  have ⟨_, htrace_tmp⟩ := htrace.without_length.to_star
  have hinit_s₂ : s₂.1 = (prog.semanticsᵢ i).init.1 :=
    prog_semanticsᵢ_output_init (htrace_tmp.prepend hinputs) houtput
  have ⟨hfinal_init, hfinal_eq⟩ := hsim₁.sim_prop _ _ hsim_s₂''
  specialize hfinal_init hinit_s₂
  have hfinal_s₁''' : Dataflow.Config.Step.IsFinalFor _ _ := proc_interp_guarded_output_init_invert houtput'
    (by simp [hfinal_init, Proc.semantics, Semantics.guard, Dataflow.Config.init])
  -- Use determinacy
  have ⟨_, _, htrace''', hlen₁, heq₃⟩ := proc_interp_guarded_hetero_terminal_confl hconfl hdet hnb
    sorry sorry -- Some invariants
    hmiddle hfinal_s₁''' htrace''
  -- Convert the determinacy result to τ steps after `htrace'`
  have this := congr_eq_mod_ghost_proc_interp_unguarded_tau_star_n htrace'''
    (by
      constructor
      · exact IsSymm.symm _ _ heq₂.1
      · exact heq₂.2.symm)
  have ⟨s₁'''', htrace'''', heq₄⟩ := this
  -- Carry the final output step over through ≈
  have houtput'' := Config.InterpGuardStep.to_interp_unguarded houtput'
  have ⟨_, houtput''', heq₅⟩ := congr_eq_mod_ghost_proc_interp_unguarded_output
    (s₁' := s₁'''')
    houtput'' (by
      constructor
      · trans
        · exact heq₃.1
        · exact heq₄.1
      · simp [heq₃.2, heq₄.2])
  exact ⟨_, _, _,
    hlen₁,
    htrace'''',
    houtput''',
    by
      simp [← houtput'''.output_eq_state,
        ← heq₄.2, ← heq₃.2,
        houtput'.output_eq_state,
        ← hfinal_eq]
      have := IsSymm.symm _ _ heq₅.1
      apply IsTrans.trans _ _ _ this
      simp [hfinal_init, Semantics.guard, Semantics.interpret, Proc.semantics]
      apply IsRefl.refl
  ⟩

end Wavelet
