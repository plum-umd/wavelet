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
      ≲ᵣ (prog.semantics i).guard (opSpec.Guard (progSpec i))
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
      ≲ᵣ (compileProg prog i).semantics.guard (opSpec.Guard (progSpec i))
  := by
  apply IORestrictedSimilarity.trans
  · exact sim_wt_prog prog hwt
  apply sim_guard
  apply sim_compile_prog prog i haff₁ haff₂

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
  · apply compile_forward_sim_guarded prog hwt haff₁ haff₂ i
  sorry

theorem compile_strong_norm
  {Op V T : Type u}
  [Arity Op] [PCM T] [PCM.Lawful T] [PCM.Cancellative T]
  [DecidableEq χ]
  [InterpConsts V]
  [opInterp : OpInterp.{_, _, w} Op V]
  {sigs : Sigs k}
  {opSpec : OpSpec Op V T}
  {progSpec : ProgSpec Op V T sigs}

  (hconfl : opSpec.Confluent opInterp)
  (hdet : opInterp.Deterministic)
  (hnb : opInterp.NonBlocking)

  (prog : Prog (WithSpec Op opSpec) χ (V ⊕ T) (extendSigs sigs))
  (hwt : ProgWithSpec.WellPermTyped progSpec prog)
  (haff₁ : ∀ (i : Fin k), (prog i).AffineVar)
  (haff₂ : prog.AffineInrOp)
  (i : Fin k)
  {args : Vector V (sigs i).ι}
  {outputVals : Vector V (sigs i).ω}

  {proc : Proc (WithSpec Op opSpec) (LinkName (ChanName χ)) (V ⊕ T) _ _}
  (hcomp : proc = compileProg prog i)

  {s s₁ s₂ : (prog.semanticsᵢ i).S}
  {s' s₁' : proc.semanticsᵢ.S}

  -- There exists a terminating trace in the sequential semantics
  -- that output `outputVals`.
  (hinputs : (prog.semanticsᵢ i).lts.Step (prog.semanticsᵢ i).init (.input args) s)
  (htrace : (prog.semanticsᵢ i).lts.TauStarN .τ k s s₁)
  (hterm : (prog.semanticsᵢ i).lts.IsFinalFor (·.isSilent) s₁)
  (houtput : (prog.semanticsᵢ i).lts.Step s₁ (.output outputVals) s₂)

  (hinputs' : proc.semanticsᵢ.lts.Step proc.semanticsᵢ.init (.input args) s')
  (htrace' : proc.semanticsᵢ.lts.TauStarN .τ k' s' s₁') :
    ∃ (s₁'' s₂' : proc.semanticsᵢ.S) (k'' : Nat),
      -- k = k' + k'' ∧
      proc.semanticsᵢ.lts.TauStarN .τ k'' s₁' s₁'' ∧
      proc.semanticsᵢ.lts.IsFinalFor (·.isSilent) s₁'' ∧
      proc.semanticsᵢ.lts.Step s₁'' (.output outputVals) s₂' ∧
      s₂'.2 = s₂.2 -- Equal "memory" states
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
  -- Carry the silent steps after the first input steps
  have := congr_eq_mod_ghost_proc_interp_unguarded_tau_star_n htrace'
    (by
      constructor
      · exact IsSymm.symm _ _ heq₁.1
      · exact heq₁.2.symm)
  have ⟨_, htrace'', heq₂⟩ := this
  -- Carry the middle τ* steps over
  have ⟨s₁'', hstep_s₁'', hsim_s₁''⟩ := hsim₁.map_tau_star hsim_s''' htrace.without_length
  -- Carry the final output step over
  have ⟨s₂'', houtput', hsim_s₂''⟩ := hsim₁.sim_step _ _ _ _ hsim_s₁'' houtput
  cases houtput' with | step_output htau₂ houtput' =>
  rename_i s₁'''
  -- Concatenate the middle steps in guarded proc semantics
  have hmiddle := (htau₁.trans hstep_s₁'').trans htau₂
  replace ⟨k', hmiddle⟩ := hmiddle.with_length
  -- have hfinal_s₁''' :
  -- Use determinacy
  have ⟨_, _, htrace''', hlen₁, heq₃⟩ := proc_interp_guarded_hetero_terminal_confl hconfl hdet hnb
    sorry sorry hmiddle
    (by sorry) htrace''
  -- Convert the determinacy result to τ steps after `htrace'`
  have this := congr_eq_mod_ghost_proc_interp_unguarded_tau_star_n htrace'''
    (by
      constructor
      · exact IsSymm.symm _ _ heq₂.1
      · exact heq₂.2.symm)
  have ⟨s₁'''', htrace'''', heq₄⟩ := this
  -- Carry the final output step over through ≈
  have houtput'' := Config.InterpGuardStep.to_indexed_interp_unguarded houtput'
  have ⟨_, houtput''', _⟩ := congr_eq_mod_ghost_proc_interp_unguarded_output
    (s₁' := s₁'''')
    houtput'' (by
      constructor
      · trans
        · exact heq₃.1
        · exact heq₄.1
      · simp [heq₃.2, heq₄.2])
  -- have := htrace'.trans htrace''''
  exact ⟨
    _, _, _, htrace'''',
    sorry,
    houtput''',
    by
      have := hsim₁.sim_prop _ _ hsim_s₂''
      simp [← houtput'''.output_eq_state,
        ← heq₄.2, ← heq₃.2,
        houtput'.output_eq_state,
        ← this.2]
  ⟩

end Wavelet
