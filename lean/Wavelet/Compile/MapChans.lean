import Wavelet.Dataflow.Proc

/-! Renaming channels of a `Proc`/`AtomicProc`. -/

namespace Wavelet.Dataflow

open Semantics

def AtomicProc.mapChans [Arity Op] (f : χ → χ') : AtomicProc Op χ V → AtomicProc Op χ' V
  | .op o inputs outputs => .op o (inputs.map f) (outputs.map f)
  | .async aop inputs outputs => .async aop (inputs.map f) (outputs.map f)

def AtomicProcs.mapChans [Arity Op] (f : χ → χ')
  : AtomicProcs Op χ V → AtomicProcs Op χ' V
  := List.map (AtomicProc.mapChans f)

def Proc.mapChans [Arity Op] (f : χ → χ') (p : Proc Op χ V m n) : Proc Op χ' V m n :=
  {
    inputs := p.inputs.map f,
    outputs := p.outputs.map f,
    atoms := p.atoms.mapChans f,
  }

section Simulation

private def SimRel
  [Arity Op] {χ χ' : Type u}
  [DecidableEq χ] [DecidableEq χ']
  (f : χ → χ')
  (s₁ : Config Op χ V m n)
  (s₂ : Config Op χ' V m n) : Prop :=
  s₂.proc = s₁.proc.mapChans f ∧
  s₁.chans = s₂.chans ∘ f ∧
  -- No other names other than those in the image of `f`
  s₂.chans.AllNames (∃ n', f n' = ·)

theorem async_op_interp_map_chans
  [InterpConsts V]
  {aop : AsyncOp V}
  (f : χ → χ')
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    AsyncOp.Interp aop
      (.mk (allInputs.map f) (allOutputs.map f) (inputs.map f) inputVals (outputs.map f) outputVals)
      aop'
  := by
  cases hinterp with
  | interp_switch h₁ h₂ h₃ =>
    rename Bool => deciderBool
    cases deciderBool <;> {
      simp
      rw [← List.length_map f] at h₁ h₂
      exact .interp_switch h₁ h₂ h₃
    }
  | interp_steer_true h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_steer_true h₁ h₂ h₃ h₄
  | interp_steer_false h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_steer_false h₁ h₂ h₃ h₄
  | interp_merge_left h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    simp
    exact .interp_merge_left h₁ h₂
  | interp_merge_right h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    simp
    exact .interp_merge_right h₁ h₂
  | interp_merge_decider h₁ h₂ h₃ =>
    rw [← List.length_map f] at h₁ h₂
    simp
    exact .interp_merge_decider h₁ h₂ h₃
  | interp_forward h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_forward h₁ h₂
  | interp_fork h₁ h₂ =>
    rw [← List.length_map f] at h₁
    exact .interp_fork h₁ h₂
  | interp_order h₁ h₂ =>
    rw [← List.length_map f] at h₁
    exact .interp_order h₁ h₂
  | interp_const h₁ =>
    rw [← List.length_map f] at h₁
    exact .interp_const h₁
  | interp_forwardc h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_forwardc h₁ h₂
  | interp_sink h₁ =>
    rw [← List.length_map f] at h₁
    exact .interp_sink h₁
  | interp_inv_init h₁ h₂ h₃ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_inv_init h₁ h₂ h₃
  | interp_inv_true h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_inv_true h₁ h₂ h₃ h₄
  | interp_inv_false h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_inv_false h₁ h₂ h₃ h₄

theorem sim_map_chans_inj_preserves_init
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f) :
    proc.semantics ≲ₛ[PreservesInit] (proc.mapChans f).semantics
  := by
  apply Lts.SimilaritySt.intro (SimRel f)
  · constructor
    · constructor
      · rfl
      · simp [Proc.semantics, Config.init, ChanMap.empty, ChanMap.AllNames]
    · intros s₁ s₂ l s₁' hsim hstep
      have ⟨hsim_proc, hsim_chans, hsim_emp⟩ := hsim
      cases hstep with
      | step_init =>
        exact ⟨_,
          .step_init,
          by
            and_intros
            · exact hsim_proc
            · simp [hsim_proc, hsim_chans, Proc.mapChans]
              rw [push_vals_map_chans hf]
            · simp [hsim_proc, Proc.mapChans]
              apply push_vals_preserves_all_names hsim_emp
              simp,
        ⟩
      | step_output hpop =>
        simp [hsim_chans] at hpop
        have ⟨map', heq', hpop'⟩ := pop_vals_map_chans hf hpop
        subst heq'
        exact ⟨_,
          .step_output (by
            simp [hsim_proc, Proc.mapChans]
            exact hpop'),
          by
            and_intros
            · exact hsim_proc
            · simp
            · with_reducible
              exact pop_vals_preserves_all_names hsim_emp hpop',
        ⟩
      | step_op hmem hpop =>
        simp [hsim_chans] at hmem hpop
        have ⟨_, heq', hpop'⟩ := pop_vals_map_chans hf hpop
        subst heq'
        exact ⟨_,
          .step_op
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans]
              exact ⟨_, hmem, by simp [AtomicProc.mapChans]; constructor <;> rfl⟩)
            (by exact hpop'),
          by
            and_intros
            · exact hsim_proc
            · simp
              rw [push_vals_map_chans hf]
            · with_reducible
              simp
              apply push_vals_preserves_all_names
              · exact pop_vals_preserves_all_names hsim_emp hpop'
              · simp,
        ⟩
      | step_async hi hget hinterp hpop =>
        simp [hsim_chans] at hget hpop
        have ⟨_, heq', hpop'⟩ := pop_vals_map_chans hf hpop
        subst heq'
        exact ⟨_,
          .step_async
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans]
              exact hi)
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans, hget,
                AtomicProc.mapChans]
              and_intros <;> rfl)
            (by
              have := async_op_interp_map_chans f hinterp
              simp only [← Vector.toList_map] at this
              exact this)
            (by exact hpop'),
          by
            and_intros
            · simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans,
                AtomicProc.mapChans]
            · simp
              rw [push_vals_map_chans hf]
            · with_reducible
              simp
              apply push_vals_preserves_all_names
              · exact pop_vals_preserves_all_names hsim_emp hpop'
              · simp,
        ⟩
  · intros s₁ s₂ hsim hinit
    subst hinit
    rcases s₂ with ⟨proc₂, chans₂⟩
    have ⟨hsim_proc, hsim_chans, hsim_emp⟩ := hsim
    simp [Proc.semantics, Config.init] at hsim_proc hsim_chans hsim_emp
    simp [Proc.semantics, Config.init, hsim_proc]
    funext n
    by_cases hemp : chans₂ n = []
    · simp [hemp, ChanMap.empty]
    · have ⟨n', hfn'⟩ := hsim_emp hemp
      simp [← hfn']
      have : (chans₂ ∘ f) n' = [] := by
        rw [← hsim_chans, ChanMap.empty]
      simp at this
      simp [this, ChanMap.empty]

theorem sim_map_chans_inj
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f) :
    proc.semantics ≲ₛ (proc.mapChans f).semantics
  := (sim_map_chans_inj_preserves_init hf).weaken (by simp)

end Simulation

end Wavelet.Dataflow
