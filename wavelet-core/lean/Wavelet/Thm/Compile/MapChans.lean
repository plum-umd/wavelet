import Wavelet.Compile.MapChans

import Wavelet.Thm.Semantics.Simulation
import Wavelet.Thm.Dataflow.ChanMap
import Wavelet.Thm.Dataflow.AffineChan

/-! Simulation and other utility lemmas about `Proc.mapChans`. -/

namespace Wavelet.Dataflow

open Semantics

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

section Affineness

variable {χ χ' : Type u} {Op : Type v} {V : Type w} {m n : Nat}
variable {f : χ → χ'}

private theorem atomicProc_mapChans_inputs [Arity Op]
  (f : χ → χ') (ap : AtomicProc Op χ V) :
    (ap.mapChans f).inputs = ap.inputs.map f := by
  cases ap <;> simp [AtomicProc.mapChans, AtomicProc.inputs, Vector.toList_map]

private theorem atomicProc_mapChans_outputs [Arity Op]
  (f : χ → χ') (ap : AtomicProc Op χ V) :
    (ap.mapChans f).outputs = ap.outputs.map f := by
  cases ap <;> simp [AtomicProc.mapChans, AtomicProc.outputs, Vector.toList_map]

theorem map_chans_preserves_aff_var
  [Arity Op]
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f)
  (haff : proc.AffineChan) :
    (proc.mapChans f).AffineChan
  := by
  obtain ⟨h_in, h_out, ⟨h_atom_nodup, h_atom_pw⟩, h_ao_di, h_ai_do⟩ := haff
  simp only [Proc.AffineChan, Proc.mapChans, AtomicProcs.AffineChan]
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Vector.toList_map]; exact h_in.map hf
  · rw [Vector.toList_map]; exact h_out.map hf
  · intro ap hap
    simp [AtomicProcs.mapChans] at hap
    obtain ⟨ap', hap', rfl⟩ := hap
    constructor
    · rw [atomicProc_mapChans_inputs]; exact (h_atom_nodup ap' hap').1.map hf
    · rw [atomicProc_mapChans_outputs]; exact (h_atom_nodup ap' hap').2.map hf
  · apply List.Pairwise.map _ _ h_atom_pw
    intro a b ⟨hdi, hdo⟩
    constructor
    · rw [atomicProc_mapChans_inputs, atomicProc_mapChans_inputs]; exact hdi.map hf
    · rw [atomicProc_mapChans_outputs, atomicProc_mapChans_outputs]; exact hdo.map hf
  · intro ap hap
    simp [AtomicProcs.mapChans] at hap
    obtain ⟨ap', hap', rfl⟩ := hap
    rw [atomicProc_mapChans_outputs, Vector.toList_map]
    exact (h_ao_di ap' hap').map hf
  · intro ap hap
    simp [AtomicProcs.mapChans] at hap
    obtain ⟨ap', hap', rfl⟩ := hap
    rw [atomicProc_mapChans_inputs, Vector.toList_map]
    exact (h_ai_do ap' hap').map hf

end Affineness

end Wavelet.Dataflow
