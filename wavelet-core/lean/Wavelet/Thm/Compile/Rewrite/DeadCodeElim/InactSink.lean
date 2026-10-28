import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `inact-sink`: channels between an inact and a sink can be removed. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

theorem inact_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k₁ k₂ : Nat} [NeZero k₂] {outputs inputs' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.inact k₁) [] outputs))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink k₂) inputs' []))
  (hne : i₂ ≠ i₁)
  (hndisj : ¬ outputs.Disjoint inputs') :
    RuleOK proc [i₂, i₁] [
      .inact (outputs.removeAll inputs').toVector,
      .sink (inputs'.removeAll outputs).toVector,
    ]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink k₂) inputs' [], .async (.inact k₁) [] outputs] := by
    simp [h₁, h₂]
  have hnd : outputs.Nodup := by simpa using (haff.atom_nodup h₁).2
  have hnd' : inputs'.Nodup := by simpa using (haff.atom_nodup h₂).1
  -- A channel between the inact and the sink, which is always empty.
  obtain ⟨c, hc, hc'⟩ : ∃ c ∈ outputs, c ∈ inputs' := by
    by_contra h
    exact hndisj (λ a ha ha' => h ⟨a, ha, ha'⟩)
  -- The outputs of the inact are always empty, so the sink never fires.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.inact (outputs.removeAll inputs').toVector, .sink (inputs'.removeAll outputs).toVector] ∧
    chans₀ = chans₁ ∧
    ∀ y ∈ outputs, chans₀ y = [], ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simpa [sink_inputs, AtomicProc.inact, toList_toVector] using List.removeAll_nodup hnd'
    · simpa [sink_outputs, AtomicProc.inact, toList_toVector] using List.removeAll_nodup hnd
    · intro x hx
      simp only [AtomicProcs.inputNames_cons, sink_inputs, AtomicProc.inact,
        AtomicProc.inputs_async, AtomicProcs.inputNames_nil, List.append_nil, List.nil_append,
        toList_toVector] at hx
      simp [hP, (List.mem_removeAll_to_mem hx).1]
    · intro x hx
      simp only [AtomicProcs.outputNames_cons, sink_outputs, AtomicProc.inact,
        AtomicProc.outputs_async, AtomicProcs.outputNames_nil, List.append_nil,
        toList_toVector] at hx
      simp [hP, (List.mem_removeAll_to_mem hx).1]
  · constructor
    · exact ⟨rfl, rfl, rfl, λ _ _ => rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' _ _ ⟨rfl, rfl, rfl, hempty⟩ hpop
      refine ⟨_, hpop, rfl, rfl, rfl, λ y hy => ?_⟩
      have := hpop y
      rw [hempty y hy] at this
      exact (List.append_eq_nil_iff.mp this.symm).2
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, rfl, hempty⟩
      refine ⟨rfl, rfl, rfl, λ y hy => ?_⟩
      have : y ∉ outs := λ h => by simpa [hP, hy] using (hx y h).1
      simp [hempty y hy, ChanMap.pushed_not_mem this]
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs₀ outputs₀ inputVals outputVals chans₀' _ _ ⟨rfl, rfl, rfl, hempty⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget
      exfalso
      match i, hget with
      | 0, hget =>
        -- The sink cannot fire since `c` is empty.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, -, rfl, rfl⟩ := hinterp.sink_inv
        subst inputs₀
        have := hpop c
        rw [hempty c hc] at this
        exact pushed_ne_nil hc' hlen₁ (List.append_eq_nil_iff.mp this.symm).1
      | 1, hget =>
        -- The inact never fires.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        exact hinterp.inact_inv
  · rintro L₁ chans₁ ⟨_, rfl, rfl, -⟩
    exact ⟨rfl, rfl⟩

end Wavelet.Compile.DeadCodeElim
