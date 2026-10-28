import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `order-sink`: an order into a sink can be removed. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

theorem order_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k₁ k₂ : Nat} [NeZero k₁] [NeZero k₂] {inputs inputs' : List χ} {output : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.order k₁) inputs [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink k₂) inputs' []))
  (hne : i₂ ≠ i₁)
  (hmem : output ∈ inputs') :
    RuleOK proc [i₂, i₁] [
      .sink inputs.toVector,
      .sink (inputs'.erase output).toVector,
    ]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink k₂) inputs' [], .async (.order k₁) inputs [output]] := by
    simp [h₁, h₂]
  -- Facts from affineness
  have hnd : inputs.Nodup := by simpa using (haff.atom_nodup h₁).1
  have hnd' : inputs'.Nodup := by simpa using (haff.atom_nodup h₂).1
  have hdisj : inputs'.Disjoint inputs := by simpa using (haff.atom_disjoint h₂ h₁ hne).1
  have hoi : output ∉ inputs := λ h => hdisj hmem h
  -- `output` is no longer used after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.sink inputs.toVector, .sink (inputs'.erase output).toVector] ∧
    chans₁ = (λ y => if y = output then [] else chans₀ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp only [AtomicProcs.inputNames_cons, sink_inputs, AtomicProcs.inputNames_nil,
        List.append_nil, toList_toVector]
      exact hnd.append (hnd'.erase output)
        (λ x hx hx' => hdisj (List.mem_of_mem_erase hx') hx)
    · simp [sink_outputs]
    · intro x hx
      simp only [AtomicProcs.inputNames_cons, sink_inputs, AtomicProcs.inputNames_nil,
        List.append_nil, toList_toVector] at hx
      left
      rcases List.mem_append.mp hx with hx | hx
      · simp [hP, hx]
      · simp [hP, List.mem_of_mem_erase hx]
    · simp [sink_outputs]
  · constructor
    · exact ⟨rfl, rfl, except_empty⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, rfl⟩ hpop
      have hxo : x ≠ output := λ h => hx (by simp [hP, h, hmem])
      exact ⟨_, except_frame_pop hxo hpop, rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, rfl⟩
      have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨rfl, rfl, except_push this⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs₀ outputs₀ inputVals outputVals chans₀' _ _ ⟨rfl, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The sink fires: the rewritten sink consumes the other inputs.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, -, rfl, rfl⟩ := hinterp.sink_inv
        subst inputs₀
        obtain ⟨vals', hlen'', hpop'⟩ := except_pop_erase (s := output) hnd' hlen₁ hpop
        refine ⟨_, _, sink_step (names := (inputs'.erase output).toVector) (vals := vals')
          (by simp) hlen'' hpop', ?_, rfl, ?_⟩
        · simp
        · funext y
          simp
      | 1, hget =>
        -- The order fires: the rewritten sink consumes the same inputs.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, rfl, -, v, rest, rfl, rfl⟩ := hinterp.order_inv
        subst inputs₀
        refine ⟨_, _, sink_step (names := inputs.toVector) (vals := v :: rest)
          (by simp) hlen₁ (except_pop hoi hpop), ?_, rfl, ?_⟩
        · simp
        · exact except_push_only (λ y hy => by simp [Ne.symm hy])
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, except_empty.symm⟩

end Wavelet.Compile.DeadCodeElim
