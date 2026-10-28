import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `merge-sink`: a merge into a sink can be removed. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

theorem merge_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k : Nat} [NeZero k] {decider inputL inputR output : χ} {inputs' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink k) inputs' []))
  (hne : i₂ ≠ i₁)
  (hmem : output ∈ inputs') :
    RuleOK proc [i₂, i₁] [
      .sink #v[decider],
      .sink #v[inputL],
      .sink #v[inputR],
      .sink (inputs'.erase output).toVector,
    ]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink k) inputs' [],
        .async (.merge .decider 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂]
  -- Facts from affineness
  have hnd := (haff.atom_nodup h₁).1
  have hnd' : inputs'.Nodup := by simpa using (haff.atom_nodup h₂).1
  have hdisj : inputs'.Disjoint [decider, inputL, inputR] := by
    simpa using (haff.atom_disjoint h₂ h₁ hne).1
  have hod : output ≠ decider := λ h => hdisj hmem (by simp [h])
  have hol : output ≠ inputL := λ h => hdisj hmem (by simp [h])
  have hor : output ≠ inputR := λ h => hdisj hmem (by simp [h])
  -- The merge can be in any state; `output` is no longer used after the rewrite.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    (∃ st, L₀ = [.async (.sink k) inputs' [],
      .async (.merge st 1) [decider, inputL, inputR] [output]]) ∧
    L₁ = [.sink #v[decider], .sink #v[inputL], .sink #v[inputR],
      .sink (inputs'.erase output).toVector] ∧
    chans₁ = (λ y => if y = output then [] else chans₀ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp only [AtomicProcs.inputNames_cons, sink_inputs, AtomicProcs.inputNames_nil,
        List.append_nil, toList_toVector]
      exact (hnd.append (hnd'.erase output)
        (λ x hx hx' => hdisj (List.mem_of_mem_erase hx') hx) :)
    · simp [sink_outputs]
    · intro x hx
      simp only [AtomicProcs.inputNames_cons, sink_inputs, AtomicProcs.inputNames_nil,
        List.append_nil, toList_toVector] at hx
      left
      simp only [List.mem_append] at hx
      rcases hx with hx | hx | hx | hx
      · obtain rfl : x = decider := by simpa using hx
        simp [hP]
      · obtain rfl : x = inputL := by simpa using hx
        simp [hP]
      · obtain rfl : x = inputR := by simpa using hx
        simp [hP]
      · simp [hP, List.mem_of_mem_erase hx]
    · simp [sink_outputs]
  · constructor
    · exact ⟨⟨_, hP⟩, rfl, except_empty⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨⟨st, rfl⟩, rfl, rfl⟩ hpop
      have hxo : x ≠ output := λ h => hx (by simp [hP, h, hmem])
      exact ⟨_, except_frame_pop hxo hpop, ⟨st, rfl⟩, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨⟨st, rfl⟩, rfl, rfl⟩
      have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨⟨st, rfl⟩, rfl, except_push this⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨⟨st, rfl⟩, rfl, _⟩ hmem
      simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs₀ outputs₀ inputVals outputVals chans₀' _ _ ⟨⟨st, rfl⟩, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      match i, hget with
      | 0, hget =>
        -- The sink fires: the rewritten sink consumes the other inputs.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, -, rfl, rfl⟩ := hinterp.sink_inv
        subst inputs₀
        obtain ⟨vals', hlen'', hpop'⟩ := except_pop_erase (s := output) hnd' hlen₁ hpop
        refine ⟨_, _, sink_step (names := (inputs'.erase output).toVector) (vals := vals')
          (by simp) hlen'' hpop', ⟨st, by simp⟩, rfl, ?_⟩
        funext y
        simp
      | 1, hget =>
        -- The merge fires: the rewritten sink of the input read by the merge fires.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        rcases hinterp.merge_inv hlen₁ with
          ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl, dv, b, rfl, -, rfl⟩
        · refine ⟨_, _, sink_step (names := #v[inputL]) (vals := [v])
            (by simp) rfl (except_pop (by simpa using hol) hpop), ⟨.decider, by simp⟩, rfl,
            except_push_only (λ y hy => by simp [Ne.symm hy])⟩
        · refine ⟨_, _, sink_step (names := #v[inputR]) (vals := [v])
            (by simp) rfl (except_pop (by simpa using hor) hpop), ⟨.decider, by simp⟩, rfl,
            except_push_only (λ y hy => by simp [Ne.symm hy])⟩
        · refine ⟨_, _, sink_step (names := #v[decider]) (vals := [dv])
            (by simp) rfl (except_pop (by simpa using hod) hpop),
            ⟨if b then .popRight else .popLeft, by simp⟩, rfl,
            except_push_only (λ y hy => by simp)⟩
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, except_empty.symm⟩

end Wavelet.Compile.DeadCodeElim
