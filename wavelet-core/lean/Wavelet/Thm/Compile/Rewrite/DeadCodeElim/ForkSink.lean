import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `fork-sink`: a sunk output of a fork can be removed. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

theorem fork_sink_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k : Nat} {input sink : χ} {outputs : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.fork k) [input] outputs))
  (h₂ : proc.atoms[i₂]? = some (.async (.sink 1) [sink] []))
  (hne : i₂ ≠ i₁)
  (hlen : outputs.length = k)
  (hmem : sink ∈ outputs) :
    RuleOK proc [i₂, i₁] [.fork input (outputs.erase sink).toVector]
  := by
  subst hlen
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.sink 1) [sink] [], .async (.fork outputs.length) [input] outputs] := by
    simp [h₁, h₂]
  have hP' : ([.fork input (outputs.erase sink).toVector] : AtomicProcs Op χ V) =
      [.async (.fork (outputs.erase sink).length) [input] (outputs.erase sink)] := by
    simp [AtomicProc.fork, List.toVector]
  -- Facts from affineness
  have hnd : outputs.Nodup := by simpa using (haff.atom_nodup h₁).2
  have hsi : sink ≠ input := Ne.symm (by simpa using (haff.atom_disjoint h₂ h₁ hne).1)
  -- `sink` is no longer used after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.fork input (outputs.erase sink).toVector] ∧
    chans₁ = (λ y => if y = sink then [] else chans₀ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP']
    · simpa [hP'] using hnd.erase sink
    · simp [hP', hP]
    · intro x hx
      simp only [hP', AtomicProcs.outputNames_cons, AtomicProc.outputs_async,
        AtomicProcs.outputNames_nil, List.append_nil] at hx
      simp [hP, List.mem_of_mem_erase hx]
  · constructor
    · exact ⟨rfl, rfl, except_empty⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, rfl⟩ hpop
      simp [hP] at hx
      exact ⟨_, except_frame_pop hx.1 hpop, rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, rfl⟩
      have : sink ∉ outs := λ h => by simpa [hP, hmem] using (hx sink h).1
      exact ⟨rfl, rfl, except_push this⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs' inputVals outputVals chans₀' _ _ ⟨rfl, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The sink fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hinterp.sink_inv
        obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen₁.symm
        refine ⟨_, _, .refl, ?_, rfl, ?_⟩
        · simp
        · refine except_pop_same (names := [sink]) (vals := [v]) (λ y => ?_) (λ y hy => ?_)
          · simpa using hpop y
          · simp [Ne.symm hy]
      | 1, hget =>
        -- The fork fires: the rewritten fork fires with the same value.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, v, rfl, hclone, rfl⟩ := hinterp.fork_inv hlen₁
        refine ⟨_, _, fork_step (by simp) hclone (except_pop (by simpa using hsi) hpop),
          ?_, rfl, except_push_erase hnd⟩
        simp
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, except_empty.symm⟩

end Wavelet.Compile.DeadCodeElim
