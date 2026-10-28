import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `order-sync-path`: a non-first order input from a fork can be removed
(forward simulation holds regardless of the synchronous path check). -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

theorem order_sync_path_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k₁ k₂ : Nat} [NeZero k₁] {inputs outputs' : List χ} {output input' input₁ : χ}
  [NeZero (inputs.erase input₁).length]
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.order k₁) inputs [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork k₂) [input'] outputs'))
  (hne : i₂ ≠ i₁)
  (hlen : inputs.length = k₁) (hlen' : outputs'.length = k₂)
  (hmem₁ : input₁ ∈ inputs.drop 1)
  (hmem₂ : input₁ ∈ outputs') :
    RuleOK proc [i₂, i₁] [
      .fork input' (outputs'.erase input₁).toVector,
      .order (inputs.erase input₁).toVector output,
    ]
  := by
  subst hlen'
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.fork outputs'.length) [input'] outputs', .async (.order k₁) inputs [output]] := by
    simp [h₁, h₂]
  have hP' : ([.fork input' (outputs'.erase input₁).toVector,
      .order (inputs.erase input₁).toVector output] : AtomicProcs Op χ V) =
      [.async (.fork (outputs'.erase input₁).length) [input'] (outputs'.erase input₁),
        .async (.order (inputs.erase input₁).length) (inputs.erase input₁) [output]] := by
    simp [AtomicProc.fork, AtomicProc.order, toList_toVector]
  -- Facts from affineness
  have hnd : inputs.Nodup := by simpa using (haff.atom_nodup h₁).1
  have hnd' : outputs'.Nodup := by simpa using (haff.atom_nodup h₂).2
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  have hii : input' ∉ inputs := λ h => hdisj.1 (by simp) h
  have hoo : output ∉ outputs' := λ h => hdisj.2 h (by simp)
  have hmem₁' : input₁ ∈ inputs := List.mem_of_mem_drop hmem₁
  have hi₁ : input' ≠ input₁ := λ h => hii (h ▸ hmem₁')
  have ho₁ : output ≠ input₁ := λ h => hoo (h ▸ hmem₂)
  -- `input₁` is no longer used after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.fork input' (outputs'.erase input₁).toVector,
      .order (inputs.erase input₁).toVector output] ∧
    chans₁ = (λ y => if y = input₁ then [] else chans₀ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp only [hP', AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil, List.singleton_append]
      exact List.nodup_cons.mpr ⟨λ h => hii (List.mem_of_mem_erase h), hnd.erase input₁⟩
    · simp only [hP', AtomicProcs.outputNames_cons, AtomicProc.outputs_async,
        AtomicProcs.outputNames_nil, List.append_nil]
      exact (hnd'.erase input₁).append (List.nodup_singleton output)
        (λ x hx hx' => hoo (by simp at hx'; exact hx' ▸ List.mem_of_mem_erase hx))
    · intro x hx
      simp only [hP', AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil, List.mem_append] at hx
      left
      rcases hx with hx | hx
      · obtain rfl := List.mem_singleton.mp hx
        simp [hP]
      · simp [hP, List.mem_of_mem_erase hx]
    · intro x hx
      simp only [hP', AtomicProcs.outputNames_cons, AtomicProc.outputs_async,
        AtomicProcs.outputNames_nil, List.append_nil, List.mem_append] at hx
      left
      rcases hx with hx | hx
      · simp [hP, List.mem_of_mem_erase hx]
      · simp [hP, hx]
  · constructor
    · exact ⟨rfl, rfl, except_empty⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, rfl⟩ hpop
      have hx₁ : x ≠ input₁ := λ h => hx (by simp [hP, h, hmem₁'])
      exact ⟨_, except_frame_pop hx₁ hpop, rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, rfl⟩
      have : input₁ ∉ outs := λ h => by simpa [hP, hmem₂] using (hx input₁ h).1
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
        -- The fork fires: the rewritten fork fires with the same value.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, hout, -, v, rfl, hclone, rfl⟩ := hinterp.fork_inv hlen₁
        subst outputs₀
        refine ⟨_, _, fork_step (by simp) hclone (except_pop (by simpa using Ne.symm hi₁) hpop),
          ?_, rfl, except_push_erase hnd'⟩
        simp
      | 1, hget =>
        -- The order fires: the rewritten order fires with the same first value.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, rfl, -, v, restVals, rfl, rfl⟩ := hinterp.order_inv
        subst inputs₀
        -- `input₁` is not the first input.
        obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem₁')
        have hmem₁'' : input₁ ∈ rest := by simpa using hmem₁
        have ha : a ≠ input₁ := λ h => (List.nodup_cons.mp hnd).1 (h ▸ hmem₁'')
        have hrest : rest.Nodup := (List.nodup_cons.mp hnd).2
        have herase : (a :: rest).erase input₁ = a :: rest.erase input₁ :=
          List.erase_cons_tail (by simpa using ha)
        obtain ⟨restVals', hlen'', hpe⟩ := pushed_erase input₁ (vals := restVals)
          (by simpa using hlen₁)
        have hlen₂ : ((a :: rest).erase input₁).length = (v :: restVals').length := by
          simp [herase, hlen'']
        have hstep := LocalTauStar.async_list_mem
          (L := ([.fork input' (outputs'.erase input₁).toVector,
            .order ((a :: rest).erase input₁).toVector output] : AtomicProcs Op χ V))
          (aop := .order ((a :: rest).erase input₁).length)
          (allInputs := (a :: rest).erase input₁) (allOutputs := [output])
          (inputs := (a :: rest).erase input₁) (inputVals := v :: restVals')
          (outputs := [output]) (outputVals := [v])
          (chans := λ y => if y = input₁ then [] else chans₀ y)
          (chans' := λ y => if y = input₁ then [] else chans₀' y)
          (by simp [AtomicProc.order, toList_toVector])
          (.interp_order rfl hlen₂.symm) hlen₂ rfl
          (by
            intro y
            beta_reduce
            rw [herase, ChanMap.pushed_cons]
            by_cases hy : y = input₁
            · subst hy
              simp [ha, ChanMap.pushed_not_mem hrest.not_mem_erase]
            · rw [if_neg hy, if_neg hy, hpe y hy, hpop y, ChanMap.pushed_cons])
        refine ⟨_, _, hstep, ?_, rfl, except_push (by simpa using Ne.symm ho₁)⟩
        simp
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, except_empty.symm⟩

end Wavelet.Compile.DeadCodeElim
