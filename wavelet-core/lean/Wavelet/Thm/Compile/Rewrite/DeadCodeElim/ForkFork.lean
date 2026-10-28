import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `fork-fork`: two consecutive forks can be folded. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

/-- Channels of the rewritten graph: the values still in the middle channel `y`
(the input of the second fork) are already in the outputs `outs'` of the second fork. -/
private def foldChans [DecidableEq χ] (y : χ) (outs' : List χ) (chans : ChanMap χ V) :
    ChanMap χ V :=
  λ z => if z ∈ outs' then chans z ++ chans y else if z = y then [] else chans z

private theorem foldChans_empty [DecidableEq χ] {y : χ} {outs' : List χ} :
    foldChans y outs' (ChanMap.empty : ChanMap χ V) = .empty := by
  funext z
  simp only [foldChans, ChanMap.empty_apply, List.append_nil]
  split <;> (try split) <;> rfl

/-- Popping channels other than `y`. -/
private theorem foldChans_pop [DecidableEq χ] {y : χ} {outs' : List χ} {c c' : ChanMap χ V}
  (P : χ → List V) (hP : P y = []) (hpop : ∀ z, c z = P z ++ c' z) (z : χ) :
    foldChans y outs' c z = P z ++ foldChans y outs' c' z := by
  unfold foldChans
  split
  · rw [hpop z, hpop y, hP]
    simp
  · split
    · subst_vars
      simp [hP]
    · exact hpop z

/-- Pushing to channels other than `y` and `outs'`. -/
private theorem foldChans_push [DecidableEq χ] {y : χ} {outs' : List χ} {c : ChanMap χ V}
  (P : χ → List V) (hP : P y = []) (hP' : ∀ z ∈ outs', P z = []) :
    foldChans y outs' (λ z => c z ++ P z) = λ z => foldChans y outs' c z ++ P z := by
  funext z
  unfold foldChans
  split
  · rename_i hz
    simp [hP, hP' z hz]
  · split
    · subst_vars
      simp [hP]
    · rfl

/-- The second fork fires. -/
private theorem foldChans_fork₂ [DecidableEq χ] {y : χ} {outs' : List χ} {c c' : ChanMap χ V}
  {v : V} (hy : y ∉ outs') (hnd : outs'.Nodup)
  (hpop : ∀ z, c z = ChanMap.pushed [y] [v] z ++ c' z) :
    foldChans y outs' (λ z => c' z ++ ChanMap.pushed outs' (List.replicate outs'.length v) z) =
      foldChans y outs' c := by
  funext z
  unfold foldChans
  simp only [pushed_replicate]
  split
  · rename_i hz
    have hzy : z ≠ y := λ h => hy (h ▸ hz)
    rw [hpop z, hpop y, List.count_eq_one_of_mem hnd hz, List.count_eq_zero.mpr hy]
    simp [Ne.symm hzy]
  · split
    · rfl
    · rename_i hz hzy
      rw [hpop z, List.count_eq_zero.mpr hz]
      simp [Ne.symm hzy]

/-- The first fork fires (on both sides). -/
private theorem foldChans_fork₁ [DecidableEq χ] {y : χ} {outs outs' : List χ} {c : ChanMap χ V}
  {v : V} (hy : y ∈ outs) (hnd : outs.Nodup) (hnd' : outs'.Nodup)
  (hdisj : outs'.Disjoint outs) :
    foldChans y outs' (λ z => c z ++ ChanMap.pushed outs (List.replicate outs.length v) z) =
      λ z => foldChans y outs' c z ++
        ChanMap.pushed (outs.erase y ++ outs') (List.replicate (outs.erase y ++ outs').length v) z := by
  funext z
  unfold foldChans
  simp only [pushed_replicate, List.count_append]
  have hy' : y ∉ outs' := λ h => hdisj h hy
  split
  · rename_i hz
    have hz' : z ∉ outs := λ h => hdisj hz h
    have hzy : z ≠ y := λ h => hz' (h ▸ hy)
    rw [List.count_eq_zero.mpr hz', List.count_eq_one_of_mem hnd hy, List.count_erase_of_ne hzy,
      List.count_eq_zero.mpr hz', List.count_eq_one_of_mem hnd' hz]
    simp
  · split
    · subst_vars
      rw [List.count_erase_self, List.count_eq_one_of_mem hnd hy, List.count_eq_zero.mpr hy']
      simp
    · rename_i hz hzy
      rw [List.count_erase_of_ne hzy, List.count_eq_zero.mpr hz]
      simp

theorem fork_fork_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k k' : Nat} {input input' : χ} {outputs outputs' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.fork k) [input] outputs))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork k') [input'] outputs'))
  (hne : i₂ ≠ i₁)
  (hlen : outputs.length = k) (hlen' : outputs'.length = k')
  (hmem : input' ∈ outputs) :
    RuleOK proc [i₂, i₁] [.fork input (outputs.erase input' ++ outputs').toVector]
  := by
  subst hlen hlen'
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.fork outputs'.length) [input'] outputs',
        .async (.fork outputs.length) [input] outputs] := by
    simp [h₁, h₂]
  have hP' : ([.fork input (outputs.erase input' ++ outputs').toVector] : AtomicProcs Op χ V) =
      [.async (.fork (outputs.erase input' ++ outputs').length) [input]
        (outputs.erase input' ++ outputs')] := by
    simp [AtomicProc.fork, toList_toVector]
  -- Facts from affineness
  have hnd : outputs.Nodup := by simpa using (haff.atom_nodup h₁).2
  have hnd' : outputs'.Nodup := by simpa using (haff.atom_nodup h₂).2
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  have hii : input' ≠ input := Ne.symm (by simpa using hdisj.1)
  have hdisj' : outputs'.Disjoint outputs := by simpa using hdisj.2
  have hio : input' ∉ outputs' := λ h => hdisj' h hmem
  -- The values in `input'` are already in `outputs'` after the rewrite.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.fork input (outputs.erase input' ++ outputs').toVector] ∧
    chans₁ = foldChans input' outputs' chans₀, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP']
    · simpa [hP'] using (hnd.erase input').append hnd'
        (λ x hx hx' => hdisj' hx' (List.mem_of_mem_erase hx))
    · simp [hP', hP]
    · intro x hx
      simp only [hP', AtomicProcs.outputNames_cons, AtomicProc.outputs_async,
        AtomicProcs.outputNames_nil, List.append_nil, List.mem_append] at hx
      left
      rcases hx with hx | hx
      · simp [hP, List.mem_of_mem_erase hx]
      · simp [hP, hx]
  · constructor
    · exact ⟨rfl, rfl, foldChans_empty.symm⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, rfl⟩ hpop
      have hxi : x ≠ input' := λ h => hx (by simp [hP, h])
      exact ⟨_, foldChans_pop (λ z => if z = x then [v] else []) (by simp [Ne.symm hxi]) hpop,
        rfl, rfl, rfl⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, rfl⟩
      have hout : ∀ z, z ∈ outputs' ∨ z ∈ outputs → z ∉ outs := λ z hz h => by
        simpa [hP, hz] using (hx z h).1
      refine ⟨rfl, rfl, (foldChans_push (ChanMap.pushed outs vals) ?_ ?_).symm⟩
      · exact ChanMap.pushed_not_mem (hout _ (.inr hmem))
      · exact λ z hz => ChanMap.pushed_not_mem (hout _ (.inl hz))
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs₀ outputs₀ inputVals outputVals chans₀' _ _ ⟨rfl, rfl, rfl⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The second fork fires: its outputs already have the value after the rewrite.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, hout, -, v, rfl, -, rfl⟩ := hinterp.fork_inv hlen₁
        subst outputs₀
        exact ⟨_, _, .refl, by simp, rfl, (foldChans_fork₂ hio hnd' hpop).symm⟩
      | 1, hget =>
        -- The first fork fires: the rewritten fork fires with the same value.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, hout, -, v, rfl, hclone, rfl⟩ := hinterp.fork_inv hlen₁
        subst outputs₀
        refine ⟨_, _, fork_step (x := input) (outs := outputs.erase input' ++ outputs')
          (by simp) hclone
          (foldChans_pop (ChanMap.pushed [input] [v]) (by simp [Ne.symm hii]) hpop),
          by simp, rfl, (foldChans_fork₁ hmem hnd hnd' hdisj').symm⟩
  · rintro L₁ chans₁ ⟨_, rfl, rfl⟩
    exact ⟨rfl, foldChans_empty⟩

end Wavelet.Compile.DeadCodeElim
