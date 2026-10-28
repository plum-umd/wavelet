import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstLemmas

/-! `merge-same-const`/`merge-true-false-const`: merging constants. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ConstLemmas

/-- Channels for `merge-same-const`: the activations consumed by the original constants are still
in `input₁`/`input₂` after the rewrite; `inputL`, `inputR` and `r` are empty after the rewrite. -/
private structure SameConstChans (input₁ inputL input₂ inputR r : χ) (v : V)
    (chans₀ chans₁ : ChanMap χ V) : Prop where
  left : ∃ X, chans₁ input₁ = X ++ chans₀ input₁ ∧ X.length = (chans₀ inputL).length
  right : ∃ X, chans₁ input₂ = X ++ chans₀ input₂ ∧ X.length = (chans₀ inputR).length
  valsL : ∀ w ∈ chans₀ inputL, w = v
  valsR : ∀ w ∈ chans₀ inputR, w = v
  emptyL : chans₁ inputL = []
  emptyR : chans₁ inputR = []
  emptyr : chans₁ r = []
  eq : ∀ y, y ≠ input₁ → y ≠ input₂ → y ≠ inputL → y ≠ inputR → y ≠ r → chans₀ y = chans₁ y

theorem merge_same_const_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {decider inputL inputR output input₁ input₂ r : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.const v 1) [input₁] [inputL]))
  (h₃ : proc.atoms[i₃]? = some (.async (.const v 1) [input₂] [inputR]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hr : r ∉ proc.allNames) :
    RuleOK proc [i₃, i₂, i₁] [
      .merge decider #v[input₁] #v[input₂] #v[r],
      .const v r #v[output],
    ]
  := by
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] =
      [.async (.const v 1) [input₂] [inputR], .async (.const v 1) [input₁] [inputL],
        .async (.merge .decider 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂, h₃]
  have hP' : ([.merge decider #v[input₁] #v[input₂] #v[r], .const v r #v[output]] :
      AtomicProcs Op χ V) =
      [.async (.merge .decider 1) [decider, input₁, input₂] [r],
        .async (.const v 1) [r] [output]] := by
    simp [AtomicProc.merge, AtomicProc.const]
  -- Facts from affineness and freshness
  have hnd := (haff.atom_nodup h₁).1
  have hd₂₁ := haff.atom_disjoint h₂ h₁ hne₂₁
  have hd₃₁ := haff.atom_disjoint h₃ h₁ hne₃₁
  have hd₃₂ := haff.atom_disjoint h₃ h₂ hne₃₂
  simp at hnd hd₂₁ hd₃₁ hd₃₂
  obtain ⟨⟨hdl, hdr⟩, hlr⟩ := hnd
  obtain ⟨⟨h1d, h1l, h1r⟩, hol⟩ := hd₂₁
  obtain ⟨⟨h2d, h2l, h2r⟩, hor⟩ := hd₃₁
  obtain ⟨h12, -⟩ := hd₃₂
  have hrd : r ≠ decider := ne_of_fresh_input hr h₁ (by simp)
  have hrl : r ≠ inputL := ne_of_fresh_input hr h₁ (by simp)
  have hrr : r ≠ inputR := ne_of_fresh_input hr h₁ (by simp)
  have hro : r ≠ output := ne_of_fresh_output hr h₁ (by simp)
  have hr1 : r ≠ input₁ := ne_of_fresh_input hr h₂ (by simp)
  have hr2 : r ≠ input₂ := ne_of_fresh_input hr h₃ (by simp)
  -- Both merges are in the same state; the rewritten const fires right after
  -- the rewritten merge reads `input₁` or `input₂`.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ => ∃ st,
    L₀ = [.async (.const v 1) [input₂] [inputR], .async (.const v 1) [input₁] [inputL],
      .async (.merge st 1) [decider, inputL, inputR] [output]] ∧
    L₁ = [.async (.merge st 1) [decider, input₁, input₂] [r], .async (.const v 1) [r] [output]] ∧
    SameConstChans input₁ inputL input₂ inputR r v chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne₃₂, hne₃₁, hne₂₁]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
        (List.getElem?_eq_some_iff.mp h₃).1]
    · simp [hP', Ne.symm h1d, Ne.symm h2d, Ne.symm hrd, h12, Ne.symm hr1, Ne.symm hr2]
    · simp [hP', hro]
    · simp [hP', hP, hr]
    · simp [hP', hP, hr]
  · constructor
    · exact ⟨.decider, hP, hP', ⟨[], by simp, by simp⟩, ⟨[], by simp, by simp⟩, by simp, by simp,
        rfl, rfl, rfl, λ _ _ _ _ _ _ => rfl⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx₁ hx₂ ⟨st, rfl, rfl, hc⟩ hpop
      have hx1 : x ≠ input₁ := by rintro rfl; simp [hP] at hx₁
      have hx2 : x ≠ input₂ := by rintro rfl; simp [hP] at hx₁
      have hxl : x ≠ inputL := by rintro rfl; simp [hP] at hx₁
      have hxr : x ≠ inputR := by rintro rfl; simp [hP] at hx₁
      have hxr' : x ≠ r := by rintro rfl; simp [hP'] at hx₂
      obtain ⟨hx₀, h₀⟩ := ChanMap.frame_pop_inv hpop
      obtain ⟨chans₁', hpop₁, hx₁', h₁'⟩ := ChanMap.frame_pop_head
        (chans := chans₁) (x := x) (w := w) (rest := chans₀' x)
        (by rw [← hc.eq x hx1 hx2 hxl hxr hxr', hx₀])
      obtain ⟨X₁, hX₁, hX₁len⟩ := hc.left
      obtain ⟨X₂, hX₂, hX₂len⟩ := hc.right
      refine ⟨chans₁', hpop₁, st, rfl, rfl, ⟨X₁, ?_, ?_⟩, ⟨X₂, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h₁' _ (Ne.symm hx1), h₀ _ (Ne.symm hx1), hX₁]
      · rw [h₀ _ (Ne.symm hxl), hX₁len]
      · rw [h₁' _ (Ne.symm hx2), h₀ _ (Ne.symm hx2), hX₂]
      · rw [h₀ _ (Ne.symm hxr), hX₂len]
      · rw [h₀ _ (Ne.symm hxl)]; exact hc.valsL
      · rw [h₀ _ (Ne.symm hxr)]; exact hc.valsR
      · rw [h₁' _ (Ne.symm hxl), hc.emptyL]
      · rw [h₁' _ (Ne.symm hxr), hc.emptyR]
      · rw [h₁' _ (Ne.symm hxr'), hc.emptyr]
      · intro y hy1 hy2 hyl hyr hyr'
        by_cases hyx : y = x
        · subst hyx; rw [hx₁']
        · rw [h₁' _ hyx, h₀ _ hyx, hc.eq y hy1 hy2 hyl hyr hyr']
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨st, rfl, rfl, hc⟩
      have hl : inputL ∉ outs := λ h => by simpa [hP] using (hx inputL h).1
      have hr₀ : inputR ∉ outs := λ h => by simpa [hP] using (hx inputR h).1
      have hr' : r ∉ outs := λ h => by simpa [hP'] using (hx r h).2
      obtain ⟨X₁, hX₁, hX₁len⟩ := hc.left
      obtain ⟨X₂, hX₂, hX₂len⟩ := hc.right
      refine ⟨st, rfl, rfl, ⟨X₁, by simp [hX₁], by simp [ChanMap.pushed_not_mem hl, hX₁len]⟩,
        ⟨X₂, by simp [hX₂], by simp [ChanMap.pushed_not_mem hr₀, hX₂len]⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [ChanMap.pushed_not_mem hl] using hc.valsL
      · simpa [ChanMap.pushed_not_mem hr₀] using hc.valsR
      · simp [ChanMap.pushed_not_mem hl, hc.emptyL]
      · simp [ChanMap.pushed_not_mem hr₀, hc.emptyR]
      · simp [ChanMap.pushed_not_mem hr', hc.emptyr]
      · intro y hy1 hy2 hyl hyr hyr'
        simp [hc.eq y hy1 hy2 hyl hyr hyr']
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨st, rfl, rfl, _⟩ hmem
      simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨st, rfl, rfl, hc⟩ hget hinterp hlen₁ _ hpop
      obtain ⟨X₁, hX₁, hX₁len⟩ := hc.left
      obtain ⟨X₂, hX₂, hX₂len⟩ := hc.right
      match i, hget with
      | 0, hget =>
        -- The const of `inputR` fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨_, av, -, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        have hp := hpop input₂
        simp at hp
        have h₀ : ∀ y, y ≠ input₂ → chans₀' y = chans₀ y := λ y hy => by
          simpa [Ne.symm hy] using (hpop y).symm
        refine ⟨_, _, .refl, st, by simp, rfl, ⟨X₁, ?_, ?_⟩, ⟨X₂ ++ [av], ?_, ?_⟩, ?_, ?_,
          hc.emptyL, hc.emptyR, hc.emptyr, ?_⟩
        · simp [hX₁, h₀ _ h12, Ne.symm h1r]
        · simp [h₀ _ (Ne.symm h2l), Ne.symm hlr, hX₁len]
        · simp [hX₂, hp, Ne.symm h2r]
        · simp [h₀ _ (Ne.symm h2r), hX₂len]
        · simpa [h₀ _ (Ne.symm h2l), Ne.symm hlr] using hc.valsL
        · intro w hw
          simp [h₀ _ (Ne.symm h2r)] at hw
          rcases hw with hw | rfl
          · exact hc.valsR w hw
          · rfl
        · intro y hy1 hy2 hyl hyr hyr'
          simp [Ne.symm hyr, h₀ _ hy2, hc.eq y hy1 hy2 hyl hyr hyr']
      | 1, hget =>
        -- The const of `inputL` fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨_, av, -, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        have hp := hpop input₁
        simp at hp
        have h₀ : ∀ y, y ≠ input₁ → chans₀' y = chans₀ y := λ y hy => by
          simpa [Ne.symm hy] using (hpop y).symm
        refine ⟨_, _, .refl, st, by simp, rfl, ⟨X₁ ++ [av], ?_, ?_⟩, ⟨X₂, ?_, ?_⟩, ?_, ?_,
          hc.emptyL, hc.emptyR, hc.emptyr, ?_⟩
        · simp [hX₁, hp, Ne.symm h1l]
        · simp [h₀ _ (Ne.symm h1l), hX₁len]
        · simp [hX₂, h₀ _ (Ne.symm h12), Ne.symm h2l]
        · simp [h₀ _ (Ne.symm h1r), hlr, hX₂len]
        · intro w hw
          simp [h₀ _ (Ne.symm h1l)] at hw
          rcases hw with hw | rfl
          · exact hc.valsL w hw
          · rfl
        · simpa [h₀ _ (Ne.symm h1r), hlr] using hc.valsR
        · intro y hy1 hy2 hyl hyr hyr'
          simp [Ne.symm hyl, h₀ _ hy1, hc.eq y hy1 hy2 hyl hyr hyr']
      | 2, hget =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        rcases hinterp.merge_inv hlen₁ with
          ⟨rfl, rfl, rfl, rfl, w, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, w, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
        · -- `popLeft`: the rewritten merge reads the head of `X₁`, then the rewritten const fires.
          have hp := hpop inputL
          simp at hp
          have h₀ : ∀ y, y ≠ inputL → chans₀' y = chans₀ y := λ y hy => by
            simpa [Ne.symm hy] using (hpop y).symm
          have hw : w = v := hc.valsL w (by simp [hp])
          cases X₁ with
          | nil => simp [hp] at hX₁len
          | cons x₀ X₁ =>
          have hX₁len' : X₁.length = (chans₀' inputL).length := by simpa [hp] using hX₁len
          rw [List.cons_append] at hX₁
          obtain ⟨M₁, hpop₁, hM₁1, hM₁⟩ := ChanMap.pop_one hX₁
          have hstep₁ := LocalTauStar.async_list (i := 0)
            (L := ([.async (.merge .popLeft 1) [decider, input₁, input₂] [r],
              .async (.const v 1) [r] [output]] : AtomicProcs Op χ V))
            (aop := .merge .popLeft 1) (aop' := .merge .decider 1)
            (allInputs := [decider, input₁, input₂]) (allOutputs := [r])
            (inputs := [input₁]) (inputVals := [x₀]) (outputs := [r]) (outputVals := [x₀])
            (by simp) (.interp_merge_left rfl rfl) rfl rfl hpop₁
          obtain ⟨M₂, hpop₂, hM₂r, hM₂⟩ := ChanMap.pop_one
            (chans := λ y => M₁ y ++ ChanMap.pushed [r] [x₀] y) (x := r) (w := x₀) (rest := [])
            (by simp [hM₁ r hr1, hc.emptyr])
          have hstep₂ := LocalTauStar.async_list_mem
            (L := ([.async (.merge .decider 1) [decider, input₁, input₂] [r],
              .async (.const v 1) [r] [output]] : AtomicProcs Op χ V))
            (aop := .const v 1) (allInputs := [r]) (allOutputs := [output])
            (outputs := [output]) (outputVals := [v])
            (by simp) (.interp_const rfl) rfl rfl hpop₂
          refine ⟨_, _, (hstep₁.eq_rhs (by simp) rfl).trans hstep₂, .decider, by simp, rfl,
            ⟨X₁, ?_, ?_⟩, ⟨X₂, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hM₂ input₁ (Ne.symm hr1), hM₁1, hr1, h₀ _ h1l, hw]
          · simp [hol, hX₁len']
          · simp [hM₂ input₂ (Ne.symm hr2), hM₁ input₂ (Ne.symm h12), hX₂, hr2, h₀ _ h2l, hw]
          · simp [h₀ _ (Ne.symm hlr), hor, hX₂len]
          · intro w' hw'
            simp [hol] at hw'
            exact hc.valsL w' (by simp [hp, hw'])
          · intro w' hw'
            simp [h₀ _ (Ne.symm hlr), hor] at hw'
            exact hc.valsR w' hw'
          · simp [hM₂ inputL (Ne.symm hrl), hM₁ inputL (Ne.symm h1l), hc.emptyL, hrl, hol]
          · simp [hM₂ inputR (Ne.symm hrr), hM₁ inputR (Ne.symm h1r), hc.emptyR, hrr, hor]
          · simp [hM₂r, Ne.symm hro]
          · intro y hy1 hy2 hyl hyr hyr'
            simp [hM₂ y hyr', hM₁ y hy1, Ne.symm hyr', h₀ y hyl, hc.eq y hy1 hy2 hyl hyr hyr', hw]
        · -- `popRight`: the rewritten merge reads the head of `X₂`, then the rewritten const fires.
          have hp := hpop inputR
          simp at hp
          have h₀ : ∀ y, y ≠ inputR → chans₀' y = chans₀ y := λ y hy => by
            simpa [Ne.symm hy] using (hpop y).symm
          have hw : w = v := hc.valsR w (by simp [hp])
          cases X₂ with
          | nil => simp [hp] at hX₂len
          | cons x₀ X₂ =>
          have hX₂len' : X₂.length = (chans₀' inputR).length := by simpa [hp] using hX₂len
          rw [List.cons_append] at hX₂
          obtain ⟨M₁, hpop₁, hM₁2, hM₁⟩ := ChanMap.pop_one hX₂
          have hstep₁ := LocalTauStar.async_list (i := 0)
            (L := ([.async (.merge .popRight 1) [decider, input₁, input₂] [r],
              .async (.const v 1) [r] [output]] : AtomicProcs Op χ V))
            (aop := .merge .popRight 1) (aop' := .merge .decider 1)
            (allInputs := [decider, input₁, input₂]) (allOutputs := [r])
            (inputs := [input₂]) (inputVals := [x₀]) (outputs := [r]) (outputVals := [x₀])
            (by simp) (.interp_merge_right rfl rfl) rfl rfl hpop₁
          obtain ⟨M₂, hpop₂, hM₂r, hM₂⟩ := ChanMap.pop_one
            (chans := λ y => M₁ y ++ ChanMap.pushed [r] [x₀] y) (x := r) (w := x₀) (rest := [])
            (by simp [hM₁ r hr2, hc.emptyr])
          have hstep₂ := LocalTauStar.async_list_mem
            (L := ([.async (.merge .decider 1) [decider, input₁, input₂] [r],
              .async (.const v 1) [r] [output]] : AtomicProcs Op χ V))
            (aop := .const v 1) (allInputs := [r]) (allOutputs := [output])
            (outputs := [output]) (outputVals := [v])
            (by simp) (.interp_const rfl) rfl rfl hpop₂
          refine ⟨_, _, (hstep₁.eq_rhs (by simp) rfl).trans hstep₂, .decider, by simp, rfl,
            ⟨X₁, ?_, ?_⟩, ⟨X₂, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hM₂ input₁ (Ne.symm hr1), hM₁ input₁ h12, hX₁, hr1, h₀ _ h1r, hw]
          · simp [h₀ _ hlr, hol, hX₁len]
          · simp [hM₂ input₂ (Ne.symm hr2), hM₁2, hr2, h₀ _ h2r, hw]
          · simp [hor, hX₂len']
          · intro w' hw'
            simp [h₀ _ hlr, hol] at hw'
            exact hc.valsL w' hw'
          · intro w' hw'
            simp [hor] at hw'
            exact hc.valsR w' (by simp [hp, hw'])
          · simp [hM₂ inputL (Ne.symm hrl), hM₁ inputL (Ne.symm h2l), hc.emptyL, hrl, hol]
          · simp [hM₂ inputR (Ne.symm hrr), hM₁ inputR (Ne.symm h2r), hc.emptyR, hrr, hor]
          · simp [hM₂r, Ne.symm hro]
          · intro y hy1 hy2 hyl hyr hyr'
            simp [hM₂ y hyr', hM₁ y hy2, Ne.symm hyr', h₀ y hyr, hc.eq y hy1 hy2 hyl hyr hyr', hw]
        · -- `decider`: both merges read the decider.
          have hp := hpop decider
          simp at hp
          have h₀ : ∀ y, y ≠ decider → chans₀' y = chans₀ y := λ y hy => by
            simpa [Ne.symm hy] using (hpop y).symm
          have hd₁ : chans₁ decider = dv :: chans₀' decider := by
            rw [← hc.eq decider (Ne.symm h1d) (Ne.symm h2d) hdl hdr (Ne.symm hrd), hp]
          obtain ⟨M₁, hpop₁, hM₁d, hM₁⟩ := ChanMap.pop_one hd₁
          have hstep := LocalTauStar.async_list (i := 0)
            (L := ([.async (.merge .decider 1) [decider, input₁, input₂] [r],
              .async (.const v 1) [r] [output]] : AtomicProcs Op χ V))
            (aop := .merge .decider 1)
            (allInputs := [decider, input₁, input₂]) (allOutputs := [r])
            (inputs := [decider]) (inputVals := [dv]) (outputs := []) (outputVals := [])
            (by simp) (.interp_merge_decider (inputs := [input₁, input₂]) rfl rfl hb) rfl rfl hpop₁
          refine ⟨_, _, hstep, if b then .popRight else .popLeft, by simp, by simp,
            ⟨X₁, ?_, ?_⟩, ⟨X₂, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hM₁ input₁ h1d, hX₁, h₀ _ h1d]
          · simp [h₀ _ (Ne.symm hdl), hX₁len]
          · simp [hM₁ input₂ h2d, hX₂, h₀ _ h2d]
          · simp [h₀ _ (Ne.symm hdr), hX₂len]
          · simpa [h₀ _ (Ne.symm hdl)] using hc.valsL
          · simpa [h₀ _ (Ne.symm hdr)] using hc.valsR
          · simp [hM₁ inputL (Ne.symm hdl), hc.emptyL]
          · simp [hM₁ inputR (Ne.symm hdr), hc.emptyR]
          · simp [hM₁ r hrd, hc.emptyr]
          · intro y hy1 hy2 hyl hyr hyr'
            by_cases hyd : y = decider
            · subst hyd; simp [hM₁d]
            · simp [hM₁ y hyd, h₀ y hyd, hc.eq y hy1 hy2 hyl hyr hyr']
  · rintro L₁ chans₁ ⟨st, hL₀, rfl, hc⟩
    rw [hP] at hL₀
    simp at hL₀
    subst hL₀
    refine ⟨hP'.symm, ?_⟩
    obtain ⟨X₁, hX₁, hX₁len⟩ := hc.left
    obtain ⟨X₂, hX₂, hX₂len⟩ := hc.right
    simp at hX₁len hX₂len
    subst hX₁len hX₂len
    funext y
    by_cases hy1 : y = input₁
    · subst hy1; simpa using hX₁
    · by_cases hy2 : y = input₂
      · subst hy2; simpa using hX₂
      · by_cases hyl : y = inputL
        · subst hyl; exact hc.emptyL
        · by_cases hyr : y = inputR
          · subst hyr; exact hc.emptyR
          · by_cases hyr' : y = r
            · subst hyr'; exact hc.emptyr
            · exact (hc.eq y hy1 hy2 hyl hyr hyr').symm

/-- Values already pushed to the output by the rewritten forward but not yet by the original
merge in state `st`. -/
private def pending (v₁ v₂ : V) : AsyncOp.MergeState → List V
  | .popLeft => [v₁]
  | .popRight => [v₂]
  | .decider => []

theorem merge_true_false_const_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {decider inputL inputR output input₁ input₂ : χ} {v₁ v₂ : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.const v₁ 1) [input₁] [inputL]))
  (h₃ : proc.atoms[i₃]? = some (.async (.const v₂ 1) [input₂] [inputR]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hbool₁ : InterpConsts.toBool v₁ = some false)
  (hbool₂ : InterpConsts.toBool v₂ = some true) :
    RuleOK proc [i₃, i₂, i₁] [
      .forward #v[decider] #v[output],
      .sink #v[input₁],
      .sink #v[input₂],
    ]
  := by
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] =
      [.async (.const v₂ 1) [input₂] [inputR], .async (.const v₁ 1) [input₁] [inputL],
        .async (.merge .decider 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂, h₃]
  have hP' : ([.forward #v[decider] #v[output], .sink #v[input₁], .sink #v[input₂]] :
      AtomicProcs Op χ V) =
      [.async (.forward 1) [decider] [output], .async (.sink 1) [input₁] [],
        .async (.sink 1) [input₂] []] := by
    simp [AtomicProc.forward, AtomicProc.sink]
  -- Facts from affineness
  have hnd := (haff.atom_nodup h₁).1
  have hd₂₁ := haff.atom_disjoint h₂ h₁ hne₂₁
  have hd₃₁ := haff.atom_disjoint h₃ h₁ hne₃₁
  have hd₃₂ := haff.atom_disjoint h₃ h₂ hne₃₂
  simp at hnd hd₂₁ hd₃₁ hd₃₂
  obtain ⟨⟨hdl, hdr⟩, hlr⟩ := hnd
  obtain ⟨⟨h1d, h1l, h1r⟩, hol⟩ := hd₂₁
  obtain ⟨⟨h2d, h2l, h2r⟩, hor⟩ := hd₃₁
  obtain ⟨h12, -⟩ := hd₃₂
  -- The rewritten forward is ahead of the original merge by the pending value; the consts
  -- fire together with the sinks after the rewrite; `inputL`, `inputR` are empty after the rewrite.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ => ∃ st,
    L₀ = [.async (.const v₂ 1) [input₂] [inputR], .async (.const v₁ 1) [input₁] [inputL],
      .async (.merge st 1) [decider, inputL, inputR] [output]] ∧
    L₁ = [.async (.forward 1) [decider] [output], .async (.sink 1) [input₁] [],
      .async (.sink 1) [input₂] []] ∧
    (∀ w ∈ chans₀ inputL, w = v₁) ∧ (∀ w ∈ chans₀ inputR, w = v₂) ∧
    chans₁ inputL = [] ∧ chans₁ inputR = [] ∧
    (∀ y, y ≠ inputL → y ≠ inputR →
      chans₁ y = chans₀ y ++ ChanMap.pushed [output] (pending v₁ v₂ st) y), ?_, ?_⟩
  · constructor
    · simp [hne₃₂, hne₃₁, hne₂₁]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
        (List.getElem?_eq_some_iff.mp h₃).1]
    · simp [hP', Ne.symm h1d, Ne.symm h2d, h12]
    · simp [hP']
    · simp [hP', hP]
    · simp [hP', hP]
  · constructor
    · exact ⟨.decider, hP, hP', by simp, by simp, rfl, rfl, λ _ _ _ => by simp [pending]⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx₁ _ ⟨st, rfl, rfl, hvl, hvr, hel, her, heq⟩ hpop
      have hxl : x ≠ inputL := by rintro rfl; simp [hP] at hx₁
      have hxr : x ≠ inputR := by rintro rfl; simp [hP] at hx₁
      obtain ⟨hx₀, h₀⟩ := ChanMap.frame_pop_inv hpop
      obtain ⟨chans₁', hpop₁, hx₁', h₁'⟩ := ChanMap.frame_pop_head
        (chans := chans₁) (x := x) (w := w)
        (rest := chans₀' x ++ ChanMap.pushed [output] (pending v₁ v₂ st) x)
        (by rw [heq x hxl hxr, hx₀, List.cons_append])
      refine ⟨chans₁', hpop₁, st, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h₀ _ (Ne.symm hxl)]; exact hvl
      · rw [h₀ _ (Ne.symm hxr)]; exact hvr
      · rw [h₁' _ (Ne.symm hxl), hel]
      · rw [h₁' _ (Ne.symm hxr), her]
      · intro y hyl hyr
        by_cases hyx : y = x
        · subst hyx; rw [hx₁']
        · rw [h₁' _ hyx, h₀ _ hyx, heq y hyl hyr]
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨st, rfl, rfl, hvl, hvr, hel, her, heq⟩
      have hl : inputL ∉ outs := λ h => by simpa [hP] using (hx inputL h).1
      have hr₀ : inputR ∉ outs := λ h => by simpa [hP] using (hx inputR h).1
      have ho : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      refine ⟨st, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [ChanMap.pushed_not_mem hl] using hvl
      · simpa [ChanMap.pushed_not_mem hr₀] using hvr
      · simp [ChanMap.pushed_not_mem hl, hel]
      · simp [ChanMap.pushed_not_mem hr₀, her]
      · intro y hyl hyr
        simp only [heq y hyl hyr]
        by_cases hyo : y = output
        · subst hyo; simp [ChanMap.pushed_not_mem ho]
        · simp [ChanMap.pushed_not_mem (show y ∉ [output] by simpa using hyo)]
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨st, rfl, rfl, _⟩ hmem
      simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨st, rfl, rfl, hvl, hvr, hel, her, heq⟩
        hget hinterp hlen₁ _ hpop
      match i, hget with
      | 0, hget =>
        -- The const of `inputR` fires: the rewritten sink of `input₂` fires.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨_, av, -, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        have hp := hpop input₂
        simp at hp
        have h₀ : ∀ y, y ≠ input₂ → chans₀' y = chans₀ y := λ y hy => by
          simpa [Ne.symm hy] using (hpop y).symm
        obtain ⟨M₁, hpop₁, hM₁2, hM₁⟩ := ChanMap.pop_one (chans := chans₁) (x := input₂) (w := av)
          (rest := chans₀' input₂ ++ ChanMap.pushed [output] (pending v₁ v₂ st) input₂)
          (by rw [heq input₂ h2l h2r, hp, List.cons_append])
        have hstep := LocalTauStar.async_list_mem
          (L := ([.async (.forward 1) [decider] [output], .async (.sink 1) [input₁] [],
            .async (.sink 1) [input₂] []] : AtomicProcs Op χ V))
          (aop := .sink 1) (allInputs := [input₂]) (allOutputs := [])
          (inputs := [input₂]) (outputs := []) (outputVals := [])
          (by simp) (.interp_sink rfl) rfl rfl hpop₁
        refine ⟨_, _, hstep, st, by simp, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [h₀ _ (Ne.symm h2l), Ne.symm hlr] using hvl
        · intro w hw
          simp [h₀ _ (Ne.symm h2r)] at hw
          rcases hw with hw | rfl
          · exact hvr w hw
          · rfl
        · simp [hM₁ inputL (Ne.symm h2l), hel]
        · simp [hM₁ inputR (Ne.symm h2r), her]
        · intro y hyl hyr
          by_cases hy2 : y = input₂
          · subst hy2; simp [hM₁2, Ne.symm h2r]
          · simp [hM₁ y hy2, heq y hyl hyr, h₀ y hy2, Ne.symm hyr]
      | 1, hget =>
        -- The const of `inputL` fires: the rewritten sink of `input₁` fires.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨_, av, -, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        have hp := hpop input₁
        simp at hp
        have h₀ : ∀ y, y ≠ input₁ → chans₀' y = chans₀ y := λ y hy => by
          simpa [Ne.symm hy] using (hpop y).symm
        obtain ⟨M₁, hpop₁, hM₁1, hM₁⟩ := ChanMap.pop_one (chans := chans₁) (x := input₁) (w := av)
          (rest := chans₀' input₁ ++ ChanMap.pushed [output] (pending v₁ v₂ st) input₁)
          (by rw [heq input₁ h1l h1r, hp, List.cons_append])
        have hstep := LocalTauStar.async_list_mem
          (L := ([.async (.forward 1) [decider] [output], .async (.sink 1) [input₁] [],
            .async (.sink 1) [input₂] []] : AtomicProcs Op χ V))
          (aop := .sink 1) (allInputs := [input₁]) (allOutputs := [])
          (inputs := [input₁]) (outputs := []) (outputVals := [])
          (by simp) (.interp_sink rfl) rfl rfl hpop₁
        refine ⟨_, _, hstep, st, by simp, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · intro w hw
          simp [h₀ _ (Ne.symm h1l)] at hw
          rcases hw with hw | rfl
          · exact hvl w hw
          · rfl
        · simpa [h₀ _ (Ne.symm h1r), hlr] using hvr
        · simp [hM₁ inputL (Ne.symm h1l), hel]
        · simp [hM₁ inputR (Ne.symm h1r), her]
        · intro y hyl hyr
          by_cases hy1 : y = input₁
          · subst hy1; simp [hM₁1, Ne.symm h1l]
          · simp [hM₁ y hy1, heq y hyl hyr, h₀ y hy1, Ne.symm hyl]
      | 2, hget =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        rcases hinterp.merge_inv hlen₁ with
          ⟨rfl, rfl, rfl, rfl, w, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, w, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
        · -- `popLeft`: the rewritten forward already pushed this value.
          have hp := hpop inputL
          simp at hp
          have h₀ : ∀ y, y ≠ inputL → chans₀' y = chans₀ y := λ y hy => by
            simpa [Ne.symm hy] using (hpop y).symm
          have hw : w = v₁ := hvl w (by simp [hp])
          refine ⟨_, _, .refl, .decider, by simp, rfl, ?_, ?_, hel, her, ?_⟩
          · intro w' hw'
            simp [hol] at hw'
            exact hvl w' (by simp [hp, hw'])
          · simpa [h₀ _ (Ne.symm hlr), hor] using hvr
          · intro y hyl hyr
            simp [heq y hyl hyr, h₀ y hyl, pending, hw]
        · -- `popRight`: the rewritten forward already pushed this value.
          have hp := hpop inputR
          simp at hp
          have h₀ : ∀ y, y ≠ inputR → chans₀' y = chans₀ y := λ y hy => by
            simpa [Ne.symm hy] using (hpop y).symm
          have hw : w = v₂ := hvr w (by simp [hp])
          refine ⟨_, _, .refl, .decider, by simp, rfl, ?_, ?_, hel, her, ?_⟩
          · simpa [h₀ _ hlr, hol] using hvl
          · intro w' hw'
            simp [hor] at hw'
            exact hvr w' (by simp [hp, hw'])
          · intro y hyl hyr
            simp [heq y hyl hyr, h₀ y hyr, pending, hw]
        · -- `decider`: the rewritten forward pushes the decider, which is the pending value.
          have hp := hpop decider
          simp at hp
          have h₀ : ∀ y, y ≠ decider → chans₀' y = chans₀ y := λ y hy => by
            simpa [Ne.symm hy] using (hpop y).symm
          have hd₁ : chans₁ decider = dv :: chans₀' decider := by
            rw [heq decider hdl hdr, hp]
            simp [pending]
          obtain ⟨M₁, hpop₁, hM₁d, hM₁⟩ := ChanMap.pop_one hd₁
          have hstep := LocalTauStar.async_list_mem
            (L := ([.async (.forward 1) [decider] [output], .async (.sink 1) [input₁] [],
              .async (.sink 1) [input₂] []] : AtomicProcs Op χ V))
            (aop := .forward 1) (allInputs := [decider]) (allOutputs := [output])
            (inputs := [decider]) (inputVals := [dv]) (outputs := [output]) (outputVals := [dv])
            (by simp) (.interp_forward rfl rfl) rfl rfl hpop₁
          have hpend : pending v₁ v₂ (if b then .popRight else .popLeft) = [dv] := by
            have hdv := InterpConsts.unique_toBool_fromBool _ _ hb
            cases b
            · simp [pending, hdv, InterpConsts.unique_toBool_fromBool _ _ hbool₁]
            · simp [pending, hdv, InterpConsts.unique_toBool_fromBool _ _ hbool₂]
          refine ⟨_, _, hstep, if b then .popRight else .popLeft, by simp, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [h₀ _ (Ne.symm hdl)] using hvl
          · simpa [h₀ _ (Ne.symm hdr)] using hvr
          · simp [hM₁ inputL (Ne.symm hdl), hel, hol]
          · simp [hM₁ inputR (Ne.symm hdr), her, hor]
          · intro y hyl hyr
            rw [hpend]
            by_cases hyd : y = decider
            · subst hyd; simp [hM₁d]
            · simp [hM₁ y hyd, heq y hyl hyr, h₀ y hyd, pending]
  · rintro L₁ chans₁ ⟨st, hL₀, rfl, -, -, hel, her, heq⟩
    rw [hP] at hL₀
    simp at hL₀
    subst hL₀
    refine ⟨hP'.symm, ?_⟩
    funext y
    by_cases hyl : y = inputL
    · subst hyl; exact hel
    · by_cases hyr : y = inputR
      · subst hyr; exact her
      · simpa [pending] using heq y hyl hyr

end Wavelet.Compile.DeadCodeElim
