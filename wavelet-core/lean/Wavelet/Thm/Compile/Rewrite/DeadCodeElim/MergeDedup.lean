import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ParLemmas

/-! `merge-dedup`: two merges with inputs from the same forks can be combined
(only a forward simulation without `PreservesInit`). -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ParLemmas

/-- `MergeRun st ds xs ys st' out`: a merge in state `st` reading exactly `ds`, `xs`, `ys`
from its decider, left and right inputs reaches state `st'` and outputs `out`. -/
private inductive MergeRun {V : Type _} [InterpConsts V] :
    AsyncOp.MergeState → List V → List V → List V → AsyncOp.MergeState → List V → Prop
  | refl {st} : MergeRun st [] [] [] st []
  | decider {dv b ds xs ys st out} : InterpConsts.toBool dv = some b →
    MergeRun (if b then .popRight else .popLeft) ds xs ys st out →
    MergeRun .decider (dv :: ds) xs ys st out
  | left {v ds xs ys st out} : MergeRun .decider ds xs ys st out →
    MergeRun .popLeft ds (v :: xs) ys st (v :: out)
  | right {v ds xs ys st out} : MergeRun .decider ds xs ys st out →
    MergeRun .popRight ds xs (v :: ys) st (v :: out)

section MergeRun

variable {V : Type _} [InterpConsts V] {st st' : AsyncOp.MergeState}
  {ds xs ys out : List V} {dv v : V} {b : Bool}

private theorem MergeRun.snoc_decider (h : MergeRun st ds xs ys st' out) (hst : st' = .decider)
  (hb : InterpConsts.toBool dv = some b) :
    MergeRun st (ds ++ [dv]) xs ys (if b then .popRight else .popLeft) out := by
  induction h with
  | refl => subst hst; exact .decider hb .refl
  | decider hb' _ ih => exact .decider hb' (ih hst)
  | left _ ih => exact .left (ih hst)
  | right _ ih => exact .right (ih hst)

private theorem MergeRun.snoc_left (h : MergeRun st ds xs ys st' out) (hst : st' = .popLeft) :
    MergeRun st ds (xs ++ [v]) ys .decider (out ++ [v]) := by
  induction h with
  | refl => subst hst; exact .left .refl
  | decider hb' _ ih => exact .decider hb' (ih hst)
  | left _ ih => exact .left (ih hst)
  | right _ ih => exact .right (ih hst)

private theorem MergeRun.snoc_right (h : MergeRun st ds xs ys st' out) (hst : st' = .popRight) :
    MergeRun st ds xs (ys ++ [v]) .decider (out ++ [v]) := by
  induction h with
  | refl => subst hst; exact .right .refl
  | decider hb' _ ih => exact .decider hb' (ih hst)
  | left _ ih => exact .left (ih hst)
  | right _ ih => exact .right (ih hst)

private theorem MergeRun.decider_cons_inv (h : MergeRun .decider (dv :: ds) xs ys st out)
  (hb : InterpConsts.toBool dv = some b) :
    MergeRun (if b then .popRight else .popLeft) ds xs ys st out := by
  cases h with
  | decider hb' h =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact h

private theorem MergeRun.decider_nil_inv (h : MergeRun .decider [] xs ys st out) :
    xs = [] ∧ ys = [] ∧ st = .decider ∧ out = [] := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem MergeRun.left_cons_inv (h : MergeRun .popLeft ds (v :: xs) ys st out) :
    ∃ out', out = v :: out' ∧ MergeRun .decider ds xs ys st out' := by
  cases h with
  | left h => exact ⟨_, rfl, h⟩

private theorem MergeRun.left_nil_inv (h : MergeRun .popLeft ds [] ys st out) :
    ds = [] ∧ ys = [] ∧ st = .popLeft ∧ out = [] := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem MergeRun.right_cons_inv (h : MergeRun .popRight ds xs (v :: ys) st out) :
    ∃ out', out = v :: out' ∧ MergeRun .decider ds xs ys st out' := by
  cases h with
  | right h => exact ⟨_, rfl, h⟩

private theorem MergeRun.right_nil_inv (h : MergeRun .popRight ds xs [] st out) :
    ds = [] ∧ xs = [] ∧ st = .popRight ∧ out = [] := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

end MergeRun

private theorem suffix_append_same {l₁ l₂ : List α} (h : l₁ <:+ l₂) (l : List α) :
    l₁ ++ l <:+ l₂ ++ l := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by simp⟩

private theorem suffix_of_eq_cons {l₁ l₂ l : List α} {v : α} (h : l = v :: l₁) (h' : l <:+ l₂) :
    l₁ <:+ l₂ :=
  (List.suffix_cons v l₁).trans (h ▸ h')

private theorem fork_inv' [InterpConsts V] {k : Nat} {ins ys inputs outputs : List χ}
  {inputVals outputVals : List V} {aop' : AsyncOp V}
  (h : (AsyncOp.fork k).Interp (.mk ins ys inputs inputVals outputs outputVals) aop') :
    ∃ x v, ins = [x] ∧ aop' = .fork k ∧ inputs = [x] ∧ outputs = ys ∧ ys.length = k ∧
      inputVals = [v] ∧ InterpConsts.isClonable v ∧ outputVals = List.replicate k v := by
  cases h with
  | interp_fork hk hclone => exact ⟨_, _, rfl, rfl, rfl, rfl, hk, rfl, hclone, rfl⟩

/-- The rewritten merge reads its decider. -/
private theorem merge_dec_tau [Arity Op] [DecidableEq χ] [InterpConsts V]
  {F S : AtomicProc Op χ V} {chans : ChanMap χ V}
  {d l rr r o o' : χ} {dv : V} {T : List V} {b : Bool}
  (hd : chans d = dv :: T) (hb : InterpConsts.toBool dv = some b) :
    LocalTauStar
      [F, .async (.merge .decider 1) [d, l, rr] [r], .async (.fork 2) [r] [o, o'], S] chans
      [F, .async (.merge (if b then .popRight else .popLeft) 1) [d, l, rr] [r],
        .async (.fork 2) [r] [o, o'], S]
      (λ y => if y = d then T else chans y) := by
  have := LocalTauStar.async_list (i := 1)
    (L := [F, .async (.merge .decider 1) [d, l, rr] [r], .async (.fork 2) [r] [o, o'], S])
    (chans := chans) (chans' := λ y => if y = d then T else chans y)
    (aop := .merge .decider 1) (aop' := .merge (if b then .popRight else .popLeft) 1)
    (allInputs := [d, l, rr]) (allOutputs := [r])
    (inputs := [d]) (inputVals := [dv]) (outputs := []) (outputVals := [])
    rfl (.interp_merge_decider (inputs := [l, rr]) (outputs := [r]) rfl rfl hb) rfl rfl (by
      intro y
      by_cases hy : y = d
      · subst hy; simp [hd]
      · simp [hy, Ne.symm hy])
  exact this.eq_rhs (by simp) (by funext y; simp)

/-- The rewritten merge reads a data input `x`, and its output is copied by the fork. -/
private theorem merge_data_fork_tau [Arity Op] [DecidableEq χ] [InterpConsts V]
  {F S : AtomicProc Op χ V} {chans : ChanMap χ V} {st : AsyncOp.MergeState}
  {d l rr r o o' x : χ} {v : V} {T : List V}
  (hinterp : (AsyncOp.merge st 1).Interp (.mk [d, l, rr] [r] [x] [v] [r] [v]) (.merge .decider 1))
  (hx : chans x = v :: T) (hr : chans r = []) (hclone : InterpConsts.isClonable v)
  (hrx : r ≠ x) (hro : r ≠ o) (hro' : r ≠ o') (hox : o ≠ x) (ho'x : o' ≠ x) (hoo' : o ≠ o') :
    ∃ chans', LocalTauStar
      [F, .async (.merge st 1) [d, l, rr] [r], .async (.fork 2) [r] [o, o'], S] chans
      [F, .async (.merge .decider 1) [d, l, rr] [r], .async (.fork 2) [r] [o, o'], S] chans' ∧
      chans' x = T ∧ chans' r = [] ∧ chans' o = chans o ++ [v] ∧ chans' o' = chans o' ++ [v] ∧
      ∀ y, y ≠ x → y ≠ o → y ≠ o' → chans' y = chans y := by
  have hstep₁ := LocalTauStar.async_list (i := 1)
    (L := [F, .async (.merge st 1) [d, l, rr] [r], .async (.fork 2) [r] [o, o'], S])
    (chans := chans) (chans' := λ y => if y = x then T else chans y)
    (aop := .merge st 1) (aop' := .merge .decider 1)
    (allInputs := [d, l, rr]) (allOutputs := [r])
    (inputs := [x]) (inputVals := [v]) (outputs := [r]) (outputVals := [v])
    rfl hinterp rfl rfl (by
      intro y
      by_cases hy : y = x
      · subst hy; simp [hx]
      · simp [hy, Ne.symm hy])
  have hstep₂ := LocalTauStar.async_list_mem
    (L := [F, .async (.merge .decider 1) [d, l, rr] [r], .async (.fork 2) [r] [o, o'], S])
    (chans := λ y => (if y = x then T else chans y) ++ ChanMap.pushed [r] [v] y)
    (chans' := λ y => if y = x then T else chans y)
    (aop := .fork 2) (allInputs := [r]) (allOutputs := [o, o'])
    (inputs := [r]) (inputVals := [v]) (outputs := [o, o']) (outputVals := [v, v])
    (by simp) (.interp_fork rfl hclone) rfl rfl (by
      intro y
      by_cases hy : y = r
      · subst hy; simp [hrx, hr]
      · simp [Ne.symm hy])
  refine ⟨_, (hstep₁.eq_rhs (by simp) rfl).trans hstep₂, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hox, ho'x]
  · simp [hrx, hr, Ne.symm hro, Ne.symm hro']
  · simp [hox, Ne.symm hoo']
  · simp [ho'x, hoo']
  · intro y hyx hyo hyo'
    simp [hyx, Ne.symm hyo, Ne.symm hyo']

theorem merge_dedup_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {k : Nat} {decider inputL inputR output decider' inputL' inputR' output' r : χ}
  {inputs₀ outputs₀ : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork k) inputs₀ outputs₀))
  (h₃ : proc.atoms[i₃]? = some (.async (.merge .decider 1) [decider', inputL', inputR'] [output']))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hfork₁ : SameFork proc.atoms decider decider')
  (hfork₂ : SameFork proc.atoms inputL inputL')
  (hfork₃ : SameFork proc.atoms inputR inputR')
  (hr : r ∉ proc.allNames) :
    RuleOKNoInit proc [i₃, i₂, i₁] [
      .async (.fork k) inputs₀ outputs₀,
      .merge decider #v[inputL] #v[inputR] #v[r],
      .fork r #v[output, output'],
      .sink #v[decider', inputL', inputR'],
    ]
  := by
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] = [
      .async (.merge .decider 1) [decider', inputL', inputR'] [output'],
      .async (.fork k) inputs₀ outputs₀,
      .async (.merge .decider 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂, h₃]
  have hP' : ([
      .async (.fork k) inputs₀ outputs₀,
      .merge decider #v[inputL] #v[inputR] #v[r],
      .fork r #v[output, output'],
      .sink #v[decider', inputL', inputR'],
    ] : AtomicProcs Op χ V) = [
      .async (.fork k) inputs₀ outputs₀,
      .async (.merge .decider 1) [decider, inputL, inputR] [r],
      .async (.fork 2) [r] [output, output'],
      .async (.sink 3) [decider', inputL', inputR'] []] := by
    simp [AtomicProc.merge, AtomicProc.sink, AtomicProc.fork]
  rw [hP']
  -- Facts from affineness
  have hn₁ := (haff.atom_nodup h₁).1
  have hn₃ := (haff.atom_nodup h₃).1
  have hn₀ := (haff.atom_nodup h₂).1
  have hno₀ := (haff.atom_nodup h₂).2
  simp at hn₁ hn₃
  have hdisj₃₁ := haff.atom_disjoint h₃ h₁ hne₃₁
  have hdisj₂₁ := haff.atom_disjoint h₂ h₁ hne₂₁
  have hdisj₃₂ := haff.atom_disjoint h₃ h₂ hne₃₂
  simp at hdisj₃₁ hdisj₂₁ hdisj₃₂
  obtain ⟨⟨hdL, hdR⟩, hLR⟩ := hn₁
  obtain ⟨⟨hd'L', hd'R'⟩, hL'R'⟩ := hn₃
  obtain ⟨⟨⟨hdd', hdL', hdR'⟩, ⟨hLd', hLL', hLR'⟩, hRd', hRL', hRR'⟩, hoo'⟩ := hdisj₃₁
  obtain ⟨⟨hd₀, hL₀, hR₀⟩, ho₀⟩ := hdisj₂₁
  obtain ⟨⟨hd'₀, hL'₀, hR'₀⟩, ho'₀⟩ := hdisj₃₂
  -- The copies are fork outputs, so not outputs of the merges
  have hnf₁ : ∀ k ins outs, (AtomicProc.async (.merge .decider 1) [decider, inputL, inputR]
      [output] : AtomicProc Op χ V) ≠ .async (.fork k) ins outs := by
    intro _ _ _ h; cases h
  have hnf₃ : ∀ k ins outs, (AtomicProc.async (.merge .decider 1) [decider', inputL', inputR']
      [output'] : AtomicProc Op χ V) ≠ .async (.fork k) ins outs := by
    intro _ _ _ h; cases h
  have hod : output ≠ decider := by
    have := SameFork.not_mem_outputs haff hfork₁ h₁ hnf₁; simp at this; exact Ne.symm this
  have hod' : output ≠ decider' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₁) h₁ hnf₁
    simp at this; exact Ne.symm this
  have hoL : output ≠ inputL := by
    have := SameFork.not_mem_outputs haff hfork₂ h₁ hnf₁; simp at this; exact Ne.symm this
  have hoL' : output ≠ inputL' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₂) h₁ hnf₁
    simp at this; exact Ne.symm this
  have hoR : output ≠ inputR := by
    have := SameFork.not_mem_outputs haff hfork₃ h₁ hnf₁; simp at this; exact Ne.symm this
  have hoR' : output ≠ inputR' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₃) h₁ hnf₁
    simp at this; exact Ne.symm this
  have ho'd : output' ≠ decider := by
    have := SameFork.not_mem_outputs haff hfork₁ h₃ hnf₃; simp at this; exact Ne.symm this
  have ho'd' : output' ≠ decider' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₁) h₃ hnf₃
    simp at this; exact Ne.symm this
  have ho'L : output' ≠ inputL := by
    have := SameFork.not_mem_outputs haff hfork₂ h₃ hnf₃; simp at this; exact Ne.symm this
  have ho'L' : output' ≠ inputL' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₂) h₃ hnf₃
    simp at this; exact Ne.symm this
  have ho'R : output' ≠ inputR := by
    have := SameFork.not_mem_outputs haff hfork₃ h₃ hnf₃; simp at this; exact Ne.symm this
  have ho'R' : output' ≠ inputR' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₃) h₃ hnf₃
    simp at this; exact Ne.symm this
  -- `r` is fresh
  have hrne : ∀ {x}, x ∈ proc.allNames → r ≠ x := λ hx h => hr (h ▸ hx)
  have hrd : r ≠ decider := hrne (Proc.mem_allNames_of_input h₁ (by simp))
  have hrL : r ≠ inputL := hrne (Proc.mem_allNames_of_input h₁ (by simp))
  have hrR : r ≠ inputR := hrne (Proc.mem_allNames_of_input h₁ (by simp))
  have hro : r ≠ output := hrne (Proc.mem_allNames_of_output h₁ (by simp))
  have hrd' : r ≠ decider' := hrne (Proc.mem_allNames_of_input h₃ (by simp))
  have hrL' : r ≠ inputL' := hrne (Proc.mem_allNames_of_input h₃ (by simp))
  have hrR' : r ≠ inputR' := hrne (Proc.mem_allNames_of_input h₃ (by simp))
  have hro' : r ≠ output' := hrne (Proc.mem_allNames_of_output h₃ (by simp))
  have hr₀ : r ∉ inputs₀ := λ h => hr (Proc.mem_allNames_of_input h₂ h)
  have hro₀ : r ∉ outputs₀ := λ h => hr (Proc.mem_allNames_of_output h₂ h)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hne₃₂, hne₃₁, hne₂₁]
  · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
      (List.getElem?_eq_some_iff.mp h₃).1]
  · simp only [AtomicProc.inputs_async] at hn₀
    simp [List.nodup_append, hn₀, hdL, hdR, hLR, hd'L', hd'R', hL'R', hdd', hdL', hdR', hLd', hLL',
      hLR', hRd', hRL', hRR', Ne.symm hrd, Ne.symm hrL, Ne.symm hrR, hrd', hrL', hrR']
    intro a ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> contradiction
  · simp only [AtomicProc.outputs_async] at hno₀
    simp [List.nodup_append, hno₀, hro, hro', hoo']
    intro a ha
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> contradiction
  · rw [hP]
    simp
    rintro x (hx | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · simp [hx]
    all_goals first | exact .inr hr | simp
  · rw [hP]
    simp
    rintro x (hx | rfl | rfl | rfl)
    · exact .inl (.inr (.inl hx))
    · exact .inr hr
    · exact .inl (.inr (.inr rfl))
    · exact .inl (.inl rfl)
  -- The rewritten merge runs as far as the faster original merge: `MergeRun st₁ D₁ X₁ Y₁ stR O₁`
  -- describes how `merge₁` catches up with it by reading `D₁`, `X₁`, `Y₁` (consumed ahead by the
  -- rewritten merge) and producing `O₁` (pending in `output`); similarly for `merge₂`.
  -- The rewritten sink never fires, so the inputs of `merge₂` are suffixes of the rewritten ones.
  refine ⟨λ L₀ chans₀ L₁ chans₁ => ∃ st₁ st₂ stR,
    L₀ = [.async (.merge st₂ 1) [decider', inputL', inputR'] [output'],
      .async (.fork k) inputs₀ outputs₀,
      .async (.merge st₁ 1) [decider, inputL, inputR] [output]] ∧
    L₁ = [.async (.fork k) inputs₀ outputs₀,
      .async (.merge stR 1) [decider, inputL, inputR] [r],
      .async (.fork 2) [r] [output, output'],
      .async (.sink 3) [decider', inputL', inputR'] []] ∧
    chans₁ r = [] ∧ (∀ v ∈ chans₁ inputL, InterpConsts.isClonable v) ∧
    (∀ v ∈ chans₁ inputR, InterpConsts.isClonable v) ∧
    chans₀ decider' <:+ chans₁ decider' ∧ chans₀ inputL' <:+ chans₁ inputL' ∧
    chans₀ inputR' <:+ chans₁ inputR' ∧
    ∃ D₁ X₁ Y₁ O₁ D₂ X₂ Y₂ O₂,
      MergeRun st₁ D₁ X₁ Y₁ stR O₁ ∧ MergeRun st₂ D₂ X₂ Y₂ stR O₂ ∧
      ((D₁ = [] ∧ X₁ = [] ∧ Y₁ = []) ∨ (D₂ = [] ∧ X₂ = [] ∧ Y₂ = [])) ∧
      chans₀ decider = D₁ ++ chans₁ decider ∧ chans₀ decider' = D₂ ++ chans₁ decider ∧
      chans₀ inputL = X₁ ++ chans₁ inputL ∧ chans₀ inputL' = X₂ ++ chans₁ inputL ∧
      chans₀ inputR = Y₁ ++ chans₁ inputR ∧ chans₀ inputR' = Y₂ ++ chans₁ inputR ∧
      ∀ y ∉ [decider, inputL, inputR, decider', inputL', inputR', r],
        chans₁ y = chans₀ y ++ (if y = output then O₁ else if y = output' then O₂ else []),
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · -- init
    refine ⟨.decider, .decider, .decider, hP, rfl, rfl, by simp, by simp,
      List.suffix_refl _, List.suffix_refl _, List.suffix_refl _,
      [], [], [], [], [], [], [], [], .refl, .refl, .inl ⟨rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro y _
    simp
  · -- frame_pop: `x` is not read by the merges
    rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx₀ hx₁
      ⟨st₁, st₂, stR, rfl, rfl, hr₁, hclL, hclR, hsd, hsL, hsR,
        D₁, X₁, Y₁, O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂, hlag, hd, hd', hL, hL', hR, hR', heq⟩ hpop
    rw [hP] at hx₀
    simp at hx₀ hx₁
    obtain ⟨hxd', hxL', hxR', -, hxd, hxL, hxR⟩ := hx₀
    have hxr : x ≠ r := hx₁.2.2.2.2.1
    have hpx : chans₀ x = v :: chans₀' x := by simpa using hpop x
    have hpy : ∀ y, y ≠ x → chans₀ y = chans₀' y := λ y hy => by simpa [hy] using hpop y
    have hxS : x ∉ [decider, inputL, inputR, decider', inputL', inputR', r] := by
      simp [hxd, hxL, hxR, hxd', hxL', hxR', hxr]
    refine ⟨λ y => if y = x then (chans₁ y).tail else chans₁ y, ?_, st₁, st₂, stR, rfl, rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, D₁, X₁, Y₁, O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂, hlag,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      by_cases hy : y = x
      · subst hy
        have := heq _ hxS
        rw [hpx] at this
        simp [this]
      · simp [hy]
    · simp [Ne.symm hxr, hr₁]
    · simpa [Ne.symm hxL] using hclL
    · simpa [Ne.symm hxR] using hclR
    · rw [← hpy _ (Ne.symm hxd')]; simpa [Ne.symm hxd'] using hsd
    · rw [← hpy _ (Ne.symm hxL')]; simpa [Ne.symm hxL'] using hsL
    · rw [← hpy _ (Ne.symm hxR')]; simpa [Ne.symm hxR'] using hsR
    · rw [← hpy _ (Ne.symm hxd)]; simpa [Ne.symm hxd] using hd
    · rw [← hpy _ (Ne.symm hxd')]; simpa [Ne.symm hxd] using hd'
    · rw [← hpy _ (Ne.symm hxL)]; simpa [Ne.symm hxL] using hL
    · rw [← hpy _ (Ne.symm hxL')]; simpa [Ne.symm hxL] using hL'
    · rw [← hpy _ (Ne.symm hxR)]; simpa [Ne.symm hxR] using hR
    · rw [← hpy _ (Ne.symm hxR')]; simpa [Ne.symm hxR] using hR'
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        have := heq _ hy
        rw [hpx] at this
        simp [this]
      · have := heq _ hy
        rw [hpy _ hyx] at this
        simp [hyx, this]
  · -- frame_push: pushes to the copies come from their forks
    rintro L₀ chans₀ L₁ chans₁ outs vals hlen' hx hnd hfp
      ⟨st₁, st₂, stR, rfl, rfl, hr₁, hclL, hclR, hsd, hsL, hsR,
        D₁, X₁, Y₁, O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂, hlag, hd, hd', hL, hL', hR, hR', heq⟩
    rw [hP] at hx
    have hro' : r ∉ outs := λ h => by simpa using (hx r h).2
    have hoo' : output ∉ outs := λ h => by simpa using (hx output h).1
    have ho'o' : output' ∉ outs := λ h => by simpa using (hx output' h).1
    refine ⟨st₁, st₂, stR, rfl, rfl, ?_, ?_, ?_, suffix_append_same hsd _,
      suffix_append_same hsL _, suffix_append_same hsR _,
      D₁, X₁, Y₁, O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂, hlag, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hr₁, ChanMap.pushed_not_mem hro']
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hclL w hw
      · exact ForkPush.clonable hfp hfork₂ hw
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hclR w hw
      · exact ForkPush.clonable hfp hfork₃ hw
    · simp [hd]
    · simp [hd', ForkPush.pushed_eq hfp hnd hlen' hfork₁]
    · simp [hL]
    · simp [hL', ForkPush.pushed_eq hfp hnd hlen' hfork₂]
    · simp [hR]
    · simp [hR', ForkPush.pushed_eq hfp hnd hlen' hfork₃]
    · intro y hy
      simp only [heq y hy, List.append_assoc]
      by_cases hyo : y = output
      · subst hyo; simp [ChanMap.pushed_not_mem hoo']
      · by_cases hyo' : y = output'
        · subst hyo'; simp [hyo, ChanMap.pushed_not_mem ho'o']
        · simp [hyo, hyo']
  · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
      _ _ ⟨_, _, _, rfl, -⟩ hmem
    simp at hmem
  · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
      inputs outputs inputVals outputVals chans₀' _ _
      ⟨st₁, st₂, stR, rfl, rfl, hr₁, hclL, hclR, hsd, hsL, hsR,
        D₁, X₁, Y₁, O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂, hlag, hd, hd', hL, hL', hR, hR', heq⟩
      hget hinterp hlen₁ hlen₂ hpop
    match i, hget with
    | 0, hget =>
      -- `merge₂` fires
      simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      rcases hinterp.merge_inv hlen₁ with
        ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
      · -- `merge₂` reads its left input
        have hpl : chans₀ inputL' = v :: chans₀' inputL' := by simpa using hpop inputL'
        have hpy : ∀ y, y ≠ inputL' → chans₀ y = chans₀' y := λ y h => by
          simpa [Ne.symm h] using hpop y
        rcases X₂ with _ | ⟨v', X₂⟩
        · -- level with the rewritten merge: it fires, then the fork
          obtain ⟨rfl, rfl, rfl, rfl⟩ := MergeRun.left_nil_inv hm₂
          have hL₁ : chans₁ inputL = v :: chans₀' inputL' := by
            rw [← hpl]; simpa using hL'.symm
          obtain ⟨c, hτ, hcx, hcr, hco, hco', hcy⟩ := merge_data_fork_tau (Op := Op)
            (F := .async (.fork k) inputs₀ outputs₀)
            (S := .async (.sink 3) [decider', inputL', inputR'] [])
            (.interp_merge_left rfl rfl) hL₁ hr₁ (hclL v (by simp [hL₁]))
            hrL hro hro' hoL ho'L hoo'
          refine ⟨_, c, hτ, st₁, .decider, .decider, by simp, rfl, hcr, ?_, ?_, ?_, ?_, ?_,
            D₁, X₁ ++ [v], Y₁, O₁ ++ [v], [], [], [], [], hm₁.snoc_left rfl, .refl,
            .inr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · intro w hw; rw [hcx] at hw; exact hclL w (by simp [hL₁, hw])
          · rw [hcy _ (Ne.symm hLR) (Ne.symm hoR) (Ne.symm ho'R)]; exact hclR
          · rw [hcy _ (Ne.symm hLd') (Ne.symm hod') (Ne.symm ho'd'), ← hpy _ hd'L']
            simpa [ho'd'] using hsd
          · rw [hcy _ (Ne.symm hLL') (Ne.symm hoL') (Ne.symm ho'L')]
            simpa [ho'L'] using suffix_of_eq_cons hpl hsL
          · rw [hcy _ (Ne.symm hLR') (Ne.symm hoR') (Ne.symm ho'R'), ← hpy _ (Ne.symm hL'R')]
            simpa [ho'R'] using hsR
          · rw [hcy _ hdL (Ne.symm hod) (Ne.symm ho'd), ← hpy _ hdL', hd]; simp [ho'd]
          · rw [hcy _ hdL (Ne.symm hod) (Ne.symm ho'd), ← hpy _ hd'L', hd']; simp [ho'd']
          · rw [hcx, ← hpy _ hLL', hL, hL₁]; simp [ho'L]
          · rw [hcx]; simp [ho'L']
          · rw [hcy _ (Ne.symm hLR) (Ne.symm hoR) (Ne.symm ho'R), ← hpy _ hRL', hR]
            simp [ho'R]
          · rw [hcy _ (Ne.symm hLR) (Ne.symm hoR) (Ne.symm ho'R), ← hpy _ (Ne.symm hL'R'), hR']
            simp [ho'R']
          · intro y hy
            have hyL : y ≠ inputL := by rintro rfl; simp at hy
            have hyL' : y ≠ inputL' := by rintro rfl; simp at hy
            rw [← hpy _ hyL']
            by_cases hyo : y = output
            · subst hyo
              rw [hco, heq _ hy]
              simp [Ne.symm hoo']
            · by_cases hyo' : y = output'
              · subst hyo'
                rw [hco', heq _ hy]
                simp [hyo]
              · rw [hcy _ hyL hyo hyo', heq _ hy]
                simp [hyo, hyo', Ne.symm hyo']
        · -- behind the rewritten merge: `merge₂` catches up
          rw [hpl] at hL'
          simp only [List.cons_append, List.cons.injEq] at hL'
          obtain ⟨rfl, hL'⟩ := hL'
          obtain ⟨O₂', rfl, hm₂'⟩ := MergeRun.left_cons_inv hm₂
          obtain ⟨rfl, rfl, rfl⟩ : D₁ = [] ∧ X₁ = [] ∧ Y₁ = [] := by simpa using hlag
          refine ⟨_, _, .refl, st₁, .decider, stR, by simp, rfl, hr₁, hclL, hclR, ?_, ?_, ?_,
            [], [], [], O₁, D₂, X₂, Y₂, O₂', hm₁, hm₂', .inl ⟨rfl, rfl, rfl⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [← hpy _ hd'L']; simpa [ho'd'] using hsd
          · simpa [ho'L'] using suffix_of_eq_cons hpl hsL
          · rw [← hpy _ (Ne.symm hL'R')]; simpa [ho'R'] using hsR
          · rw [← hpy _ hdL', hd]; simp [ho'd]
          · rw [← hpy _ hd'L', hd']; simp [ho'd']
          · rw [← hpy _ hLL', hL]; simp [ho'L]
          · rw [hL']; simp [ho'L']
          · rw [← hpy _ hRL', hR]; simp [ho'R]
          · rw [← hpy _ (Ne.symm hL'R'), hR']; simp [ho'R']
          · intro y hy
            have hyL' : y ≠ inputL' := by rintro rfl; simp at hy
            rw [← hpy _ hyL', heq _ hy]
            by_cases hyo' : y = output'
            · subst hyo'; simp [Ne.symm hoo']
            · simp [hyo', Ne.symm hyo']
      · -- `merge₂` reads its right input
        have hpr : chans₀ inputR' = v :: chans₀' inputR' := by simpa using hpop inputR'
        have hpy : ∀ y, y ≠ inputR' → chans₀ y = chans₀' y := λ y h => by
          simpa [Ne.symm h] using hpop y
        rcases Y₂ with _ | ⟨v', Y₂⟩
        · -- level with the rewritten merge: it fires, then the fork
          obtain ⟨rfl, rfl, rfl, rfl⟩ := MergeRun.right_nil_inv hm₂
          have hR₁ : chans₁ inputR = v :: chans₀' inputR' := by
            rw [← hpr]; simpa using hR'.symm
          obtain ⟨c, hτ, hcx, hcr, hco, hco', hcy⟩ := merge_data_fork_tau (Op := Op)
            (F := .async (.fork k) inputs₀ outputs₀)
            (S := .async (.sink 3) [decider', inputL', inputR'] [])
            (.interp_merge_right rfl rfl) hR₁ hr₁ (hclR v (by simp [hR₁]))
            hrR hro hro' hoR ho'R hoo'
          refine ⟨_, c, hτ, st₁, .decider, .decider, by simp, rfl, hcr, ?_, ?_, ?_, ?_, ?_,
            D₁, X₁, Y₁ ++ [v], O₁ ++ [v], [], [], [], [], hm₁.snoc_right rfl, .refl,
            .inr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [hcy _ hLR (Ne.symm hoL) (Ne.symm ho'L)]; exact hclL
          · intro w hw; rw [hcx] at hw; exact hclR w (by simp [hR₁, hw])
          · rw [hcy _ (Ne.symm hRd') (Ne.symm hod') (Ne.symm ho'd'), ← hpy _ hd'R']
            simpa [ho'd'] using hsd
          · rw [hcy _ (Ne.symm hRL') (Ne.symm hoL') (Ne.symm ho'L'), ← hpy _ hL'R']
            simpa [ho'L'] using hsL
          · rw [hcy _ (Ne.symm hRR') (Ne.symm hoR') (Ne.symm ho'R')]
            simpa [ho'R'] using suffix_of_eq_cons hpr hsR
          · rw [hcy _ hdR (Ne.symm hod) (Ne.symm ho'd), ← hpy _ hdR', hd]; simp [ho'd]
          · rw [hcy _ hdR (Ne.symm hod) (Ne.symm ho'd), ← hpy _ hd'R', hd']; simp [ho'd']
          · rw [hcy _ hLR (Ne.symm hoL) (Ne.symm ho'L), ← hpy _ hLR', hL]; simp [ho'L]
          · rw [hcy _ hLR (Ne.symm hoL) (Ne.symm ho'L), ← hpy _ hL'R', hL']; simp [ho'L']
          · rw [hcx, ← hpy _ hRR', hR, hR₁]; simp [ho'R]
          · rw [hcx]; simp [ho'R']
          · intro y hy
            have hyR : y ≠ inputR := by rintro rfl; simp at hy
            have hyR' : y ≠ inputR' := by rintro rfl; simp at hy
            rw [← hpy _ hyR']
            by_cases hyo : y = output
            · subst hyo
              rw [hco, heq _ hy]
              simp [Ne.symm hoo']
            · by_cases hyo' : y = output'
              · subst hyo'
                rw [hco', heq _ hy]
                simp [hyo]
              · rw [hcy _ hyR hyo hyo', heq _ hy]
                simp [hyo, hyo', Ne.symm hyo']
        · -- behind the rewritten merge: `merge₂` catches up
          rw [hpr] at hR'
          simp only [List.cons_append, List.cons.injEq] at hR'
          obtain ⟨rfl, hR'⟩ := hR'
          obtain ⟨O₂', rfl, hm₂'⟩ := MergeRun.right_cons_inv hm₂
          obtain ⟨rfl, rfl, rfl⟩ : D₁ = [] ∧ X₁ = [] ∧ Y₁ = [] := by simpa using hlag
          refine ⟨_, _, .refl, st₁, .decider, stR, by simp, rfl, hr₁, hclL, hclR, ?_, ?_, ?_,
            [], [], [], O₁, D₂, X₂, Y₂, O₂', hm₁, hm₂', .inl ⟨rfl, rfl, rfl⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [← hpy _ hd'R']; simpa [ho'd'] using hsd
          · rw [← hpy _ hL'R']; simpa [ho'L'] using hsL
          · simpa [ho'R'] using suffix_of_eq_cons hpr hsR
          · rw [← hpy _ hdR', hd]; simp [ho'd]
          · rw [← hpy _ hd'R', hd']; simp [ho'd']
          · rw [← hpy _ hLR', hL]; simp [ho'L]
          · rw [← hpy _ hL'R', hL']; simp [ho'L']
          · rw [← hpy _ hRR', hR]; simp [ho'R]
          · rw [hR']; simp [ho'R']
          · intro y hy
            have hyR' : y ≠ inputR' := by rintro rfl; simp at hy
            rw [← hpy _ hyR', heq _ hy]
            by_cases hyo' : y = output'
            · subst hyo'; simp [Ne.symm hoo']
            · simp [hyo', Ne.symm hyo']
      · -- `merge₂` reads its decider
        have hpd : chans₀ decider' = dv :: chans₀' decider' := by simpa using hpop decider'
        have hpy : ∀ y, y ≠ decider' → chans₀ y = chans₀' y := λ y h => by
          simpa [Ne.symm h] using hpop y
        rcases D₂ with _ | ⟨dv', D₂⟩
        · -- level with the rewritten merge: it reads the decider too
          obtain ⟨rfl, rfl, rfl, rfl⟩ := MergeRun.decider_nil_inv hm₂
          have hd₁ : chans₁ decider = dv :: chans₀' decider' := by
            rw [← hpd]; simpa using hd'.symm
          have hτ := merge_dec_tau (Op := Op) (F := .async (.fork k) inputs₀ outputs₀)
            (S := .async (.sink 3) [decider', inputL', inputR'] [])
            (l := inputL) (rr := inputR) (r := r) (o := output) (o' := output') hd₁ hb
          refine ⟨_, _, hτ, st₁, (if b then .popRight else .popLeft),
            (if b then .popRight else .popLeft), by simp, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
            D₁ ++ [dv], X₁, Y₁, O₁, [], [], [], [], hm₁.snoc_decider rfl hb, .refl,
            .inr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · simp [hrd, hr₁]
          · simpa [Ne.symm hdL] using hclL
          · simpa [Ne.symm hdR] using hclR
          · simpa [Ne.symm hdd'] using suffix_of_eq_cons hpd hsd
          · rw [← hpy _ (Ne.symm hd'L')]; simpa [Ne.symm hdL'] using hsL
          · rw [← hpy _ (Ne.symm hd'R')]; simpa [Ne.symm hdR'] using hsR
          · rw [← hpy _ hdd', hd, hd₁]; simp
          · simp
          · rw [← hpy _ hLd', hL]; simp [Ne.symm hdL]
          · rw [← hpy _ (Ne.symm hd'L'), hL']; simp [Ne.symm hdL]
          · rw [← hpy _ hRd', hR]; simp [Ne.symm hdR]
          · rw [← hpy _ (Ne.symm hd'R'), hR']; simp [Ne.symm hdR]
          · intro y hy
            have hyd : y ≠ decider := by rintro rfl; simp at hy
            have hyd' : y ≠ decider' := by rintro rfl; simp at hy
            rw [if_neg hyd, heq _ hy, hpy _ hyd']
            simp
        · -- behind the rewritten merge: `merge₂` catches up
          rw [hpd] at hd'
          simp only [List.cons_append, List.cons.injEq] at hd'
          obtain ⟨rfl, hd'⟩ := hd'
          have hm₂' := MergeRun.decider_cons_inv hm₂ hb
          obtain ⟨rfl, rfl, rfl⟩ : D₁ = [] ∧ X₁ = [] ∧ Y₁ = [] := by simpa using hlag
          refine ⟨_, _, .refl, st₁, (if b then .popRight else .popLeft), stR, by simp, rfl,
            hr₁, hclL, hclR, ?_, ?_, ?_, [], [], [], O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂',
            .inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · simpa using suffix_of_eq_cons hpd hsd
          · rw [← hpy _ (Ne.symm hd'L')]; simpa using hsL
          · rw [← hpy _ (Ne.symm hd'R')]; simpa using hsR
          · rw [← hpy _ hdd', hd]; simp
          · simp [hd']
          · rw [← hpy _ hLd', hL]; simp
          · rw [← hpy _ (Ne.symm hd'L'), hL']; simp
          · rw [← hpy _ hRd', hR]; simp
          · rw [← hpy _ (Ne.symm hd'R'), hR']; simp
          · intro y hy
            have hyd' : y ≠ decider' := by rintro rfl; simp at hy
            rw [heq _ hy, hpy _ hyd']
            simp
    | 1, hget =>
      -- The fork fires: the same fork fires on the rewritten side
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, h, h'⟩ := hget
      subst allInputs allOutputs
      obtain ⟨x₀, v, rfl, rfl, rfl, h, hk, rfl, hclone, rfl⟩ := fork_inv' hinterp
      subst outputs
      simp only [List.mem_singleton] at hd₀ hL₀ hR₀ hd'₀ hL'₀ hR'₀ hr₀
      have hpx : chans₀ x₀ = v :: chans₀' x₀ := by simpa using hpop x₀
      have hpy : ∀ y, y ≠ x₀ → chans₀ y = chans₀' y := λ y h => by
        simpa [Ne.symm h] using hpop y
      have hxS : x₀ ∉ [decider, inputL, inputR, decider', inputL', inputR', r] := by
        simp [Ne.symm hd₀, Ne.symm hL₀, Ne.symm hR₀, Ne.symm hd'₀, Ne.symm hL'₀, Ne.symm hR'₀,
          Ne.symm hr₀]
      have hc : chans₁ x₀ = v :: (chans₀' x₀ ++
          (if x₀ = output then O₁ else if x₀ = output' then O₂ else [])) := by
        rw [heq _ hxS, hpx, List.cons_append]
      have hτ := LocalTauStar.async_list_mem (L := ([.async (.fork k) [x₀] outputs₀,
          .async (.merge stR 1) [decider, inputL, inputR] [r],
          .async (.fork 2) [r] [output, output'],
          .async (.sink 3) [decider', inputL', inputR'] []] : AtomicProcs Op χ V)) (chans := chans₁)
        (chans' := λ y => if y = x₀ then (chans₁ y).tail else chans₁ y)
        (aop := .fork k) (allInputs := [x₀]) (allOutputs := outputs₀)
        (inputs := [x₀]) (inputVals := [v]) (outputs := outputs₀)
        (outputVals := List.replicate k v)
        (by simp) (.interp_fork hk hclone) rfl (by simp [hk]) (by
          intro y
          by_cases hy : y = x₀
          · subst hy; simp [hc]
          · simp [hy, Ne.symm hy])
      have hPd := SameFork.pushed_replicate_eq (v := v) haff hfork₁ h₂ hk
      have hPL := SameFork.pushed_replicate_eq (v := v) haff hfork₂ h₂ hk
      have hPR := SameFork.pushed_replicate_eq (v := v) haff hfork₃ h₂ hk
      refine ⟨_, _, hτ, st₁, st₂, stR, by simp, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
        D₁, X₁, Y₁, O₁, D₂, X₂, Y₂, O₂, hm₁, hm₂, hlag,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
      · simp [hr₀, hr₁, ChanMap.pushed_not_mem hro₀]
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hclL w (by simpa [hL₀] using hw)
        · rw [List.eq_of_mem_replicate (mem_pushed hw)]; exact hclone
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hclR w (by simpa [hR₀] using hw)
        · rw [List.eq_of_mem_replicate (mem_pushed hw)]; exact hclone
      · rw [← hpy _ hd'₀, if_neg hd'₀]; exact suffix_append_same hsd _
      · rw [← hpy _ hL'₀, if_neg hL'₀]; exact suffix_append_same hsL _
      · rw [← hpy _ hR'₀, if_neg hR'₀]; exact suffix_append_same hsR _
      · rw [← hpy _ hd₀, if_neg hd₀, hd, List.append_assoc]
      · rw [← hpy _ hd'₀, if_neg hd₀, hd', hPd, List.append_assoc]
      · rw [← hpy _ hL₀, if_neg hL₀, hL, List.append_assoc]
      · rw [← hpy _ hL'₀, if_neg hL₀, hL', hPL, List.append_assoc]
      · rw [← hpy _ hR₀, if_neg hR₀, hR, List.append_assoc]
      · rw [← hpy _ hR'₀, if_neg hR₀, hR', hPR, List.append_assoc]
      · intro y hy
        have hcomm : (if y = output then O₁ else if y = output' then O₂ else []) ++
            ChanMap.pushed outputs₀ (List.replicate k v) y =
            ChanMap.pushed outputs₀ (List.replicate k v) y ++
              (if y = output then O₁ else if y = output' then O₂ else []) := by
          by_cases hyo : y = output
          · subst hyo; simp [ChanMap.pushed_not_mem ho₀]
          · by_cases hyo' : y = output'
            · subst hyo'; simp [hyo, ChanMap.pushed_not_mem ho'₀]
            · simp [hyo, hyo']
        by_cases hyx : y = x₀
        · subst hyx
          rw [if_pos rfl, hc, List.tail_cons]
          simp only [List.append_assoc, hcomm]
        · rw [if_neg hyx, heq _ hy, hpy _ hyx]
          simp only [List.append_assoc, hcomm]
    | 2, hget =>
      -- `merge₁` fires
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      rcases hinterp.merge_inv hlen₁ with
        ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
      · -- `merge₁` reads its left input
        have hpl : chans₀ inputL = v :: chans₀' inputL := by simpa using hpop inputL
        have hpy : ∀ y, y ≠ inputL → chans₀ y = chans₀' y := λ y h => by
          simpa [Ne.symm h] using hpop y
        rcases X₁ with _ | ⟨v', X₁⟩
        · -- level with the rewritten merge: it fires, then the fork
          obtain ⟨rfl, rfl, rfl, rfl⟩ := MergeRun.left_nil_inv hm₁
          have hL₁ : chans₁ inputL = v :: chans₀' inputL := by rw [← hpl]; simpa using hL.symm
          obtain ⟨c, hτ, hcx, hcr, hco, hco', hcy⟩ := merge_data_fork_tau (Op := Op)
            (F := .async (.fork k) inputs₀ outputs₀)
            (S := .async (.sink 3) [decider', inputL', inputR'] [])
            (.interp_merge_left rfl rfl) hL₁ hr₁ (hclL v (by simp [hL₁]))
            hrL hro hro' hoL ho'L hoo'
          refine ⟨_, c, hτ, .decider, st₂, .decider, by simp, rfl, hcr, ?_, ?_, ?_, ?_, ?_,
            [], [], [], [], D₂, X₂ ++ [v], Y₂, O₂ ++ [v], .refl, hm₂.snoc_left rfl,
            .inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · intro w hw; rw [hcx] at hw; exact hclL w (by simp [hL₁, hw])
          · rw [hcy _ (Ne.symm hLR) (Ne.symm hoR) (Ne.symm ho'R)]; exact hclR
          · rw [hcy _ (Ne.symm hLd') (Ne.symm hod') (Ne.symm ho'd'), ← hpy _ (Ne.symm hLd')]
            simpa [hod'] using hsd
          · rw [hcy _ (Ne.symm hLL') (Ne.symm hoL') (Ne.symm ho'L'), ← hpy _ (Ne.symm hLL')]
            simpa [hoL'] using hsL
          · rw [hcy _ (Ne.symm hLR') (Ne.symm hoR') (Ne.symm ho'R'), ← hpy _ (Ne.symm hLR')]
            simpa [hoR'] using hsR
          · rw [hcy _ hdL (Ne.symm hod) (Ne.symm ho'd), ← hpy _ hdL, hd]; simp [hod]
          · rw [hcy _ hdL (Ne.symm hod) (Ne.symm ho'd), ← hpy _ (Ne.symm hLd'), hd']
            simp [hod']
          · rw [hcx]; simp [hoL]
          · rw [hcx, ← hpy _ (Ne.symm hLL'), hL', hL₁]; simp [hoL']
          · rw [hcy _ (Ne.symm hLR) (Ne.symm hoR) (Ne.symm ho'R), ← hpy _ (Ne.symm hLR), hR]
            simp [hoR]
          · rw [hcy _ (Ne.symm hLR) (Ne.symm hoR) (Ne.symm ho'R), ← hpy _ (Ne.symm hLR'), hR']
            simp [hoR']
          · intro y hy
            have hyL : y ≠ inputL := by rintro rfl; simp at hy
            rw [← hpy _ hyL]
            by_cases hyo : y = output
            · subst hyo
              rw [hco, heq _ hy]
              simp
            · by_cases hyo' : y = output'
              · subst hyo'
                rw [hco', heq _ hy]
                simp [hyo, Ne.symm hyo]
              · rw [hcy _ hyL hyo hyo', heq _ hy]
                simp [hyo, hyo', Ne.symm hyo]
        · -- behind the rewritten merge: `merge₁` catches up
          rw [hpl] at hL
          simp only [List.cons_append, List.cons.injEq] at hL
          obtain ⟨rfl, hL⟩ := hL
          obtain ⟨O₁', rfl, hm₁'⟩ := MergeRun.left_cons_inv hm₁
          obtain ⟨rfl, rfl, rfl⟩ : D₂ = [] ∧ X₂ = [] ∧ Y₂ = [] := by simpa using hlag
          refine ⟨_, _, .refl, .decider, st₂, stR, by simp, rfl, hr₁, hclL, hclR, ?_, ?_, ?_,
            D₁, X₁, Y₁, O₁', [], [], [], O₂, hm₁', hm₂, .inr ⟨rfl, rfl, rfl⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [← hpy _ (Ne.symm hLd')]; simpa [hod'] using hsd
          · rw [← hpy _ (Ne.symm hLL')]; simpa [hoL'] using hsL
          · rw [← hpy _ (Ne.symm hLR')]; simpa [hoR'] using hsR
          · rw [← hpy _ hdL, hd]; simp [hod]
          · rw [← hpy _ (Ne.symm hLd'), hd']; simp [hod']
          · rw [hL]; simp [hoL]
          · rw [← hpy _ (Ne.symm hLL'), hL']; simp [hoL']
          · rw [← hpy _ (Ne.symm hLR), hR]; simp [hoR]
          · rw [← hpy _ (Ne.symm hLR'), hR']; simp [hoR']
          · intro y hy
            have hyL : y ≠ inputL := by rintro rfl; simp at hy
            rw [← hpy _ hyL, heq _ hy]
            by_cases hyo : y = output
            · subst hyo; simp
            · simp [hyo, Ne.symm hyo]
      · -- `merge₁` reads its right input
        have hpr : chans₀ inputR = v :: chans₀' inputR := by simpa using hpop inputR
        have hpy : ∀ y, y ≠ inputR → chans₀ y = chans₀' y := λ y h => by
          simpa [Ne.symm h] using hpop y
        rcases Y₁ with _ | ⟨v', Y₁⟩
        · -- level with the rewritten merge: it fires, then the fork
          obtain ⟨rfl, rfl, rfl, rfl⟩ := MergeRun.right_nil_inv hm₁
          have hR₁ : chans₁ inputR = v :: chans₀' inputR := by rw [← hpr]; simpa using hR.symm
          obtain ⟨c, hτ, hcx, hcr, hco, hco', hcy⟩ := merge_data_fork_tau (Op := Op)
            (F := .async (.fork k) inputs₀ outputs₀)
            (S := .async (.sink 3) [decider', inputL', inputR'] [])
            (.interp_merge_right rfl rfl) hR₁ hr₁ (hclR v (by simp [hR₁]))
            hrR hro hro' hoR ho'R hoo'
          refine ⟨_, c, hτ, .decider, st₂, .decider, by simp, rfl, hcr, ?_, ?_, ?_, ?_, ?_,
            [], [], [], [], D₂, X₂, Y₂ ++ [v], O₂ ++ [v], .refl, hm₂.snoc_right rfl,
            .inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [hcy _ hLR (Ne.symm hoL) (Ne.symm ho'L)]; exact hclL
          · intro w hw; rw [hcx] at hw; exact hclR w (by simp [hR₁, hw])
          · rw [hcy _ (Ne.symm hRd') (Ne.symm hod') (Ne.symm ho'd'), ← hpy _ (Ne.symm hRd')]
            simpa [hod'] using hsd
          · rw [hcy _ (Ne.symm hRL') (Ne.symm hoL') (Ne.symm ho'L'), ← hpy _ (Ne.symm hRL')]
            simpa [hoL'] using hsL
          · rw [hcy _ (Ne.symm hRR') (Ne.symm hoR') (Ne.symm ho'R'), ← hpy _ (Ne.symm hRR')]
            simpa [hoR'] using hsR
          · rw [hcy _ hdR (Ne.symm hod) (Ne.symm ho'd), ← hpy _ hdR, hd]; simp [hod]
          · rw [hcy _ hdR (Ne.symm hod) (Ne.symm ho'd), ← hpy _ (Ne.symm hRd'), hd']
            simp [hod']
          · rw [hcy _ hLR (Ne.symm hoL) (Ne.symm ho'L), ← hpy _ hLR, hL]; simp [hoL]
          · rw [hcy _ hLR (Ne.symm hoL) (Ne.symm ho'L), ← hpy _ (Ne.symm hRL'), hL']
            simp [hoL']
          · rw [hcx]; simp [hoR]
          · rw [hcx, ← hpy _ (Ne.symm hRR'), hR', hR₁]; simp [hoR']
          · intro y hy
            have hyR : y ≠ inputR := by rintro rfl; simp at hy
            rw [← hpy _ hyR]
            by_cases hyo : y = output
            · subst hyo
              rw [hco, heq _ hy]
              simp
            · by_cases hyo' : y = output'
              · subst hyo'
                rw [hco', heq _ hy]
                simp [hyo, Ne.symm hyo]
              · rw [hcy _ hyR hyo hyo', heq _ hy]
                simp [hyo, hyo', Ne.symm hyo]
        · -- behind the rewritten merge: `merge₁` catches up
          rw [hpr] at hR
          simp only [List.cons_append, List.cons.injEq] at hR
          obtain ⟨rfl, hR⟩ := hR
          obtain ⟨O₁', rfl, hm₁'⟩ := MergeRun.right_cons_inv hm₁
          obtain ⟨rfl, rfl, rfl⟩ : D₂ = [] ∧ X₂ = [] ∧ Y₂ = [] := by simpa using hlag
          refine ⟨_, _, .refl, .decider, st₂, stR, by simp, rfl, hr₁, hclL, hclR, ?_, ?_, ?_,
            D₁, X₁, Y₁, O₁', [], [], [], O₂, hm₁', hm₂, .inr ⟨rfl, rfl, rfl⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [← hpy _ (Ne.symm hRd')]; simpa [hod'] using hsd
          · rw [← hpy _ (Ne.symm hRL')]; simpa [hoL'] using hsL
          · rw [← hpy _ (Ne.symm hRR')]; simpa [hoR'] using hsR
          · rw [← hpy _ hdR, hd]; simp [hod]
          · rw [← hpy _ (Ne.symm hRd'), hd']; simp [hod']
          · rw [← hpy _ hLR, hL]; simp [hoL]
          · rw [← hpy _ (Ne.symm hRL'), hL']; simp [hoL']
          · rw [hR]; simp [hoR]
          · rw [← hpy _ (Ne.symm hRR'), hR']; simp [hoR']
          · intro y hy
            have hyR : y ≠ inputR := by rintro rfl; simp at hy
            rw [← hpy _ hyR, heq _ hy]
            by_cases hyo : y = output
            · subst hyo; simp
            · simp [hyo, Ne.symm hyo]
      · -- `merge₁` reads its decider
        have hpd : chans₀ decider = dv :: chans₀' decider := by simpa using hpop decider
        have hpy : ∀ y, y ≠ decider → chans₀ y = chans₀' y := λ y h => by
          simpa [Ne.symm h] using hpop y
        rcases D₁ with _ | ⟨dv', D₁⟩
        · -- level with the rewritten merge: it reads the decider too
          obtain ⟨rfl, rfl, rfl, rfl⟩ := MergeRun.decider_nil_inv hm₁
          have hd₁ : chans₁ decider = dv :: chans₀' decider := by rw [← hpd]; simpa using hd.symm
          have hτ := merge_dec_tau (Op := Op) (F := .async (.fork k) inputs₀ outputs₀)
            (S := .async (.sink 3) [decider', inputL', inputR'] [])
            (l := inputL) (rr := inputR) (r := r) (o := output) (o' := output') hd₁ hb
          refine ⟨_, _, hτ, (if b then .popRight else .popLeft), st₂,
            (if b then .popRight else .popLeft), by simp, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
            [], [], [], [], D₂ ++ [dv], X₂, Y₂, O₂, .refl, hm₂.snoc_decider rfl hb,
            .inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · simp [hrd, hr₁]
          · simpa [Ne.symm hdL] using hclL
          · simpa [Ne.symm hdR] using hclR
          · rw [← hpy _ (Ne.symm hdd')]; simpa [Ne.symm hdd'] using hsd
          · rw [← hpy _ (Ne.symm hdL')]; simpa [Ne.symm hdL'] using hsL
          · rw [← hpy _ (Ne.symm hdR')]; simpa [Ne.symm hdR'] using hsR
          · simp
          · rw [← hpy _ (Ne.symm hdd'), hd', hd₁]; simp
          · rw [← hpy _ (Ne.symm hdL), hL]; simp [Ne.symm hdL]
          · rw [← hpy _ (Ne.symm hdL'), hL']; simp [Ne.symm hdL]
          · rw [← hpy _ (Ne.symm hdR), hR]; simp [Ne.symm hdR]
          · rw [← hpy _ (Ne.symm hdR'), hR']; simp [Ne.symm hdR]
          · intro y hy
            have hyd : y ≠ decider := by rintro rfl; simp at hy
            rw [if_neg hyd, heq _ hy, hpy _ hyd]
            simp
        · -- behind the rewritten merge: `merge₁` catches up
          rw [hpd] at hd
          simp only [List.cons_append, List.cons.injEq] at hd
          obtain ⟨rfl, hd⟩ := hd
          have hm₁' := MergeRun.decider_cons_inv hm₁ hb
          obtain ⟨rfl, rfl, rfl⟩ : D₂ = [] ∧ X₂ = [] ∧ Y₂ = [] := by simpa using hlag
          refine ⟨_, _, .refl, (if b then .popRight else .popLeft), st₂, stR, by simp, rfl,
            hr₁, hclL, hclR, ?_, ?_, ?_, D₁, X₁, Y₁, O₁, [], [], [], O₂, hm₁', hm₂,
            .inr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
          · rw [← hpy _ (Ne.symm hdd')]; simpa using hsd
          · rw [← hpy _ (Ne.symm hdL')]; simpa using hsL
          · rw [← hpy _ (Ne.symm hdR')]; simpa using hsR
          · simp [hd]
          · rw [← hpy _ (Ne.symm hdd'), hd']; simp
          · rw [← hpy _ (Ne.symm hdL), hL]; simp
          · rw [← hpy _ (Ne.symm hdL'), hL']; simp
          · rw [← hpy _ (Ne.symm hdR), hR]; simp
          · rw [← hpy _ (Ne.symm hdR'), hR']; simp
          · intro y hy
            have hyd : y ≠ decider := by rintro rfl; simp at hy
            rw [heq _ hy, hpy _ hyd]
            simp

end Wavelet.Compile.DeadCodeElim
