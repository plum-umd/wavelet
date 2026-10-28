import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Dataflow.AffineChan

/-!
Main theorems of the local rewrite framework: replacing the atoms at indices `I`
with `P'` is a forward simulation if there is a `LocalSimRel`.
-/

namespace Wavelet.Compile

open Semantics Dataflow

/-! Index bookkeeping for `matchedOf` and `unmatchedOf`. -/
section Index

/-- `unmatchedOf` with all indices shifted by `k`. -/
private def unmatchedFrom (l : List α) (I : List Nat) (k : Nat) : List α :=
  (l.mapIdx (λ i x => (i + k, x))).filter (λ (i, _) => i ∉ I) |>.map (·.snd)

private theorem unmatchedOf_eq_from {l : List α} {I : List Nat} :
    unmatchedOf l I = unmatchedFrom l I 0 := rfl

private theorem unmatchedFrom_cons {x : α} {l : List α} {I : List Nat} {k : Nat} :
    unmatchedFrom (x :: l) I k = (if k ∈ I then [] else [x]) ++ unmatchedFrom l I (k + 1) := by
  have : (λ i (y : α) => (i + 1 + k, y)) = (λ i y => (i + (k + 1), y)) := by
    funext i y; congr 1; omega
  simp only [unmatchedFrom, List.mapIdx_cons, Nat.zero_add, this]
  by_cases h : k ∈ I <;> simp [h]

private theorem unmatchedFrom_set_of_mem {l : List α} {I : List Nat} {i k : Nat} {a : α}
  (h : i + k ∈ I) : unmatchedFrom (l.set i a) I k = unmatchedFrom l I k := by
  induction l generalizing i k with
  | nil => simp
  | cons x l ih =>
    cases i with
    | zero => simp at h; simp [unmatchedFrom_cons, h]
    | succ i =>
      simp only [List.set_cons_succ, unmatchedFrom_cons]
      rw [ih (by rwa [show i + (k + 1) = i + 1 + k by omega])]

private theorem unmatchedFrom_set_of_not_mem {l : List α} {I : List Nat} {i k : Nat}
  (h : i + k ∉ I) (hi : i < l.length) :
    ∃ j, (unmatchedFrom l I k)[j]? = l[i]? ∧
      ∀ a, unmatchedFrom (l.set i a) I k = (unmatchedFrom l I k).set j a := by
  induction l generalizing i k with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero =>
      simp at h
      exact ⟨0, by simp [unmatchedFrom_cons, h], λ a => by simp [unmatchedFrom_cons, h]⟩
    | succ i =>
      obtain ⟨j, hj, hset⟩ := ih (i := i) (k := k + 1)
        (by rwa [show i + (k + 1) = i + 1 + k by omega]) (by simpa using hi)
      refine ⟨(if k ∈ I then ([] : List α) else [x]).length + j, ?_, λ a => ?_⟩
      · rw [unmatchedFrom_cons, List.getElem?_append_right (by omega)]
        simpa using hj
      · rw [List.set_cons_succ, unmatchedFrom_cons, unmatchedFrom_cons, hset,
          List.set_append_right _ _ (by omega)]
        simp

private theorem unmatchedFrom_sublist {l : List α} {I : List Nat} {k : Nat} :
    (unmatchedFrom l I k).Sublist l := by
  induction l generalizing k with
  | nil => simp [unmatchedFrom]
  | cons x l ih =>
    rw [unmatchedFrom_cons]
    split
    · exact .cons _ ih
    · exact .cons₂ _ ih

private theorem unmatchedOf_set_of_mem {l : List α} {I : List Nat} {i : Nat} {a : α}
  (h : i ∈ I) : unmatchedOf (l.set i a) I = unmatchedOf l I := by
  simp only [unmatchedOf_eq_from]
  exact unmatchedFrom_set_of_mem (by simpa using h)

private theorem unmatchedOf_set_of_not_mem {l : List α} {I : List Nat} {i : Nat}
  (h : i ∉ I) (hi : i < l.length) :
    ∃ j, (unmatchedOf l I)[j]? = l[i]? ∧
      ∀ a, unmatchedOf (l.set i a) I = (unmatchedOf l I).set j a := by
  simp only [unmatchedOf_eq_from]
  exact unmatchedFrom_set_of_not_mem (by simpa using h) hi

private theorem unmatchedOf_sublist {l : List α} {I : List Nat} : (unmatchedOf l I).Sublist l := by
  rw [unmatchedOf_eq_from]
  exact unmatchedFrom_sublist

private theorem mem_unmatchedOf_iff {l : List α} {I : List Nat} {x : α} :
    x ∈ unmatchedOf l I ↔ ∃ i, i ∉ I ∧ l[i]? = some x := by
  simp only [unmatchedOf, List.mem_map, List.mem_filter, List.mem_mapIdx]
  constructor
  · rintro ⟨⟨j, y⟩, ⟨⟨i, hi, heq⟩, hj⟩, rfl⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨i, by simpa using hj, by simp [hi]⟩
  · rintro ⟨i, hi, hget⟩
    have ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hget
    exact ⟨(i, x), ⟨⟨i, hlt, by simp [hget]⟩, by simpa using hi⟩, rfl⟩

private theorem mem_matchedOf_iff {l : List α} {I : List Nat} {x : α} :
    x ∈ matchedOf l I ↔ ∃ i ∈ I, l[i]? = some x := by
  simp [matchedOf]

private theorem matchedOf_set_of_not_mem {l : List α} {I : List Nat} {i : Nat} {a : α}
  (h : i ∉ I) : matchedOf (l.set i a) I = matchedOf l I := by
  apply List.filterMap_congr
  intro k hk
  exact List.getElem?_set_ne (by rintro rfl; exact h hk)

private theorem getElem?_matchedOf {l : List α} {I : List Nat} {p : Nat}
  (hlt : ∀ i ∈ I, i < l.length) (hp : p < I.length) :
    (matchedOf l I)[p]? = l[I[p]]? := by
  induction I generalizing p with
  | nil => simp at hp
  | cons i I ih =>
    have hi : i < l.length := hlt i (by simp)
    rw [matchedOf_cons, List.getElem?_eq_getElem hi]
    cases p with
    | zero => simp [List.getElem?_eq_getElem hi]
    | succ p =>
      simp only [Option.toList_some, List.singleton_append, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      exact ih (λ j hj => hlt j (by simp [hj])) (by simpa using hp)

private theorem matchedOf_set_getElem {l : List α} {I : List Nat} {p : Nat} {a : α}
  (hnodup : I.Nodup) (hlt : ∀ i ∈ I, i < l.length) (hp : p < I.length) :
    matchedOf (l.set I[p] a) I = (matchedOf l I).set p a := by
  induction I generalizing p with
  | nil => simp at hp
  | cons i I ih =>
    have hi : i < l.length := hlt i (by simp)
    have hnotin : i ∉ I := (List.nodup_cons.mp hnodup).1
    cases p with
    | zero =>
      simp only [List.getElem_cons_zero, matchedOf_cons, matchedOf_set_of_not_mem hnotin]
      simp [hi]
    | succ p =>
      have hp' : p < I.length := by simpa using hp
      have hne : I[p] ≠ i := λ heq => hnotin (heq ▸ List.getElem_mem hp')
      simp only [List.getElem_cons_succ, matchedOf_cons, List.getElem?_set_ne hne,
        ih (List.nodup_cons.mp hnodup).2 (λ j hj => hlt j (by simp [hj])) hp',
        List.getElem?_eq_getElem hi]
      simp

private theorem forall₂_getElem?_toList {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
  (h : List.Forall₂ R l₁ l₂) (i : Nat) : List.Forall₂ R l₁[i]?.toList l₂[i]?.toList := by
  induction h generalizing i with
  | nil => simp
  | cons hhd _ ih => cases i <;> simp [hhd, ih]

private theorem forall₂_matchedOf {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {I : List Nat}
  (h : List.Forall₂ R l₁ l₂) : List.Forall₂ R (matchedOf l₁ I) (matchedOf l₂ I) := by
  induction I with
  | nil => simp
  | cons i I ih =>
    simp only [matchedOf_cons]
    exact List.forall₂_append (forall₂_getElem?_toList h i) ih

end Index

/-! Facts about names, from `AffineChan` and `RewriteNames`. -/
section Names

variable [Arity Op] {proc : Proc Op χ V m n} {I : List Nat} {P' : AtomicProcs Op χ V}

/-- Two atoms sharing an input are at the same index. -/
private theorem idx_eq_of_mem_inputs (haff : proc.AffineChan)
  {i j : Nat} {ap₁ ap₂ : AtomicProc Op χ V}
  (hget₁ : proc.atoms[i]? = some ap₁) (hget₂ : proc.atoms[j]? = some ap₂)
  (hx₁ : x ∈ ap₁.inputs) (hx₂ : x ∈ ap₂.inputs) : i = j := by
  by_contra hne
  exact (haff.atom_disjoint hget₁ hget₂ hne).1 hx₁ hx₂

/-- Two atoms sharing an output are at the same index. -/
private theorem idx_eq_of_mem_outputs (haff : proc.AffineChan)
  {i j : Nat} {ap₁ ap₂ : AtomicProc Op χ V}
  (hget₁ : proc.atoms[i]? = some ap₁) (hget₂ : proc.atoms[j]? = some ap₂)
  (hx₁ : x ∈ ap₁.outputs) (hx₂ : x ∈ ap₂.outputs) : i = j := by
  by_contra hne
  exact (haff.atom_disjoint hget₁ hget₂ hne).2 hx₁ hx₂

/-- Inputs of an atom outside `I` are not read by the matched atoms. -/
private theorem not_mem_inputNames_matchedOf (haff : proc.AffineChan)
  {i : Nat} {ap : AtomicProc Op χ V} (hget : proc.atoms[i]? = some ap) (hi : i ∉ I)
  (hx : x ∈ ap.inputs) : x ∉ AtomicProcs.inputNames (matchedOf proc.atoms I) := by
  simp only [AtomicProcs.inputNames, List.mem_flatMap, not_exists, not_and]
  intro ap' hmem hx'
  obtain ⟨j, hj, hget'⟩ := mem_matchedOf_iff.mp hmem
  obtain rfl := idx_eq_of_mem_inputs haff hget hget' hx hx'
  exact hi hj

/-- Outputs of an atom outside `I` are not written by the matched atoms. -/
private theorem not_mem_outputNames_matchedOf (haff : proc.AffineChan)
  {i : Nat} {ap : AtomicProc Op χ V} (hget : proc.atoms[i]? = some ap) (hi : i ∉ I)
  (hx : x ∈ ap.outputs) : x ∉ AtomicProcs.outputNames (matchedOf proc.atoms I) := by
  simp only [AtomicProcs.outputNames, List.mem_flatMap, not_exists, not_and]
  intro ap' hmem hx'
  obtain ⟨j, hj, hget'⟩ := mem_matchedOf_iff.mp hmem
  obtain rfl := idx_eq_of_mem_outputs haff hget hget' hx hx'
  exact hi hj

/-- Global inputs are not written by the matched atoms. -/
private theorem not_mem_outputNames_of_input (haff : proc.AffineChan)
  (hx : x ∈ proc.inputs.toList) : x ∉ AtomicProcs.outputNames (matchedOf proc.atoms I) := by
  simp only [AtomicProcs.outputNames, List.mem_flatMap, not_exists, not_and]
  intro ap hmem hx'
  obtain ⟨j, -, hget⟩ := mem_matchedOf_iff.mp hmem
  exact haff.atom_outputs_disjoint_inputs hget hx' hx

/-- Global outputs are not read by the matched atoms. -/
private theorem not_mem_inputNames_of_output (haff : proc.AffineChan)
  (hx : x ∈ proc.outputs.toList) : x ∉ AtomicProcs.inputNames (matchedOf proc.atoms I) := by
  simp only [AtomicProcs.inputNames, List.mem_flatMap, not_exists, not_and]
  intro ap hmem hx'
  obtain ⟨j, -, hget⟩ := mem_matchedOf_iff.mp hmem
  exact haff.atom_inputs_disjoint_outputs hget hx' hx

private theorem mem_allNames_of_global_input (hx : x ∈ proc.inputs.toList) :
    x ∈ proc.allNames := by
  simp [Proc.allNames, hx]

private theorem mem_allNames_of_global_output (hx : x ∈ proc.outputs.toList) :
    x ∈ proc.allNames := by
  simp [Proc.allNames, hx]

/-- Names of the original process read by `P'` are read by the matched atoms. -/
private theorem not_mem_inputNames_rhs (hnames : RewriteNames proc I P')
  (hx : x ∉ AtomicProcs.inputNames (matchedOf proc.atoms I)) (hall : x ∈ proc.allNames) :
    x ∉ P'.inputNames :=
  λ h => (hnames.inputs_sub x h).elim hx (· hall)

/-- Names of the original process written by `P'` are written by the matched atoms. -/
private theorem not_mem_outputNames_rhs (hnames : RewriteNames proc I P')
  (hx : x ∉ AtomicProcs.outputNames (matchedOf proc.atoms I)) (hall : x ∈ proc.allNames) :
    x ∉ P'.outputNames :=
  λ h => (hnames.outputs_sub x h).elim hx (· hall)

end Names

/-- Replacing the atoms at `I` with `P'` preserves `AffineChan`. -/
theorem rewrite_affine_chan
  [Arity Op]
  {proc : Proc Op χ V m n} {I : List Nat} {P' : AtomicProcs Op χ V}
  (haff : proc.AffineChan)
  (hnames : RewriteNames proc I P') :
    ({ proc with atoms := P' ++ unmatchedOf proc.atoms I } : Proc Op χ V m n).AffineChan
  := by
  have ⟨hins, houts, ⟨hnodup, hpw⟩, hdisj₁, hdisj₂⟩ := haff
  have hP'in := List.nodup_flatMap.mp hnames.inputs_nodup
  have hP'out := List.nodup_flatMap.mp hnames.outputs_nodup
  have hsub : (unmatchedOf proc.atoms I).Sublist proc.atoms := unmatchedOf_sublist
  refine ⟨hins, houts, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro ap hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ⟨hP'in.1 ap hmem, hP'out.1 ap hmem⟩
    · exact hnodup ap (hsub.subset hmem)
  · refine List.pairwise_append.mpr ⟨hP'in.2.and hP'out.2, hpw.sublist hsub, ?_⟩
    intro a ha b hb
    obtain ⟨j, hj, hget⟩ := mem_unmatchedOf_iff.mp hb
    constructor
    · intro x hxa hxb
      rcases hnames.inputs_sub x (List.mem_flatMap.mpr ⟨a, ha, hxa⟩) with hx | hx
      · exact not_mem_inputNames_matchedOf haff hget hj hxb hx
      · exact hx (Proc.mem_allNames_of_input hget hxb)
    · intro x hxa hxb
      rcases hnames.outputs_sub x (List.mem_flatMap.mpr ⟨a, ha, hxa⟩) with hx | hx
      · exact not_mem_outputNames_matchedOf haff hget hj hxb hx
      · exact hx (Proc.mem_allNames_of_output hget hxb)
  · intro ap hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · intro x hxa hxin
      rcases hnames.outputs_sub x (List.mem_flatMap.mpr ⟨ap, hmem, hxa⟩) with hx | hx
      · exact not_mem_outputNames_of_input haff hxin hx
      · exact hx (mem_allNames_of_global_input hxin)
    · exact hdisj₁ ap (hsub.subset hmem)
  · intro ap hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · intro x hxa hxout
      rcases hnames.inputs_sub x (List.mem_flatMap.mpr ⟨ap, hmem, hxa⟩) with hx | hx
      · exact not_mem_inputNames_of_output haff hxout hx
      · exact hx (mem_allNames_of_global_output hxout)
    · exact hdisj₂ ap (hsub.subset hmem)

/-! `ConstInv` is preserved by the steps of the original process. -/
section ConstInv

variable [Arity Op] {proc : Proc Op χ V m n}

/-- `SameShape` is transitive. -/
private theorem sameShape_trans {a b c : AtomicProc Op χ V}
  (h₁ : a.SameShape b) (h₂ : b.SameShape c) : a.SameShape c := by
  cases h₁ <;> cases h₂ <;> first | exact .refl | exact .merge | exact .inv

/-- Values pushed to any channel are among the pushed values. -/
private theorem mem_pushed [DecidableEq χ] {names : List χ} {vals : List V} {y : χ} {w : V}
  (h : w ∈ ChanMap.pushed names vals y) : w ∈ vals := by
  simp only [ChanMap.pushed, List.mem_filterMap] at h
  obtain ⟨⟨x, v⟩, hmem, h⟩ := h
  split at h
  · cases h; exact (List.of_mem_zip hmem).2
  · cases h

private theorem constInv_empty : ConstInv proc (ChanMap.empty : ChanMap χ V) := by
  intro v k ins outs _ o _
  simp

private theorem constInv_pop [DecidableEq χ] {chans chans' : ChanMap χ V}
  {names : List χ} {vals : List V}
  (hinv : ConstInv proc chans) (hpop : ∀ y, chans y = ChanMap.pushed names vals y ++ chans' y) :
    ConstInv proc chans' := by
  intro v k ins outs hmem o ho
  have ⟨h₁, h₂⟩ := hinv v k ins outs hmem o ho
  refine ⟨λ w hw => h₁ w ?_, λ k' outs' hfork o' ho' w hw => h₂ k' outs' hfork o' ho' w ?_⟩
  · rw [hpop]; exact List.mem_append_right _ hw
  · rw [hpop]; exact List.mem_append_right _ hw

private theorem constInv_append {chans₁ chans₂ : ChanMap χ V}
  (h₁ : ConstInv proc chans₁) (h₂ : ConstInv proc chans₂) :
    ConstInv proc (λ y => chans₁ y ++ chans₂ y) := by
  intro v k ins outs hmem o ho
  have ⟨h₁₁, h₁₂⟩ := h₁ v k ins outs hmem o ho
  have ⟨h₂₁, h₂₂⟩ := h₂ v k ins outs hmem o ho
  refine ⟨λ w hw => ?_, λ k' outs' hfork o' ho' w hw => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact h₁₁ w hw
    · exact h₂₁ w hw
  · rcases List.mem_append.mp hw with hw | hw
    · exact h₁₂ k' outs' hfork o' ho' w hw
    · exact h₂₂ k' outs' hfork o' ho' w hw

/-- No values in the outputs of constants and forks. -/
private theorem constInv_of_nil {chans : ChanMap χ V}
  (hconst : ∀ v k ins outs, .async (.const v k) ins outs ∈ proc.atoms → ∀ o ∈ outs, chans o = [])
  (hfork : ∀ k ins outs, .async (.fork k) ins outs ∈ proc.atoms → ∀ o ∈ outs, chans o = []) :
    ConstInv proc chans := by
  intro v k ins outs hmem o ho
  refine ⟨λ w hw => ?_, λ k' outs' hfork' o' ho' w hw => ?_⟩
  · rw [hconst v k ins outs hmem o ho] at hw; simp at hw
  · rw [hfork k' [o] outs' hfork' o' ho'] at hw; simp at hw

/-- Firing an operator preserves `ConstInv`. -/
private theorem constInv_op [DecidableEq χ] (haff : proc.AffineChan)
  {atoms₀ : AtomicProcs Op χ V} {chans chans' : ChanMap χ V}
  {o : Op} {inputs : Vector χ (Arity.ι o)} {outputs : Vector χ (Arity.ω o)}
  {inputVals outputVals : List V}
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hinv : ConstInv proc chans)
  (hmem : .op o inputs outputs ∈ atoms₀)
  (hpop : ∀ y, chans y = ChanMap.pushed inputs.toList inputVals y ++ chans' y) :
    ConstInv proc (λ y => chans' y ++ ChanMap.pushed outputs.toList outputVals y) := by
  obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨ap₀, hget₀, hshape₀⟩ := forall₂_sameShape_getElem? hshape hget
  rw [hshape₀.op_eq] at hget₀
  refine constInv_append (constInv_pop hinv hpop) (constInv_of_nil ?_ ?_)
  · intro v k ins outs hc x hx
    apply ChanMap.pushed_not_mem
    intro hx'
    obtain ⟨j, hgetj⟩ := List.mem_iff_getElem?.mp hc
    obtain rfl := idx_eq_of_mem_outputs haff hget₀ hgetj hx' hx
    rw [hgetj] at hget₀; cases hget₀
  · intro k ins outs hf x hx
    apply ChanMap.pushed_not_mem
    intro hx'
    obtain ⟨j, hgetj⟩ := List.mem_iff_getElem?.mp hf
    obtain rfl := idx_eq_of_mem_outputs haff hget₀ hgetj hx' hx
    rw [hgetj] at hget₀; cases hget₀

/-- Firing an async operator preserves `ConstInv`. -/
private theorem constInv_async [DecidableEq χ] [InterpConsts V] (haff : proc.AffineChan)
  {atoms₀ : AtomicProcs Op χ V} {chans chans' : ChanMap χ V} {i : Nat}
  {aop aop' : AsyncOp V} {allInputs allOutputs inputs outputs : List χ}
  {inputVals outputVals : List V}
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hinv : ConstInv proc chans)
  (hget : atoms₀[i]? = some (.async aop allInputs allOutputs))
  (hinterp : aop.Interp (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop')
  (hpop : ∀ y, chans y = ChanMap.pushed inputs inputVals y ++ chans' y) :
    ConstInv proc (λ y => chans' y ++ ChanMap.pushed outputs outputVals y) := by
  obtain ⟨ap₀, hget₀, hshape₀⟩ := forall₂_sameShape_getElem? hshape hget
  have hout : outputs ⊆ ap₀.outputs := by
    rw [hshape₀.outputs_eq]; exact hinterp.output_sublist.subset
  refine constInv_append (constInv_pop hinv hpop) ?_
  intro v k ins outs hc x hx
  refine ⟨λ w hw => ?_, λ k' outs' hf x' hx' w hw => ?_⟩
  · -- only the constant itself writes to `x`
    by_cases hx' : x ∈ outputs
    · obtain ⟨j, hgetj⟩ := List.mem_iff_getElem?.mp hc
      obtain rfl := idx_eq_of_mem_outputs haff hget₀ hgetj (hout hx') hx
      rw [hgetj] at hget₀; cases hget₀
      have heq := hshape₀.eq_of_not_stateful (by simp) (by simp)
      simp only [AtomicProc.async.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      cases hinterp
      exact List.eq_of_mem_replicate (mem_pushed hw)
    · rw [ChanMap.pushed_not_mem hx'] at hw; simp at hw
  · -- only the fork itself writes to `x'`, and it reads `x`
    by_cases hx'' : x' ∈ outputs
    · obtain ⟨j, hgetj⟩ := List.mem_iff_getElem?.mp hf
      obtain rfl := idx_eq_of_mem_outputs haff hget₀ hgetj (hout hx'') hx'
      rw [hgetj] at hget₀; cases hget₀
      have heq := hshape₀.eq_of_not_stateful (by simp) (by simp)
      simp only [AtomicProc.async.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      cases hinterp
      have hval := (hinv v k ins outs hc x hx).1
      rw [hpop x] at hval
      simp at hval
      exact (List.eq_of_mem_replicate (mem_pushed hw)).trans hval.1
    · rw [ChanMap.pushed_not_mem hx''] at hw; simp at hw

/-- If an async operator pushes to a fork output, then it is that fork. -/
private theorem forkPush_async [InterpConsts V] (haff : proc.AffineChan)
  {atoms₀ : AtomicProcs Op χ V} {i : Nat}
  {aop aop' : AsyncOp V} {allInputs allOutputs inputs outputs : List χ}
  {inputVals outputVals : List V}
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hget : atoms₀[i]? = some (.async aop allInputs allOutputs))
  (hinterp : aop.Interp (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    ForkPush proc outputs outputVals := by
  obtain ⟨ap₀, hget₀, hshape₀⟩ := forall₂_sameShape_getElem? hshape hget
  have hout : outputs ⊆ ap₀.outputs := by
    rw [hshape₀.outputs_eq]; exact hinterp.output_sublist.subset
  intro x hx k ins outs hf hx'
  obtain ⟨j, hgetj⟩ := List.mem_iff_getElem?.mp hf
  obtain rfl := idx_eq_of_mem_outputs haff hget₀ hgetj (hout hx) hx'
  rw [hgetj] at hget₀; cases hget₀
  have heq := hshape₀.eq_of_not_stateful (by simp) (by simp)
  simp only [AtomicProc.async.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  cases hinterp with | interp_fork _ hclone =>
  exact ⟨rfl, _, hclone, λ w hw => List.eq_of_mem_replicate hw⟩

end ConstInv

/-! Lifting local τ steps to the rewritten process. -/
section Lift

variable [Arity Op] [DecidableEq χ] [InterpConsts V]

/-- A local τ step is also a step with more atoms appended. -/
private theorem lift_step
  {ins : Vector χ m} {outs : Vector χ n} {U : AtomicProcs Op χ V}
  {c c' : Config Op χ V 0 0}
  (h : Config.Step c .τ c') :
    Config.Step (m := m) (n := n)
      ⟨⟨ins, outs, c.proc.atoms ++ U⟩, c.chans⟩ .τ ⟨⟨ins, outs, c'.proc.atoms ++ U⟩, c'.chans⟩ := by
  cases h with
  | step_async hi hget hinterp hpop =>
    rename_i i
    refine Lts.Step.eq_rhs (Config.Step.step_async (c := ⟨⟨ins, outs, c.proc.atoms ++ U⟩, c.chans⟩)
      (i := i) (by simp; omega) ?_ hinterp hpop) ?_
    · rw [List.getElem_append_left hi]; exact hget
    · simp [List.set_append_left _ _ hi]

private theorem lift_tau_star
  {ins : Vector χ m} {outs : Vector χ n} {U : AtomicProcs Op χ V}
  {c c' : Config Op χ V 0 0}
  (h : (Config.Step (Op := Op) (χ := χ) (V := V) (m := 0) (n := 0)).TauStar .τ c c') :
    (Config.Step (Op := Op) (χ := χ) (V := V) (m := m) (n := n)).TauStar .τ
      ⟨⟨ins, outs, c.proc.atoms ++ U⟩, c.chans⟩ ⟨⟨ins, outs, c'.proc.atoms ++ U⟩, c'.chans⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (lift_step hstep)

private theorem lift_local_tau_star
  {ins : Vector χ m} {outs : Vector χ n} {U : AtomicProcs Op χ V}
  {L L' : AtomicProcs Op χ V} {chans chans' : ChanMap χ V}
  (h : LocalTauStar L chans L' chans') :
    (Config.Step (Op := Op) (χ := χ) (V := V) (m := m) (n := n)).TauStar .τ
      ⟨⟨ins, outs, L ++ U⟩, chans⟩ ⟨⟨ins, outs, L' ++ U⟩, chans'⟩ :=
  lift_tau_star (c := LocalConfig L chans) (c' := LocalConfig L' chans') h

end Lift

/-! The simulation. -/
section Simulation

/-- The original configuration `c₀` and the rewritten configuration `c₁` only differ
in the atoms at `I` (related by `R`), and the state of the original process satisfies
`ConstInv`. -/
private def SimRel [Arity Op]
  (proc : Proc Op χ V m n) (I : List Nat)
  (R : AtomicProcs Op χ V → ChanMap χ V → AtomicProcs Op χ V → ChanMap χ V → Prop)
  (c₀ c₁ : Config Op χ V m n) : Prop :=
  ∃ atoms₀ L₁,
    c₀.proc = { proc with atoms := atoms₀ } ∧
    c₁.proc = { proc with atoms := L₁ ++ unmatchedOf atoms₀ I } ∧
    List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀ ∧
    ConstInv proc c₀.chans ∧
    R (matchedOf atoms₀ I) c₀.chans L₁ c₁.chans

variable [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {I : List Nat} {P' : AtomicProcs Op χ V}
  {R : AtomicProcs Op χ V → ChanMap χ V → AtomicProcs Op χ V → ChanMap χ V → Prop}

/-- Pops a list of channels read by neither the matched nor the replacement atoms. -/
private theorem frame_pop_list
  (hR : LocalSimRel proc I P' R)
  {L₀ L₁ : AtomicProcs Op χ V} {chans₀ chans₀' chans₁ : ChanMap χ V}
  {xs : List χ} {vs : List V}
  (hxs : ∀ x ∈ xs, x ∉ AtomicProcs.inputNames (matchedOf proc.atoms I) ∧ x ∉ P'.inputNames)
  (hrel : R L₀ chans₀ L₁ chans₁)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed xs vs y ++ chans₀' y) :
    ∃ chans₁', (∀ y, chans₁ y = ChanMap.pushed xs vs y ++ chans₁' y) ∧
      R L₀ chans₀' L₁ chans₁' := by
  induction xs generalizing vs chans₀ chans₁ with
  | nil =>
    obtain rfl : chans₀ = chans₀' := funext λ y => by simpa using hpop y
    exact ⟨chans₁, by simp, hrel⟩
  | cons x xs ih =>
    cases vs with
    | nil =>
      obtain rfl : chans₀ = chans₀' := funext λ y => by simpa using hpop y
      exact ⟨chans₁, by simp, hrel⟩
    | cons v vs =>
      have hx := hxs x (by simp)
      obtain ⟨chans₁'', hpop₁, hrel''⟩ := hR.frame_pop (x := x) (v := v)
        (chans₀' := λ y => ChanMap.pushed xs vs y ++ chans₀' y) hx.1 hx.2 hrel (λ y => by
          rw [hpop y, ChanMap.pushed_cons]
          by_cases h : y = x
          · subst h; simp
          · simp [h, Ne.symm h])
      obtain ⟨chans₁', hpop₁', hrel'⟩ := ih (λ x' hx' => hxs x' (by simp [hx'])) hrel'' (λ _ => rfl)
      refine ⟨chans₁', λ y => ?_, hrel'⟩
      rw [hpop₁ y, hpop₁' y, ChanMap.pushed_cons]
      by_cases h : y = x
      · subst h; simp
      · simp [h, Ne.symm h]

variable {atoms₀ L₁ : AtomicProcs Op χ V} {chans₀ chans₁ : ChanMap χ V}

/-- The environment pushes to the global inputs, which are not written by any atom. -/
private theorem sim_step_init
  (haff : proc.AffineChan) (hnames : RewriteNames proc I P') (hR : LocalSimRel proc I P' R)
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hinv : ConstInv proc chans₀)
  (hrel : R (matchedOf atoms₀ I) chans₀ L₁ chans₁)
  (args : Vector V m) :
    SimRel proc I R
      ⟨{ proc with atoms := atoms₀ }, chans₀.pushVals proc.inputs args⟩
      ⟨{ proc with atoms := L₁ ++ unmatchedOf atoms₀ I }, chans₁.pushVals proc.inputs args⟩ := by
  refine ⟨atoms₀, L₁, rfl, rfl, hshape, ?_, ?_⟩
  · simp only [ChanMap.pushVals_eq]
    exact constInv_append hinv (constInv_of_nil
      (λ _ _ _ _ hmem _ ho => ChanMap.pushed_not_mem λ hin => haff.2.2.2.1 _ hmem ho hin)
      (λ _ _ _ hmem _ ho => ChanMap.pushed_not_mem λ hin => haff.2.2.2.1 _ hmem ho hin))
  · simp only [ChanMap.pushVals_eq]
    refine hR.frame_push (by simp) (λ x hx => ?_) haff.1
      (λ x hx _ _ _ hf hx' => (haff.2.2.2.1 _ hf hx' hx).elim) hrel
    have h := not_mem_outputNames_of_input (I := I) haff hx
    exact ⟨h, not_mem_outputNames_rhs hnames h (mem_allNames_of_global_input hx)⟩

/-- The environment pops from the global outputs, which are not read by any atom. -/
private theorem sim_step_output
  (haff : proc.AffineChan) (hnames : RewriteNames proc I P') (hR : LocalSimRel proc I P' R)
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hinv : ConstInv proc chans₀)
  (hrel : R (matchedOf atoms₀ I) chans₀ L₁ chans₁)
  {outputVals : Vector V n} {chans₀' : ChanMap χ V}
  (hpop : chans₀.popVals proc.outputs = some (outputVals, chans₀')) :
    ∃ c₁', Lts.IORestrictedStep Config.Step
      ⟨{ proc with atoms := L₁ ++ unmatchedOf atoms₀ I }, chans₁⟩ (.output outputVals) c₁' ∧
      SimRel proc I R ⟨{ proc with atoms := atoms₀ }, chans₀'⟩ c₁' := by
  have hpop' := ChanMap.popVals_eq_some_iff.mp hpop
  obtain ⟨chans₁', hpop₁, hrel'⟩ := frame_pop_list hR (λ x hx => by
    have h := not_mem_inputNames_of_output (I := I) haff hx
    exact ⟨h, not_mem_inputNames_rhs hnames h (mem_allNames_of_global_output hx)⟩) hrel hpop'
  exact ⟨_, .step_output .refl (.step_output (ChanMap.popVals_eq_some_iff.mpr hpop₁)),
    atoms₀, L₁, rfl, rfl, hshape, constInv_pop hinv hpop', hrel'⟩

/-- An operator fires: either a matched one (`step_op`) or one outside the rewrite (frame). -/
private theorem sim_step_op
  (haff : proc.AffineChan) (hnames : RewriteNames proc I P') (hR : LocalSimRel proc I P' R)
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hinv : ConstInv proc chans₀)
  (hrel : R (matchedOf atoms₀ I) chans₀ L₁ chans₁)
  {o : Op} {inputs : Vector χ (Arity.ι o)} {outputs : Vector χ (Arity.ω o)}
  {inputVals : Vector V (Arity.ι o)} {outputVals : Vector V (Arity.ω o)}
  {chans₀' : ChanMap χ V}
  (hmem : .op o inputs outputs ∈ atoms₀)
  (hpop : chans₀.popVals inputs = some (inputVals, chans₀')) :
    ∃ c₁', Lts.IORestrictedStep Config.Step
      ⟨{ proc with atoms := L₁ ++ unmatchedOf atoms₀ I }, chans₁⟩
      (.yield o inputVals outputVals) c₁' ∧
      SimRel proc I R
        ⟨{ proc with atoms := atoms₀ }, chans₀'.pushVals outputs outputVals⟩ c₁' := by
  have hpop' := ChanMap.popVals_eq_some_iff.mp hpop
  have hinv' : ConstInv proc (chans₀'.pushVals outputs outputVals) := by
    rw [ChanMap.pushVals_eq]; exact constInv_op haff hshape hinv hmem hpop'
  obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hmem
  by_cases hiI : i ∈ I
  · -- A matched operator fires.
    obtain ⟨inputs', outputs', chans₁', hmem₁, hpop₁, hrel'⟩ :=
      hR.step_op hinv (forall₂_matchedOf hshape) hrel (mem_matchedOf_iff.mpr ⟨i, hiI, hget⟩) hpop'
    refine ⟨_, .step_yield (.step_op (List.mem_append_left _ hmem₁)
      (ChanMap.popVals_eq_some_iff.mpr hpop₁)), atoms₀, L₁, rfl, rfl, hshape, hinv', ?_⟩
    simp only [ChanMap.pushVals_eq]
    exact hrel'
  · -- An operator outside the rewrite fires.
    obtain ⟨ap₀, hget₀, hshape₀⟩ := forall₂_sameShape_getElem? hshape hget
    rw [hshape₀.op_eq] at hget₀
    obtain ⟨chans₁', hpop₁, hrel'⟩ := frame_pop_list hR (λ x hx => by
      have h := not_mem_inputNames_matchedOf haff hget₀ hiI hx
      exact ⟨h, not_mem_inputNames_rhs hnames h (Proc.mem_allNames_of_input hget₀ hx)⟩) hrel hpop'
    have hrel'' := hR.frame_push (outs := outputs.toList) (vals := outputVals.toList) (by simp)
      (λ x hx => by
        have h := not_mem_outputNames_matchedOf haff hget₀ hiI hx
        exact ⟨h, not_mem_outputNames_rhs hnames h (Proc.mem_allNames_of_output hget₀ hx)⟩)
      (haff.atom_nodup hget₀).2
      (λ x hx _ _ _ hf hx' => by
        obtain ⟨j, hgetj⟩ := List.mem_iff_getElem?.mp hf
        obtain rfl := idx_eq_of_mem_outputs haff hget₀ hgetj hx hx'
        rw [hgetj] at hget₀; cases hget₀)
      hrel'
    refine ⟨_, .step_yield (.step_op (List.mem_append_right _ (mem_unmatchedOf_iff.mpr
      ⟨i, hiI, hget⟩)) (ChanMap.popVals_eq_some_iff.mpr hpop₁)),
      atoms₀, L₁, rfl, rfl, hshape, hinv', ?_⟩
    simp only [ChanMap.pushVals_eq]
    exact hrel''

/-- An async operator fires: either a matched one (`step_async`)
or one outside the rewrite (frame). -/
private theorem sim_step_async
  (haff : proc.AffineChan) (hnames : RewriteNames proc I P') (hR : LocalSimRel proc I P' R)
  (hshape : List.Forall₂ AtomicProc.SameShape proc.atoms atoms₀)
  (hinv : ConstInv proc chans₀)
  (hrel : R (matchedOf atoms₀ I) chans₀ L₁ chans₁)
  {aop aop' : AsyncOp V} {allInputs allOutputs : List χ}
  {inputs : Vector χ k₁} {inputVals : Vector V k₁}
  {outputs : Vector χ k₂} {outputVals : Vector V k₂}
  {chans₀' : ChanMap χ V} {i : Nat}
  (hi : i < atoms₀.length)
  (hget : atoms₀[i] = .async aop allInputs allOutputs)
  (hinterp : aop.Interp (.mk allInputs allOutputs
    inputs.toList inputVals.toList outputs.toList outputVals.toList) aop')
  (hpop : chans₀.popVals inputs = some (inputVals, chans₀')) :
    ∃ c₁', Lts.IORestrictedStep Config.Step
      ⟨{ proc with atoms := L₁ ++ unmatchedOf atoms₀ I }, chans₁⟩ .τ c₁' ∧
      SimRel proc I R
        ⟨{ proc with atoms := atoms₀.set i (.async aop' allInputs allOutputs) },
          chans₀'.pushVals outputs outputVals⟩ c₁' := by
  have hpop' := ChanMap.popVals_eq_some_iff.mp hpop
  have hget' : atoms₀[i]? = some (.async aop allInputs allOutputs) :=
    List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  obtain ⟨ap₀, hget₀, hshape₀⟩ := forall₂_sameShape_getElem? hshape hget'
  have hshape' : List.Forall₂ AtomicProc.SameShape proc.atoms
      (atoms₀.set i (.async aop' allInputs allOutputs)) := by
    have ⟨hi₀, hget₀'⟩ := List.getElem?_eq_some_iff.mp hget₀
    have := List.forall₂_set (i := i) hshape
      (sameShape_trans hshape₀ (AtomicProc.SameShape.of_interp hinterp))
    rwa [← hget₀', List.set_getElem_self] at this
  have hinv' : ConstInv proc (chans₀'.pushVals outputs outputVals) := by
    rw [ChanMap.pushVals_eq]; exact constInv_async haff hshape hinv hget' hinterp hpop'
  by_cases hiI : i ∈ I
  · -- A matched atom fires.
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hiI
    have hlt : ∀ j ∈ I, j < atoms₀.length := λ j hj => hshape.length_eq ▸ hnames.idx_lt j hj
    obtain ⟨L₁', chans₁', htau, hrel'⟩ := hR.step_async hinv (forall₂_matchedOf hshape) hrel
      (by rw [getElem?_matchedOf hlt hp]; exact hget') hinterp (by simp) (by simp) hpop'
    refine ⟨_, .step_tau (lift_local_tau_star htau), _, L₁', rfl, ?_, hshape', hinv', ?_⟩
    · simp only [unmatchedOf_set_of_mem hiI]
    · rw [matchedOf_set_getElem hnames.idx_nodup hlt hp, ChanMap.pushVals_eq]
      exact hrel'
  · -- An atom outside the rewrite fires.
    have hin : inputs.toList ⊆ ap₀.inputs := by
      rw [hshape₀.inputs_eq]; exact hinterp.input_sublist.subset
    have hout : outputs.toList.Sublist ap₀.outputs := by
      rw [hshape₀.outputs_eq]; exact hinterp.output_sublist
    obtain ⟨chans₁', hpop₁, hrel'⟩ := frame_pop_list hR (λ x hx => by
      have h := not_mem_inputNames_matchedOf haff hget₀ hiI (hin hx)
      exact ⟨h, not_mem_inputNames_rhs hnames h (Proc.mem_allNames_of_input hget₀ (hin hx))⟩)
      hrel hpop'
    have hrel'' := hR.frame_push (outs := outputs.toList) (vals := outputVals.toList) (by simp)
      (λ x hx => by
        have h := not_mem_outputNames_matchedOf haff hget₀ hiI (hout.subset hx)
        exact ⟨h, not_mem_outputNames_rhs hnames h
          (Proc.mem_allNames_of_output hget₀ (hout.subset hx))⟩)
      ((haff.atom_nodup hget₀).2.sublist hout)
      (forkPush_async haff hshape hget' hinterp)
      hrel'
    obtain ⟨j, hj, hset⟩ := unmatchedOf_set_of_not_mem hiI hi
    rw [hget'] at hj
    have ⟨hj', hgetj⟩ := List.getElem?_eq_some_iff.mp hj
    have hstep := Config.Step.step_async
      (c := ⟨{ proc with atoms := L₁ ++ unmatchedOf atoms₀ I }, chans₁⟩) (i := L₁.length + j)
      (by simp; omega) (by rw [List.getElem_append_right (by omega)]; simpa using hgetj) hinterp
      (ChanMap.popVals_eq_some_iff.mpr hpop₁)
    refine ⟨_, .step_tau (.single hstep), _, L₁, rfl, ?_, hshape', hinv', ?_⟩
    · simp [hset, List.set_append_right _ _ (Nat.le_add_right _ _)]
    · rw [matchedOf_set_of_not_mem hiI]
      simp only [ChanMap.pushVals_eq]
      exact hrel''

/-- The core simulation, without the extra properties. -/
private theorem sim_rewrite_core
  (haff : proc.AffineChan) (hnames : RewriteNames proc I P') (hR : LocalSimRel proc I P' R) :
    Lts.Simulation (Config.Step (Op := Op) (χ := χ) (V := V) (m := m) (n := n))
      (Lts.IORestrictedStep Config.Step) (SimRel proc I R)
      (Config.init proc) (Config.init { proc with atoms := P' ++ unmatchedOf proc.atoms I }) := by
  constructor
  · exact ⟨proc.atoms, P', rfl, rfl, List.forall₂_same.mpr λ _ _ => .refl, constInv_empty,
      hR.init⟩
  · rintro ⟨proc₀, chans₀⟩ ⟨proc₁, chans₁⟩ l c₀' ⟨atoms₀, L₁, h₀, h₁, hshape, hinv, hrel⟩ hstep
    simp only at h₀ h₁ hinv hrel
    subst h₀ h₁
    cases hstep with
    | step_init =>
      exact ⟨_, .step_input .step_init .refl, sim_step_init haff hnames hR hshape hinv hrel _⟩
    | step_output hpop => exact sim_step_output haff hnames hR hshape hinv hrel hpop
    | step_op hmem hpop => exact sim_step_op haff hnames hR hshape hinv hrel hmem hpop
    | step_async hi hget hinterp hpop =>
      exact sim_step_async haff hnames hR hshape hinv hrel hi hget hinterp hpop

end Simulation

/-- Replacing the atoms at `I` with `P'` is a forward simulation preserving initial states. -/
theorem sim_rewrite_preserves_init
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {I : List Nat} {P' : AtomicProcs Op χ V}
  (haff : proc.AffineChan)
  (hok : RuleOK proc I P') :
    proc.semantics ≲ᵣ[PreservesInit]
      ({ proc with atoms := P' ++ unmatchedOf proc.atoms I } : Proc Op χ V m n).semantics
  := by
  obtain ⟨hnames, R, hR, hinit⟩ := hok
  refine Lts.SimilaritySt.intro (SimRel proc I R) (sim_rewrite_core haff hnames hR) ?_
  rintro ⟨proc₀, chans₀⟩ ⟨proc₁, chans₁⟩ ⟨atoms₀, L₁, h₀, h₁, -, -, hrel⟩ heq
  simp only [Proc.semantics, Config.init, Config.mk.injEq] at heq h₀ h₁ hrel ⊢
  obtain ⟨rfl, rfl⟩ := heq
  obtain rfl : atoms₀ = proc₀.atoms := (congrArg Proc.atoms h₀).symm
  obtain ⟨rfl, rfl⟩ := hinit hrel
  exact ⟨h₁, rfl⟩

/-- Replacing the atoms at `I` with `P'` is a forward simulation. -/
theorem sim_rewrite
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {I : List Nat} {P' : AtomicProcs Op χ V}
  (haff : proc.AffineChan)
  (hok : RuleOKNoInit proc I P') :
    proc.semantics ≲ᵣ
      ({ proc with atoms := P' ++ unmatchedOf proc.atoms I } : Proc Op χ V m n).semantics
  := by
  obtain ⟨hnames, R, hR⟩ := hok
  exact Lts.Similarity.intro (SimRel proc I R) (sim_rewrite_core haff hnames hR)

end Wavelet.Compile
