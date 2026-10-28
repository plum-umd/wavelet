import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstLemmas

/-! `order-const*`: waiting on a constant is the same as waiting on its activation. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ConstLemmas

theorem order_const_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k : Nat} [NeZero k] {first output act output' : χ} {rest : List χ} {v : V}
  [NeZero ((first :: rest).erase output' ++ [act]).length]
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.order k) (first :: rest) [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.const v 1) [act] [output']))
  (hne : i₂ ≠ i₁)
  (hlen : (first :: rest).length = k)
  (hmem : output' ∈ rest) (hne' : output' ≠ first) :
    RuleOK proc [i₂, i₁] [
      .order ((first :: rest).erase output' ++ [act]).toVector output,
    ]
  := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.const v 1) [act] [output'],
        .async (.order k) (first :: (s ++ output' :: t)) [output]] := by
    simp [h₁, h₂]
  have hP' : ([.order ((first :: (s ++ output' :: t)).erase output' ++ [act]).toVector output] :
      AtomicProcs Op χ V) =
      [.async (.order ((first :: (s ++ output' :: t)).erase output' ++ [act]).length)
        ((first :: (s ++ output' :: t)).erase output' ++ [act]) [output]] := rfl
  -- Facts from affineness
  have hnd := (haff.atom_nodup h₁).1
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  simp at hnd hdisj
  obtain ⟨⟨hfs, hfo, hft⟩, hnd⟩ := hnd
  rw [List.nodup_append] at hnd
  simp at hnd
  obtain ⟨hsn, ⟨hot, htn⟩, hst⟩ := hnd
  have hos : output' ∉ s := λ h => (hst _ h).1 rfl
  obtain ⟨⟨haf, has, hao, hat⟩, hoo⟩ := hdisj
  have herase : (first :: (s ++ output' :: t)).erase output' ++ [act] =
      first :: (s ++ (t ++ [act])) := by
    rw [List.erase_cons_tail (by simpa using hfo), List.erase_append_right _ hos,
      List.erase_cons_head]
    simp
  -- The activations `X` consumed by the original const are still in `act` after the rewrite;
  -- `output'` is empty after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.async (.order ((first :: (s ++ output' :: t)).erase output' ++ [act]).length)
        ((first :: (s ++ output' :: t)).erase output' ++ [act]) [output]] ∧
    (∃ X, chans₁ act = X ++ chans₀ act ∧ X.length = (chans₀ output').length) ∧
    chans₁ output' = [] ∧
    (∀ y, y ≠ act → y ≠ output' → chans₀ y = chans₁ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · rw [hP']
      simp only [AtomicProcs.inputNames_cons, AtomicProc.inputs_async, AtomicProcs.inputNames_nil,
        List.append_nil, herase]
      simp [hfs, hft, Ne.symm haf]
      rw [List.nodup_append, List.nodup_append]
      refine ⟨hsn, ⟨htn, by simp, ?_⟩, ?_⟩
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact λ h => hat (h ▸ ha)
      · intro a ha b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact (hst a ha).2 b hb
        · rw [List.mem_singleton] at hb
          subst hb
          exact λ h => has (h ▸ ha)
    · simp [hP']
    · rw [hP']
      simp only [AtomicProcs.inputNames_cons, AtomicProc.inputs_async, AtomicProcs.inputNames_nil,
        List.append_nil, herase, hP]
      intro x hx
      left
      simp at hx ⊢
      tauto
    · simp [hP', hP]
  · constructor
    · exact ⟨rfl, hP', ⟨[], by simp, by simp⟩, rfl, λ _ _ _ => rfl⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx₁ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hout, heq⟩ hpop
      have hxa : x ≠ act := by rintro rfl; simp [hP] at hx₁
      have hxo : x ≠ output' := by rintro rfl; simp [hP] at hx₁
      obtain ⟨hx₀, h₀⟩ := ChanMap.frame_pop_inv hpop
      obtain ⟨chans₁', hpop₁, hx₁', h₁'⟩ := ChanMap.frame_pop_head
        (chans := chans₁) (x := x) (w := w) (rest := chans₀' x)
        (by rw [← heq x hxa hxo, hx₀])
      refine ⟨chans₁', hpop₁, rfl, rfl, ⟨X, ?_, ?_⟩, ?_, ?_⟩
      · rw [h₁' _ (Ne.symm hxa), h₀ _ (Ne.symm hxa), hX]
      · rw [h₀ _ (Ne.symm hxo), hXlen]
      · rw [h₁' _ (Ne.symm hxo), hout]
      · intro y hya hyo
        by_cases hyx : y = x
        · subst hyx; rw [hx₁']
        · rw [h₁' _ hyx, h₀ _ hyx, heq y hya hyo]
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hout, heq⟩
      have ho : output' ∉ outs := λ h => by simpa [hP] using (hx output' h).1
      refine ⟨rfl, rfl, ⟨X, by simp [hX], by simp [ChanMap.pushed_not_mem ho, hXlen]⟩, ?_, ?_⟩
      · simp [ChanMap.pushed_not_mem ho, hout]
      · intro y hya hyo
        simp [heq y hya hyo]
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hout, heq⟩ hget hinterp hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The const fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨_, av, -, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        have hpa := hpop act
        simp at hpa
        have h₀ : ∀ y, y ≠ act → chans₀' y = chans₀ y := λ y hy => by
          simpa [Ne.symm hy] using (hpop y).symm
        refine ⟨_, _, .refl, ?_, rfl, ⟨X ++ [av], ?_, ?_⟩, hout, ?_⟩
        · simp
        · simp [hX, hpa, Ne.symm hao]
        · simp [h₀ _ (Ne.symm hao), hXlen]
        · intro y hya hyo
          simp [Ne.symm hyo, h₀ _ hya, heq y hya hyo]
      | 1, hget =>
        -- The order fires: the rewritten order reads the head of `X` instead of `output'`.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, w₀, ws, rfl, rfl⟩ := hinterp.order_inv
        obtain ⟨sv, wo, tv, rfl, hsv, htv⟩ := exists_split_of_length (ws := ws) (s := s) (t := t)
          (x := output') (by simpa using hlen₁.symm)
        have hpush : ∀ y,
            ChanMap.pushed (first :: (s ++ output' :: t)) (w₀ :: (sv ++ wo :: tv)) y =
            (if first = y then [w₀] else []) ++ ChanMap.pushed s sv y ++
              ((if output' = y then [wo] else []) ++ ChanMap.pushed t tv y) := by
          intro y
          rw [ChanMap.pushed_cons, ChanMap.pushed_append hsv.symm, ChanMap.pushed_cons]
          simp only [List.append_assoc]
        have hpo : chans₀ output' = wo :: chans₀' output' := by
          rw [hpop, hpush]
          simp [hfo, ChanMap.pushed_not_mem hos, ChanMap.pushed_not_mem hot]
        have hpa : chans₀' act = chans₀ act := by
          rw [hpop act, hpush]
          simp [Ne.symm haf, ChanMap.pushed_not_mem has, Ne.symm hao, ChanMap.pushed_not_mem hat]
        cases X with
        | nil => simp [hpo] at hXlen
        | cons x₀ X =>
        have hXlen' : X.length = (chans₀' output').length := by simpa [hpo] using hXlen
        have hpush' : ∀ y,
            ChanMap.pushed ((first :: (s ++ output' :: t)).erase output' ++ [act])
              (w₀ :: (sv ++ (tv ++ [x₀]))) y =
            (if first = y then [w₀] else []) ++ ChanMap.pushed s sv y ++
              (ChanMap.pushed t tv y ++ (if act = y then [x₀] else [])) := by
          intro y
          rw [herase, ChanMap.pushed_cons, ChanMap.pushed_append hsv.symm,
            ChanMap.pushed_append htv.symm]
          simp only [ChanMap.pushed_cons, ChanMap.pushed_nil_left, List.append_nil,
            List.append_assoc]
        obtain ⟨chans₁', hpop₁, hca, hco, hc⟩ : ∃ chans₁' : ChanMap χ V,
            (∀ y, chans₁ y = ChanMap.pushed ((first :: (s ++ output' :: t)).erase output' ++ [act])
              (w₀ :: (sv ++ (tv ++ [x₀]))) y ++ chans₁' y) ∧
            chans₁' act = X ++ chans₀ act ∧ chans₁' output' = [] ∧
            ∀ y, y ≠ act → y ≠ output' → chans₁' y = chans₀' y := by
          refine ⟨λ y => if y = act then X ++ chans₀ act else if y = output' then [] else chans₀' y,
            ?_, by simp, by simp [Ne.symm hao], λ y h₁ h₂ => by simp [h₁, h₂]⟩
          intro y
          rw [hpush']
          by_cases hya : y = act
          · subst hya
            simp [Ne.symm haf, ChanMap.pushed_not_mem has, ChanMap.pushed_not_mem hat, hX]
          · by_cases hyo : y = output'
            · subst hyo
              simp [hfo, ChanMap.pushed_not_mem hos, ChanMap.pushed_not_mem hot, hao, Ne.symm hao,
                hout]
            · have := hpop y
              rw [hpush] at this
              simp [hya, hyo, Ne.symm hya, Ne.symm hyo] at this ⊢
              rw [← heq y hya hyo, this]
        have hlenv : (w₀ :: (sv ++ (tv ++ [x₀]))).length =
            ((first :: (s ++ output' :: t)).erase output' ++ [act]).length := by
          rw [herase]; simp [hsv, htv]
        have hstep := LocalTauStar.async_list_mem
          (L := ([.async (.order ((first :: (s ++ output' :: t)).erase output' ++ [act]).length)
            ((first :: (s ++ output' :: t)).erase output' ++ [act]) [output]] :
              AtomicProcs Op χ V))
          (aop := .order ((first :: (s ++ output' :: t)).erase output' ++ [act]).length)
          (allInputs := (first :: (s ++ output' :: t)).erase output' ++ [act])
          (allOutputs := [output]) (outputs := [output]) (outputVals := [w₀])
          (List.mem_singleton_self _) (AsyncOp.Interp.order_mk rfl hlenv) hlenv.symm rfl hpop₁
        refine ⟨_, _, hstep, ?_, rfl, ⟨X, ?_, ?_⟩, ?_, ?_⟩
        · simp
        · simp [hca, hpa]
        · simp [hoo, hXlen']
        · simp [hco, hoo]
        · intro y hya hyo
          simp [hc y hya hyo]
  · rintro L₁ chans₁ ⟨_, rfl, ⟨X, hX, hXlen⟩, hout, heq⟩
    refine ⟨hP'.symm, ?_⟩
    simp at hXlen
    subst hXlen
    funext y
    by_cases hya : y = act
    · subst hya; simpa using hX
    · by_cases hyo : y = output'
      · subst hyo; exact hout
      · exact (heq y hya hyo).symm

theorem order_const_head_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k : Nat} [NeZero k] {output act output' : χ} {rest : List χ} {v : V}
  [NeZero (act :: rest).length]
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.order k) (output' :: rest) [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.const v 1) [act] [output']))
  (hne : i₂ ≠ i₁)
  (hlen : (output' :: rest).length = k) :
    RuleOK proc [i₂, i₁] [
      .order (act :: rest).toVector output',
      .const v output' #v[output],
    ]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.const v 1) [act] [output'], .async (.order k) (output' :: rest) [output]] := by
    simp [h₁, h₂]
  have hP' : ([.order (act :: rest).toVector output', .const v output' #v[output]] :
      AtomicProcs Op χ V) =
      [.async (.order (act :: rest).length) (act :: rest) [output'],
        .async (.const v 1) [output'] [output]] := rfl
  -- Facts from affineness
  have hnd := (haff.atom_nodup h₁).1
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  simp at hnd hdisj
  obtain ⟨hor, hrn⟩ := hnd
  obtain ⟨⟨hao, har⟩, hoo⟩ := hdisj
  -- The activations `X` consumed by the original const are still in `act` after the rewrite;
  -- `output'` is empty after the rewrite, since the rewritten order and const fire together;
  -- other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.async (.order (act :: rest).length) (act :: rest) [output'],
      .async (.const v 1) [output'] [output]] ∧
    (∃ X, chans₁ act = X ++ chans₀ act ∧ X.length = (chans₀ output').length) ∧
    (∀ w ∈ chans₀ output', w = v) ∧
    chans₁ output' = [] ∧
    (∀ y, y ≠ act → y ≠ output' → chans₀ y = chans₁ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · rw [hP']
      simp only [AtomicProcs.inputNames_cons, AtomicProc.inputs_async, AtomicProcs.inputNames_nil,
        List.append_nil]
      rw [List.nodup_append]
      refine ⟨List.nodup_cons.mpr ⟨har, hrn⟩, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hao
      · exact λ h => hor (h ▸ ha)
    · simp [hP', Ne.symm hoo]
    · rw [hP']
      simp only [AtomicProcs.inputNames_cons, AtomicProc.inputs_async, AtomicProcs.inputNames_nil,
        List.append_nil, hP]
      intro x hx
      left
      simp at hx ⊢
      tauto
    · simp [hP', hP]
  · constructor
    · exact ⟨rfl, hP', ⟨[], by simp, by simp⟩, by simp, rfl, λ _ _ _ => rfl⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx₁ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hvals, hout, heq⟩ hpop
      have hxa : x ≠ act := by rintro rfl; simp [hP] at hx₁
      have hxo : x ≠ output' := by rintro rfl; simp [hP] at hx₁
      obtain ⟨hx₀, h₀⟩ := ChanMap.frame_pop_inv hpop
      obtain ⟨chans₁', hpop₁, hx₁', h₁'⟩ := ChanMap.frame_pop_head
        (chans := chans₁) (x := x) (w := w) (rest := chans₀' x)
        (by rw [← heq x hxa hxo, hx₀])
      refine ⟨chans₁', hpop₁, rfl, rfl, ⟨X, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [h₁' _ (Ne.symm hxa), h₀ _ (Ne.symm hxa), hX]
      · rw [h₀ _ (Ne.symm hxo), hXlen]
      · rw [h₀ _ (Ne.symm hxo)]; exact hvals
      · rw [h₁' _ (Ne.symm hxo), hout]
      · intro y hya hyo
        by_cases hyx : y = x
        · subst hyx; rw [hx₁']
        · rw [h₁' _ hyx, h₀ _ hyx, heq y hya hyo]
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hvals, hout, heq⟩
      have ho : output' ∉ outs := λ h => by simpa [hP] using (hx output' h).1
      refine ⟨rfl, rfl, ⟨X, by simp [hX], by simp [ChanMap.pushed_not_mem ho, hXlen]⟩,
        ?_, ?_, ?_⟩
      · simpa [ChanMap.pushed_not_mem ho] using hvals
      · simp [ChanMap.pushed_not_mem ho, hout]
      · intro y hya hyo
        simp [heq y hya hyo]
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hvals, hout, heq⟩ hget hinterp hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The const fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, ⟨_, av, -, rfl⟩, rfl⟩ := hinterp.const_inv hlen₁
        have hpa := hpop act
        simp at hpa
        have h₀ : ∀ y, y ≠ act → chans₀' y = chans₀ y := λ y hy => by
          simpa [Ne.symm hy] using (hpop y).symm
        refine ⟨_, _, .refl, ?_, rfl, ⟨X ++ [av], ?_, ?_⟩, ?_, hout, ?_⟩
        · simp
        · simp [hX, hpa, Ne.symm hao]
        · simp [h₀ _ (Ne.symm hao), hXlen]
        · intro w hw
          simp [h₀ _ (Ne.symm hao)] at hw
          rcases hw with hw | rfl
          · exact hvals w hw
          · rfl
        · intro y hya hyo
          simp [Ne.symm hyo, h₀ _ hya, heq y hya hyo]
      | 1, hget =>
        -- The order fires: the rewritten order reads the head of `X` instead of `output'`,
        -- then the rewritten const fires.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, -, w₀, ws, rfl, rfl⟩ := hinterp.order_inv
        have hpo : chans₀ output' = w₀ :: chans₀' output' := by
          rw [hpop]; simp [ChanMap.pushed_not_mem hor]
        have hpa : chans₀' act = chans₀ act := by
          rw [hpop act]; simp [Ne.symm hao, ChanMap.pushed_not_mem har]
        have hw₀ : w₀ = v := hvals w₀ (by simp [hpo])
        cases X with
        | nil => simp [hpo] at hXlen
        | cons x₀ X =>
        have hXlen' : X.length = (chans₀' output').length := by simpa [hpo] using hXlen
        obtain ⟨chans₁', hpop₁, hca, hco, hc⟩ : ∃ chans₁' : ChanMap χ V,
            (∀ y, chans₁ y = ChanMap.pushed (act :: rest) (x₀ :: ws) y ++ chans₁' y) ∧
            chans₁' act = X ++ chans₀ act ∧ chans₁' output' = [] ∧
            ∀ y, y ≠ act → y ≠ output' → chans₁' y = chans₀' y := by
          refine ⟨λ y => if y = act then X ++ chans₀ act else if y = output' then [] else chans₀' y,
            ?_, by simp, by simp [Ne.symm hao], λ y h₁ h₂ => by simp [h₁, h₂]⟩
          intro y
          by_cases hya : y = act
          · subst hya
            simp [ChanMap.pushed_not_mem har, hX]
          · by_cases hyo : y = output'
            · subst hyo
              simp [hao, Ne.symm hao, ChanMap.pushed_not_mem hor, hout]
            · have := hpop y
              simp [hya, hyo, Ne.symm hya, Ne.symm hyo] at this ⊢
              rw [← heq y hya hyo, this]
        have hlenv : (x₀ :: ws).length = (act :: rest).length := by simpa using hlen₁.symm
        have hstep₁ := LocalTauStar.async_list_mem
          (L := ([.async (.order (act :: rest).length) (act :: rest) [output'],
            .async (.const v 1) [output'] [output]] : AtomicProcs Op χ V))
          (aop := .order (act :: rest).length) (allInputs := act :: rest)
          (allOutputs := [output']) (outputs := [output']) (outputVals := [x₀])
          (by simp) (AsyncOp.Interp.order_mk rfl hlenv) hlenv.symm rfl hpop₁
        obtain ⟨M₂, hpop₂, hM₂o, hM₂⟩ := ChanMap.pop_one
          (chans := λ y => chans₁' y ++ ChanMap.pushed [output'] [x₀] y) (x := output') (w := x₀)
          (rest := []) (by simp [hco])
        have hstep₂ := LocalTauStar.async_list_mem
          (L := ([.async (.order (act :: rest).length) (act :: rest) [output'],
            .async (.const v 1) [output'] [output]] : AtomicProcs Op χ V))
          (aop := .const v 1) (allInputs := [output']) (allOutputs := [output])
          (outputs := [output]) (outputVals := [v])
          (by simp) (.interp_const rfl) rfl rfl hpop₂
        refine ⟨_, _, hstep₁.trans hstep₂, ?_, rfl, ⟨X, ?_, ?_⟩, ?_, ?_, ?_⟩
        · simp
        · simp [hM₂ act hao, hca, hpa, Ne.symm hao, hw₀]
        · simp [hoo, hXlen']
        · intro w hw
          simp [hoo] at hw
          exact hvals w (by simp [hpo, hw])
        · simp [hM₂o, hoo]
        · intro y hya hyo
          simp [hM₂ y hyo, hc y hya hyo, Ne.symm hyo, hw₀]
  · rintro L₁ chans₁ ⟨_, rfl, ⟨X, hX, hXlen⟩, -, hout, heq⟩
    refine ⟨hP'.symm, ?_⟩
    simp at hXlen
    subst hXlen
    funext y
    by_cases hya : y = act
    · subst hya; simpa using hX
    · by_cases hyo : y = output'
      · subst hyo; exact hout
      · exact (heq y hya hyo).symm

end Wavelet.Compile.DeadCodeElim
