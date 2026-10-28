import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SimpleLemmasB

/-! `order-order`: nested orders can be folded. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow SimpleB

/-- Channels of the rewritten graph: the values consumed by the first order (`ins → o`)
but not yet by the second one are still in `ins` (`c₀` is the first input of `ins`). -/
private def OrderChans [DecidableEq χ] (ins : List χ) (c₀ o : χ)
    (chans₀ chans₁ : ChanMap χ V) : Prop :=
  chans₁ o = [] ∧
  (∀ y, y ∉ ins → y ≠ o → chans₁ y = chans₀ y) ∧
  (∀ c ∈ ins, ∃ A, chans₁ c = A ++ chans₀ c ∧ A.length = (chans₀ o).length) ∧
  chans₁ c₀ = chans₀ o ++ chans₀ c₀

section OrderChans

variable [DecidableEq χ] {ins : List χ} {c₀ o : χ}

private theorem OrderChans.empty : OrderChans ins c₀ o (ChanMap.empty : ChanMap χ V) .empty :=
  ⟨rfl, λ _ _ _ => rfl, λ _ _ => ⟨[], rfl, rfl⟩, rfl⟩

private theorem OrderChans.eq_empty {chans₁ : ChanMap χ V}
  (h : OrderChans ins c₀ o .empty chans₁) : chans₁ = .empty := by
  obtain ⟨ho, hother, hins, -⟩ := h
  funext y
  by_cases hy : y ∈ ins
  · obtain ⟨A, hA, hAlen⟩ := hins y hy
    rw [hA, List.eq_nil_of_length_eq_zero hAlen]
    rfl
  · by_cases hyo : y = o
    · subst hyo
      exact ho
    · exact hother y hy hyo

/-- Pushing to channels other than `o`. -/
private theorem OrderChans.push {chans₀ chans₁ : ChanMap χ V}
  (P : χ → List V) (hP : P o = []) (h : OrderChans ins c₀ o chans₀ chans₁) :
    OrderChans ins c₀ o (λ y => chans₀ y ++ P y) (λ y => chans₁ y ++ P y) := by
  obtain ⟨ho, hother, hins, hhead⟩ := h
  refine ⟨by simp [ho, hP], λ y hy hyo => by simp [hother y hy hyo], λ c hc => ?_,
    by simp [hhead, hP]⟩
  obtain ⟨A, hA, hAlen⟩ := hins c hc
  exact ⟨A, by simp [hA], by simp [hAlen, hP]⟩

/-- Popping a channel read by the rest of the graph. -/
private theorem OrderChans.frame_pop {x : χ} {v : V} {chans₀ chans₀' chans₁ : ChanMap χ V}
  (hc₀ : c₀ ∈ ins) (hx : x ∉ ins) (hxo : x ≠ o) (h : OrderChans ins c₀ o chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = (if y = x then [v] else []) ++ chans₀' y) :
    ∃ chans₁', (∀ y, chans₁ y = (if y = x then [v] else []) ++ chans₁' y) ∧
      OrderChans ins c₀ o chans₀' chans₁' := by
  obtain ⟨ho, hother, hins, hhead⟩ := h
  have hpop' : ∀ y, y ≠ x → chans₀' y = chans₀ y := λ y hy => by simp [hpop y, hy]
  refine ⟨λ y => if y = x then chans₀' y else chans₁ y, λ y => ?_, ?_, λ y hy hyo => ?_,
    λ c hc => ?_, ?_⟩
  · by_cases hyx : y = x
    · rw [hyx]
      simp [hother x hx hxo, hpop x]
    · simp [hyx]
  · simp [Ne.symm hxo, ho]
  · by_cases hyx : y = x
    · simp [hyx]
    · simp [hyx, hother y hy hyo, hpop' y hyx]
  · have hcx : c ≠ x := λ h => hx (h ▸ hc)
    obtain ⟨A, hA, hAlen⟩ := hins c hc
    exact ⟨A, by simp [hcx, hA, hpop' c hcx], by rw [hAlen, hpop' o (Ne.symm hxo)]⟩
  · have hcx : c₀ ≠ x := λ h => hx (h ▸ hc₀)
    simp [hcx, hhead, hpop' c₀ hcx, hpop' o (Ne.symm hxo)]

/-- The first order fires: its consumed values are kept in its inputs. -/
private theorem OrderChans.order₁ {rest : List χ} {v : V} {restV : List V}
  {chans₀ chans₀' chans₁ : ChanMap χ V}
  (hnd : (c₀ :: rest).Nodup) (ho : o ∉ c₀ :: rest)
  (hlen : (c₀ :: rest).length = (v :: restV).length)
  (h : OrderChans (c₀ :: rest) c₀ o chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed (c₀ :: rest) (v :: restV) y ++ chans₀' y) :
    OrderChans (c₀ :: rest) c₀ o (λ y => chans₀' y ++ ChanMap.pushed [o] [v] y) chans₁ := by
  obtain ⟨hho, hother, hins, hhead⟩ := h
  have hpo : ∀ y, y ≠ o → ChanMap.pushed [o] [v] y = [] := λ y hy => by simp [Ne.symm hy]
  have hout : chans₀' o = chans₀ o := by
    rw [hpop o, ChanMap.pushed_not_mem ho]
    rfl
  refine ⟨hho, λ y hy hyo => ?_, λ c hc => ?_, ?_⟩
  · simp [hpo y hyo, hother y hy hyo, hpop y, ChanMap.pushed_not_mem hy]
  · have hco : c ≠ o := λ h => ho (h ▸ hc)
    obtain ⟨A, hA, hAlen⟩ := hins c hc
    obtain ⟨vc, hvc⟩ := pushed_singleton hnd hc hlen
    refine ⟨A ++ [vc], ?_, ?_⟩
    · beta_reduce
      rw [hA, hpop c, hvc, hpo c hco]
      simp
    · simp [hAlen, hout]
  · have hc₀ : ChanMap.pushed (c₀ :: rest) (v :: restV) c₀ = [v] := by
      simp [ChanMap.pushed_not_mem (List.nodup_cons.mp hnd).1]
    have hc₀o : c₀ ≠ o := λ h => ho (h ▸ List.mem_cons_self ..)
    beta_reduce
    rw [hhead, hpop c₀, hc₀, hpo c₀ hc₀o, hout]
    simp

/-- The values of the inputs `N` of the rewritten order are available
when the second order (with inputs `ins'`) fires. -/
private theorem OrderChans.ne_nil {ins' N : List χ} {chans₀ chans₁ : ChanMap χ V}
  (hN : ∀ y, y ∈ N ↔ y ∈ ins ∨ (y ∈ ins' ∧ y ≠ o)) (hdisj : ins'.Disjoint ins)
  (hoi : o ∈ ins') (hne₀ : ∀ y ∈ ins', chans₀ y ≠ [])
  (h : OrderChans ins c₀ o chans₀ chans₁) :
    ∀ y ∈ N, chans₁ y ≠ [] := by
  obtain ⟨-, hother, hins, -⟩ := h
  intro y hy
  rcases (hN y).mp hy with hy | ⟨hy, hyo⟩
  · obtain ⟨A, hA, hAlen⟩ := hins y hy
    rw [hA]
    intro h
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp h
    exact hne₀ o hoi (List.eq_nil_of_length_eq_zero hAlen.symm)
  · rw [hother y (λ h => hdisj hy h) hyo]
    exact hne₀ y hy

/-- The second order (with inputs `ins'`) fires, and the rewritten order
(with inputs `N`) fires on the same values. -/
private theorem OrderChans.order₂ {ins' N : List χ} {chans₀ chans₀' chans₁ : ChanMap χ V}
  (hc₀ : c₀ ∈ ins) (hoi : o ∈ ins') (hdisj : ins'.Disjoint ins)
  (hN : ∀ y, y ∈ N ↔ y ∈ ins ∨ (y ∈ ins' ∧ y ≠ o)) (hne : chans₀ o ≠ [])
  (htail : ∀ y, chans₀' y = if y ∈ ins' then (chans₀ y).tail else chans₀ y)
  (h : OrderChans ins c₀ o chans₀ chans₁) :
    OrderChans ins c₀ o chans₀' (λ y => if y ∈ N then (chans₁ y).tail else chans₁ y) := by
  obtain ⟨hho, hother, hins, hhead⟩ := h
  have hoN : o ∉ N := by
    rw [hN]
    rintro (h | ⟨-, h⟩)
    · exact hdisj hoi h
    · exact h rfl
  have hto : chans₀' o = (chans₀ o).tail := by rw [htail o, if_pos hoi]
  have htc : ∀ c ∈ ins, chans₀' c = chans₀ c := λ c hc => by
    rw [htail c, if_neg (λ h => hdisj h hc)]
  have hcN : ∀ c ∈ ins, c ∈ N := λ c hc => (hN c).mpr (.inl hc)
  refine ⟨?_, λ y hy hyo => ?_, λ c hc => ?_, ?_⟩
  · beta_reduce
    rw [if_neg hoN, hho]
  · beta_reduce
    rw [hother y hy hyo, htail y]
    by_cases hy' : y ∈ ins'
    · rw [if_pos ((hN y).mpr (.inr ⟨hy', hyo⟩)), if_pos hy']
    · have hyN : y ∉ N := λ h => by
        rcases (hN y).mp h with h | ⟨h, -⟩
        · exact hy h
        · exact hy' h
      rw [if_neg hyN, if_neg hy']
  · beta_reduce
    obtain ⟨A, hA, hAlen⟩ := hins c hc
    have hA' : A ≠ [] := λ h => hne (List.eq_nil_of_length_eq_zero (by rw [← hAlen, h]; rfl))
    refine ⟨A.tail, ?_, ?_⟩
    · rw [if_pos (hcN c hc), hA, List.tail_append_of_ne_nil hA', htc c hc]
    · rw [hto, List.length_tail, List.length_tail, hAlen]
  · beta_reduce
    rw [if_pos (hcN c₀ hc₀), hhead, List.tail_append_of_ne_nil hne, hto, htc c₀ hc₀]

end OrderChans

private theorem flatten_map_ne [DecidableEq χ] {l ins : List χ} {o : χ} (h : o ∉ l) :
    (l.map (λ name => if name = o then ins else [name])).flatten = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.map_cons, List.flatten_cons, ih h.2, if_neg (Ne.symm h.1),
      List.singleton_append]

theorem order_order_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {k₁ k₂ : Nat} [NeZero k₁] [NeZero k₂] {inputs inputs' newInputs' : List χ} {output output' : χ}
  [NeZero newInputs'.length]
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.order k₁) inputs [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.order k₂) inputs' [output']))
  (hne : i₂ ≠ i₁)
  (hk₁ : k₁ > 1) (hlen : inputs.length = k₁)
  (hlen' : inputs'.length = k₂)
  (hmem : output ∈ inputs')
  (hnew : newInputs' = (inputs'.map (λ name => if name = output then inputs else [name])).flatten) :
    RuleOK proc [i₂, i₁] [.order newInputs'.toVector output']
  := by
  -- Decompose `inputs'` around `output`, and `inputs` into its first input and the rest.
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
  obtain ⟨c₀, rest₀, rfl⟩ := List.exists_cons_of_ne_nil (l := inputs)
    (λ h => by subst h; simp at hlen; omega)
  -- Facts from affineness
  have hnd : (c₀ :: rest₀).Nodup := by simpa using (haff.atom_nodup h₁).1
  have hnd' : (s ++ output :: t).Nodup := by simpa using (haff.atom_nodup h₂).1
  have hdisj₀ := haff.atom_disjoint h₂ h₁ hne
  have hdisj : (s ++ output :: t).Disjoint (c₀ :: rest₀) := by simpa using hdisj₀.1
  have hoo' : output ≠ output' := by simpa using hdisj₀.2
  have hmid := List.nodup_cons.mp (List.nodup_middle.mp hnd')
  have hst : output ∉ s ∧ output ∉ t := by simpa using hmid.1
  have hoi : output ∉ c₀ :: rest₀ := λ h => hdisj hmem h
  -- `newInputs'` replaces `output` with `inputs`.
  have hN' : newInputs' = s ++ c₀ :: (rest₀ ++ t) := by
    rw [hnew, List.map_append, List.flatten_append, flatten_map_ne hst.1, List.map_cons,
      List.flatten_cons, flatten_map_ne hst.2, if_pos rfl]
    simp
  subst hN'
  have hN : ∀ y, y ∈ s ++ c₀ :: (rest₀ ++ t) ↔
      y ∈ c₀ :: rest₀ ∨ (y ∈ s ++ output :: t ∧ y ≠ output) := by
    intro y
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | h | h | h)
      · exact .inr ⟨.inl h, λ e => hst.1 (e ▸ h)⟩
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr ⟨.inr (.inr h), λ e => hst.2 (e ▸ h)⟩
    · rintro ((h | h) | ⟨h | h | h, hne⟩)
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inl h
      · exact absurd h hne
      · exact .inr (.inr (.inr h))
  have hNnd : (s ++ c₀ :: (rest₀ ++ t)).Nodup := by
    have hperm : (s ++ c₀ :: (rest₀ ++ t)).Perm ((c₀ :: rest₀) ++ (s ++ t)) :=
      List.perm_append_comm_assoc s (c₀ :: rest₀) t
    refine hperm.nodup_iff.mpr (hnd.append hmid.2 ?_)
    intro x hx hx'
    refine hdisj ?_ hx
    rcases List.mem_append.mp hx' with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.order k₂) (s ++ output :: t) [output'],
        .async (.order k₁) (c₀ :: rest₀) [output]] := by
    simp [h₁, h₂]
  have hP' : ([.order (s ++ c₀ :: (rest₀ ++ t)).toVector output'] : AtomicProcs Op χ V) =
      [.async (.order (s ++ c₀ :: (rest₀ ++ t)).length) (s ++ c₀ :: (rest₀ ++ t)) [output']] := by
    simp [AtomicProc.order, toList_toVector]
  -- The rewritten graph lags behind on the inputs of the first order.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.order (s ++ c₀ :: (rest₀ ++ t)).toVector output'] ∧
    OrderChans (c₀ :: rest₀) c₀ output chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp only [hP', AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil]
      exact hNnd
    · simp [hP']
    · intro x hx
      simp only [hP', AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil] at hx
      left
      simp only [hP, AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil]
      rcases (hN x).mp hx with h | ⟨h, -⟩
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    · intro x hx
      simp [hP'] at hx
      simp [hP, hx]
  · constructor
    · exact ⟨rfl, rfl, OrderChans.empty⟩
    · rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, hR⟩ hpop
      simp only [hP, AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil] at hx
      have hxi : x ∉ c₀ :: rest₀ := λ h => hx (List.mem_append_right _ h)
      have hxo : x ≠ output := λ h => hx (List.mem_append_left _ (h ▸ hmem))
      obtain ⟨chans₁', h₁', h₂'⟩ :=
        OrderChans.frame_pop (List.mem_cons_self ..) hxi hxo hR hpop
      exact ⟨chans₁', h₁', rfl, rfl, h₂'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, hR⟩
      have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨rfl, rfl, OrderChans.push (ChanMap.pushed outs vals) (ChanMap.pushed_not_mem this) hR⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs₀ outputs₀ inputVals outputVals chans₀' _ _ ⟨rfl, rfl, hR⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget =>
        -- The second order fires: the rewritten order fires on the same values.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, rfl, -, w, restW, rfl, rfl⟩ := hinterp.order_inv
        subst inputs₀
        have htail := pop_eq_tail hnd' hlen₁ hpop
        have hne₀ : ∀ y ∈ s ++ output :: t, chans₀ y ≠ [] := λ y hy h =>
          pushed_ne_nil hy hlen₁ (List.append_eq_nil_iff.mp ((hpop y).symm.trans h)).1
        obtain ⟨vals, hlenv, hpop₁⟩ :=
          pop_exists hNnd (OrderChans.ne_nil hN hdisj hmem hne₀ hR)
        obtain ⟨w', restW', rfl⟩ := List.exists_cons_of_ne_nil (l := vals)
          (λ h => by simp [h] at hlenv)
        -- The rewritten order outputs the same value.
        have hw : w' = w := by
          obtain ⟨-, hother, -, hhead⟩ := id hR
          cases s with
          | nil =>
            have h₁' : (chans₁ c₀).head? = some w' := by rw [hpop₁ c₀]; simp
            have h₂' : (chans₁ c₀).head? = some w := by rw [hhead, hpop output]; simp
            exact Option.some.inj (h₁'.symm.trans h₂')
          | cons x s' =>
            have hx₁ : x ∉ c₀ :: rest₀ := λ h => hdisj (by simp) h
            have hxo : x ≠ output := λ h => hst.1 (by simp [h])
            have h₁' : (chans₁ x).head? = some w' := by rw [hpop₁ x]; simp
            have h₂' : (chans₁ x).head? = some w := by rw [hother x hx₁ hxo, hpop x]; simp
            exact Option.some.inj (h₁'.symm.trans h₂')
        subst w'
        refine ⟨_, _, LocalTauStar.async_list_mem
          (L := ([.order (s ++ c₀ :: (rest₀ ++ t)).toVector output'] : AtomicProcs Op χ V))
          (aop := .order (s ++ c₀ :: (rest₀ ++ t)).length)
          (allInputs := s ++ c₀ :: (rest₀ ++ t)) (allOutputs := [output'])
          (inputs := s ++ c₀ :: (rest₀ ++ t)) (inputVals := w :: restW')
          (outputs := [output']) (outputVals := [w])
          (by simp [AtomicProc.order, toList_toVector])
          (.interp_order rfl hlenv.symm) hlenv rfl hpop₁, by simp, rfl, ?_⟩
        exact OrderChans.push (ChanMap.pushed [output'] [w]) (by simp [Ne.symm hoo'])
          (OrderChans.order₂ (List.mem_cons_self ..) hmem hdisj hN (hne₀ output hmem) htail hR)
      | 1, hget =>
        -- The first order fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, hin, rfl, -, v, restV, rfl, rfl⟩ := hinterp.order_inv
        subst inputs₀
        exact ⟨_, _, .refl, by simp, rfl, OrderChans.order₁ hnd hoi hlen₁ hR hpop⟩
  · rintro L₁ chans₁ ⟨_, rfl, hR⟩
    exact ⟨rfl, OrderChans.eq_empty hR⟩

end Wavelet.Compile.DeadCodeElim
