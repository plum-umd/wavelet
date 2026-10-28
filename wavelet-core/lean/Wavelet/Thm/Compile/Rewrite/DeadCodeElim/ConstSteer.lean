import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstLemmas

/-! `const-steer`: a constant followed by a steer can commute. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ConstLemmas

theorem const_steer_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {flavor : Bool} {decider input output act r : χ} {v : V}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.const v 1) [act] [input]))
  (hne : i₂ ≠ i₁)
  (hr : r ∉ proc.allNames) :
    RuleOK proc [i₂, i₁] [
      .steer flavor decider #v[act] #v[r],
      .const v r #v[output],
    ]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.const v 1) [act] [input], .async (.steer flavor 1) [decider, input] [output]] := by
    simp [h₁, h₂]
  have hP' : ([.steer flavor decider #v[act] #v[r], .const v r #v[output]] : AtomicProcs Op χ V) =
      [.async (.steer flavor 1) [decider, act] [r], .async (.const v 1) [r] [output]] := by
    simp [AtomicProc.steer, AtomicProc.const]
  -- Facts from affineness and freshness
  have hdi : decider ≠ input := by simpa using (haff.atom_nodup h₁).1
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  simp at hdisj
  obtain ⟨⟨had, hai⟩, hio⟩ := hdisj
  have hrd : r ≠ decider := ne_of_fresh_input hr h₁ (by simp)
  have hri : r ≠ input := ne_of_fresh_input hr h₁ (by simp)
  have hro : r ≠ output := ne_of_fresh_output hr h₁ (by simp)
  have hra : r ≠ act := ne_of_fresh_input hr h₂ (by simp)
  -- The activations `X` consumed by the original const are still in `act` after the rewrite;
  -- `input` and `r` are empty after the rewrite; other channels are the same.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.async (.steer flavor 1) [decider, act] [r], .async (.const v 1) [r] [output]] ∧
    (∃ X, chans₁ act = X ++ chans₀ act ∧ X.length = (chans₀ input).length) ∧
    (∀ w ∈ chans₀ input, w = v) ∧
    chans₁ input = [] ∧ chans₁ r = [] ∧
    (∀ y, y ≠ act → y ≠ input → y ≠ r → chans₀ y = chans₁ y), ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP', Ne.symm had, Ne.symm hrd, Ne.symm hra]
    · simp [hP', hro]
    · simp [hP', hP, hr]
    · simp [hP', hP, hr]
  · constructor
    · exact ⟨rfl, hP', ⟨[], by simp, by simp⟩, by simp, rfl, rfl, λ _ _ _ _ => rfl⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x w chans₀' hx₁ hx₂
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hvals, hinp, hrr, heq⟩ hpop
      simp [hP] at hx₁
      simp [hP'] at hx₂
      obtain ⟨hxa, -, hxi⟩ := hx₁
      obtain ⟨-, -, hxr⟩ := hx₂
      obtain ⟨hx₀, h₀⟩ := ChanMap.frame_pop_inv hpop
      obtain ⟨chans₁', hpop₁, hx₁', h₁'⟩ := ChanMap.frame_pop_head
        (chans := chans₁) (x := x) (w := w) (rest := chans₀' x)
        (by rw [← heq x hxa hxi hxr, hx₀])
      refine ⟨chans₁', hpop₁, rfl, rfl, ⟨X, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [h₁' _ (Ne.symm hxa), h₀ _ (Ne.symm hxa), hX]
      · rw [h₀ _ (Ne.symm hxi), hXlen]
      · rw [h₀ _ (Ne.symm hxi)]; exact hvals
      · rw [h₁' _ (Ne.symm hxi), hinp]
      · rw [h₁' _ (Ne.symm hxr), hrr]
      · intro y hya hyi hyr
        by_cases hyx : y = x
        · subst hyx; rw [hx₁']
        · rw [h₁' _ hyx, h₀ _ hyx, heq y hya hyi hyr]
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hvals, hinp, hrr, heq⟩
      have hi : input ∉ outs := λ h => by simpa [hP] using (hx input h).1
      have hr' : r ∉ outs := λ h => by simpa [hP'] using (hx r h).2
      refine ⟨rfl, rfl, ⟨X, by simp [hX], by simp [ChanMap.pushed_not_mem hi, hXlen]⟩,
        ?_, ?_, ?_, ?_⟩
      · simpa [ChanMap.pushed_not_mem hi] using hvals
      · simp [ChanMap.pushed_not_mem hi, hinp]
      · simp [ChanMap.pushed_not_mem hr', hrr]
      · intro y hya hyi hyr
        simp [heq y hya hyi hyr]
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, _⟩ hmem
      simp [hP] at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _
        ⟨rfl, rfl, ⟨X, hX, hXlen⟩, hvals, hinp, hrr, heq⟩ hget hinterp hlen₁ _ hpop
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
        refine ⟨_, _, .refl, ?_, rfl, ⟨X ++ [av], ?_, ?_⟩, ?_, hinp, hrr, ?_⟩
        · simp
        · simp [hX, hpa, Ne.symm hai]
        · simp [h₀ _ (Ne.symm hai), hXlen]
        · intro w hw
          simp [h₀ _ (Ne.symm hai)] at hw
          rcases hw with hw | rfl
          · exact hvals w hw
          · rfl
        · intro y hya hyi hyr
          simp [Ne.symm hyi, h₀ _ hya, heq y hya hyi hyr]
      | 1, hget =>
        -- The steer fires: the rewritten steer reads the decider and the head of `X`,
        -- then the rewritten const fires if the steer passes.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, houts, hovals⟩ := hinterp.steer_inv hlen₁
        have hpd := hpop decider
        have hpi := hpop input
        simp [hdi, Ne.symm hdi] at hpd hpi
        have h₀ : ∀ y, y ≠ decider → y ≠ input → chans₀' y = chans₀ y := λ y hyd hyi => by
          simpa [Ne.symm hyd, Ne.symm hyi] using (hpop y).symm
        have hxv : xv = v := hvals xv (by simp [hpi])
        cases X with
        | nil => simp [hpi] at hXlen
        | cons x₀ X =>
        have hXlen' : X.length = (chans₀' input).length := by simpa [hpi] using hXlen
        have hd₁ : chans₁ decider = dv :: chans₀' decider := by
          rw [← heq decider (Ne.symm had) hdi (Ne.symm hrd), hpd]
        obtain ⟨M₁, hpop₁, hM₁d, hM₁a, hM₁⟩ := ChanMap.pop_two (Ne.symm had) hd₁ hX
        have hstep₁ := LocalTauStar.async_list_mem
          (L := ([.async (.steer flavor 1) [decider, act] [r], .async (.const v 1) [r] [output]] :
            AtomicProcs Op χ V))
          (aop := .steer flavor 1) (allInputs := [decider, act]) (allOutputs := [r])
          (by simp) (AsyncOp.Interp.steer_mk hb) rfl (by split <;> rfl) hpop₁
        by_cases hbf : b = flavor
        · -- The steer passes: the rewritten const fires too.
          simp only [if_pos hbf] at houts hovals hstep₁
          subst houts hovals
          obtain ⟨M₂, hpop₂, hM₂r, hM₂⟩ := ChanMap.pop_one
            (chans := λ y => M₁ y ++ ChanMap.pushed [r] [x₀] y) (x := r) (w := x₀) (rest := [])
            (by simp [hM₁ r hrd hra, hrr])
          have hstep₂ := LocalTauStar.async_list_mem
            (L := ([.async (.steer flavor 1) [decider, act] [r], .async (.const v 1) [r] [output]] :
              AtomicProcs Op χ V))
            (aop := .const v 1) (allInputs := [r]) (allOutputs := [output])
            (outputs := [output]) (outputVals := [v])
            (by simp) (.interp_const rfl) rfl rfl hpop₂
          refine ⟨_, _, hstep₁.trans hstep₂, ?_, rfl, ⟨X, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · simp
          · simp [hM₂ act (Ne.symm hra), hM₁a, hra, h₀ act had hai, hxv]
          · simp [hio, hXlen']
          · intro w hw
            simp [hio] at hw
            exact hvals w (by simp [hpi, hw])
          · simp [hM₂ input (Ne.symm hri), hM₁ input (Ne.symm hdi) (Ne.symm hai), hri,
              hio, hinp]
          · simp [hM₂r, Ne.symm hro]
          · intro y hya hyi hyr
            simp only [hM₂ y hyr, ChanMap.pushed_cons, ChanMap.pushed_nil_left, List.append_nil,
              if_neg (Ne.symm hyr), hxv]
            by_cases hyd : y = decider
            · subst hyd; rw [hM₁d]
            · rw [hM₁ y hyd hya, h₀ y hyd hyi, heq y hya hyi hyr]
        · -- The steer does not pass.
          simp only [if_neg hbf] at houts hovals hstep₁
          subst houts hovals
          refine ⟨_, _, hstep₁, ?_, rfl, ⟨X, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · simp
          · simp [hM₁a, h₀ act had hai]
          · simp [hXlen']
          · intro w hw
            simp at hw
            exact hvals w (by simp [hpi, hw])
          · simp [hM₁ input (Ne.symm hdi) (Ne.symm hai), hinp]
          · simp [hM₁ r hrd hra, hrr]
          · intro y hya hyi hyr
            simp only [ChanMap.pushed_nil_left, List.append_nil]
            by_cases hyd : y = decider
            · subst hyd; rw [hM₁d]
            · rw [hM₁ y hyd hya, h₀ y hyd hyi, heq y hya hyi hyr]
  · rintro L₁ chans₁ ⟨_, rfl, ⟨X, hX, hXlen⟩, -, hinp, hrr, heq⟩
    refine ⟨hP'.symm, ?_⟩
    simp at hXlen
    subst hXlen
    funext y
    by_cases hya : y = act
    · subst hya; simpa using hX
    · by_cases hyi : y = input
      · subst hyi; exact hinp
      · by_cases hyr : y = r
        · subst hyr; exact hrr
        · exact (heq y hya hyi hyr).symm

end Wavelet.Compile.DeadCodeElim
