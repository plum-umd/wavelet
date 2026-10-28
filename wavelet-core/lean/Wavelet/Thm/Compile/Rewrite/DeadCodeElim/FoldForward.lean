import Wavelet.Thm.Compile.MapChans
import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `fold-forward-*`: a forward can be folded into its sender or receiver. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-! Renaming one channel name in a list of names. -/
section Rename

variable [DecidableEq χ]

private theorem map_rename_of_not_mem {l : List χ} {a b : χ} (h : a ∉ l) :
    l.map (λ z => if z = a then b else z) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mem_cons, not_or] at h
    simp [Ne.symm h.1, ih h.2]

private theorem replace_eq_map {l : List χ} {a b : χ} (h : l.Nodup) :
    l.replace a b = l.map (λ z => if z = a then b else z) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at h
    by_cases hx : x = a
    · subst hx
      simp [map_rename_of_not_mem h.1]
    · rw [List.replace_cons, beq_eq_false_iff_ne.mpr (Ne.symm hx)]
      simp [hx, ih h.2]

private theorem vector_toList_replace {xs : Vector χ k} {a b : χ} :
    (xs.replace a b).toList = xs.toList.replace a b := by
  rcases xs with ⟨⟨l⟩, rfl⟩
  simp [Vector.replace]

private theorem nodup_map_rename {l : List χ} {a b : χ} (h : l.Nodup) (hb : b ∉ l) :
    (l.map (λ z => if z = a then b else z)).Nodup := by
  apply h.map_on
  intro x hx y hy hxy
  by_cases hxa : x = a <;> by_cases hya : y = a <;>
    simp only [hxa, hya, if_true, if_false] at hxy
  · exact hxa.trans hya.symm
  · exact absurd (hxy ▸ hy) hb
  · exact absurd (hxy ▸ hx) hb
  · exact hxy

private theorem mem_map_rename {l : List χ} {a b x : χ}
  (h : x ∈ l.map (λ z => if z = a then b else z)) : x ∈ l ∨ x = b := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
  by_cases hza : z = a <;> simp [hza, hz]

/-- Values pushed to `y` along renamed names are the values pushed to `y'`. -/
private theorem pushed_map {names : List χ} {vals : List V} {f : χ → χ} {y y' : χ}
  (h : ∀ z ∈ names, f z = y ↔ z = y') :
    ChanMap.pushed (names.map f) vals y = ChanMap.pushed names vals y' := by
  induction names generalizing vals with
  | nil => simp
  | cons x names ih =>
    cases vals with
    | nil => simp
    | cons v vals =>
      simp only [List.map_cons, ChanMap.pushed_cons, h x List.mem_cons_self,
        ih (λ z hz => h z (List.mem_cons_of_mem _ hz))]

/-- Values pushed to the new name `b` are those pushed to the old name `a`. -/
private theorem pushed_map_rename_new {names : List χ} {vals : List V} {a b : χ}
  (hb : b ∉ names) :
    ChanMap.pushed (names.map (λ z => if z = a then b else z)) vals b =
      ChanMap.pushed names vals a :=
  pushed_map λ z hz => by
    by_cases hza : z = a
    · simp [hza]
    · simp only [hza, if_false, iff_false]
      rintro rfl
      exact hb hz

/-- Nothing is pushed to the old name `a`. -/
private theorem pushed_map_rename_old {names : List χ} {vals : List V} {a b : χ}
  (hab : a ≠ b) :
    ChanMap.pushed (names.map (λ z => if z = a then b else z)) vals a = [] := by
  apply ChanMap.pushed_not_mem
  intro h
  obtain ⟨z, -, hz⟩ := List.mem_map.mp h
  by_cases hza : z = a
  · simp only [hza, if_true] at hz
    exact hab hz.symm
  · simp [hza] at hz

/-- Other names are unchanged. -/
private theorem pushed_map_rename_other {names : List χ} {vals : List V} {a b y : χ}
  (hya : y ≠ a) (hyb : y ≠ b) :
    ChanMap.pushed (names.map (λ z => if z = a then b else z)) vals y =
      ChanMap.pushed names vals y :=
  pushed_map λ z _ => by
    by_cases hza : z = a
    · simp [hza, Ne.symm hya, Ne.symm hyb]
    · simp [hza]

end Rename

/-! Channels after folding a forward `input → output` into its receiver:
the receiver now reads the values in `output` and then those in `input` from `input`. -/
section Receiver

private def RecvChans (input output : χ) (chans₀ chans₁ : ChanMap χ V) : Prop :=
  chans₁ input = chans₀ output ++ chans₀ input ∧ chans₁ output = [] ∧
  ∀ y, y ≠ input → y ≠ output → chans₀ y = chans₁ y

private theorem RecvChans.empty {input output : χ} :
    RecvChans input output (ChanMap.empty : ChanMap χ V) .empty :=
  ⟨rfl, rfl, λ _ _ _ => rfl⟩

private theorem RecvChans.eq_empty {input output : χ} {chans₁ : ChanMap χ V}
  (h : RecvChans input output .empty chans₁) : chans₁ = .empty := by
  funext y
  by_cases hi : y = input
  · subst y; exact h.1
  · by_cases ho : y = output
    · subst y; exact h.2.1
    · exact (h.2.2 y hi ho).symm

/-- The original pops `p` (nothing from `input`), and the rewritten pops `q`,
which reads from `input` what the original reads from `output`. -/
private theorem RecvChans.pop [DecidableEq χ] {input output : χ}
  {chans₀ chans₁ chans₀' : ChanMap χ V} {p q : χ → List V}
  (hio : input ≠ output)
  (h : RecvChans input output chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = p y ++ chans₀' y)
  (hpi : p input = [])
  (hq₁ : q input = p output) (hq₂ : q output = [])
  (hq₃ : ∀ y, y ≠ input → y ≠ output → q y = p y) :
    ∃ chans₁', (∀ y, chans₁ y = q y ++ chans₁' y) ∧
      RecvChans input output chans₀' chans₁' := by
  refine ⟨λ y => if y = input then chans₀' output ++ chans₀' input
    else if y = output then [] else chans₀' y, λ y => ?_,
    by simp, by simp [Ne.symm hio], λ y hi ho => by simp [hi, ho]⟩
  by_cases hi : y = input
  · subst y
    simp [h.1, hpop output, hpop input, hpi, hq₁]
  · by_cases ho : y = output
    · subst y
      simp [hi, h.2.1, hq₂]
    · simp [hi, ho, ← h.2.2 y hi ho, hpop y, hq₃ y hi ho]

/-- Popping the same values (nothing from `input` or `output`) on both sides. -/
private theorem RecvChans.pop_same [DecidableEq χ] {input output : χ}
  {chans₀ chans₁ chans₀' : ChanMap χ V} {p : χ → List V}
  (hio : input ≠ output)
  (h : RecvChans input output chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = p y ++ chans₀' y)
  (hpi : p input = []) (hpo : p output = []) :
    ∃ chans₁', (∀ y, chans₁ y = p y ++ chans₁' y) ∧
      RecvChans input output chans₀' chans₁' :=
  h.pop hio hpop hpi (by rw [hpi, hpo]) hpo (λ _ _ _ => rfl)

/-- Pushing the same values (nothing to `output`) on both sides. -/
private theorem RecvChans.push {input output : χ} {chans₀ chans₁ : ChanMap χ V}
  {p : χ → List V}
  (h : RecvChans input output chans₀ chans₁) (hpo : p output = []) :
    RecvChans input output (λ y => chans₀ y ++ p y) (λ y => chans₁ y ++ p y) :=
  ⟨by simp [h.1, hpo], by simp [h.2.1, hpo], λ y hi ho => by simp [h.2.2 y hi ho]⟩

/-- The forward moves a value from `input` to `output`. -/
private theorem RecvChans.fwd [DecidableEq χ] {input output : χ} {v : V}
  {chans₀ chans₁ chans₀' : ChanMap χ V}
  (hio : input ≠ output)
  (h : RecvChans input output chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed [input] [v] y ++ chans₀' y) :
    RecvChans input output (λ y => chans₀' y ++ ChanMap.pushed [output] [v] y) chans₁ := by
  have h₁ := hpop input
  have h₂ := hpop output
  simp [hio] at h₁ h₂
  refine ⟨by simp [h.1, h₁, h₂, Ne.symm hio], h.2.1, λ y hi ho => ?_⟩
  have := hpop y
  simp [Ne.symm hi, Ne.symm ho] at this ⊢
  rw [← this, h.2.2 y hi ho]

end Receiver

/-! Channels after folding a forward `input → output` into its sender:
the sender now writes to `output` directly, so `output` may be ahead. -/
section Sender

private def SendChans (input output : χ) (chans₀ chans₁ : ChanMap χ V) : Prop :=
  chans₁ output = chans₀ output ++ chans₀ input ∧ chans₁ input = [] ∧
  ∀ y, y ≠ input → y ≠ output → chans₀ y = chans₁ y

private theorem SendChans.empty {input output : χ} :
    SendChans input output (ChanMap.empty : ChanMap χ V) .empty :=
  ⟨rfl, rfl, λ _ _ _ => rfl⟩

private theorem SendChans.eq_empty {input output : χ} {chans₁ : ChanMap χ V}
  (h : SendChans input output .empty chans₁) : chans₁ = .empty := by
  funext y
  by_cases ho : y = output
  · subst y; exact h.1
  · by_cases hi : y = input
    · subst y; exact h.2.1
    · exact (h.2.2 y hi ho).symm

/-- Popping the same values (nothing from `input`) on both sides. -/
private theorem SendChans.pop [DecidableEq χ] {input output : χ}
  {chans₀ chans₁ chans₀' : ChanMap χ V} {p : χ → List V}
  (hio : input ≠ output)
  (h : SendChans input output chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = p y ++ chans₀' y) (hpi : p input = []) :
    ∃ chans₁', (∀ y, chans₁ y = p y ++ chans₁' y) ∧
      SendChans input output chans₀' chans₁' := by
  refine ⟨λ y => if y = output then chans₀' output ++ chans₀' input
    else if y = input then [] else chans₀' y, λ y => ?_,
    by simp, by simp [hio], λ y hi ho => by simp [hi, ho]⟩
  by_cases ho : y = output
  · subst y
    simp [h.1, hpop output, hpop input, hpi]
  · by_cases hi : y = input
    · subst y
      simp [ho, h.2.1, hpi]
    · simp [hi, ho, ← h.2.2 y hi ho, hpop y]

/-- The original pushes `p₀` (nothing to `output`), and the rewritten pushes `p₁`,
which writes to `output` what the original writes to `input`. -/
private theorem SendChans.push {input output : χ} {chans₀ chans₁ : ChanMap χ V}
  {p₀ p₁ : χ → List V}
  (h : SendChans input output chans₀ chans₁)
  (hpo : p₀ output = []) (hq₁ : p₁ output = p₀ input) (hq₂ : p₁ input = [])
  (hq₃ : ∀ y, y ≠ input → y ≠ output → p₁ y = p₀ y) :
    SendChans input output (λ y => chans₀ y ++ p₀ y) (λ y => chans₁ y ++ p₁ y) :=
  ⟨by simp [h.1, hpo, hq₁], by simp [h.2.1, hq₂],
    λ y hi ho => by simp [h.2.2 y hi ho, hq₃ y hi ho]⟩

/-- The forward moves a value from `input` to `output`. -/
private theorem SendChans.fwd [DecidableEq χ] {input output : χ} {v : V}
  {chans₀ chans₁ chans₀' : ChanMap χ V}
  (hio : input ≠ output)
  (h : SendChans input output chans₀ chans₁)
  (hpop : ∀ y, chans₀ y = ChanMap.pushed [input] [v] y ++ chans₀' y) :
    SendChans input output (λ y => chans₀' y ++ ChanMap.pushed [output] [v] y) chans₁ := by
  have h₁ := hpop input
  have h₂ := hpop output
  simp [hio] at h₁ h₂
  refine ⟨by simp [h.1, h₁, h₂, Ne.symm hio], h.2.1, λ y hi ho => ?_⟩
  have := hpop y
  simp [Ne.symm hi, Ne.symm ho] at this ⊢
  rw [← this, h.2.2 y hi ho]

end Sender

theorem fold_forward_aop_receiver_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {input output : χ} {aop : AsyncOp V} {inputs' outputs' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.forward 1) [input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async aop inputs' outputs'))
  (hne : i₂ ≠ i₁)
  (hmem : output ∈ inputs') :
    RuleOK proc [i₂, i₁] [.async aop (inputs'.replace output input) outputs']
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async aop inputs' outputs', .async (.forward 1) [input] [output]] := by
    simp [h₁, h₂]
  -- Facts from affineness
  have hnodup := haff.atom_nodup h₂
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  have hin : input ∉ inputs' := λ h => hdisj.1 h List.mem_cons_self
  have hout : output ∉ outputs' := λ h => hdisj.2 h List.mem_cons_self
  have hio : input ≠ output := λ h => hin (h ▸ hmem)
  have hrepl : inputs'.replace output input =
      inputs'.map (λ z => if z = output then input else z) := replace_eq_map hnodup.1
  -- The receiver reads the values in `output` and then those in `input` from `input`.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    ∃ aop₀, L₀ = [.async aop₀ inputs' outputs', .async (.forward 1) [input] [output]] ∧
      L₁ = [.async aop₀ (inputs'.replace output input) outputs'] ∧
      RecvChans input output chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simpa [hrepl] using nodup_map_rename hnodup.1 hin
    · simpa using hnodup.2
    · intro x hx
      simp only [AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.append_nil, hrepl] at hx
      rcases mem_map_rename hx with hx | rfl <;> simp [hP, hx]
    · intro x hx
      simp at hx
      simp [hP, hx]
  · constructor
    · exact ⟨aop, hP, rfl, .empty⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨aop₀, rfl, rfl, hrel⟩ hpop
      simp [hP] at hx
      have hxo : x ≠ output := λ h => hx.1 (h ▸ hmem)
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop_same hio hpop
        (by simp [Ne.symm hx.2]) (by simp [Ne.symm hxo])
      exact ⟨chans₁', hpop₁, aop₀, rfl, rfl, hrel'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨aop₀, rfl, rfl, hrel⟩
      have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨aop₀, rfl, rfl, hrel.push (ChanMap.pushed_not_mem this)⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨aop₀, rfl, rfl, _⟩ hmem
      simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop₁ aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨aop₀, rfl, rfl, hrel⟩ hget hinterp
        hlen₁ hlen₂ hpop
      match i, hget with
      | 0, hget =>
        -- The receiver fires: the rewritten one reads the values of `output` from `input`.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        have hin' : input ∉ inputs := λ h => hin (hinterp.input_sublist.subset h)
        have hout' : output ∉ outputs := λ h => hout (hinterp.output_sublist.subset h)
        have hinterp' := async_op_interp_map_chans (λ z => if z = output then input else z) hinterp
        rw [← hrepl, map_rename_of_not_mem hout, map_rename_of_not_mem hout'] at hinterp'
        obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hio hpop (ChanMap.pushed_not_mem hin')
          (pushed_map_rename_new hin') (pushed_map_rename_old (Ne.symm hio))
          (λ _ hi ho => pushed_map_rename_other ho hi)
        refine ⟨_, _, LocalTauStar.async_list (i := 0) rfl hinterp'
          (by simpa using hlen₁) hlen₂ hpop₁,
          aop', by simp, by simp, hrel'.push (ChanMap.pushed_not_mem hout')⟩
      | 1, hget =>
        -- The forward fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, v, rfl, rfl⟩ := hinterp.forward_inv hlen₁
        exact ⟨_, _, .refl, aop₀, by simp, rfl, hrel.fwd hio hpop⟩
  · rintro L₁ chans₁ ⟨aop₀, hL₀, rfl, hrel⟩
    rw [hP] at hL₀
    simp only [List.cons.injEq, AtomicProc.async.injEq, and_true] at hL₀
    subst hL₀
    exact ⟨rfl, hrel.eq_empty⟩

theorem fold_forward_aop_sender_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {input output : χ} {aop : AsyncOp V} {inputs' outputs' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.forward 1) [input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async aop inputs' outputs'))
  (hne : i₂ ≠ i₁)
  (hnmem : output ∉ inputs')
  (hmem : input ∈ outputs') :
    RuleOK proc [i₂, i₁] [.async aop inputs' (outputs'.replace input output)]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async aop inputs' outputs', .async (.forward 1) [input] [output]] := by
    simp [h₁, h₂]
  -- Facts from affineness
  have hnodup := haff.atom_nodup h₂
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  have hin : input ∉ inputs' := λ h => hdisj.1 h List.mem_cons_self
  have hout : output ∉ outputs' := λ h => hdisj.2 h List.mem_cons_self
  have hio : input ≠ output := λ h => hout (h ▸ hmem)
  have hrepl : outputs'.replace input output =
      outputs'.map (λ z => if z = input then output else z) := replace_eq_map hnodup.2
  -- The sender writes to `output` directly, so `output` may be ahead.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    ∃ aop₀, L₀ = [.async aop₀ inputs' outputs', .async (.forward 1) [input] [output]] ∧
      L₁ = [.async aop₀ inputs' (outputs'.replace input output)] ∧
      SendChans input output chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simpa using hnodup.1
    · simpa [hrepl] using nodup_map_rename hnodup.2 hout
    · intro x hx
      simp at hx
      simp [hP, hx]
    · intro x hx
      simp only [AtomicProcs.outputNames_cons, AtomicProc.outputs_async,
        AtomicProcs.outputNames_nil, List.append_nil, hrepl] at hx
      rcases mem_map_rename hx with hx | rfl <;> simp [hP, hx]
  · constructor
    · exact ⟨aop, hP, rfl, .empty⟩
    · -- `x` is read by the environment or the rest of the graph, and may be `output`.
      rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨aop₀, rfl, rfl, hrel⟩ hpop
      simp [hP] at hx
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hio hpop (by simp [Ne.symm hx.2])
      exact ⟨chans₁', hpop₁, aop₀, rfl, rfl, hrel'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨aop₀, rfl, rfl, hrel⟩
      have hi : input ∉ outs := λ h => by simpa [hP, hmem] using (hx input h).1
      have ho : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨aop₀, rfl, rfl, hrel.push (ChanMap.pushed_not_mem ho)
        (by rw [ChanMap.pushed_not_mem ho, ChanMap.pushed_not_mem hi])
        (ChanMap.pushed_not_mem hi) (λ _ _ _ => rfl)⟩
    · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨aop₀, rfl, rfl, _⟩ hmem
      simp at hmem
    · rintro L₀ chans₀ L₁ chans₁ i aop₁ aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨aop₀, rfl, rfl, hrel⟩ hget hinterp
        hlen₁ hlen₂ hpop
      match i, hget with
      | 0, hget =>
        -- The sender fires: the rewritten one writes to `output` instead of `input`.
        simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        have hin' : input ∉ inputs := λ h => hin (hinterp.input_sublist.subset h)
        have hout' : output ∉ outputs := λ h => hout (hinterp.output_sublist.subset h)
        have hinterp' := async_op_interp_map_chans (λ z => if z = input then output else z) hinterp
        rw [← hrepl, map_rename_of_not_mem hin, map_rename_of_not_mem hin'] at hinterp'
        obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hio hpop (ChanMap.pushed_not_mem hin')
        refine ⟨_, _, LocalTauStar.async_list (i := 0) rfl hinterp'
          hlen₁ (by simpa using hlen₂) hpop₁,
          aop', by simp, by simp, hrel'.push (ChanMap.pushed_not_mem hout')
          (pushed_map_rename_new hout') (pushed_map_rename_old hio)
          (λ _ hi ho => pushed_map_rename_other hi ho)⟩
      | 1, hget =>
        -- The forward fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, v, rfl, rfl⟩ := hinterp.forward_inv hlen₁
        exact ⟨_, _, .refl, aop₀, by simp, rfl, hrel.fwd hio hpop⟩
  · rintro L₁ chans₁ ⟨aop₀, hL₀, rfl, hrel⟩
    rw [hP] at hL₀
    simp only [List.cons.injEq, AtomicProc.async.injEq, and_true] at hL₀
    subst hL₀
    exact ⟨rfl, hrel.eq_empty⟩

theorem fold_forward_op_receiver_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {input output : χ} {o : Op} {inputs' : Vector χ (Arity.ι o)} {outputs' : Vector χ (Arity.ω o)}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.forward 1) [input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.op o inputs' outputs'))
  (hne : i₂ ≠ i₁)
  (hmem : output ∈ inputs') :
    RuleOK proc [i₂, i₁] [.op o (inputs'.replace output input) outputs']
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.op o inputs' outputs', .async (.forward 1) [input] [output]] := by
    simp [h₁, h₂]
  -- Facts from affineness
  have hnodup : inputs'.toList.Nodup ∧ outputs'.toList.Nodup := haff.atom_nodup h₂
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  have hin : input ∉ inputs'.toList := λ h => hdisj.1 h List.mem_cons_self
  have hout : output ∉ outputs'.toList := λ h => hdisj.2 h List.mem_cons_self
  have hio : input ≠ output := λ h => hin (h ▸ Vector.mem_toList_iff.mpr hmem)
  have hrepl : (inputs'.replace output input).toList =
      inputs'.toList.map (λ z => if z = output then input else z) := by
    rw [vector_toList_replace, replace_eq_map hnodup.1]
  -- The receiver reads the values in `output` and then those in `input` from `input`.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.op o (inputs'.replace output input) outputs'] ∧
    RecvChans input output chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simpa [hrepl] using nodup_map_rename hnodup.1 hin
    · simpa using hnodup.2
    · intro x hx
      simp only [AtomicProcs.inputNames_cons, AtomicProc.inputs_op,
        AtomicProcs.inputNames_nil, List.append_nil, hrepl] at hx
      rcases mem_map_rename hx with hx | rfl <;> simp [hP, hx]
    · intro x hx
      simp at hx
      simp [hP, hx]
  · constructor
    · exact ⟨rfl, rfl, .empty⟩
    · -- `x` is read by the environment or the rest of the graph.
      rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, hrel⟩ hpop
      simp [hP] at hx
      have hxo : x ≠ output := λ h => hx.1 (h ▸ hmem)
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop_same hio hpop
        (by simp [Ne.symm hx.2]) (by simp [Ne.symm hxo])
      exact ⟨chans₁', hpop₁, rfl, rfl, hrel'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, hrel⟩
      have : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨rfl, rfl, hrel.push (ChanMap.pushed_not_mem this)⟩
    · -- The receiver fires: the rewritten one reads the values of `output` from `input`.
      rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, hrel⟩ hmem' hpop
      rw [hP] at hmem'
      simp at hmem'
      obtain ⟨rfl, hi, ho⟩ := hmem'
      obtain rfl := eq_of_heq hi
      obtain rfl := eq_of_heq ho
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hio hpop (ChanMap.pushed_not_mem hin)
        (pushed_map_rename_new hin) (pushed_map_rename_old (Ne.symm hio))
        (λ _ hi ho => pushed_map_rename_other ho hi)
      refine ⟨_, _, chans₁', List.mem_singleton_self _, ?_, rfl, rfl,
        hrel'.push (ChanMap.pushed_not_mem hout)⟩
      rw [hrepl]
      exact hpop₁
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨rfl, rfl, hrel⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget => simp at hget
      | 1, hget =>
        -- The forward fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, v, rfl, rfl⟩ := hinterp.forward_inv hlen₁
        exact ⟨_, _, .refl, by simp, rfl, hrel.fwd hio hpop⟩
  · rintro L₁ chans₁ ⟨_, rfl, hrel⟩
    exact ⟨rfl, hrel.eq_empty⟩

theorem fold_forward_op_sender_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {input output : χ} {o : Op} {inputs' : Vector χ (Arity.ι o)} {outputs' : Vector χ (Arity.ω o)}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.forward 1) [input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.op o inputs' outputs'))
  (hne : i₂ ≠ i₁)
  (hnmem : output ∉ inputs')
  (hmem : input ∈ outputs') :
    RuleOK proc [i₂, i₁] [.op o inputs' (outputs'.replace input output)]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.op o inputs' outputs', .async (.forward 1) [input] [output]] := by
    simp [h₁, h₂]
  -- Facts from affineness
  have hnodup : inputs'.toList.Nodup ∧ outputs'.toList.Nodup := haff.atom_nodup h₂
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  have hin : input ∉ inputs'.toList := λ h => hdisj.1 h List.mem_cons_self
  have hout : output ∉ outputs'.toList := λ h => hdisj.2 h List.mem_cons_self
  have hio : input ≠ output := λ h => hout (h ▸ Vector.mem_toList_iff.mpr hmem)
  have hrepl : (outputs'.replace input output).toList =
      outputs'.toList.map (λ z => if z = input then output else z) := by
    rw [vector_toList_replace, replace_eq_map hnodup.2]
  -- The sender writes to `output` directly, so `output` may be ahead.
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₂, i₁] ∧
    L₁ = [.op o inputs' (outputs'.replace input output)] ∧
    SendChans input output chans₀ chans₁, ?_, ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simpa using hnodup.1
    · simpa [hrepl] using nodup_map_rename hnodup.2 hout
    · intro x hx
      simp at hx
      simp [hP, hx]
    · intro x hx
      simp only [AtomicProcs.outputNames_cons, AtomicProc.outputs_op,
        AtomicProcs.outputNames_nil, List.append_nil, hrepl] at hx
      rcases mem_map_rename hx with hx | rfl <;> simp [hP, hx]
  · constructor
    · exact ⟨rfl, rfl, .empty⟩
    · -- `x` is read by the environment or the rest of the graph, and may be `output`.
      rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx _ ⟨rfl, rfl, hrel⟩ hpop
      simp [hP] at hx
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hio hpop (by simp [Ne.symm hx.2])
      exact ⟨chans₁', hpop₁, rfl, rfl, hrel'⟩
    · rintro L₀ chans₀ L₁ chans₁ outs vals _ hx _ _ ⟨rfl, rfl, hrel⟩
      have hi : input ∉ outs := λ h => by simpa [hP, hmem] using (hx input h).1
      have ho : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
      exact ⟨rfl, rfl, hrel.push (ChanMap.pushed_not_mem ho)
        (by rw [ChanMap.pushed_not_mem ho, ChanMap.pushed_not_mem hi])
        (ChanMap.pushed_not_mem hi) (λ _ _ _ => rfl)⟩
    · -- The sender fires: the rewritten one writes to `output` instead of `input`.
      rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
        _ _ ⟨rfl, rfl, hrel⟩ hmem' hpop
      rw [hP] at hmem'
      simp at hmem'
      obtain ⟨rfl, hi, ho⟩ := hmem'
      obtain rfl := eq_of_heq hi
      obtain rfl := eq_of_heq ho
      obtain ⟨chans₁', hpop₁, hrel'⟩ := hrel.pop hio hpop (ChanMap.pushed_not_mem hin)
      refine ⟨_, _, chans₁', List.mem_singleton_self _, hpop₁, rfl, rfl, ?_⟩
      rw [hrepl]
      exact hrel'.push (ChanMap.pushed_not_mem hout) (pushed_map_rename_new hout)
        (pushed_map_rename_old hio) (λ _ hi ho => pushed_map_rename_other hi ho)
    · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
        inputs outputs inputVals outputVals chans₀' _ _ ⟨rfl, rfl, hrel⟩ hget hinterp
        hlen₁ _ hpop
      rw [hP] at hget ⊢
      match i, hget with
      | 0, hget => simp at hget
      | 1, hget =>
        -- The forward fires: nothing to do on the rewritten side.
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          AtomicProc.async.injEq] at hget
        obtain ⟨rfl, rfl, rfl⟩ := hget
        obtain ⟨rfl, rfl, rfl, v, rfl, rfl⟩ := hinterp.forward_inv hlen₁
        exact ⟨_, _, .refl, by simp, rfl, hrel.fwd hio hpop⟩
  · rintro L₁ chans₁ ⟨_, rfl, hrel⟩
    exact ⟨rfl, hrel.eq_empty⟩

end Wavelet.Compile.DeadCodeElim
