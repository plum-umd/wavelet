import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ParLemmas

/-! `par-steer-steer`: two parallel steers with the same decider and input can be combined. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow ParLemmas

/-- Outputs of a steer on the given deciders and inputs. -/
private def steerOut [InterpConsts V] (flavor : Bool) (ds xs : List V) : List V :=
  (ds.zip xs).filterMap λ p => if InterpConsts.toBool p.1 = some flavor then some p.2 else none

@[simp]
private theorem steerOut_nil [InterpConsts V] {flavor : Bool} {xs : List V} :
    steerOut flavor [] xs = [] := rfl

private theorem steerOut_cons [InterpConsts V] {flavor : Bool} {dv xv : V} {ds xs : List V} :
    steerOut flavor (dv :: ds) (xv :: xs) =
      (if InterpConsts.toBool dv = some flavor then [xv] else []) ++ steerOut flavor ds xs := by
  by_cases h : InterpConsts.toBool dv = some flavor <;> simp [steerOut, h]

private theorem steerOut_snoc [InterpConsts V] {flavor : Bool} {dv xv : V} {ds xs : List V}
  (hlen : ds.length = xs.length) :
    steerOut flavor (ds ++ [dv]) (xs ++ [xv]) =
      steerOut flavor ds xs ++ (if InterpConsts.toBool dv = some flavor then [xv] else []) := by
  by_cases h : InterpConsts.toBool dv = some flavor <;>
    simp [steerOut, List.zip_append hlen, h]

/-- A unary sink fires. -/
private theorem sink_tau [Arity Op] [DecidableEq χ] [InterpConsts V]
  {L : AtomicProcs Op χ V} {chans : ChanMap χ V} {a : χ} {v : V} {rest : List V}
  (hmem : .async (.sink 1) [a] [] ∈ L) (ha : chans a = v :: rest) :
    LocalTauStar L chans L (λ y => if y = a then rest else chans y) := by
  have := LocalTauStar.async_list_mem (L := L) (chans := chans)
    (chans' := λ y => if y = a then rest else chans y)
    (aop := .sink 1) (allInputs := [a]) (allOutputs := [])
    (inputs := [a]) (inputVals := [v]) (outputs := []) (outputVals := [])
    hmem (.interp_sink rfl) rfl rfl (by
      intro y
      by_cases hy : y = a
      · subst hy; simp [ha]
      · simp [hy, Ne.symm hy])
  exact this.eq_rhs rfl (by funext y; simp)

/-- The rewritten steer fires, followed by the fork of its output (if it passes). -/
private theorem steer_fork_tau [Arity Op] [DecidableEq χ] [InterpConsts V]
  {L : AtomicProcs Op χ V} {chans : ChanMap χ V}
  {flavor b : Bool} {d x r o o₂ : χ} {dv xv : V} {Td Tx : List V}
  (hsteer : .async (.steer flavor 1) [d, x] [r] ∈ L)
  (hfork : .async (.fork 2) [r] [o, o₂] ∈ L)
  (hdx : d ≠ x) (hrd : r ≠ d) (hrx : r ≠ x) (hro : r ≠ o) (hro₂ : r ≠ o₂)
  (hod : o ≠ d) (hox : o ≠ x) (ho₂d : o₂ ≠ d) (ho₂x : o₂ ≠ x) (hoo₂ : o ≠ o₂)
  (hd : chans d = dv :: Td) (hx : chans x = xv :: Tx) (hr : chans r = [])
  (hb : InterpConsts.toBool dv = some b) (hclone : InterpConsts.isClonable xv) :
    ∃ chans', LocalTauStar L chans L chans' ∧
      chans' d = Td ∧ chans' x = Tx ∧ chans' r = [] ∧
      chans' o = chans o ++ (if b = flavor then [xv] else []) ∧
      chans' o₂ = chans o₂ ++ (if b = flavor then [xv] else []) ∧
      ∀ y, y ≠ d → y ≠ x → y ≠ o → y ≠ o₂ → chans' y = chans y := by
  -- Pop the decider and the input
  have hpop : ∀ y, chans y = ChanMap.pushed [d, x] [dv, xv] y ++
      (λ y => if y = d then Td else if y = x then Tx else chans y) y := by
    intro y
    by_cases hyd : y = d
    · subst hyd; simp [hd, Ne.symm hdx]
    · by_cases hyx : y = x
      · subst hyx; simp [hx, hdx, hyd]
      · simp [hyd, hyx, Ne.symm hyd, Ne.symm hyx]
  by_cases hbf : b = flavor
  · have hstep₁ := LocalTauStar.async_list_mem (L := L) (chans := chans)
      (chans' := λ y => if y = d then Td else if y = x then Tx else chans y)
      (aop := .steer flavor 1) (allInputs := [d, x]) (allOutputs := [r])
      (inputs := [d, x]) (inputVals := [dv, xv]) (outputs := [r]) (outputVals := [xv])
      hsteer (.interp_steer_true rfl rfl hb hbf) rfl rfl hpop
    have hstep₂ := LocalTauStar.async_list_mem (L := L)
      (chans := λ y => (if y = d then Td else if y = x then Tx else chans y) ++
        ChanMap.pushed [r] [xv] y)
      (chans' := λ y => if y = d then Td else if y = x then Tx else chans y)
      (aop := .fork 2) (allInputs := [r]) (allOutputs := [o, o₂])
      (inputs := [r]) (inputVals := [xv]) (outputs := [o, o₂]) (outputVals := [xv, xv])
      hfork (.interp_fork rfl hclone) rfl rfl (by
        intro y
        by_cases hy : y = r
        · subst hy; simp [hrd, hrx, hr]
        · simp [Ne.symm hy])
    refine ⟨_, hstep₁.trans hstep₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hod, ho₂d]
    · simp [hox, ho₂x, hdx.symm]
    · simp [hrd, hrx, hr, Ne.symm hro, Ne.symm hro₂]
    · simp [hod, hox, hbf, Ne.symm hoo₂]
    · simp [ho₂d, ho₂x, hbf, hoo₂]
    · intro y hyd hyx hyo hyo₂
      simp [hyd, hyx, Ne.symm hyo, Ne.symm hyo₂]
  · have hstep := LocalTauStar.async_list_mem (L := L) (chans := chans)
      (chans' := λ y => if y = d then Td else if y = x then Tx else chans y)
      (aop := .steer flavor 1) (allInputs := [d, x]) (allOutputs := [r])
      (inputs := [d, x]) (inputVals := [dv, xv]) (outputs := []) (outputVals := [])
      hsteer (.interp_steer_false (inputs := [x]) (outputs := [r]) rfl rfl hb hbf) rfl rfl hpop
    refine ⟨_, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [hdx.symm]
    · simp [hrd, hrx, hr]
    · simp [hod, hox, hbf]
    · simp [ho₂d, ho₂x, hbf]
    · intro y hyd hyx _ _
      simp [hyd, hyx]

theorem par_steer_steer_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {flavor : Bool} {decider input output input' decider'' input'' output'' r : χ}
  {k : Nat} {outputs' : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.steer flavor 1) [decider, input] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork k) [input'] outputs'))
  (h₃ : proc.atoms[i₃]? = some (.async (.steer flavor 1) [decider'', input''] [output'']))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hlen : outputs'.length = k)
  (hfork₁ : SameFork proc.atoms decider decider'')
  (hfork₂ : SameFork proc.atoms input input'')
  (hr : r ∉ proc.allNames) :
    RuleOK proc [i₃, i₂, i₁] [
      .async (.fork k) [input'] outputs',
      .steer flavor decider #v[input] #v[r],
      .sink #v[decider''],
      .sink #v[input''],
      .fork r #v[output, output''],
    ]
  := by
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] = [
      .async (.steer flavor 1) [decider'', input''] [output''],
      .async (.fork k) [input'] outputs',
      .async (.steer flavor 1) [decider, input] [output]] := by
    simp [h₁, h₂, h₃]
  have hP' : ([
      .async (.fork k) [input'] outputs',
      .steer flavor decider #v[input] #v[r],
      .sink #v[decider''],
      .sink #v[input''],
      .fork r #v[output, output''],
    ] : AtomicProcs Op χ V) = [
      .async (.fork k) [input'] outputs',
      .async (.steer flavor 1) [decider, input] [r],
      .async (.sink 1) [decider''] [],
      .async (.sink 1) [input''] [],
      .async (.fork 2) [r] [output, output'']] := by
    simp [AtomicProc.steer, AtomicProc.sink, AtomicProc.fork]
  rw [hP']
  -- Facts from affineness
  have hdi : decider ≠ input := by simpa using (haff.atom_nodup h₁).1
  have hdi₂ : decider'' ≠ input'' := by simpa using (haff.atom_nodup h₃).1
  have hnd' : outputs'.Nodup := (haff.atom_nodup h₂).2
  have hdisj₃₁ := haff.atom_disjoint h₃ h₁ hne₃₁
  have hdisj₂₁ := haff.atom_disjoint h₂ h₁ hne₂₁
  have hdisj₃₂ := haff.atom_disjoint h₃ h₂ hne₃₂
  simp at hdisj₃₁ hdisj₂₁ hdisj₃₂
  obtain ⟨⟨⟨hdd₂, hdi₂'⟩, hid₂, hii₂⟩, hoo₂⟩ := hdisj₃₁
  obtain ⟨⟨hi'd, hi'i⟩, hoouts⟩ := hdisj₂₁
  obtain ⟨⟨hi'd₂, hi'i₂⟩, ho₂outs⟩ := hdisj₃₂
  -- The copies are fork outputs, so not outputs of the steers
  have hnf₁ : ∀ k ins outs, (AtomicProc.async (.steer flavor 1) [decider, input] [output] :
      AtomicProc Op χ V) ≠ .async (.fork k) ins outs := by
    intro _ _ _ h; cases h
  have hnf₃ : ∀ k ins outs, (AtomicProc.async (.steer flavor 1) [decider'', input''] [output''] :
      AtomicProc Op χ V) ≠ .async (.fork k) ins outs := by
    intro _ _ _ h; cases h
  have hod : output ≠ decider := by
    have := SameFork.not_mem_outputs haff hfork₁ h₁ hnf₁; simp at this; exact Ne.symm this
  have hod₂ : output ≠ decider'' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₁) h₁ hnf₁
    simp at this; exact Ne.symm this
  have hoi : output ≠ input := by
    have := SameFork.not_mem_outputs haff hfork₂ h₁ hnf₁; simp at this; exact Ne.symm this
  have hoi₂ : output ≠ input'' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₂) h₁ hnf₁
    simp at this; exact Ne.symm this
  have ho₂d : output'' ≠ decider := by
    have := SameFork.not_mem_outputs haff hfork₁ h₃ hnf₃; simp at this; exact Ne.symm this
  have ho₂d₂ : output'' ≠ decider'' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₁) h₃ hnf₃
    simp at this; exact Ne.symm this
  have ho₂i : output'' ≠ input := by
    have := SameFork.not_mem_outputs haff hfork₂ h₃ hnf₃; simp at this; exact Ne.symm this
  have ho₂i₂ : output'' ≠ input'' := by
    have := SameFork.not_mem_outputs haff (SameFork.symm hfork₂) h₃ hnf₃
    simp at this; exact Ne.symm this
  -- `r` is fresh
  have hrne : ∀ {x}, x ∈ proc.allNames → r ≠ x := λ hx h => hr (h ▸ hx)
  have hrd : r ≠ decider := hrne (Proc.mem_allNames_of_input h₁ (by simp))
  have hri : r ≠ input := hrne (Proc.mem_allNames_of_input h₁ (by simp))
  have hro : r ≠ output := hrne (Proc.mem_allNames_of_output h₁ (by simp))
  have hrd₂ : r ≠ decider'' := hrne (Proc.mem_allNames_of_input h₃ (by simp))
  have hri₂ : r ≠ input'' := hrne (Proc.mem_allNames_of_input h₃ (by simp))
  have hro₂ : r ≠ output'' := hrne (Proc.mem_allNames_of_output h₃ (by simp))
  have hri' : r ≠ input' := hrne (Proc.mem_allNames_of_input h₂ (by simp))
  have hrouts : r ∉ outputs' := λ h => hr (Proc.mem_allNames_of_output h₂ h)
  -- The rewritten steer runs as far as the faster original steer: `A`/`B` (resp. `A₂`/`B₂`)
  -- are the deciders/inputs it has consumed ahead of `steer₁` (resp. `steer₂`), and the
  -- corresponding passed values are pending in `output` (resp. `output''`).
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hne₃₂, hne₃₁, hne₂₁]
  · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1,
      (List.getElem?_eq_some_iff.mp h₃).1]
  · simp [hi'd, hi'i, hi'd₂, hi'i₂, Ne.symm hri', hdi, hdd₂, hdi₂', Ne.symm hrd, hid₂, hii₂,
      Ne.symm hri, hdi₂, Ne.symm hrd₂, Ne.symm hri₂]
  · simp [List.nodup_append, hnd', hro, hro₂, hoo₂]
    intro a ha
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> contradiction
  · rw [hP]
    simp [hr]
  · rw [hP]
    simp
    rintro x (hx | rfl | rfl | rfl)
    · exact .inl (.inr (.inl hx))
    · exact .inr hr
    · exact .inl (.inr (.inr rfl))
    · exact .inl (.inl rfl)
  generalize hPn : ([.async (.fork k) [input'] outputs',
    .async (.steer flavor 1) [decider, input] [r],
    .async (.sink 1) [decider''] [],
    .async (.sink 1) [input''] [],
    .async (.fork 2) [r] [output, output'']] : AtomicProcs Op χ V) = Pn
  have hmemF : (.async (.fork k) [input'] outputs' : AtomicProc Op χ V) ∈ Pn := by
    rw [← hPn]; simp
  have hmemS : (.async (.steer flavor 1) [decider, input] [r] : AtomicProc Op χ V) ∈ Pn := by
    rw [← hPn]; simp
  have hmemSd : (.async (.sink 1) [decider''] [] : AtomicProc Op χ V) ∈ Pn := by
    rw [← hPn]; simp
  have hmemSi : (.async (.sink 1) [input''] [] : AtomicProc Op χ V) ∈ Pn := by
    rw [← hPn]; simp
  have hmemF₂ : (.async (.fork 2) [r] [output, output''] : AtomicProc Op χ V) ∈ Pn := by
    rw [← hPn]; simp
  have hrin : r ∈ AtomicProcs.inputNames Pn := by rw [← hPn]; simp
  have hrout : r ∈ AtomicProcs.outputNames Pn := by rw [← hPn]; simp
  -- The rewritten steer runs as far as the faster original steer: `A`/`B` (resp. `A₂`/`B₂`)
  -- are the deciders/inputs it has consumed ahead of `steer₁` (resp. `steer₂`), and the
  -- corresponding passed values are pending in `output` (resp. `output''`).
  refine ⟨λ L₀ chans₀ L₁ chans₁ =>
    L₀ = matchedOf proc.atoms [i₃, i₂, i₁] ∧ L₁ = Pn ∧
    chans₁ r = [] ∧ (∀ v ∈ chans₁ input, InterpConsts.isClonable v) ∧
    ∃ A B A₂ B₂ : List V, A.length = B.length ∧ A₂.length = B₂.length ∧ (A = [] ∨ A₂ = []) ∧
      chans₀ decider = A ++ chans₁ decider ∧ chans₀ decider'' = A₂ ++ chans₁ decider ∧
      chans₀ input = B ++ chans₁ input ∧ chans₀ input'' = B₂ ++ chans₁ input ∧
      ∀ y, y ≠ decider → y ≠ input → y ≠ r →
        chans₁ y = chans₀ y ++ (if y = output then steerOut flavor A B
          else if y = output'' then steerOut flavor A₂ B₂ else []),
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- init
    refine ⟨rfl, rfl, rfl, by simp, [], [], [], [], rfl, rfl, .inl rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro y _ _ _
    simp
  · -- frame_pop: `x` is not read by the steers
    rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx₀ hx₁
      ⟨rfl, rfl, hr₁, hcl, A, B, A₂, B₂, hAB, hAB₂, hA, hd, hd₂, hi, hi₂, heq⟩ hpop
    rw [hP] at hx₀
    simp at hx₀
    obtain ⟨hxd₂, hxi₂, -, hxd, hxi⟩ := hx₀
    have hxr : x ≠ r := λ h => hx₁ (h ▸ hrin)
    have hpx : chans₀ x = v :: chans₀' x := by simpa using hpop x
    have hpy : ∀ y, y ≠ x → chans₀ y = chans₀' y := λ y hy => by simpa [hy] using hpop y
    refine ⟨λ y => if y = x then (chans₁ y).tail else chans₁ y, ?_, rfl, rfl, ?_, ?_,
      A, B, A₂, B₂, hAB, hAB₂, hA, ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      by_cases hy : y = x
      · subst hy
        have := heq _ hxd hxi hxr
        rw [hpx] at this
        simp [this]
      · simp [hy]
    · simp [Ne.symm hxr, hr₁]
    · simpa [Ne.symm hxi] using hcl
    · rw [← hpy _ (Ne.symm hxd)]; simpa [Ne.symm hxd] using hd
    · rw [← hpy _ (Ne.symm hxd₂)]; simpa [Ne.symm hxd] using hd₂
    · rw [← hpy _ (Ne.symm hxi)]; simpa [Ne.symm hxi] using hi
    · rw [← hpy _ (Ne.symm hxi₂)]; simpa [Ne.symm hxi] using hi₂
    · intro y hyd hyi hyr
      by_cases hy : y = x
      · subst hy
        have := heq _ hyd hyi hyr
        rw [hpx] at this
        simp [this]
      · have := heq _ hyd hyi hyr
        rw [hpy _ hy] at this
        simp [hy, this]
  · -- frame_push: pushes to the copies come from their forks
    rintro L₀ chans₀ L₁ chans₁ outs vals hlen' hx hnd hfp
      ⟨rfl, rfl, hr₁, hcl, A, B, A₂, B₂, hAB, hAB₂, hA, hd, hd₂, hi, hi₂, heq⟩
    rw [hP] at hx
    have hro' : r ∉ outs := λ h => (hx r h).2 hrout
    have hoo' : output ∉ outs := λ h => by simpa using (hx output h).1
    have ho₂o' : output'' ∉ outs := λ h => by simpa using (hx output'' h).1
    refine ⟨rfl, rfl, ?_, ?_, A, B, A₂, B₂, hAB, hAB₂, hA, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hr₁, ChanMap.pushed_not_mem hro']
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hcl w hw
      · exact ForkPush.clonable hfp hfork₂ hw
    · simp [hd]
    · simp [hd₂, ForkPush.pushed_eq hfp hnd hlen' hfork₁]
    · simp [hi]
    · simp [hi₂, ForkPush.pushed_eq hfp hnd hlen' hfork₂]
    · intro y hyd hyi hyr
      simp only [heq y hyd hyi hyr, List.append_assoc]
      by_cases hyo : y = output
      · subst hyo; simp [ChanMap.pushed_not_mem hoo']
      · by_cases hyo₂ : y = output''
        · subst hyo₂; simp [hyo, ChanMap.pushed_not_mem ho₂o']
        · simp [hyo, hyo₂]
  · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
      _ _ ⟨rfl, -⟩ hmem
    rw [hP] at hmem
    simp at hmem
  · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
      inputs outputs inputVals outputVals chans₀' _ _
      ⟨rfl, rfl, hr₁, hcl, A, B, A₂, B₂, hAB, hAB₂, hA, hd, hd₂, hi, hi₂, heq⟩ hget hinterp
      hlen₁ hlen₂ hpop
    rw [hP] at hget ⊢
    match i, hget with
    | 0, hget =>
      -- `steer₂` fires
      simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, rfl, rfl⟩ := hinterp.steer_inv hlen₁
      have hpd : chans₀ decider'' = dv :: chans₀' decider'' := by
        simpa [Ne.symm hdi₂] using hpop decider''
      have hpi : chans₀ input'' = xv :: chans₀' input'' := by simpa [hdi₂] using hpop input''
      have hpy : ∀ y, y ≠ decider'' → y ≠ input'' → chans₀ y = chans₀' y := λ y h₁ h₂ => by
        simpa [Ne.symm h₁, Ne.symm h₂] using hpop y
      have hout : (if InterpConsts.toBool dv = some flavor then [xv] else []) =
          (if b = flavor then [xv] else []) := by simp [hb]
      -- The inputs of the rewritten sinks are the same as in the original
      have hd₂' : chans₁ decider'' = dv :: chans₀' decider'' := by
        rw [heq _ (Ne.symm hdd₂) (Ne.symm hid₂) (Ne.symm hrd₂), hpd]
        simp [Ne.symm hod₂, Ne.symm ho₂d₂]
      have hi₂' : chans₁ input'' = xv :: chans₀' input'' := by
        rw [heq _ (Ne.symm hdi₂') (Ne.symm hii₂) (Ne.symm hri₂), hpi]
        simp [Ne.symm hoi₂, Ne.symm ho₂i₂]
      rcases A₂ with _ | ⟨a, A₂⟩
      · -- `steer₂` is ahead (or level): the rewritten steer fires, then the sinks
        obtain rfl : B₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hAB₂.symm)
        have hd' : chans₁ decider = dv :: chans₀' decider'' := by
          rw [← hpd]; simpa using hd₂.symm
        have hi' : chans₁ input = xv :: chans₀' input'' := by
          rw [← hpi]; simpa using hi₂.symm
        obtain ⟨c, hτ, hcd, hci, hcr, hco, hco₂, hcy⟩ := steer_fork_tau hmemS hmemF₂
          hdi hrd hri hro hro₂ hod hoi ho₂d ho₂i hoo₂ hd' hi' hr₁ hb (hcl xv (by simp [hi']))
        have hcd₂ : c decider'' = dv :: chans₀' decider'' := by
          rw [hcy _ (Ne.symm hdd₂) (Ne.symm hid₂) (Ne.symm hod₂) (Ne.symm ho₂d₂), hd₂']
        have hτ₂ := sink_tau hmemSd hcd₂
        have hci₂ : (λ y => if y = decider'' then chans₀' decider'' else c y) input'' =
            xv :: chans₀' input'' := by
          dsimp only
          rw [if_neg (Ne.symm hdi₂),
            hcy _ (Ne.symm hdi₂') (Ne.symm hii₂) (Ne.symm hoi₂) (Ne.symm ho₂i₂), hi₂']
        have hτ₃ := sink_tau (chans := λ y => if y = decider'' then chans₀' decider'' else c y)
          hmemSi hci₂
        refine ⟨_, _, hτ.trans (hτ₂.trans hτ₃), by simp, rfl, ?_, ?_,
          A ++ [dv], B ++ [xv], [], [], by simp [hAB], rfl, .inr rfl,
          ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
        · simp [hri₂, hrd₂, hcr]
        · intro w hw
          simp only [hii₂, hid₂, if_false] at hw
          rw [hci] at hw
          exact hcl w (by simp [hi', hw])
        · rw [← hpy _ hdd₂ hdi₂', hd, hd']
          simp [pushed_ite, ho₂d, hdi₂', hdd₂, hcd]
        · simp [pushed_ite, ho₂d₂, hdi₂', hdd₂, hcd]
        · rw [← hpy _ hid₂ hii₂, hi, hi']
          simp [pushed_ite, ho₂i, hii₂, hid₂, hci]
        · simp [pushed_ite, ho₂i₂, hii₂, hid₂, hci]
        · intro y hyd hyi hyr
          rw [pushed_ite]
          by_cases hyi₂ : y = input''
          · subst hyi₂
            simp [ho₂i₂, Ne.symm hoi₂, Ne.symm ho₂i₂]
          · by_cases hyd₂ : y = decider''
            · subst hyd₂
              simp [hyi₂, ho₂d₂, Ne.symm hod₂, Ne.symm ho₂d₂]
            · rw [← hpy y hyd₂ hyi₂, if_neg hyi₂, if_neg hyd₂]
              by_cases hyo : y = output
              · subst hyo
                rw [hco, heq _ hyd hyi hyr, steerOut_snoc hAB, hout]
                simp [Ne.symm hoo₂]
              · by_cases hyo₂ : y = output''
                · subst hyo₂
                  rw [hco₂, heq _ hyd hyi hyr]
                  simp [hyo]
                · rw [hcy y hyd hyi hyo hyo₂, heq _ hyd hyi hyr]
                  simp [hyo, hyo₂, Ne.symm hyo₂]
      · -- `steer₁` is ahead: `steer₂` catches up, the rewritten sinks fire
        obtain ⟨b', B₂', rfl⟩ : ∃ b' B', B₂ = b' :: B' := by
          cases B₂ with
          | nil => simp at hAB₂
          | cons b' B' => exact ⟨b', B', rfl⟩
        obtain rfl : A = [] := by simpa using hA
        obtain rfl : B = [] := List.eq_nil_of_length_eq_zero (by simpa using hAB.symm)
        rw [hpd] at hd₂
        rw [hpi] at hi₂
        simp only [List.cons_append, List.cons.injEq] at hd₂ hi₂
        obtain ⟨rfl, hd₂⟩ := hd₂
        obtain ⟨rfl, hi₂⟩ := hi₂
        have hτ₂ := sink_tau hmemSd hd₂'
        have hi₂'' : (λ y => if y = decider'' then chans₀' decider'' else chans₁ y) input'' =
            xv :: chans₀' input'' := by
          dsimp only
          rw [if_neg (Ne.symm hdi₂), hi₂']
        have hτ₃ := sink_tau (chans := λ y => if y = decider'' then chans₀' decider'' else chans₁ y)
          hmemSi hi₂''
        refine ⟨_, _, hτ₂.trans hτ₃, by simp, rfl, ?_, ?_, [], [], A₂, B₂',
          rfl, by simpa using hAB₂, .inl rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
        · simp [hri₂, hrd₂, hr₁]
        · intro w hw
          simp only [hii₂, hid₂, if_false] at hw
          exact hcl w hw
        · rw [← hpy _ hdd₂ hdi₂', hd]
          simp [pushed_ite, ho₂d, hdi₂', hdd₂]
        · simp [pushed_ite, ho₂d₂, hdi₂', hdd₂, hd₂]
        · rw [← hpy _ hid₂ hii₂, hi]
          simp [pushed_ite, ho₂i, hii₂, hid₂]
        · simp [pushed_ite, ho₂i₂, hii₂, hid₂, hi₂]
        · intro y hyd hyi hyr
          rw [pushed_ite]
          by_cases hyi₂ : y = input''
          · subst hyi₂
            simp [ho₂i₂, Ne.symm hoi₂, Ne.symm ho₂i₂]
          · by_cases hyd₂ : y = decider''
            · subst hyd₂
              simp [hyi₂, ho₂d₂, Ne.symm hod₂, Ne.symm ho₂d₂]
            · rw [← hpy y hyd₂ hyi₂, if_neg hyi₂, if_neg hyd₂, heq _ hyd hyi hyr]
              by_cases hyo₂ : y = output''
              · subst hyo₂
                rw [steerOut_cons, hout]
                simp [Ne.symm hoo₂]
              · simp [hyo₂, Ne.symm hyo₂]
    | 1, hget =>
      -- The fork fires: the same fork fires on the rewritten side
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, h⟩ := hget
      subst allOutputs
      obtain ⟨rfl, rfl, h, -, v, rfl, hclone, rfl⟩ := hinterp.fork_inv hlen₁
      subst outputs
      have hpi' : chans₀ input' = v :: chans₀' input' := by simpa using hpop input'
      have hpy : ∀ y, y ≠ input' → chans₀ y = chans₀' y := λ y h => by
        simpa [Ne.symm h] using hpop y
      have hc : chans₁ input' = v :: (chans₀' input' ++
          (if input' = output then steerOut flavor A B
            else if input' = output'' then steerOut flavor A₂ B₂ else [])) := by
        rw [heq _ hi'd hi'i (Ne.symm hri'), hpi', List.cons_append]
      have hτ := LocalTauStar.async_list_mem (chans := chans₁)
        (chans' := λ y => if y = input' then (chans₁ y).tail else chans₁ y)
        (aop := .fork k) (allInputs := [input']) (allOutputs := outputs')
        (inputs := [input']) (inputVals := [v]) (outputs := outputs')
        (outputVals := List.replicate k v)
        hmemF (.interp_fork hlen hclone) rfl (by simp [hlen]) (by
          intro y
          by_cases hy : y = input'
          · subst hy; simp [hc]
          · simp [hy, Ne.symm hy])
      have hPd := SameFork.pushed_replicate_eq (v := v) haff hfork₁ h₂ hlen
      have hPi := SameFork.pushed_replicate_eq (v := v) haff hfork₂ h₂ hlen
      refine ⟨_, _, hτ, by simp, rfl, ?_, ?_, A, B, A₂, B₂, hAB, hAB₂, hA,
        ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
      · simp [hr₁, ChanMap.pushed_not_mem hrouts]
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hcl w (by simpa [Ne.symm hi'i] using hw)
        · rw [List.eq_of_mem_replicate (mem_pushed hw)]; exact hclone
      · rw [← hpy _ (Ne.symm hi'd), hd]; simp [Ne.symm hi'd]
      · rw [← hpy _ (Ne.symm hi'd₂), hd₂, hPd]; simp [Ne.symm hi'd]
      · rw [← hpy _ (Ne.symm hi'i), hi]; simp [Ne.symm hi'i]
      · rw [← hpy _ (Ne.symm hi'i₂), hi₂, hPi]; simp [Ne.symm hi'i]
      · intro y hyd hyi hyr
        have hcomm : (if y = output then steerOut flavor A B
            else if y = output'' then steerOut flavor A₂ B₂ else []) ++
            ChanMap.pushed outputs' (List.replicate k v) y =
            ChanMap.pushed outputs' (List.replicate k v) y ++ (if y = output then steerOut flavor A B
            else if y = output'' then steerOut flavor A₂ B₂ else []) := by
          by_cases hyo : y = output
          · subst hyo; simp [ChanMap.pushed_not_mem hoouts]
          · by_cases hyo₂ : y = output''
            · subst hyo₂; simp [hyo, ChanMap.pushed_not_mem ho₂outs]
            · simp [hyo, hyo₂]
        by_cases hy : y = input'
        · subst hy
          rw [if_pos rfl, hc, List.tail_cons]
          simp only [List.append_assoc, hcomm]
        · rw [if_neg hy, heq _ hyd hyi hyr, hpy _ hy]
          simp only [List.append_assoc, hcomm]
    | 2, hget =>
      -- `steer₁` fires
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, rfl, rfl⟩ := hinterp.steer_inv hlen₁
      have hpd : chans₀ decider = dv :: chans₀' decider := by
        simpa [Ne.symm hdi] using hpop decider
      have hpi : chans₀ input = xv :: chans₀' input := by simpa [hdi] using hpop input
      have hpy : ∀ y, y ≠ decider → y ≠ input → chans₀ y = chans₀' y := λ y h₁ h₂ => by
        simpa [Ne.symm h₁, Ne.symm h₂] using hpop y
      have hout : (if InterpConsts.toBool dv = some flavor then [xv] else []) =
          (if b = flavor then [xv] else []) := by simp [hb]
      rcases A with _ | ⟨a, A⟩
      · -- `steer₁` is ahead (or level): the rewritten steer fires
        obtain rfl : B = [] := List.eq_nil_of_length_eq_zero (by simpa using hAB.symm)
        have hd' : chans₁ decider = dv :: chans₀' decider := by rw [← hpd]; simpa using hd.symm
        have hi' : chans₁ input = xv :: chans₀' input := by rw [← hpi]; simpa using hi.symm
        obtain ⟨c, hτ, hcd, hci, hcr, hco, hco₂, hcy⟩ := steer_fork_tau hmemS hmemF₂
          hdi hrd hri hro hro₂ hod hoi ho₂d ho₂i hoo₂ hd' hi' hr₁ hb (hcl xv (by simp [hi']))
        refine ⟨_, c, hτ, by simp, rfl, hcr, ?_, [], [], A₂ ++ [dv], B₂ ++ [xv], rfl,
          by simp [hAB₂], .inl rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
        · intro w hw
          rw [hci] at hw
          exact hcl w (by simp [hi', hw])
        · rw [hcd]; simp [pushed_ite, hod]
        · rw [← hpy _ (Ne.symm hdd₂) (Ne.symm hid₂), hd₂, hd', hcd]; simp [pushed_ite, hod₂]
        · rw [hci]; simp [pushed_ite, hoi]
        · rw [← hpy _ (Ne.symm hdi₂') (Ne.symm hii₂), hi₂, hi', hci]; simp [pushed_ite, hoi₂]
        · intro y hyd hyi hyr
          rw [← hpy y hyd hyi, pushed_ite]
          by_cases hyo : y = output
          · subst hyo
            rw [hco, heq _ hyd hyi hyr]
            simp
          · by_cases hyo₂ : y = output''
            · subst hyo₂
              rw [hco₂, heq _ hyd hyi hyr, steerOut_snoc hAB₂, hout]
              simp [hyo, Ne.symm hyo]
            · rw [hcy y hyd hyi hyo hyo₂, heq _ hyd hyi hyr]
              simp [hyo, hyo₂, Ne.symm hyo]
      · -- `steer₂` is ahead: `steer₁` catches up, nothing to do on the rewritten side
        obtain ⟨b', B', rfl⟩ : ∃ b' B', B = b' :: B' := by
          cases B with
          | nil => simp at hAB
          | cons b' B' => exact ⟨b', B', rfl⟩
        obtain rfl : A₂ = [] := by simpa using hA
        obtain rfl : B₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hAB₂.symm)
        rw [hpd] at hd
        rw [hpi] at hi
        simp only [List.cons_append, List.cons.injEq] at hd hi
        obtain ⟨rfl, hd⟩ := hd
        obtain ⟨rfl, hi⟩ := hi
        refine ⟨_, _, .refl, by simp, rfl, hr₁, hcl, A, B', [], [], by simpa using hAB, rfl,
          .inr rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
        · simp [pushed_ite, hod, hd]
        · rw [← hpy _ (Ne.symm hdd₂) (Ne.symm hid₂)]; simp [pushed_ite, hod₂, hd₂]
        · simp [pushed_ite, hoi, hi]
        · rw [← hpy _ (Ne.symm hdi₂') (Ne.symm hii₂)]; simp [pushed_ite, hoi₂, hi₂]
        · intro y hyd hyi hyr
          rw [← hpy y hyd hyi, pushed_ite, heq y hyd hyi hyr]
          by_cases hyo : y = output
          · subst hyo
            rw [steerOut_cons, hout]
            simp
          · simp [hyo, Ne.symm hyo]
  · rintro L₁ chans₁ ⟨-, rfl, hr₁, -, A, B, A₂, B₂, -, -, -, hd, hd₂, hi, -, heq⟩
    refine ⟨rfl, ?_⟩
    simp only [ChanMap.empty_apply, List.nil_eq_append_iff] at hd hd₂ hi
    obtain ⟨rfl, hd⟩ := hd
    obtain ⟨rfl, -⟩ := hd₂
    obtain ⟨-, hi⟩ := hi
    funext y
    by_cases hyd : y = decider
    · subst hyd; exact hd
    · by_cases hyi : y = input
      · subst hyi; exact hi
      · by_cases hyr : y = r
        · subst hyr; exact hr₁
        · rw [heq y hyd hyi hyr]; simp

end Wavelet.Compile.DeadCodeElim
