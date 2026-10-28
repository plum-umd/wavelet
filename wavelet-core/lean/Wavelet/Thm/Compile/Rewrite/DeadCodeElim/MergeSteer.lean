import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `merge-steer-*`: a merge followed by a steer with the same decider
(only a forward simulation without `PreservesInit`). -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-- Values of `vs` let through by a steer reading the deciders `ds`. -/
private def steered [InterpConsts V] (flavor : Bool) : List V → List V → List V
  | dv :: ds, v :: vs =>
    (if InterpConsts.toBool dv = some flavor then [v] else []) ++ steered flavor ds vs
  | _, _ => []

@[simp]
private theorem steered_nil_left [InterpConsts V] {flavor : Bool} {vs : List V} :
    steered flavor [] vs = [] := by
  cases vs <;> rfl

@[simp]
private theorem steered_cons_cons [InterpConsts V] {flavor : Bool} {dv v : V} {ds vs : List V} :
    steered flavor (dv :: ds) (v :: vs) =
      (if InterpConsts.toBool dv = some flavor then [v] else []) ++ steered flavor ds vs := rfl

private theorem steered_append [InterpConsts V] {flavor : Bool} {ds₁ ds₂ vs₁ vs₂ : List V}
  (hlen : ds₁.length = vs₁.length) :
    steered flavor (ds₁ ++ ds₂) (vs₁ ++ vs₂) =
      steered flavor ds₁ vs₁ ++ steered flavor ds₂ vs₂ := by
  induction ds₁ generalizing vs₁ with
  | nil => cases vs₁ <;> simp_all
  | cons dv ds₁ ih =>
    cases vs₁ with
    | nil => simp at hlen
    | cons v vs₁ => simp [ih (by simpa using hlen)]

/-- `Q` is the decider value read by a merge in state `st` but not used yet. -/
private def MergeDec [InterpConsts V] (st : AsyncOp.MergeState) (Q : List V) : Prop :=
  (st = .decider ∧ Q = []) ∨
  ∃ b₀ b, Q = [b₀] ∧ InterpConsts.toBool b₀ = some b ∧ st = (if b then .popRight else .popLeft)

private theorem pushed_eq_singleton [DecidableEq χ]
  {names : List χ} {vals : List V} {v : V} {y : χ}
  (hnodup : names.Nodup) (hlen : names.length = vals.length) (hvals : ∀ w ∈ vals, w = v)
  (hy : y ∈ names) : ChanMap.pushed names vals y = [v] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons w vals =>
      have ⟨hx, hnodup'⟩ := List.nodup_cons.mp hnodup
      rw [ChanMap.pushed_cons]
      by_cases hxy : x = y
      · subst hxy
        rw [ChanMap.pushed_not_mem hx, hvals w (by simp)]
        simp
      · simp only [hxy, if_false, List.nil_append]
        exact ih hnodup' (by simpa using hlen) (λ w hw => hvals w (by simp [hw]))
          (by simpa [Ne.symm hxy] using hy)

/-- Two outputs of the same fork are always pushed together with the same value. -/
private theorem pushed_sameFork [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {d d' : χ} {outs : List χ} {vals : List V}
  (hfork : SameFork proc.atoms d d')
  (hlen : outs.length = vals.length) (hnodup : outs.Nodup) (hfp : ForkPush proc outs vals) :
    ChanMap.pushed outs vals d = ChanMap.pushed outs vals d' := by
  obtain ⟨k, ins, fouts, hmem, hd, hd'⟩ := hfork
  by_cases h : d ∈ outs ∨ d' ∈ outs
  · obtain ⟨heq, v, -, hvals⟩ : outs = fouts ∧
        ∃ v, InterpConsts.isClonable v ∧ ∀ w ∈ vals, w = v := by
      rcases h with h | h
      · exact hfp d h k ins fouts hmem hd
      · exact hfp d' h k ins fouts hmem hd'
    subst heq
    rw [pushed_eq_singleton hnodup hlen hvals hd, pushed_eq_singleton hnodup hlen hvals hd']
  · simp only [not_or] at h
    rw [ChanMap.pushed_not_mem h.1, ChanMap.pushed_not_mem h.2]

/-- Generic version of `merge-steer-*`: the steer only lets through the values
from `inP`, and `inS` is the other merge input. -/
private theorem merge_steer_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat} {flavor : Bool}
  {decider inputL inputR output decider' output' inP inS : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.steer flavor 1) [decider', output] [output']))
  (hne : i₂ ≠ i₁)
  (hfork : SameFork proc.atoms decider decider')
  (hin : (flavor = true ∧ inP = inputR ∧ inS = inputL) ∨
    (flavor = false ∧ inP = inputL ∧ inS = inputR)) :
    RuleOKNoInit proc [i₂, i₁] [.forward #v[inP] #v[output'], .sink #v[decider, decider', inS]]
  := by
  have hP : matchedOf proc.atoms [i₂, i₁] =
      [.async (.steer flavor 1) [decider', output] [output'],
        .async (.merge .decider 1) [decider, inputL, inputR] [output]] := by
    simp [h₁, h₂]
  have hP' : ([.forward #v[inP] #v[output'], .sink #v[decider, decider', inS]] :
      AtomicProcs Op χ V) =
      [.async (.forward 1) [inP] [output'], .async (.sink 3) [decider, decider', inS] []] := by
    simp [AtomicProc.forward, AtomicProc.sink]
  -- Facts from affineness
  have hnd₁ := (haff.atom_nodup h₁).1
  have hnd₂ := (haff.atom_nodup h₂).1
  have hdisj := haff.atom_disjoint h₂ h₁ hne
  simp at hnd₁ hnd₂ hdisj
  obtain ⟨⟨hdl, hdr⟩, hlr⟩ := hnd₁
  obtain ⟨⟨⟨hdd', hdo⟩, ⟨hld', hlo⟩, hrd', hro⟩, hoo'⟩ := hdisj
  -- `output'` is not a copy of the decider
  have ⟨hdo', hd'o'⟩ : decider ≠ output' ∧ decider' ≠ output' := by
    obtain ⟨k, ins, fouts, hmem, hd, hd'⟩ := hfork
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hmem
    have hget' : proc.atoms[j]? = some (.async (.fork k) ins fouts) :=
      List.getElem?_eq_some_iff.mpr ⟨hj, hget⟩
    have hj₂ : j ≠ i₂ := by rintro rfl; rw [h₂] at hget'; simp at hget'
    have := (haff.atom_disjoint hget' h₂ hj₂).2
    simp at this
    exact ⟨λ h => this (h ▸ hd), λ h => this (h ▸ hd')⟩
  have ⟨⟨hPo, hPd, hPd', hPS⟩, ⟨hSo, hSd, hSd'⟩, hPmem, hSmem⟩ :
      (inP ≠ output ∧ inP ≠ decider ∧ inP ≠ decider' ∧ inP ≠ inS) ∧
      (inS ≠ output ∧ inS ≠ decider ∧ inS ≠ decider') ∧
      (inP = inputL ∨ inP = inputR) ∧ (inS = inputL ∨ inS = inputR) := by
    rcases hin with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact ⟨⟨hro, Ne.symm hdr, hrd', Ne.symm hlr⟩, ⟨hlo, Ne.symm hdl, hld'⟩, .inr rfl, .inl rfl⟩
    · exact ⟨⟨hlo, Ne.symm hdl, hld', hlr⟩, ⟨hro, Ne.symm hdr, hrd'⟩, .inl rfl, .inr rfl⟩
  /- The relation:
    - `X` are the deciders (in `decider'`) of the values pending in `output`,
      and `Q` is the decider read by the merge but not used yet;
    - `output'` is ahead by the pending values from `inP` (`steered`);
    - the sink never fires, so the rewritten graph lags behind (`lag`) on its inputs;
    - `output` is unused in the rewritten graph. -/
  refine ⟨?_, λ L₀ chans₀ L₁ chans₁ => ∃ st X Q, ∃ lag : χ → List V,
    L₀ = [.async (.steer flavor 1) [decider', output] [output'],
      .async (.merge st 1) [decider, inputL, inputR] [output]] ∧
    L₁ = [.forward #v[inP] #v[output'], .sink #v[decider, decider', inS]] ∧
    MergeDec st Q ∧
    chans₀ decider' = X ++ Q ++ chans₀ decider ∧
    X.length = (chans₀ output).length ∧
    (∀ y, y ≠ output → y ≠ decider → y ≠ decider' → y ≠ inS → lag y = []) ∧
    (∀ y, y ≠ output → chans₁ y = lag y ++ chans₀ y ++
      (if y = output' then steered flavor X (chans₀ output) else [])), ?_⟩
  · constructor
    · simp [hne]
    · simp [(List.getElem?_eq_some_iff.mp h₁).1, (List.getElem?_eq_some_iff.mp h₂).1]
    · simp [hP', hPd, hPd', hPS, hdd', Ne.symm hSd, Ne.symm hSd']
    · simp [hP']
    · intro x hx
      left
      simp [hP'] at hx
      simp [hP]
      rcases hx with rfl | rfl | rfl | rfl
      · rcases hPmem with rfl | rfl <;> simp
      · simp
      · simp
      · rcases hSmem with rfl | rfl <;> simp
    · intro x hx
      left
      simp [hP'] at hx
      simp [hP, hx]
  constructor
  · refine ⟨.decider, [], [], λ _ => [], hP, rfl, .inl ⟨rfl, rfl⟩, rfl, rfl,
      λ _ _ _ _ _ => rfl, λ y _ => by simp⟩
  · -- `x` is read by the environment or the rest of the graph
    rintro L₀ chans₀ L₁ chans₁ x v chans₀' hx hx' ⟨st, X, Q, lag, rfl, rfl, hdec, hd, hlen,
      hlag, heq⟩ hpop
    simp [hP] at hx
    simp [hP'] at hx'
    obtain ⟨hxd', hxo, hxd, -, -⟩ := hx
    obtain ⟨-, -, -, hxS⟩ := hx'
    have hpo : chans₀ output = chans₀' output := by simpa [Ne.symm hxo] using hpop output
    refine ⟨λ y => if y = output then chans₁ output else lag y ++ chans₀' y ++
        (if y = output' then steered flavor X (chans₀' output) else []), ?_,
      st, X, Q, lag, rfl, rfl, hdec, ?_, ?_, hlag, ?_⟩
    · intro y
      by_cases hyo : y = output
      · subst hyo; simp [Ne.symm hxo]
      · rw [heq y hyo, hpop y, hpo]
        by_cases hyx : y = x
        · subst hyx; simp [hyo, hlag y hyo hxd hxd' hxS]
        · simp [hyo, hyx]
    · have h₁ := hpop decider
      have h₂ := hpop decider'
      simp [Ne.symm hxd, Ne.symm hxd'] at h₁ h₂
      rw [← h₁, ← h₂]
      exact hd
    · rw [← hpo]
      exact hlen
    · intro y hy
      simp [hy]
  · -- Pushes to `decider` and `decider'` are always the same
    rintro L₀ chans₀ L₁ chans₁ outs vals hlen' hx hnodup hfp ⟨st, X, Q, lag, rfl, rfl, hdec,
      hd, hlen, hlag, heq⟩
    have ho : output ∉ outs := λ h => by simpa [hP] using (hx output h).1
    have ho' : output' ∉ outs := λ h => by simpa [hP] using (hx output' h).1
    have hpd := pushed_sameFork hfork hlen' hnodup hfp
    refine ⟨st, X, Q, lag, rfl, rfl, hdec, ?_, ?_, hlag, ?_⟩
    · simp only [hd, List.append_assoc, hpd]
    · simp [ChanMap.pushed_not_mem ho, hlen]
    · intro y hy
      simp only [heq y hy, ChanMap.pushed_not_mem ho, List.append_nil, List.append_assoc]
      by_cases hyo' : y = output'
      · subst hyo'; simp [ChanMap.pushed_not_mem ho']
      · simp [hyo']
  · rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀'
      _ _ ⟨st, X, Q, lag, rfl, -⟩ hmem
    simp at hmem
  · rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs
      inputs outputs inputVals outputVals chans₀' _ _ ⟨st, X, Q, lag, rfl, rfl, hdec, hd, hlen,
      hlag, heq⟩ hget hinterp hlen₁ hlen₂ hpop
    match i, hget with
    | 0, hget =>
      -- The steer fires: it reads the first decider in `X`, nothing to do on the rewritten side
      simp only [List.getElem?_cons_zero, Option.some.injEq, AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      obtain ⟨rfl, rfl, dv, xv, b, rfl, hb, houts, hovals⟩ := hinterp.steer_inv hlen₁
      have hpo : ∀ y, ChanMap.pushed outputs outputVals y =
          if y = output' then (if b = flavor then [xv] else []) else [] := by
        intro y
        rw [houts, hovals]
        by_cases hbf : b = flavor
        · by_cases hy : y = output'
          · subst hy; simp [hbf]
          · simp [hbf, hy, Ne.symm hy]
        · simp [hbf]
      have hpd' := hpop decider'
      have hpo₀ := hpop output
      have hpd₀ := hpop decider
      simp [hnd₂, Ne.symm hnd₂, Ne.symm hdd', Ne.symm hdo] at hpd' hpo₀ hpd₀
      obtain ⟨x₀, X', rfl⟩ : ∃ x₀ X', X = x₀ :: X' := by
        cases X with
        | nil => simp [hpo₀] at hlen
        | cons x₀ X' => exact ⟨x₀, X', rfl⟩
      rw [hpd', hpd₀] at hd
      simp only [List.cons_append, List.cons.injEq] at hd
      obtain ⟨rfl, hd⟩ := hd
      refine ⟨_, _, .refl, st, X', Q, λ y => lag y ++ ChanMap.pushed [decider', output] [dv, xv] y,
        by simp, rfl, hdec, ?_, ?_, ?_, ?_⟩
      · simp only [hpo, hd'o', hdo', if_false, List.append_nil]
        exact hd
      · simp only [hpo, hoo', if_false, List.append_nil]
        simpa [hpo₀] using hlen
      · intro y hyo hyd hyd' hyS
        simp [hlag y hyo hyd hyd' hyS, Ne.symm hyd', Ne.symm hyo]
      · intro y hyo
        dsimp only
        rw [heq y hyo, hpop y, hpo₀, hpo y, hpo output]
        simp only [hoo', if_false, List.append_nil, steered_cons_cons, hb, Option.some.injEq,
          List.append_assoc]
        by_cases hy : y = output' <;> simp [hy]
    | 1, hget =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      rcases hdec with ⟨rfl, rfl⟩ | ⟨b₀, b, rfl, hb₀, rfl⟩
      · -- The merge reads a decider, which becomes pending (`Q`)
        rcases hinterp.merge_inv hlen₁ with ⟨h, -⟩ | ⟨h, -⟩ |
          ⟨-, rfl, rfl, rfl, dv, b, rfl, hb, rfl⟩
        · cases h
        · cases h
        have hpd₀ := hpop decider
        have hpd' := hpop decider'
        have hpo₀ := hpop output
        simp [hdd', hdo] at hpd₀ hpd' hpo₀
        refine ⟨_, _, .refl, if b then .popRight else .popLeft, X, [dv],
          λ y => lag y ++ ChanMap.pushed [decider] [dv] y, by simp, rfl,
          .inr ⟨dv, b, rfl, hb, rfl⟩, ?_, ?_, ?_, ?_⟩
        · simp only [ChanMap.pushed_nil_left, List.append_nil]
          rw [← hpd', hd, hpd₀]
          simp
        · simpa [hpo₀] using hlen
        · intro y hyo hyd hyd' hyS
          simp [hlag y hyo hyd hyd' hyS, Ne.symm hyd]
        · intro y hyo
          dsimp only
          rw [heq y hyo, hpop y, hpo₀]
          simp
      · -- The merge pops `c` and uses the pending decider `b₀`
        obtain ⟨rfl, rfl, c, v, rfl, rfl, rfl, hc⟩ : aop' = .merge .decider 1 ∧
            outputs = [output] ∧ ∃ c v, inputs = [c] ∧ inputVals = [v] ∧ outputVals = [v] ∧
            ((c = inP ∧ InterpConsts.toBool b₀ = some flavor) ∨
              (c = inS ∧ InterpConsts.toBool b₀ ≠ some flavor)) := by
          rcases hinterp.merge_inv hlen₁ with ⟨hst, rfl, rfl, rfl, v, rfl, rfl⟩ |
            ⟨hst, rfl, rfl, rfl, v, rfl, rfl⟩ | ⟨hst, -⟩
          · cases b <;> simp at hst
            refine ⟨rfl, rfl, inputL, v, rfl, rfl, rfl, ?_⟩
            rcases hin with ⟨rfl, -, rfl⟩ | ⟨rfl, rfl, -⟩
            · exact .inr ⟨rfl, by simp [hb₀]⟩
            · exact .inl ⟨rfl, hb₀⟩
          · cases b <;> simp at hst
            refine ⟨rfl, rfl, inputR, v, rfl, rfl, rfl, ?_⟩
            rcases hin with ⟨rfl, rfl, -⟩ | ⟨rfl, -, rfl⟩
            · exact .inl ⟨rfl, hb₀⟩
            · exact .inr ⟨rfl, by simp [hb₀]⟩
          · cases b <;> simp at hst
        obtain ⟨hco, hcd, hcd'⟩ : c ≠ output ∧ c ≠ decider ∧ c ≠ decider' := by
          rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact ⟨hPo, hPd, hPd'⟩
          · exact ⟨hSo, hSd, hSd'⟩
        have hpc := hpop c
        have hpd₀ := hpop decider
        have hpd' := hpop decider'
        have hpo₀ := hpop output
        simp [hcd, hcd', hco] at hpc hpd₀ hpd' hpo₀
        -- The value is pending in `output`, decided by `b₀`
        have hd'' : chans₀' decider' ++ ChanMap.pushed [output] [v] decider' =
            (X ++ [b₀]) ++ [] ++ (chans₀' decider ++ ChanMap.pushed [output] [v] decider) := by
          simp only [ChanMap.pushed_cons, ChanMap.pushed_nil_left, Ne.symm hnd₂, Ne.symm hdo,
            if_false, List.append_nil]
          rw [← hpd', hd, hpd₀]
        have hlen'' : (X ++ [b₀]).length =
            (chans₀' output ++ ChanMap.pushed [output] [v] output).length := by
          simp [← hpo₀, hlen]
        have hsteered : steered flavor (X ++ [b₀])
            (chans₀' output ++ ChanMap.pushed [output] [v] output) =
            steered flavor X (chans₀ output) ++
              (if InterpConsts.toBool b₀ = some flavor then [v] else []) := by
          simp only [ChanMap.pushed_cons, ChanMap.pushed_nil_left, if_true, List.append_nil]
          rw [← hpo₀, steered_append hlen]
          simp
        rcases hc with ⟨hcP, hb⟩ | ⟨hcS, hb⟩
        · -- `c = inP`: the forward fires
          subst c
          have hc₁ : chans₁ inP = v :: (chans₀' inP ++
              (if inP = output' then steered flavor X (chans₀ output) else [])) := by
            rw [heq inP hco, hlag inP hco hcd hcd' hPS, hpc]
            simp
          have hstep := LocalTauStar.async_list_mem
            (L := ([.forward #v[inP] #v[output'], .sink #v[decider, decider', inS]] :
              AtomicProcs Op χ V))
            (aop := .forward 1) (allInputs := [inP]) (allOutputs := [output'])
            (inputs := [inP]) (inputVals := [v]) (outputs := [output']) (outputVals := [v])
            (chans := chans₁)
            (chans' := λ y => if y = inP then (chans₁ inP).tail else chans₁ y)
            (by simp [AtomicProc.forward]) (.interp_forward rfl rfl) rfl rfl
            (by
              intro y
              by_cases hy : y = inP
              · subst hy; simp [hc₁]
              · simp [Ne.symm hy, hy])
          refine ⟨_, _, hstep, .decider, X ++ [b₀], [], lag, by simp, rfl, .inl ⟨rfl, rfl⟩,
            hd'', hlen'', hlag, ?_⟩
          intro y hyo
          dsimp only
          rw [hsteered]
          simp only [hb, if_true]
          by_cases hy : y = inP
          · subst hy
            simp only [if_true, hc₁, List.tail_cons, hlag y hyo hcd hcd' hPS]
            by_cases hyo' : y = output'
            · subst hyo'; simp [Ne.symm hco]
            · simp [hyo', Ne.symm hyo', Ne.symm hco]
          · rw [if_neg hy, heq y hyo, hpop y]
            by_cases hyo' : y = output'
            · subst hyo'; simp [Ne.symm hy, Ne.symm hyo]
            · simp [hyo', Ne.symm hyo', Ne.symm hy, Ne.symm hyo]
        · -- `c = inS`: nothing fires, the sink lags behind
          subst c
          refine ⟨_, _, .refl, .decider, X ++ [b₀], [],
            λ y => lag y ++ ChanMap.pushed [inS] [v] y, by simp, rfl, .inl ⟨rfl, rfl⟩,
            hd'', hlen'', ?_, ?_⟩
          · intro y hyo hyd hyd' hyS
            simp [hlag y hyo hyd hyd' hyS, Ne.symm hyS]
          · intro y hyo
            dsimp only
            rw [hsteered, heq y hyo, hpop y]
            simp [hb, Ne.symm hyo]

theorem merge_steer_true_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {decider inputL inputR output decider' output' : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.steer true 1) [decider', output] [output']))
  (hne : i₂ ≠ i₁)
  (hfork : SameFork proc.atoms decider decider') :
    RuleOKNoInit proc [i₂, i₁] [
      .forward #v[inputR] #v[output'],
      .sink #v[decider, decider', inputL],
    ]
  := merge_steer_ok haff h₁ h₂ hne hfork (.inl ⟨rfl, rfl, rfl⟩)

theorem merge_steer_false_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ : Nat}
  {decider inputL inputR output decider' output' : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .decider 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.steer false 1) [decider', output] [output']))
  (hne : i₂ ≠ i₁)
  (hfork : SameFork proc.atoms decider decider') :
    RuleOKNoInit proc [i₂, i₁] [
      .forward #v[inputL] #v[output'],
      .sink #v[decider, decider', inputR],
    ]
  := merge_steer_ok haff h₁ h₂ hne hfork (.inr ⟨rfl, rfl, rfl⟩)

end Wavelet.Compile.DeadCodeElim
