import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.Interp
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! `carry-fork-steer-to-inv-*`: a carry-fork-steer loop with the same decider is an invariant. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

namespace CarryForkSteerToInv

/-!
Simulation invariant. Names: the carry reads `d`, `l`, `r` and writes `o`; the fork reads `o`
and writes `sIn` (read by the steer) and `ext`; the steer reads `d''`, `sIn` and writes `r`.
The rewritten graph has `inv [d, l] [ext]` and `sink [d'']`.

The inv fires when the fork fires (an init step if the token starts a new iteration,
otherwise a true-decider step). A false decider is consumed by the inv when the steer
reads it, or right before the next init step if the fork is ahead of the steer.
-/

section Pure

variable {V : Type*} [InterpConsts V]

/-- Original loop state: carry state, carry deciders `A` (on `d`), steer deciders `D`
(on `d''`), tokens in flight `T` (on `sIn` then `o`), and `r`. While tokens are in flight,
`D` = (deciders read by the carry only) ++ `A`, all false except possibly the last one
(the carry takes `r` only after the steer passed the previous token). -/
inductive CS : AsyncOp.MergeState → List V → List V → List V → List V → Prop
  /-- Tokens in flight, the carry waits for a decider. -/
  | dec {F A T : List V} : (∀ g ∈ F, InterpConsts.toBool g = some false) →
      F.length + 1 = T.length → CS .decider A (F ++ A) T []
  /-- Tokens in flight, the carry read a false decider. -/
  | left {F A T : List V} {w : V} : (∀ g ∈ F, InterpConsts.toBool g = some false) →
      F.length + 1 = T.length → InterpConsts.toBool w = some false →
      CS .popLeft A (F ++ w :: A) T []
  /-- Tokens in flight, the carry read a true decider. -/
  | right {F A T : List V} {w : V} : (∀ g ∈ F, InterpConsts.toBool g = some false) →
      F.length + 1 = T.length → InterpConsts.toBool w = some true →
      CS .popRight A (F ++ w :: A) T []
  /-- Nothing in flight, waiting for a new value. -/
  | idle {A : List V} : CS .popLeft A A [] []
  /-- The steer read a true decider not yet read by the carry. -/
  | aheadT {w : V} {D : List V} {x : V} : InterpConsts.toBool w = some true →
      CS .decider (w :: D) D [] [x]
  /-- The steer read a false decider not yet read by the carry. -/
  | aheadF {w : V} {D : List V} : InterpConsts.toBool w = some false →
      CS .decider (w :: D) D [] []
  /-- The carry waits for the token on `r`. -/
  | wait {A : List V} {x : V} : CS .popRight A A [] [x]

/-- Rewritten state (inv state `c`, inv deciders `U`, pending inputs `Pend` on `l`) relative
to the steer deciders `D`, `sIn` (`O1`), `o` (`O`) and `r` (`Rr`). Either the inv has
processed the last token forked so far (and the next token starts a new iteration), or
the next token is a continuation of the value stored in the inv. -/
def Mode (c : Option V) (U Pend D O1 O Rr : List V) : Prop :=
  (c = O1.getLast? ∧ U = D.drop (O1.length - 1) ∧ Pend = O ∧ Rr = []) ∨
  (O1 = [] ∧ ∃ x w, c = some x ∧ U = w :: D ∧ InterpConsts.toBool w = some true ∧
    Rr ++ O = x :: Pend)

theorem CS.rr_nil {st : AsyncOp.MergeState} {A D T Rr : List V}
    (h : CS st A D T Rr) (hT : T ≠ []) : Rr = [] := by
  cases h <;> first | rfl | exact absurd rfl hT

theorem CS.len_le {st : AsyncOp.MergeState} {A D T Rr : List V}
    (h : CS st A D T Rr) : T.length ≤ D.length + 1 := by
  cases h with
  | dec _ hlen => simp only [List.length_append]; omega
  | left _ hlen _ => simp only [List.length_append, List.length_cons]; omega
  | right _ hlen _ => simp only [List.length_append, List.length_cons]; omega
  | idle => simp
  | aheadT _ => simp
  | aheadF _ => simp
  | wait => simp

theorem CS.popLeft {A D O1 O Rr : List V} {v : V}
    (h : CS .popLeft A D (O1 ++ O) Rr) : CS .decider A D (O1 ++ (O ++ [v])) Rr := by
  rw [← List.append_assoc]
  generalize O1 ++ O = T at h
  cases h with
  | @left F _ _ w hF hlen hw =>
    rw [List.append_cons]
    refine .dec ?_ ?_
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hF g hg
      · exact hw
    · simp only [List.length_append, List.length_singleton] at hlen ⊢
      omega
  | idle => exact .dec (F := []) (by simp) (by simp)

theorem CS.decider {A A' D T Rr : List V} {w : V} {b : Bool}
    (h : CS .decider A D T Rr) (hA : A = w :: A') (hw : InterpConsts.toBool w = some b) :
    CS (if b then .popRight else .popLeft) A' D T Rr := by
  cases h with
  | @dec F _ _ hF hlen =>
    subst hA
    cases b
    · exact .left hF hlen hw
    · exact .right hF hlen hw
  | @aheadT w' D' x hw' =>
    simp only [List.cons.injEq] at hA
    obtain ⟨rfl, rfl⟩ := hA
    rw [hw'] at hw
    cases hw
    exact .wait
  | @aheadF w' D' hw' =>
    simp only [List.cons.injEq] at hA
    obtain ⟨rfl, rfl⟩ := hA
    rw [hw'] at hw
    cases hw
    exact .idle

theorem CS.popRight {A D T Rr Rr' : List V} {x : V}
    (h : CS .popRight A D T Rr) (hR : Rr = x :: Rr') :
    T = [] ∧ Rr' = [] ∧ CS .decider A D [x] [] := by
  cases h with
  | right => cases hR
  | @wait _ x' =>
    simp only [List.cons.injEq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    exact ⟨rfl, rfl, .dec (F := []) (by simp) (by simp)⟩

theorem CS.push {st : AsyncOp.MergeState} {A D T Rr : List V} {v : V}
    (h : CS st A D T Rr) : CS st (A ++ [v]) (D ++ [v]) T Rr := by
  cases h with
  | dec hF hlen => rw [List.append_assoc]; exact .dec hF hlen
  | left hF hlen hw => rw [List.append_assoc, List.cons_append]; exact .left hF hlen hw
  | right hF hlen hw => rw [List.append_assoc, List.cons_append]; exact .right hF hlen hw
  | idle => exact .idle
  | aheadT hw => rw [List.cons_append]; exact .aheadT hw
  | aheadF hw => rw [List.cons_append]; exact .aheadF hw
  | wait => exact .wait

theorem CS.steer_false {st : AsyncOp.MergeState} {A D D' T' Rr : List V} {t w : V}
    (h : CS st A D (t :: T') Rr) (hD : D = w :: D')
    (hw : InterpConsts.toBool w = some false) : CS st A D' T' Rr := by
  cases h with
  | @dec F _ _ hF hlen =>
    cases F with
    | nil =>
      obtain rfl : T' = [] := List.length_eq_zero_iff.mp
        (by simp only [List.length_nil, List.length_cons] at hlen; omega)
      simp only [List.nil_append] at hD
      subst hD
      exact .aheadF hw
    | cons g F =>
      simp only [List.cons_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact .dec (λ g' hg' => hF g' (List.mem_cons_of_mem _ hg')) (by simp at hlen ⊢; omega)
  | @left F _ _ w' hF hlen hw' =>
    cases F with
    | nil =>
      obtain rfl : T' = [] := List.length_eq_zero_iff.mp
        (by simp only [List.length_nil, List.length_cons] at hlen; omega)
      simp only [List.nil_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact .idle
    | cons g F =>
      simp only [List.cons_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact .left (λ g' hg' => hF g' (List.mem_cons_of_mem _ hg')) (by simp at hlen ⊢; omega) hw'
  | @right F _ _ w' hF hlen hw' =>
    cases F with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      rw [hw'] at hw
      cases hw
    | cons g F =>
      simp only [List.cons_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact .right (λ g' hg' => hF g' (List.mem_cons_of_mem _ hg')) (by simp at hlen ⊢; omega) hw'

theorem CS.steer_true {st : AsyncOp.MergeState} {A D D' T' Rr : List V} {t w : V}
    (h : CS st A D (t :: T') Rr) (hD : D = w :: D')
    (hw : InterpConsts.toBool w = some true) : T' = [] ∧ Rr = [] ∧ CS st A D' [] [t] := by
  cases h with
  | @dec F _ _ hF hlen =>
    cases F with
    | nil =>
      obtain rfl : T' = [] := List.length_eq_zero_iff.mp
        (by simp only [List.length_nil, List.length_cons] at hlen; omega)
      simp only [List.nil_append] at hD
      subst hD
      exact ⟨rfl, rfl, .aheadT hw⟩
    | cons g F =>
      simp only [List.cons_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      have := hF g (by simp)
      rw [hw] at this
      cases this
  | @left F _ _ w' hF hlen hw' =>
    cases F with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      rw [hw'] at hw
      cases hw
    | cons g F =>
      simp only [List.cons_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      have := hF g (by simp)
      rw [hw] at this
      cases this
  | @right F _ _ w' hF hlen hw' =>
    cases F with
    | nil =>
      obtain rfl : T' = [] := List.length_eq_zero_iff.mp
        (by simp only [List.length_nil, List.length_cons] at hlen; omega)
      simp only [List.nil_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact ⟨rfl, rfl, .wait⟩
    | cons g F =>
      simp only [List.cons_append, List.cons.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      have := hF g (by simp)
      rw [hw] at this
      cases this

theorem drop_false {F R : List V} {k : Nat} (hk : k < F.length)
    (hF : ∀ g ∈ F, InterpConsts.toBool g = some false) :
    ∃ u, (F ++ R).drop k = u :: (F ++ R).drop (k + 1) ∧ InterpConsts.toBool u = some false := by
  refine ⟨F[k], ?_, hF _ (List.getElem_mem hk)⟩
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp [List.getElem_append_left hk]

/-- If the fork is ahead of the steer and fires again, the next inv decider is false. -/
theorem CS.fork_false {st : AsyncOp.MergeState} {A D Rr O1 O' : List V} {v : V}
    (h : CS st A D (O1 ++ v :: O') Rr) (hne : O1 ≠ []) :
    ∃ u, D.drop (O1.length - 1) = u :: D.drop O1.length ∧
      InterpConsts.toBool u = some false := by
  have hpos := List.length_pos_iff.mpr hne
  have hO1 : O1.length - 1 + 1 = O1.length := by omega
  generalize hT : O1 ++ v :: O' = T at h
  cases h with
  | dec hF hlen =>
    subst hT
    have := drop_false (R := A) (k := O1.length - 1) (by simp at hlen; omega) hF
    rwa [hO1] at this
  | @left F _ _ w hF hlen _ =>
    subst hT
    have := drop_false (R := w :: A) (k := O1.length - 1) (by simp at hlen; omega) hF
    rwa [hO1] at this
  | @right F _ _ w hF hlen _ =>
    subst hT
    have := drop_false (R := w :: A) (k := O1.length - 1) (by simp at hlen; omega) hF
    rwa [hO1] at this
  | idle => simp at hT
  | aheadT => simp at hT
  | aheadF => simp at hT
  | wait => simp at hT

theorem Mode.popLeft {c : Option V} {U Pend D O1 O Rr : List V} {v : V}
    (h : Mode c U Pend D O1 O Rr) : Mode c U (Pend ++ [v]) D O1 (O ++ [v]) Rr := by
  rcases h with ⟨h1, h2, rfl, h4⟩ | ⟨h1, x, w, h2, h3, h4, h5⟩
  · exact .inl ⟨h1, h2, rfl, h4⟩
  · refine .inr ⟨h1, x, w, h2, h3, h4, ?_⟩
    rw [← List.append_assoc, h5]
    rfl

theorem Mode.popRight {c : Option V} {A U Pend D O1 O Rr Rr' : List V} {x : V}
    (hcs : CS .popRight A D (O1 ++ O) Rr) (hm : Mode c U Pend D O1 O Rr) (hR : Rr = x :: Rr') :
    CS .decider A D (O1 ++ (O ++ [x])) Rr' ∧ Mode c U Pend D O1 (O ++ [x]) Rr' := by
  obtain ⟨hT, rfl, hcs'⟩ := hcs.popRight hR
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hT
  refine ⟨by simpa using hcs', ?_⟩
  rcases hm with ⟨-, -, -, h4⟩ | ⟨h1, x', w, h2, h3, h4, h5⟩
  · rw [hR] at h4
    cases h4
  · subst hR
    simp only [List.append_nil, List.cons.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    exact .inr ⟨h1, x, w, h2, h3, h4, rfl⟩

theorem Mode.push {st : AsyncOp.MergeState} {c : Option V} {A U Pend D O1 O Rr : List V} {v : V}
    (hcs : CS st A D (O1 ++ O) Rr) (hm : Mode c U Pend D O1 O Rr) :
    Mode c (U ++ [v]) Pend (D ++ [v]) O1 O Rr := by
  rcases hm with ⟨h1, rfl, h3, h4⟩ | ⟨h1, x, w, h2, rfl, h3, h4⟩
  · refine .inl ⟨h1, ?_, h3, h4⟩
    have := hcs.len_le
    simp only [List.length_append] at this
    rw [List.drop_append_of_le_length (by omega)]
  · exact .inr ⟨h1, x, w, h2, rfl, h3, h4⟩

/-- The fork fires: either the inv inits, or reads a false decider and then inits,
or reads a true decider. -/
theorem fork_cases {st : AsyncOp.MergeState} {c : Option V} {A U Pend D O1 O' Rr : List V}
    {v : V} (hcs : CS st A D (O1 ++ v :: O') Rr) (hm : Mode c U Pend D O1 (v :: O') Rr) :
    (c = none ∧ Pend = v :: O' ∧ Mode (some v) U O' D (O1 ++ [v]) O' Rr) ∨
    (∃ x u U', c = some x ∧ U = u :: U' ∧ InterpConsts.toBool u = some false ∧
      Pend = v :: O' ∧ Mode (some v) U' O' D (O1 ++ [v]) O' Rr) ∨
    (∃ u U', c = some v ∧ U = u :: U' ∧ InterpConsts.toBool u = some true ∧
      Pend = O' ∧ Mode (some v) U' O' D (O1 ++ [v]) O' Rr) := by
  have hRr := hcs.rr_nil (by simp)
  rcases hm with ⟨h1, h2, h3, h4⟩ | ⟨h1, x, w, h2, h3, h4, h5⟩
  · by_cases hO1 : O1 = []
    · subst hO1
      refine .inl ⟨by simpa using h1, h3, .inl ⟨by simp, by simpa using h2, rfl, h4⟩⟩
    · obtain ⟨u, hu, hfalse⟩ := hcs.fork_false hO1
      obtain ⟨x, hx⟩ : ∃ x, O1.getLast? = some x := by
        cases h : O1.getLast? with
        | none => simp at h; exact absurd h hO1
        | some x => exact ⟨x, rfl⟩
      refine .inr (.inl ⟨x, u, D.drop O1.length, by rw [h1, hx], by rw [h2, hu], hfalse, h3,
        .inl ⟨by simp, by simp, rfl, h4⟩⟩)
  · subst h1
    simp only [hRr, List.nil_append, List.cons.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    exact .inr (.inr ⟨w, D, h2, h3, h4, rfl, .inl ⟨by simp, by simp, rfl, hRr⟩⟩)

/-- The steer drops a token and more forked tokens remain. -/
theorem steer_false_cont {c : Option V}
    {U Pend D D' O1' O Rr : List V} {t w : V}
    (hm : Mode c U Pend D (t :: O1') O Rr) (hD : D = w :: D') (hne : O1' ≠ []) :
    Mode c U Pend D' O1' O Rr := by
  rcases hm with ⟨h1, h2, h3, h4⟩ | ⟨h1, -⟩
  · obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    refine .inl ⟨by simpa using h1, ?_, h3, h4⟩
    rw [h2, hD]
    simp
  · exact absurd h1 (List.cons_ne_nil _ _)

/-- The steer drops the last forked token: the inv reads the false decider. -/
theorem steer_false_last {c : Option V} {U Pend D D' O Rr : List V} {t w : V}
    (hm : Mode c U Pend D [t] O Rr) (hD : D = w :: D') :
    c = some t ∧ U = w :: D' ∧ Mode none D' Pend D' [] O Rr := by
  rcases hm with ⟨h1, h2, h3, h4⟩ | ⟨h1, -⟩
  · exact ⟨by simpa using h1, by simpa [hD] using h2, .inl ⟨rfl, by simp, h3, h4⟩⟩
  · simp at h1

/-- The steer passes the last token to `r`. -/
theorem steer_true_last {c : Option V} {U Pend D D' : List V} {t w : V}
    (hm : Mode c U Pend D [t] [] []) (hD : D = w :: D')
    (hw : InterpConsts.toBool w = some true) :
    Mode c U Pend D' [] [] [t] := by
  rcases hm with ⟨h1, h2, h3, -⟩ | ⟨h1, -⟩
  · exact .inr ⟨rfl, t, w, by simpa using h1, by simpa [hD] using h2, hw, by simp [h3]⟩
  · simp at h1

theorem Mode.init_inv {c : Option V} {U Pend : List V}
    (hm : Mode c U Pend [] [] [] []) : c = none ∧ U = [] ∧ Pend = [] := by
  rcases hm with ⟨h1, h2, h3, -⟩ | ⟨-, x, w, -, -, -, h5⟩
  · exact ⟨h1, by simpa using h2, h3⟩
  · simp at h5

end Pure

section Chans

variable {χ : Type*} {V : Type*} [DecidableEq χ]

theorem pop_one {chans chans' : ChanMap χ V} {x : χ} {v : V}
    (h : ∀ y, chans y = ChanMap.pushed [x] [v] y ++ chans' y) :
    ∃ rest, chans x = v :: rest ∧ chans' = Function.update chans x rest := by
  refine ⟨chans' x, by simpa using h x, ?_⟩
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · have := h y
    simp [Ne.symm hy] at this
    simp [Function.update_of_ne hy, this]

theorem pop_if {chans chans' : ChanMap χ V} {x : χ} {v : V}
    (h : ∀ y, chans y = (if y = x then [v] else []) ++ chans' y) :
    ∃ rest, chans x = v :: rest ∧ chans' = Function.update chans x rest := by
  refine ⟨chans' x, by simpa using h x, ?_⟩
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · have := h y
    simp [hy] at this
    simp [Function.update_of_ne hy, this]

theorem pop_two {chans chans' : ChanMap χ V} {x₁ x₂ : χ} {v₁ v₂ : V} (hne : x₁ ≠ x₂)
    (h : ∀ y, chans y = ChanMap.pushed [x₁, x₂] [v₁, v₂] y ++ chans' y) :
    ∃ rest₁ rest₂, chans x₁ = v₁ :: rest₁ ∧ chans x₂ = v₂ :: rest₂ ∧
      chans' = Function.update (Function.update chans x₁ rest₁) x₂ rest₂ := by
  refine ⟨chans' x₁, chans' x₂, by simpa [Ne.symm hne] using h x₁, by simpa [hne] using h x₂, ?_⟩
  funext y
  by_cases hy₂ : y = x₂
  · subst hy₂; simp
  · by_cases hy₁ : y = x₁
    · subst hy₁; simp [Function.update_of_ne hy₂]
    · have := h y
      simp [Ne.symm hy₁, Ne.symm hy₂] at this
      simp [Function.update_of_ne hy₁, Function.update_of_ne hy₂, this]

theorem pushed_eq_singleton {names : List χ} {vals : List V} {y : χ} {v : V}
    (hnd : names.Nodup) (hlen : names.length = vals.length) (hy : y ∈ names)
    (hv : ∀ w ∈ vals, w = v) : ChanMap.pushed names vals y = [v] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons w vals =>
      rw [ChanMap.pushed_cons]
      have hw := hv w (by simp)
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      by_cases hxy : x = y
      · subst hxy
        rw [ChanMap.pushed_not_mem hx]
        simp [hw]
      · have hy' : y ∈ names := by
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact hy
        rw [if_neg hxy, ih hnd' (by simpa using hlen) hy' (λ w' hw' => hv w' (by simp [hw']))]
        simp

end Chans

section Atoms

variable {Op : Type*} {χ : Type*} {V : Type*} [Arity Op] [DecidableEq χ] [InterpConsts V]

/-- The replacement atoms (with the current inv state). -/
abbrev rwAtoms (d l ext d'' : χ) (c : Option V) : AtomicProcs Op χ V :=
  [.async (.inv true c) [d, l] [ext], .async (.sink 1) [d''] []]

/-- The matched atoms (with the current carry state). -/
abbrev origAtoms (d l r o sIn d'' : χ) (fouts : List χ) (st : AsyncOp.MergeState) :
    AtomicProcs Op χ V :=
  [.async (.steer true 1) [d'', sIn] [r], .async (.fork 2) [o] fouts,
    .async (.merge st 1) [d, l, r] [o]]

theorem tau_sink {d l ext d'' : χ} {c : Option V} {chans : ChanMap χ V} {w : V}
    {rest : List V} (h : chans d'' = w :: rest) :
    LocalTauStar (rwAtoms (Op := Op) d l ext d'' c) chans (rwAtoms d l ext d'' c)
      (Function.update chans d'' rest) := by
  have := LocalTauStar.async_list_mem (L := rwAtoms (Op := Op) d l ext d'' c)
    (aop := .sink 1) (allInputs := [d'']) (allOutputs := [])
    (inputs := [d'']) (inputVals := [w]) (outputs := []) (outputVals := [])
    (chans := chans) (chans' := Function.update chans d'' rest)
    (by simp) (.interp_sink rfl) rfl rfl (by
      intro y
      by_cases hy : y = d''
      · subst hy; simp [h]
      · simp [Function.update_of_ne hy, Ne.symm hy])
  exact this.eq_rhs rfl (by funext y; simp)

theorem tau_inv_init {d l ext d'' : χ} {chans : ChanMap χ V} {v : V} {rest : List V}
    (h : chans l = v :: rest) (hclone : InterpConsts.isClonable v) :
    LocalTauStar (rwAtoms (Op := Op) d l ext d'' none) chans (rwAtoms d l ext d'' (some v))
      (λ y => Function.update chans l rest y ++ ChanMap.pushed [ext] [v] y) :=
  LocalTauStar.async_list (L := rwAtoms (Op := Op) d l ext d'' none) (i := 0)
    (aop := .inv true none) (aop' := .inv true (some v))
    (allInputs := [d, l]) (allOutputs := [ext])
    (inputs := [l]) (inputVals := [v]) (outputs := [ext]) (outputVals := [v])
    (chans := chans) (chans' := Function.update chans l rest)
    rfl (.interp_inv_init rfl rfl hclone) rfl rfl (by
      intro y
      by_cases hy : y = l
      · subst hy; simp [h]
      · simp [Function.update_of_ne hy, Ne.symm hy])

theorem tau_inv_true {d l ext d'' : χ} {chans : ChanMap χ V} {x w : V} {rest : List V}
    (h : chans d = w :: rest) (hw : InterpConsts.toBool w = some true) :
    LocalTauStar (rwAtoms (Op := Op) d l ext d'' (some x)) chans (rwAtoms d l ext d'' (some x))
      (λ y => Function.update chans d rest y ++ ChanMap.pushed [ext] [x] y) :=
  LocalTauStar.async_list (L := rwAtoms (Op := Op) d l ext d'' (some x)) (i := 0)
    (aop := .inv true (some x)) (aop' := .inv true (some x))
    (allInputs := [d, l]) (allOutputs := [ext])
    (inputs := [d]) (inputVals := [w]) (outputs := [ext]) (outputVals := [x])
    (chans := chans) (chans' := Function.update chans d rest)
    rfl (.interp_inv_true rfl rfl hw rfl) rfl rfl (by
      intro y
      by_cases hy : y = d
      · subst hy; simp [h]
      · simp [Function.update_of_ne hy, Ne.symm hy])

theorem tau_inv_false {d l ext d'' : χ} {chans : ChanMap χ V} {x w : V} {rest : List V}
    (h : chans d = w :: rest) (hw : InterpConsts.toBool w = some false) :
    LocalTauStar (rwAtoms (Op := Op) d l ext d'' (some x)) chans (rwAtoms d l ext d'' none)
      (Function.update chans d rest) := by
  have := LocalTauStar.async_list (L := rwAtoms (Op := Op) d l ext d'' (some x)) (i := 0)
    (aop := .inv true (some x)) (aop' := .inv true none)
    (allInputs := [d, l]) (allOutputs := [ext])
    (inputs := [d]) (inputVals := [w]) (outputs := []) (outputVals := [])
    (chans := chans) (chans' := Function.update chans d rest)
    rfl (.interp_inv_false rfl rfl hw (by decide)) rfl rfl (by
      intro y
      by_cases hy : y = d
      · subst hy; simp [h]
      · simp [Function.update_of_ne hy, Ne.symm hy])
  exact this.eq_rhs rfl (by funext y; simp)

/-- Distinctness of the channel names (all distinct, except possibly `ext = l`). -/
structure Distinct (d l r o sIn ext d'' : χ) : Prop where
  dl : d ≠ l
  dr : d ≠ r
  dO : d ≠ o
  dd : d ≠ d''
  ds : d ≠ sIn
  de : d ≠ ext
  lr : l ≠ r
  lo : l ≠ o
  ld : l ≠ d''
  ls : l ≠ sIn
  ro : r ≠ o
  rd : r ≠ d''
  rs : r ≠ sIn
  re : r ≠ ext
  od : o ≠ d''
  os : o ≠ sIn
  oe : o ≠ ext
  ds'' : d'' ≠ sIn
  de'' : d'' ≠ ext
  se : sIn ≠ ext

/-- `simp` with the distinctness facts `hdl`, ... (as obtained from `Distinct`) in scope. -/
local syntax "simp_ne" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

set_option hygiene false in
local macro_rules
  | `(tactic| simp_ne) => `(tactic| simp_ne [])
  | `(tactic| simp_ne [$args,*]) => `(tactic| simp [Function.update_apply,
      hdl, hdl.symm, hdr, hdr.symm, hdo, hdo.symm, hdd, hdd.symm, hds, hds.symm, hde, hde.symm,
      hlr, hlr.symm, hlo, hlo.symm, hld, hld.symm, hls, hls.symm, hro, hro.symm, hrd, hrd.symm,
      hrs, hrs.symm, hre, hre.symm, hod, hod.symm, hos, hos.symm, hoe, hoe.symm,
      hds'', hds''.symm, hde'', hde''.symm, hse, hse.symm, $args,*])

/-- The simulation relation. -/
def Rel (d l r o sIn ext d'' : χ) (fouts : List χ)
    (L₀ : AtomicProcs Op χ V) (chans₀ : ChanMap χ V)
    (L₁ : AtomicProcs Op χ V) (chans₁ : ChanMap χ V) : Prop :=
  ∃ st c Pend,
    L₀ = origAtoms d l r o sIn d'' fouts st ∧
    L₁ = rwAtoms d l ext d'' c ∧
    (∀ y, y ≠ d → y ≠ l → y ≠ o → y ≠ sIn → y ≠ r → chans₁ y = chans₀ y) ∧
    chans₁ o = [] ∧ chans₁ sIn = [] ∧ chans₁ r = [] ∧
    chans₁ l = Pend ++ chans₀ l ∧
    CS st (chans₀ d) (chans₀ d'') (chans₀ sIn ++ chans₀ o) (chans₀ r) ∧
    Mode c (chans₁ d) Pend (chans₀ d'') (chans₀ sIn) (chans₀ o) (chans₀ r)

omit [DecidableEq χ] in
theorem Rel.intro {d l r o sIn ext d'' : χ} {fouts : List χ}
    {chans₀ chans₁ : ChanMap χ V} {st : AsyncOp.MergeState} {c : Option V}
    {Pend A D O1 O Rr U : List V}
    (hC1 : ∀ y, y ≠ d → y ≠ l → y ≠ o → y ≠ sIn → y ≠ r → chans₁ y = chans₀ y)
    (ho : chans₁ o = []) (hs : chans₁ sIn = []) (hr : chans₁ r = [])
    (hl : chans₁ l = Pend ++ chans₀ l)
    (e_d : chans₀ d = A) (e_d'' : chans₀ d'' = D) (e_s : chans₀ sIn = O1)
    (e_o : chans₀ o = O) (e_r : chans₀ r = Rr) (e_U : chans₁ d = U)
    (hcs : CS st A D (O1 ++ O) Rr) (hm : Mode c U Pend D O1 O Rr) :
    Rel (Op := Op) d l r o sIn ext d'' fouts (origAtoms d l r o sIn d'' fouts st) chans₀
      (rwAtoms d l ext d'' c) chans₁ := by
  subst e_d e_d'' e_s e_o e_r e_U
  exact ⟨st, c, Pend, rfl, rfl, hC1, ho, hs, hr, hl, hcs, hm⟩

/-- The carry fires: nothing happens on the rewritten side. -/
theorem step_carry {d l r o sIn ext d'' : χ} {fouts : List χ}
    (hN : Distinct d l r o sIn ext d'')
    {chans₀ chans₁ chans₀' : ChanMap χ V} {st : AsyncOp.MergeState} {c : Option V}
    {Pend : List V} {aop' : AsyncOp V} {inputs outputs : List χ} {inputVals outputVals : List V}
    (hC1 : ∀ y, y ≠ d → y ≠ l → y ≠ o → y ≠ sIn → y ≠ r → chans₁ y = chans₀ y)
    (ho : chans₁ o = []) (hs : chans₁ sIn = []) (hr : chans₁ r = [])
    (hl : chans₁ l = Pend ++ chans₀ l)
    (hcs : CS st (chans₀ d) (chans₀ d'') (chans₀ sIn ++ chans₀ o) (chans₀ r))
    (hm : Mode c (chans₁ d) Pend (chans₀ d'') (chans₀ sIn) (chans₀ o) (chans₀ r))
    (hinterp : (AsyncOp.merge st 1).Interp
      (.mk [d, l, r] [o] inputs inputVals outputs outputVals) aop')
    (hlen₁ : inputs.length = inputVals.length)
    (hpop : ∀ y, chans₀ y = ChanMap.pushed inputs inputVals y ++ chans₀' y) :
    ∃ L₁' chans₁', LocalTauStar (rwAtoms (Op := Op) d l ext d'' c) chans₁ L₁' chans₁' ∧
      Rel d l r o sIn ext d'' fouts
        ((origAtoms d l r o sIn d'' fouts st).set 2 (.async aop' [d, l, r] [o]))
        (λ y => chans₀' y ++ ChanMap.pushed outputs outputVals y) L₁' chans₁' := by
  obtain ⟨hdl, hdr, hdo, hdd, hds, hde, hlr, hlo, hld, hls, hro, hrd, hrs, hre, hod, hos, hoe,
    hds'', hde'', hse⟩ := hN
  rcases hinterp.merge_inv hlen₁ with
    ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, v, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, w, b, rfl, hb, rfl⟩
  · -- popLeft
    obtain ⟨rest, hl0, rfl⟩ := pop_one hpop
    refine ⟨_, _, .refl, Rel.intro (st := .decider) (c := c) (Pend := Pend ++ [v])
      (A := chans₀ d) (D := chans₀ d'') (O1 := chans₀ sIn) (O := chans₀ o ++ [v])
      (Rr := chans₀ r) (U := chans₁ d) ?_ ho hs hr ?_ (by simp_ne) (by simp_ne) (by simp_ne)
      (by simp_ne) (by simp_ne) rfl hcs.popLeft hm.popLeft⟩
    · intro y hyd hyl hyo hys hyr
      simp_ne [hyl, Ne.symm hyo, hC1 y hyd hyl hyo hys hyr]
    · simp_ne [hl, hl0]
  · -- popRight
    obtain ⟨rest, hr0, rfl⟩ := pop_one hpop
    rw [hr0] at hcs hm
    obtain ⟨hcs', hm'⟩ := Mode.popRight hcs hm rfl
    refine ⟨_, _, .refl, Rel.intro (st := .decider) (c := c) (Pend := Pend)
      (A := chans₀ d) (D := chans₀ d'') (O1 := chans₀ sIn) (O := chans₀ o ++ [v])
      (Rr := rest) (U := chans₁ d) ?_ ho hs hr ?_ (by simp_ne) (by simp_ne) (by simp_ne)
      (by simp_ne) (by simp_ne) rfl hcs' hm'⟩
    · intro y hyd hyl hyo hys hyr
      simp_ne [hyr, Ne.symm hyo, hC1 y hyd hyl hyo hys hyr]
    · simp_ne [hl]
  · -- decider
    obtain ⟨rest, hd0, rfl⟩ := pop_one hpop
    refine ⟨_, _, .refl, Rel.intro (st := if b then .popRight else .popLeft) (c := c)
      (Pend := Pend) (A := rest) (D := chans₀ d'') (O1 := chans₀ sIn) (O := chans₀ o)
      (Rr := chans₀ r) (U := chans₁ d) ?_ ho hs hr ?_ (by simp_ne) (by simp_ne) (by simp_ne)
      (by simp_ne) (by simp_ne) rfl (hcs.decider hd0 hb) hm⟩
    · intro y hyd hyl hyo hys hyr
      simp_ne [hyd, hC1 y hyd hyl hyo hys hyr]
    · simp_ne [hl]

/-- The fork fires: the inv outputs the same value. -/
theorem step_fork {d l r o sIn ext d'' : χ} {fouts : List χ}
    (hN : Distinct d l r o sIn ext d'')
    (hpushF : ∀ (v : V) y, ChanMap.pushed fouts [v, v] y =
      (if sIn = y then [v] else []) ++ (if ext = y then [v] else []))
    {chans₀ chans₁ chans₀' : ChanMap χ V} {st : AsyncOp.MergeState} {c : Option V}
    {Pend : List V} {aop' : AsyncOp V} {inputs outputs : List χ} {inputVals outputVals : List V}
    (hC1 : ∀ y, y ≠ d → y ≠ l → y ≠ o → y ≠ sIn → y ≠ r → chans₁ y = chans₀ y)
    (ho : chans₁ o = []) (hs : chans₁ sIn = []) (hr : chans₁ r = [])
    (hl : chans₁ l = Pend ++ chans₀ l)
    (hcs : CS st (chans₀ d) (chans₀ d'') (chans₀ sIn ++ chans₀ o) (chans₀ r))
    (hm : Mode c (chans₁ d) Pend (chans₀ d'') (chans₀ sIn) (chans₀ o) (chans₀ r))
    (hinterp : (AsyncOp.fork 2).Interp
      (.mk [o] fouts inputs inputVals outputs outputVals) aop')
    (hlen₁ : inputs.length = inputVals.length)
    (hpop : ∀ y, chans₀ y = ChanMap.pushed inputs inputVals y ++ chans₀' y) :
    ∃ L₁' chans₁', LocalTauStar (rwAtoms (Op := Op) d l ext d'' c) chans₁ L₁' chans₁' ∧
      Rel d l r o sIn ext d'' fouts
        ((origAtoms d l r o sIn d'' fouts st).set 1 (.async aop' [o] fouts))
        (λ y => chans₀' y ++ ChanMap.pushed outputs outputVals y) L₁' chans₁' := by
  obtain ⟨hdl, hdr, hdo, hdd, hds, hde, hlr, hlo, hld, hls, hro, hrd, hrs, hre, hod, hos, hoe,
    hds'', hde'', hse⟩ := hN
  obtain ⟨rfl, rfl, rfl, -, v, rfl, hclone, rfl⟩ := hinterp.fork_inv hlen₁
  obtain ⟨O', ho0, rfl⟩ := pop_one hpop
  rw [ho0] at hcs hm
  have hcs' : CS st (chans₀ d) (chans₀ d'') ((chans₀ sIn ++ [v]) ++ O') (chans₀ r) := by
    simpa using hcs
  rcases fork_cases hcs hm with ⟨rfl, hP, hm'⟩ | ⟨x, u, U', rfl, hU, hu, hP, hm'⟩ |
    ⟨u, U', rfl, hU, hu, hP, hm'⟩
  · -- the inv inits
    have hl1 : chans₁ l = v :: (O' ++ chans₀ l) := by rw [hl, hP]; rfl
    refine ⟨_, _, tau_inv_init hl1 hclone, Rel.intro (st := st) (c := some v) (Pend := O')
      (A := chans₀ d) (D := chans₀ d'') (O1 := chans₀ sIn ++ [v]) (O := O')
      (Rr := chans₀ r) (U := chans₁ d) ?_ ?_ ?_ ?_ ?_ (by simp_ne [hpushF]) (by simp_ne [hpushF])
      (by simp_ne [hpushF]) (by simp_ne [hpushF]) (by simp_ne [hpushF]) (by simp_ne) hcs' hm'⟩
    · intro y hyd hyl hyo hys hyr
      simp_ne [hpushF, hyd, hyl, hyo, hys, hyr, Ne.symm hyd, Ne.symm hyl, Ne.symm hyo,
        Ne.symm hys, Ne.symm hyr, hC1 y hyd hyl hyo hys hyr]
    · simp_ne [ho]
    · simp_ne [hs]
    · simp_ne [hr]
    · simp_ne [hpushF]
  · -- the inv reads a false decider, then inits
    have step₁ := tau_inv_false (Op := Op) (l := l) (ext := ext) (d'' := d'') (x := x) hU hu
    have hl1 : Function.update chans₁ d U' l = v :: (O' ++ chans₀ l) := by
      simp_ne [hl, hP]
    have step₂ := tau_inv_init (Op := Op) (d := d) (ext := ext) (d'' := d'') hl1 hclone
    refine ⟨_, _, step₁.trans step₂, Rel.intro (st := st) (c := some v) (Pend := O')
      (A := chans₀ d) (D := chans₀ d'') (O1 := chans₀ sIn ++ [v]) (O := O')
      (Rr := chans₀ r) (U := U') ?_ ?_ ?_ ?_ ?_ (by simp_ne [hpushF]) (by simp_ne [hpushF])
      (by simp_ne [hpushF]) (by simp_ne [hpushF]) (by simp_ne [hpushF]) (by simp_ne) hcs' hm'⟩
    · intro y hyd hyl hyo hys hyr
      simp_ne [hpushF, hyd, hyl, hyo, hys, hyr, Ne.symm hyd, Ne.symm hyl, Ne.symm hyo,
        Ne.symm hys, Ne.symm hyr, hC1 y hyd hyl hyo hys hyr]
    · simp_ne [ho]
    · simp_ne [hs]
    · simp_ne [hr]
    · simp_ne [hpushF]
  · -- the inv reads a true decider
    have step := tau_inv_true (Op := Op) (l := l) (ext := ext) (d'' := d'') (x := v) hU hu
    refine ⟨_, _, step, Rel.intro (st := st) (c := some v) (Pend := O')
      (A := chans₀ d) (D := chans₀ d'') (O1 := chans₀ sIn ++ [v]) (O := O')
      (Rr := chans₀ r) (U := U') ?_ ?_ ?_ ?_ ?_ (by simp_ne [hpushF]) (by simp_ne [hpushF])
      (by simp_ne [hpushF]) (by simp_ne [hpushF]) (by simp_ne [hpushF]) (by simp_ne) hcs' hm'⟩
    · intro y hyd hyl hyo hys hyr
      simp_ne [hpushF, hyd, hyl, hyo, hys, hyr, Ne.symm hyd, Ne.symm hyl, Ne.symm hyo,
        Ne.symm hys, Ne.symm hyr, hC1 y hyd hyl hyo hys hyr]
    · simp_ne [ho]
    · simp_ne [hs]
    · simp_ne [hr]
    · simp_ne [hpushF, hl, hP]

/-- The steer fires: the sink fires, and the inv reads the decider if it is false and
the steer dropped the last forked token. -/
theorem step_steer {d l r o sIn ext d'' : χ} {fouts : List χ}
    (hN : Distinct d l r o sIn ext d'')
    {chans₀ chans₁ chans₀' : ChanMap χ V} {st : AsyncOp.MergeState} {c : Option V}
    {Pend : List V} {aop' : AsyncOp V} {inputs outputs : List χ} {inputVals outputVals : List V}
    (hC1 : ∀ y, y ≠ d → y ≠ l → y ≠ o → y ≠ sIn → y ≠ r → chans₁ y = chans₀ y)
    (ho : chans₁ o = []) (hs : chans₁ sIn = []) (hr : chans₁ r = [])
    (hl : chans₁ l = Pend ++ chans₀ l)
    (hcs : CS st (chans₀ d) (chans₀ d'') (chans₀ sIn ++ chans₀ o) (chans₀ r))
    (hm : Mode c (chans₁ d) Pend (chans₀ d'') (chans₀ sIn) (chans₀ o) (chans₀ r))
    (hinterp : (AsyncOp.steer true 1).Interp
      (.mk [d'', sIn] [r] inputs inputVals outputs outputVals) aop')
    (hlen₁ : inputs.length = inputVals.length)
    (hpop : ∀ y, chans₀ y = ChanMap.pushed inputs inputVals y ++ chans₀' y) :
    ∃ L₁' chans₁', LocalTauStar (rwAtoms (Op := Op) d l ext d'' c) chans₁ L₁' chans₁' ∧
      Rel d l r o sIn ext d'' fouts
        ((origAtoms d l r o sIn d'' fouts st).set 0 (.async aop' [d'', sIn] [r]))
        (λ y => chans₀' y ++ ChanMap.pushed outputs outputVals y) L₁' chans₁' := by
  obtain ⟨hdl, hdr, hdo, hdd, hds, hde, hlr, hlo, hld, hls, hro, hrd, hrs, hre, hod, hos, hoe,
    hds'', hde'', hse⟩ := hN
  obtain ⟨rfl, rfl, w, t, b, rfl, hb, rfl, rfl⟩ := hinterp.steer_inv hlen₁
  obtain ⟨D', O1', hd0, hs0, rfl⟩ := pop_two hds'' hpop
  have hd1 : chans₁ d'' = w :: D' := by
    rw [hC1 d'' (Ne.symm hdd) (Ne.symm hld) (Ne.symm hod) hds'' (Ne.symm hrd)]
    exact hd0
  have hsink := tau_sink (Op := Op) (d := d) (l := l) (ext := ext) (c := c) hd1
  rw [hs0] at hcs hm
  cases b with
  | false =>
    have hcs' := CS.steer_false hcs hd0 hb
    by_cases hO1' : O1' = []
    · -- the steer dropped the last forked token: the inv reads the false decider
      subst hO1'
      obtain ⟨rfl, hU, hm'⟩ := steer_false_last hm hd0
      have hd1' : Function.update chans₁ d'' D' d = w :: D' := by simp_ne [hU]
      have hinv := tau_inv_false (Op := Op) (l := l) (ext := ext) (d'' := d'') (x := t) hd1' hb
      refine ⟨_, _, hsink.trans hinv, Rel.intro (st := st) (c := none) (Pend := Pend)
        (A := chans₀ d) (D := D') (O1 := []) (O := chans₀ o) (Rr := chans₀ r) (U := D')
        ?_ ?_ ?_ ?_ ?_ (by simp_ne) (by simp_ne) (by simp_ne) (by simp_ne) (by simp_ne)
        (by simp_ne) hcs' hm'⟩
      · intro y hyd hyl hyo hys hyr
        by_cases hyd'' : y = d''
        · subst hyd''
          simp_ne
        · simp_ne [hyd, hyl, hyo, hys, hyr, hyd'', Ne.symm hyd, Ne.symm hyl, Ne.symm hyo,
            Ne.symm hys, Ne.symm hyr, Ne.symm hyd'', hC1 y hyd hyl hyo hys hyr]
      · simp_ne [ho]
      · simp_ne [hs]
      · simp_ne [hr]
      · simp_ne [hl]
    · -- more forked tokens remain
      have hm' := steer_false_cont hm hd0 hO1'
      refine ⟨_, _, hsink, Rel.intro (st := st) (c := c) (Pend := Pend)
        (A := chans₀ d) (D := D') (O1 := O1') (O := chans₀ o) (Rr := chans₀ r) (U := chans₁ d)
        ?_ ?_ ?_ ?_ ?_ (by simp_ne) (by simp_ne) (by simp_ne) (by simp_ne) (by simp_ne)
        (by simp_ne) hcs' hm'⟩
      · intro y hyd hyl hyo hys hyr
        by_cases hyd'' : y = d''
        · subst hyd''
          simp_ne
        · simp_ne [hyd, hyl, hyo, hys, hyr, hyd'', Ne.symm hyd, Ne.symm hyl, Ne.symm hyo,
            Ne.symm hys, Ne.symm hyr, Ne.symm hyd'', hC1 y hyd hyl hyo hys hyr]
      · simp_ne [ho]
      · simp_ne [hs]
      · simp_ne [hr]
      · simp_ne [hl]
  | true =>
    obtain ⟨hT', hRr, hcs'⟩ := CS.steer_true hcs hd0 hb
    obtain ⟨rfl, ho0⟩ := List.append_eq_nil_iff.mp hT'
    rw [ho0, hRr] at hm
    have hm' := steer_true_last hm hd0 hb
    refine ⟨_, _, hsink, Rel.intro (st := st) (c := c) (Pend := Pend)
      (A := chans₀ d) (D := D') (O1 := []) (O := []) (Rr := [t]) (U := chans₁ d)
      ?_ ?_ ?_ ?_ ?_ (by simp_ne) (by simp_ne) (by simp_ne) (by simp_ne [ho0])
      (by simp_ne [hRr]) (by simp_ne) hcs' hm'⟩
    · intro y hyd hyl hyo hys hyr
      by_cases hyd'' : y = d''
      · subst hyd''
        simp_ne
      · simp_ne [hyd, hyl, hyo, hys, hyr, hyd'', Ne.symm hyd, Ne.symm hyl, Ne.symm hyo,
          Ne.symm hys, Ne.symm hyr, Ne.symm hyd'', hC1 y hyd hyl hyo hys hyr]
    · simp_ne [ho]
    · simp_ne [hs]
    · simp_ne [hr]
    · simp_ne [hl]

/-- The context pops a channel not read by the matched or the replacement atoms. -/
theorem frame_pop_rel {d l r o sIn ext d'' : χ} {fouts : List χ}
    {L₀ L₁ : AtomicProcs Op χ V} {chans₀ chans₁ chans₀' : ChanMap χ V} {x : χ} {v : V}
    (hx : x ≠ d ∧ x ≠ l ∧ x ≠ o ∧ x ≠ sIn ∧ x ≠ r ∧ x ≠ d'')
    (hR : Rel d l r o sIn ext d'' fouts L₀ chans₀ L₁ chans₁)
    (hpop : ∀ y, chans₀ y = (if y = x then [v] else []) ++ chans₀' y) :
    ∃ chans₁', (∀ y, chans₁ y = (if y = x then [v] else []) ++ chans₁' y) ∧
      Rel d l r o sIn ext d'' fouts L₀ chans₀' L₁ chans₁' := by
  obtain ⟨st, c, Pend, rfl, rfl, hC1, ho, hs, hr, hl, hcs, hm⟩ := hR
  obtain ⟨hxd, hxl, hxo, hxs, hxr, hxd''⟩ := hx
  obtain ⟨rest, hx0, rfl⟩ := pop_if hpop
  refine ⟨Function.update chans₁ x rest, ?_, Rel.intro (st := st) (c := c) (Pend := Pend)
    (A := chans₀ d) (D := chans₀ d'') (O1 := chans₀ sIn) (O := chans₀ o) (Rr := chans₀ r)
    (U := chans₁ d) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcs hm⟩
  · intro y
    by_cases hy : y = x
    · subst hy
      simp [hC1 _ hxd hxl hxo hxs hxr, hx0]
    · simp [hy]
  · intro y hyd hyl hyo hys hyr
    by_cases hy : y = x
    · subst hy; simp
    · simp [Function.update_of_ne hy, hC1 y hyd hyl hyo hys hyr]
  · simp [Function.update_of_ne (Ne.symm hxo), ho]
  · simp [Function.update_of_ne (Ne.symm hxs), hs]
  · simp [Function.update_of_ne (Ne.symm hxr), hr]
  · simp [Function.update_of_ne (Ne.symm hxl), hl]
  · simp [Function.update_of_ne (Ne.symm hxd)]
  · simp [Function.update_of_ne (Ne.symm hxd'')]
  · simp [Function.update_of_ne (Ne.symm hxs)]
  · simp [Function.update_of_ne (Ne.symm hxo)]
  · simp [Function.update_of_ne (Ne.symm hxr)]
  · simp [Function.update_of_ne (Ne.symm hxd)]

/-- The context pushes to channels not written by the matched or the replacement atoms
(the same values to `d` and `d''`). -/
theorem frame_push_rel {d l r o sIn ext d'' : χ} {fouts : List χ}
    {L₀ L₁ : AtomicProcs Op χ V} {chans₀ chans₁ : ChanMap χ V} {outs : List χ} {vals : List V}
    (hnot : o ∉ outs ∧ sIn ∉ outs ∧ r ∉ outs)
    (hdd : ∃ P : List V, ChanMap.pushed outs vals d = P ∧ ChanMap.pushed outs vals d'' = P ∧
      (P = [] ∨ ∃ v, P = [v]))
    (hR : Rel d l r o sIn ext d'' fouts L₀ chans₀ L₁ chans₁) :
    Rel d l r o sIn ext d'' fouts L₀ (λ y => chans₀ y ++ ChanMap.pushed outs vals y)
      L₁ (λ y => chans₁ y ++ ChanMap.pushed outs vals y) := by
  obtain ⟨st, c, Pend, rfl, rfl, hC1, ho, hs, hr, hl, hcs, hm⟩ := hR
  obtain ⟨ho', hs', hr'⟩ := hnot
  obtain ⟨P, hPd, hPd'', hP⟩ := hdd
  have hcs' : CS st (chans₀ d ++ P) (chans₀ d'' ++ P) (chans₀ sIn ++ chans₀ o) (chans₀ r) := by
    rcases hP with rfl | ⟨v, rfl⟩
    · simpa using hcs
    · exact hcs.push
  have hm' : Mode c (chans₁ d ++ P) Pend (chans₀ d'' ++ P) (chans₀ sIn) (chans₀ o) (chans₀ r) := by
    rcases hP with rfl | ⟨v, rfl⟩
    · simpa using hm
    · exact Mode.push hcs hm
  refine Rel.intro (st := st) (c := c) (Pend := Pend)
    (A := chans₀ d ++ P) (D := chans₀ d'' ++ P) (O1 := chans₀ sIn) (O := chans₀ o)
    (Rr := chans₀ r) (U := chans₁ d ++ P) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcs' hm'
  · intro y hyd hyl hyo hys hyr
    simp [hC1 y hyd hyl hyo hys hyr]
  · simp [ho, ChanMap.pushed_not_mem ho']
  · simp [hs, ChanMap.pushed_not_mem hs']
  · simp [hr, ChanMap.pushed_not_mem hr']
  · simp [hl]
  · simp [hPd]
  · simp [hPd'']
  · simp [ChanMap.pushed_not_mem hs']
  · simp [ChanMap.pushed_not_mem ho']
  · simp [ChanMap.pushed_not_mem hr']
  · simp [hPd]

end Atoms

theorem ne_of_disj {α : Type*} {l₁ l₂ : List α} (h : l₁.Disjoint l₂) {a b : α}
    (ha : a ∈ l₁) (hb : b ∈ l₂) : a ≠ b := by
  rintro rfl
  exact h ha hb

/-- Both variants: the steer reads `sIn`, the inv writes `ext`, and the fork writes both. -/
theorem cfs_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {d l r o sIn ext d'' : χ} {fouts : List χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popLeft 1) [d, l, r] [o]))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork 2) [o] fouts))
  (h₃ : proc.atoms[i₃]? = some (.async (.steer true 1) [d'', sIn] [r]))
  (hfouts : fouts = [sIn, ext] ∨ fouts = [ext, sIn])
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hfork : SameFork proc.atoms d d'') :
    RuleOK proc [i₃, i₂, i₁] [.inv true none d l ext, .sink #v[d'']] := by
  -- Facts from affineness
  have hn₁ := (haff.atom_nodup h₁).1
  have hn₂ := (haff.atom_nodup h₂).2
  have hn₃ := (haff.atom_nodup h₃).1
  have hd₁₂ := haff.atom_disjoint h₁ h₂ (Ne.symm hne₂₁)
  have hd₁₃ := haff.atom_disjoint h₁ h₃ (Ne.symm hne₃₁)
  have hd₂₃ := haff.atom_disjoint h₂ h₃ (Ne.symm hne₃₂)
  simp only [AtomicProc.inputs_async, AtomicProc.outputs_async] at hn₁ hn₂ hn₃ hd₁₂ hd₁₃ hd₂₃
  have hsf : sIn ∈ fouts := by rcases hfouts with rfl | rfl <;> simp
  have hef : ext ∈ fouts := by rcases hfouts with rfl | rfl <;> simp
  have hdl : d ≠ l := by intro h; subst h; simp at hn₁
  have hdr : d ≠ r := by intro h; subst h; simp at hn₁
  have hlr : l ≠ r := by intro h; subst h; simp at hn₁
  have hds'' : d'' ≠ sIn := by intro h; subst h; simp at hn₃
  have hse : sIn ≠ ext := by
    rcases hfouts with rfl | rfl <;> intro h <;> subst h <;> simp at hn₂
  have hdo : d ≠ o := ne_of_disj hd₁₂.1 (by simp) (by simp)
  have hlo : l ≠ o := ne_of_disj hd₁₂.1 (by simp) (by simp)
  have hro : r ≠ o := ne_of_disj hd₁₂.1 (by simp) (by simp)
  have hoe : o ≠ ext := ne_of_disj hd₁₂.2 (by simp) hef
  have hdd : d ≠ d'' := ne_of_disj hd₁₃.1 (by simp) (by simp)
  have hds : d ≠ sIn := ne_of_disj hd₁₃.1 (by simp) (by simp)
  have hld : l ≠ d'' := ne_of_disj hd₁₃.1 (by simp) (by simp)
  have hls : l ≠ sIn := ne_of_disj hd₁₃.1 (by simp) (by simp)
  have hrd : r ≠ d'' := ne_of_disj hd₁₃.1 (by simp) (by simp)
  have hrs : r ≠ sIn := ne_of_disj hd₁₃.1 (by simp) (by simp)
  have hod : o ≠ d'' := ne_of_disj hd₂₃.1 (by simp) (by simp)
  have hos : o ≠ sIn := ne_of_disj hd₂₃.1 (by simp) (by simp)
  have hre : r ≠ ext := Ne.symm (ne_of_disj hd₂₃.2 hef (by simp))
  -- `d` and `d''` are outputs of another fork
  obtain ⟨k', ins', outs', hmem', hd', hd''⟩ := hfork
  obtain ⟨j, hj, hgetj⟩ := List.getElem_of_mem hmem'
  have hgetj' : proc.atoms[j]? = some (.async (.fork k') ins' outs') :=
    List.getElem?_eq_some_iff.mpr ⟨hj, hgetj⟩
  have hj₂ : j ≠ i₂ := by
    rintro rfl
    rw [hgetj'] at h₂
    simp only [Option.some.injEq, AtomicProc.async.injEq] at h₂
    obtain ⟨-, -, rfl⟩ := h₂
    have hmem2 : ∀ x ∈ outs', x ≠ sIn → x = ext := by
      rcases hfouts with rfl | rfl <;> intro x hx hxs <;> simp at hx <;> tauto
    exact hdd ((hmem2 d hd' hds).trans (hmem2 d'' hd'' hds'').symm)
  have hdisj := (haff.atom_disjoint hgetj' h₂ hj₂).2
  simp only [AtomicProc.outputs_async] at hdisj
  have hde : d ≠ ext := ne_of_disj hdisj hd' hef
  have hde'' : d'' ≠ ext := ne_of_disj hdisj hd'' hef
  have hN : Distinct d l r o sIn ext d'' :=
    ⟨hdl, hdr, hdo, hdd, hds, hde, hlr, hlo, hld, hls, hro, hrd, hrs, hre, hod, hos, hoe,
      hds'', hde'', hse⟩
  have hpushF : ∀ (v : V) y, ChanMap.pushed fouts [v, v] y =
      (if sIn = y then [v] else []) ++ (if ext = y then [v] else []) := by
    intro v y
    rcases hfouts with rfl | rfl
    · simp
    · by_cases h : sIn = y
      · subst h; simp [Ne.symm hse]
      · simp [h]
  have hP : matchedOf proc.atoms [i₃, i₂, i₁] =
      origAtoms (Op := Op) d l r o sIn d'' fouts .popLeft := by
    simp [h₁, h₂, h₃]
  have hP' : ([.inv true none d l ext, .sink #v[d'']] : AtomicProcs Op χ V) =
      rwAtoms d l ext d'' none := by
    simp [AtomicProc.inv, AtomicProc.sink]
  rw [hP']
  refine ⟨?_, Rel d l r o sIn ext d'' fouts, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- names
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hne₃₂, hne₃₁, hne₂₁]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact (List.getElem?_eq_some_iff.mp h₃).1
      · exact (List.getElem?_eq_some_iff.mp h₂).1
      · exact (List.getElem?_eq_some_iff.mp h₁).1
    · simp [hdl, hdd, hld]
    · simp
    · intro x hx
      left
      rw [hP]
      simp only [rwAtoms, AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.append_nil] at hx
      simp only [origAtoms, AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
        AtomicProcs.inputNames_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.append_nil]
      tauto
    · intro x hx
      left
      rw [hP]
      simp only [rwAtoms, AtomicProcs.outputNames_cons, AtomicProc.outputs_async,
        AtomicProcs.outputNames_nil, List.mem_cons, List.not_mem_nil,
        or_false, List.append_nil] at hx
      subst hx
      simp [hef]
  · -- init
    rw [hP]
    exact Rel.intro (st := .popLeft) (c := none) (Pend := []) (A := []) (D := []) (O1 := [])
      (O := []) (Rr := []) (U := []) (λ _ _ _ _ _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl .idle (.inl ⟨rfl, rfl, rfl, rfl⟩)
  · -- frame_pop
    intro L₀ chans₀ L₁ chans₁ x v chans₀' hx₁ _ hR hpop
    rw [hP] at hx₁
    simp only [origAtoms, AtomicProcs.inputNames_cons, AtomicProc.inputs_async,
      AtomicProcs.inputNames_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.append_nil, not_or] at hx₁
    obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩ := hx₁
    exact frame_pop_rel ⟨h4, h5, h3, h2, h6, h1⟩ hR hpop
  · -- frame_push
    intro L₀ chans₀ L₁ chans₁ outs vals hlen hx hnd hfp hR
    have hnot : o ∉ outs ∧ sIn ∉ outs ∧ r ∉ outs := by
      refine ⟨λ h => (hx o h).1 ?_, λ h => (hx sIn h).1 ?_, λ h => (hx r h).1 ?_⟩ <;>
        rw [hP] <;> simp [hsf]
    have hdd' : ∃ P : List V, ChanMap.pushed outs vals d = P ∧
        ChanMap.pushed outs vals d'' = P ∧ (P = [] ∨ ∃ v, P = [v]) := by
      by_cases hin : d ∈ outs ∨ d'' ∈ outs
      · obtain ⟨y, hy, hy'⟩ : ∃ y ∈ outs, y ∈ outs' := by
          rcases hin with h | h
          · exact ⟨d, h, hd'⟩
          · exact ⟨d'', h, hd''⟩
        obtain ⟨rfl, v, -, hv⟩ := hfp y hy k' ins' outs' hmem' hy'
        exact ⟨[v], pushed_eq_singleton hnd hlen hd' hv, pushed_eq_singleton hnd hlen hd'' hv,
          .inr ⟨v, rfl⟩⟩
      · simp only [not_or] at hin
        exact ⟨[], ChanMap.pushed_not_mem hin.1, ChanMap.pushed_not_mem hin.2, .inl rfl⟩
    exact frame_push_rel hnot hdd' hR
  · -- step_op
    rintro L₀ chans₀ L₁ chans₁ op inputs outputs inputVals outputVals chans₀' - -
      ⟨st, c, Pend, rfl, -⟩ hmem
    simp at hmem
  · -- step_async
    rintro L₀ chans₀ L₁ chans₁ i aop aop' allInputs allOutputs inputs outputs inputVals
      outputVals chans₀' - - ⟨st, c, Pend, rfl, rfl, hC1, ho, hs, hr, hl, hcs, hm⟩ hget hinterp
      hlen₁ - hpop
    match i, hget with
    | 0, hget =>
      simp only [origAtoms, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      exact step_steer hN hC1 ho hs hr hl hcs hm hinterp hlen₁ hpop
    | 1, hget =>
      simp only [origAtoms, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      exact step_fork hN hpushF hC1 ho hs hr hl hcs hm hinterp hlen₁ hpop
    | 2, hget =>
      simp only [origAtoms, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        AtomicProc.async.injEq] at hget
      obtain ⟨rfl, rfl, rfl⟩ := hget
      exact step_carry hN hC1 ho hs hr hl hcs hm hinterp hlen₁ hpop
    | k + 3, hget => simp at hget
  · -- the relation only relates the initial states to the initial states
    intro L₁ chans₁ hR
    obtain ⟨st, c, Pend, -, rfl, hC1, ho, hs, hr, hl, -, hm⟩ := hR
    simp only [ChanMap.empty_apply] at hl hm
    obtain ⟨rfl, hU, rfl⟩ := Mode.init_inv hm
    refine ⟨rfl, ?_⟩
    funext y
    by_cases hyd : y = d
    · subst hyd; exact hU
    by_cases hyl : y = l
    · subst hyl; simpa using hl
    by_cases hyo : y = o
    · subst hyo; exact ho
    by_cases hys : y = sIn
    · subst hys; exact hs
    by_cases hyr : y = r
    · subst hyr; exact hr
    exact hC1 y hyd hyl hyo hys hyr

end CarryForkSteerToInv

theorem carry_fork_steer_to_inv_left_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {decider inputL inputR output output₁' output₂' decider'' : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork 2) [output] [output₁', output₂']))
  (h₃ : proc.atoms[i₃]? = some (.async (.steer true 1) [decider'', output₁'] [inputR]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hfork : SameFork proc.atoms decider decider'') :
    RuleOK proc [i₃, i₂, i₁] [
      .inv true none decider inputL output₂',
      .sink #v[decider''],
    ]
  := CarryForkSteerToInv.cfs_ok haff h₁ h₂ h₃ (.inl rfl) hne₂₁ hne₃₁ hne₃₂ hfork

theorem carry_fork_steer_to_inv_right_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {i₁ i₂ i₃ : Nat}
  {decider inputL inputR output output₁' output₂' decider'' : χ}
  (haff : proc.AffineChan)
  (h₁ : proc.atoms[i₁]? = some (.async (.merge .popLeft 1) [decider, inputL, inputR] [output]))
  (h₂ : proc.atoms[i₂]? = some (.async (.fork 2) [output] [output₁', output₂']))
  (h₃ : proc.atoms[i₃]? = some (.async (.steer true 1) [decider'', output₂'] [inputR]))
  (hne₂₁ : i₂ ≠ i₁) (hne₃₁ : i₃ ≠ i₁) (hne₃₂ : i₃ ≠ i₂)
  (hfork : SameFork proc.atoms decider decider'') :
    RuleOK proc [i₃, i₂, i₁] [
      .inv true none decider inputL output₁',
      .sink #v[decider''],
    ]
  := CarryForkSteerToInv.cfs_ok haff h₁ h₂ h₃ (.inr rfl) hne₂₁ hne₃₁ hne₃₂ hfork

end Wavelet.Compile.DeadCodeElim
