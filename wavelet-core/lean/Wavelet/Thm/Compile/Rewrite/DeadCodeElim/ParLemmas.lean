import Wavelet.Thm.Compile.Rewrite.Lemmas
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! Helper lemmas for rules relating copies of the same fork
(`par-steer-steer` and `merge-dedup`). -/

namespace Wavelet.Compile.DeadCodeElim.ParLemmas

open Semantics Dataflow

theorem mem_pushed [DecidableEq χ] {names : List χ} {vals : List V} {y : χ} {w : V}
  (h : w ∈ ChanMap.pushed names vals y) : w ∈ vals := by
  induction names generalizing vals with
  | nil => simp at h
  | cons x names ih =>
    cases vals with
    | nil => simp at h
    | cons v vals =>
      simp only [ChanMap.pushed_cons, List.mem_append] at h
      rcases h with h | h
      · by_cases hx : x = y
        · simp [hx] at h; simp [h]
        · simp [hx] at h
      · exact List.mem_cons_of_mem _ (ih h)

/-- Pushing copies of one value to distinct names. -/
theorem pushed_eq_singleton [DecidableEq χ] {names : List χ} {vals : List V} {y : χ} {v : V}
  (hnd : names.Nodup) (hlen : names.length = vals.length) (hv : ∀ w ∈ vals, w = v)
  (hy : y ∈ names) : ChanMap.pushed names vals y = [v] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons v' vals =>
      have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      simp only [ChanMap.pushed_cons]
      by_cases hxy : x = y
      · subst hxy
        rw [ChanMap.pushed_not_mem hx, hv v' (by simp)]
        simp
      · have hy' : y ∈ names := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hxy
          · exact h
        rw [ih hnd' (by simpa using hlen) (λ w hw => hv w (List.mem_cons_of_mem _ hw)) hy']
        simp [hxy]

theorem pushed_eq_of_mem_iff [DecidableEq χ] {names : List χ} {vals : List V} {a b : χ} {v : V}
  (hnd : names.Nodup) (hlen : names.length = vals.length) (hv : ∀ w ∈ vals, w = v)
  (hiff : a ∈ names ↔ b ∈ names) :
    ChanMap.pushed names vals a = ChanMap.pushed names vals b := by
  by_cases ha : a ∈ names
  · rw [pushed_eq_singleton hnd hlen hv ha, pushed_eq_singleton hnd hlen hv (hiff.mp ha)]
  · rw [ChanMap.pushed_not_mem ha, ChanMap.pushed_not_mem (mt hiff.mpr ha)]

theorem pushed_ite [DecidableEq χ] {c : Prop} [Decidable c] {y₀ y : χ} {v : V} :
    ChanMap.pushed (if c then [y₀] else []) (if c then [v] else []) y =
      if y₀ = y then (if c then [v] else []) else [] := by
  by_cases hc : c <;> by_cases hy : y₀ = y <;> simp [hc, hy]

theorem SameFork.symm [Arity Op] {aps : AtomicProcs Op χ V} {a b : χ}
  (h : SameFork aps a b) : SameFork aps b a := by
  obtain ⟨k, ins, outs, hmem, ha, hb⟩ := h
  exact ⟨k, ins, outs, hmem, hb, ha⟩

/-- Any atom writing to one copy also writes to the other. -/
theorem SameFork.mem_outputs [Arity Op] {proc : Proc Op χ V m n} {a b : χ}
  {ap : AtomicProc Op χ V} {i : Nat}
  (haff : proc.AffineChan) (h : SameFork proc.atoms a b)
  (hget : proc.atoms[i]? = some ap) (ha : a ∈ ap.outputs) : b ∈ ap.outputs := by
  obtain ⟨k, ins, outs, hmem, ha', hb'⟩ := h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  by_cases hij : i = j
  · subst hij
    rw [hget] at hj
    cases hj
    exact hb'
  · exact absurd ha' ((haff.atom_disjoint hget hj hij).2 ha)

/-- A copy is not written by any non-fork atom. -/
theorem SameFork.not_mem_outputs [Arity Op] {proc : Proc Op χ V m n} {a b : χ}
  {ap : AtomicProc Op χ V} {i : Nat}
  (haff : proc.AffineChan) (h : SameFork proc.atoms a b)
  (hget : proc.atoms[i]? = some ap) (hnf : ∀ k ins outs, ap ≠ .async (.fork k) ins outs) :
    a ∉ ap.outputs := by
  intro ha
  obtain ⟨k, ins, outs, hmem, ha', -⟩ := h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  by_cases hij : i = j
  · subst hij
    rw [hget] at hj
    cases hj
    exact hnf k ins outs rfl
  · exact (haff.atom_disjoint hget hj hij).2 ha ha'

/-- A push from the context writes the same values to both copies. -/
theorem ForkPush.pushed_eq [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {outs : List χ} {vals : List V} {a b : χ}
  (hfp : ForkPush proc outs vals) (hnd : outs.Nodup) (hlen : outs.length = vals.length)
  (h : SameFork proc.atoms a b) :
    ChanMap.pushed outs vals a = ChanMap.pushed outs vals b := by
  obtain ⟨k, ins, fouts, hmem, ha, hb⟩ := h
  by_cases ha' : a ∈ outs
  · obtain ⟨rfl, v, -, hv⟩ := hfp a ha' k ins fouts hmem ha
    exact pushed_eq_of_mem_iff hnd hlen hv ⟨λ _ => hb, λ _ => ha⟩
  · by_cases hb' : b ∈ outs
    · obtain ⟨rfl, -⟩ := hfp b hb' k ins fouts hmem hb
      exact absurd ha ha'
    · rw [ChanMap.pushed_not_mem ha', ChanMap.pushed_not_mem hb']

/-- A push from the context to a copy is clonable. -/
theorem ForkPush.clonable [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {outs : List χ} {vals : List V} {a b : χ} {w : V}
  (hfp : ForkPush proc outs vals) (h : SameFork proc.atoms a b)
  (hw : w ∈ ChanMap.pushed outs vals a) : InterpConsts.isClonable w := by
  obtain ⟨k, ins, fouts, hmem, ha, -⟩ := h
  by_cases ha' : a ∈ outs
  · obtain ⟨-, v, hclone, hv⟩ := hfp a ha' k ins fouts hmem ha
    rw [hv w (mem_pushed hw)]
    exact hclone
  · rw [ChanMap.pushed_not_mem ha'] at hw
    simp at hw

/-- A fork in the graph writes the same values to both copies. -/
theorem SameFork.pushed_replicate_eq [Arity Op] [DecidableEq χ] {proc : Proc Op χ V m n}
  {a b : χ} {i k : Nat} {ins outs : List χ} {v : V}
  (haff : proc.AffineChan) (h : SameFork proc.atoms a b)
  (hget : proc.atoms[i]? = some (.async (.fork k) ins outs)) (hlen : outs.length = k) :
    ChanMap.pushed outs (List.replicate k v) a = ChanMap.pushed outs (List.replicate k v) b :=
  pushed_eq_of_mem_iff (haff.atom_nodup hget).2 (by simp [hlen])
    (λ _ hw => List.eq_of_mem_replicate hw)
    ⟨λ ha => SameFork.mem_outputs haff h hget ha,
     λ hb => SameFork.mem_outputs haff (SameFork.symm h) hget hb⟩

end Wavelet.Compile.DeadCodeElim.ParLemmas
