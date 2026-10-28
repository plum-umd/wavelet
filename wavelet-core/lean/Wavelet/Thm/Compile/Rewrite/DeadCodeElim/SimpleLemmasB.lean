import Wavelet.Thm.Compile.Rewrite.Lemmas

/-!
Helper lemmas shared by the proofs of `fork-sink`, `fork-fork`, `order-sink`,
`merge-sink`, `inact-sink`, `order-sync-path`, and `order-order`.

Many of these rules use a relation where the rewritten channels are the same
as the original ones, except for a channel `s` that is empty in the rewritten
graph, i.e., `chans₁ = λ y => if y = s then [] else chans₀ y`.
-/

namespace Wavelet.Compile.DeadCodeElim.SimpleB

open Semantics Dataflow

theorem toList_toVector {xs : List α} : xs.toVector.toList = xs := rfl

variable [DecidableEq χ]

/-! Facts about `ChanMap.pushed`. -/

theorem pushed_replicate {names : List χ} {v : V} {y : χ} :
    ChanMap.pushed names (List.replicate names.length v) y =
      List.replicate (names.count y) v := by
  induction names with
  | nil => simp
  | cons x names ih =>
    simp only [List.length_cons, List.replicate_succ, ChanMap.pushed_cons, ih, List.count_cons]
    by_cases h : x = y
    · subst h; simp [List.replicate_succ]
    · simp [h]

theorem pushed_ne_nil {names : List χ} {vals : List V} {y : χ}
  (hy : y ∈ names) (hlen : names.length = vals.length) :
    ChanMap.pushed names vals y ≠ [] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      rw [ChanMap.pushed_cons]
      by_cases hx : x = y
      · simp [hx]
      · have hy' : y ∈ names := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hx
          · exact h
        simp [hx, ih hy' (by simpa using hlen)]

theorem pushed_singleton {names : List χ} {vals : List V} {y : χ}
  (hnd : names.Nodup) (hy : y ∈ names) (hlen : names.length = vals.length) :
    ∃ v, ChanMap.pushed names vals y = [v] := by
  induction names generalizing vals with
  | nil => simp at hy
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      rw [List.nodup_cons] at hnd
      rw [ChanMap.pushed_cons]
      by_cases hx : x = y
      · subst hx
        exact ⟨v, by simp [ChanMap.pushed_not_mem hnd.1]⟩
      · have hy' : y ∈ names := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hx
          · exact h
        obtain ⟨w, hw⟩ := ih hnd.2 hy' (by simpa using hlen)
        exact ⟨w, by simp [hx, hw]⟩

/-- Erasing a name from the pushed names (the values are taken accordingly). -/
theorem pushed_erase {names : List χ} {vals : List V} (s : χ)
  (hlen : names.length = vals.length) :
    ∃ vals', (names.erase s).length = vals'.length ∧
      ∀ y, y ≠ s → ChanMap.pushed (names.erase s) vals' y = ChanMap.pushed names vals y := by
  induction names generalizing vals with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons x names ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      have hlen' : names.length = vals.length := by simpa using hlen
      by_cases hx : x = s
      · subst hx
        refine ⟨vals, by simpa using hlen', λ y hy => ?_⟩
        simp [Ne.symm hy]
      · obtain ⟨vals', hlen'', h⟩ := ih hlen'
        have herase : (x :: names).erase s = x :: names.erase s :=
          List.erase_cons_tail (by simpa using hx)
        refine ⟨v :: vals', by simp [herase, hlen''], λ y hy => ?_⟩
        rw [herase, ChanMap.pushed_cons, ChanMap.pushed_cons, h y hy]

/-- Popping from distinct names leaves the tails. -/
theorem pop_eq_tail {names : List χ} {vals : List V} {chans chans' : ChanMap χ V}
  (hnd : names.Nodup) (hlen : names.length = vals.length)
  (hpop : ∀ y, chans y = ChanMap.pushed names vals y ++ chans' y) (y : χ) :
    chans' y = if y ∈ names then (chans y).tail else chans y := by
  split
  · rename_i hy
    obtain ⟨v, hv⟩ := pushed_singleton hnd hy hlen
    rw [hpop y, hv]
    rfl
  · rename_i hy
    rw [hpop y, ChanMap.pushed_not_mem hy]
    rfl

/-- Distinct non-empty channels can be popped. -/
theorem pop_exists {names : List χ} {chans : ChanMap χ V}
  (hnd : names.Nodup) (hne : ∀ c ∈ names, chans c ≠ []) :
    ∃ vals : List V, names.length = vals.length ∧
      ∀ y, chans y = ChanMap.pushed names vals y ++
        (if y ∈ names then (chans y).tail else chans y) := by
  induction names with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x names ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨vals, hlen, h⟩ := ih hnd.2 (λ c hc => hne c (by simp [hc]))
    obtain ⟨v, rest, hx⟩ := List.exists_cons_of_ne_nil (hne x (by simp))
    refine ⟨v :: vals, by simp [hlen], λ y => ?_⟩
    by_cases hy : y = x
    · subst hy
      simp [ChanMap.pushed_not_mem hnd.1, hx]
    · calc chans y
        _ = ChanMap.pushed names vals y ++ (if y ∈ names then (chans y).tail else chans y) := h y
        _ = _ := by simp [hy, Ne.symm hy]

/-! Channels that are the same except one channel `s` (empty in the rewritten graph). -/

theorem except_empty {s : χ} :
    (ChanMap.empty : ChanMap χ V) = λ y => if y = s then [] else ChanMap.empty y := by
  funext y
  split <;> rfl

theorem except_pop {s : χ} {names : List χ} {vals : List V} {chans chans' : ChanMap χ V}
  (hs : s ∉ names) (hpop : ∀ y, chans y = ChanMap.pushed names vals y ++ chans' y) (y : χ) :
    (if y = s then [] else chans y) =
      ChanMap.pushed names vals y ++ (if y = s then [] else chans' y) := by
  split
  · subst_vars
    simp [ChanMap.pushed_not_mem hs]
  · exact hpop y

theorem except_frame_pop {s x : χ} {v : V} {chans chans' : ChanMap χ V}
  (hxs : x ≠ s) (hpop : ∀ y, chans y = (if y = x then [v] else []) ++ chans' y) (y : χ) :
    (if y = s then [] else chans y) =
      (if y = x then [v] else []) ++ (if y = s then [] else chans' y) := by
  split
  · subst_vars
    simp [Ne.symm hxs]
  · exact hpop y

theorem except_push {s : χ} {names : List χ} {vals : List V} {chans : ChanMap χ V}
  (hs : s ∉ names) :
    (λ y => (if y = s then [] else chans y) ++ ChanMap.pushed names vals y) =
      λ y => if y = s then [] else chans y ++ ChanMap.pushed names vals y := by
  funext y
  split
  · subst_vars
    simp [ChanMap.pushed_not_mem hs]
  · rfl

/-- Pushing on the original side only to `s`. -/
theorem except_push_only {s : χ} {names : List χ} {vals : List V} {chans : ChanMap χ V}
  (hnames : ∀ y, y ≠ s → ChanMap.pushed names vals y = []) :
    (λ y => if y = s then [] else chans y) =
      λ y => if y = s then [] else chans y ++ ChanMap.pushed names vals y := by
  funext y
  split
  · rfl
  · rename_i hy
    rw [hnames y hy, List.append_nil]

/-- Popping on the original side without touching `s`. -/
theorem except_pop_same {s : χ} {names : List χ} {vals : List V} {chans chans' : ChanMap χ V}
  (hpop : ∀ y, chans y = ChanMap.pushed names vals y ++ chans' y)
  (hnames : ∀ y, y ≠ s → ChanMap.pushed names vals y = []) :
    (λ y => if y = s then [] else chans y) = λ y => if y = s then [] else chans' y := by
  funext y
  split
  · rfl
  · rename_i hy
    rw [hpop y, hnames y hy]
    rfl

/-- A fork without the output `s` pushes the same values as the original fork, except to `s`. -/
theorem except_push_erase {s : χ} {names : List χ} {v : V} {chans : ChanMap χ V}
  (hnd : names.Nodup) :
    (λ y => (if y = s then [] else chans y) ++
      ChanMap.pushed (names.erase s) (List.replicate (names.erase s).length v) y) =
      λ y => if y = s then [] else
        chans y ++ ChanMap.pushed names (List.replicate names.length v) y := by
  funext y
  simp only [pushed_replicate]
  split
  · subst_vars
    simp [List.count_eq_zero.mpr (hnd.not_mem_erase)]
  · rename_i hy
    simp [List.count_erase_of_ne hy]

/-- Popping from `names.erase s` instead of `names`. -/
theorem except_pop_erase {s : χ} {names : List χ} {vals : List V} {chans chans' : ChanMap χ V}
  (hnd : names.Nodup) (hlen : names.length = vals.length)
  (hpop : ∀ y, chans y = ChanMap.pushed names vals y ++ chans' y) :
    ∃ vals', (names.erase s).length = vals'.length ∧ ∀ y,
      (if y = s then [] else chans y) =
        ChanMap.pushed (names.erase s) vals' y ++ (if y = s then [] else chans' y) := by
  obtain ⟨vals', hlen', h⟩ := pushed_erase s hlen
  refine ⟨vals', hlen', λ y => ?_⟩
  split
  · subst_vars
    simp [ChanMap.pushed_not_mem hnd.not_mem_erase]
  · rename_i hy
    rw [h y hy]
    exact hpop y

/-! Sinks and forks. -/

omit [DecidableEq χ] in
theorem sink_inputs [Arity Op] {names : Vector χ n} :
    (AtomicProc.sink names : AtomicProc Op χ V).inputs = names.toList := by
  unfold AtomicProc.sink
  split
  · rfl
  · rename_i h
    simp only [ne_eq, Decidable.not_not] at h
    subst h
    simp [AtomicProc.inputs]

omit [DecidableEq χ] in
theorem sink_outputs [Arity Op] {names : Vector χ n} :
    (AtomicProc.sink names : AtomicProc Op χ V).outputs = [] := by
  unfold AtomicProc.sink
  split <;> rfl

/-- A sink in the local atoms consumes values from all its inputs. -/
theorem sink_step [Arity Op] [InterpConsts V]
  {L : AtomicProcs Op χ V} {chans chans' : ChanMap χ V}
  {names : Vector χ n} {vals : List V}
  (hmem : AtomicProc.sink names ∈ L) (hlen : n = vals.length)
  (hpop : ∀ y, chans y = ChanMap.pushed names.toList vals y ++ chans' y) :
    LocalTauStar L chans L chans' := by
  unfold AtomicProc.sink at hmem
  split at hmem
  · rename_i h
    haveI : NeZero n := ⟨h⟩
    have := LocalTauStar.async_list_mem
      (aop := .sink n) (allInputs := names.toList) (allOutputs := [])
      (inputs := names.toList) (inputVals := vals) (outputs := []) (outputVals := [])
      hmem (.interp_sink (by simp)) (by simp [hlen]) rfl hpop
    exact this.eq_rhs rfl (by funext y; simp)
  · rename_i h
    simp only [ne_eq, Decidable.not_not] at h
    subst h
    obtain rfl : vals = [] := List.eq_nil_of_length_eq_zero hlen.symm
    obtain rfl : chans = chans' := by
      funext y
      simpa using hpop y
    exact .refl

/-- A fork in the local atoms. -/
theorem fork_step [Arity Op] [InterpConsts V]
  {L : AtomicProcs Op χ V} {chans chans' : ChanMap χ V}
  {x : χ} {outs : List χ} {v : V}
  (hmem : AtomicProc.fork x outs.toVector ∈ L) (hclone : InterpConsts.isClonable v)
  (hpop : ∀ y, chans y = ChanMap.pushed [x] [v] y ++ chans' y) :
    LocalTauStar L chans L
      (λ y => chans' y ++ ChanMap.pushed outs (List.replicate outs.length v) y) :=
  LocalTauStar.async_list_mem
    (aop := .fork outs.length) (allInputs := [x]) (allOutputs := outs)
    (inputs := [x]) (inputVals := [v]) (outputs := outs)
    (outputVals := List.replicate outs.length v)
    (by simpa [AtomicProc.fork, List.toVector] using hmem)
    (.interp_fork rfl hclone) rfl (by simp) hpop

end Wavelet.Compile.DeadCodeElim.SimpleB
