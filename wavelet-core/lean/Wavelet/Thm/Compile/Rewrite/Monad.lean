import Wavelet.Compile.Rewrite

import Wavelet.Thm.Compile.Rewrite.Defs
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Match

/-! Specs for the `RewriteM` combinators and `Rewrite.apply`. -/

namespace Wavelet.Compile

open Semantics Dataflow DeadCodeElim

section StateTOption

variable {σ α β : Type u}

theorem StateT.orElse_some {x y : StateT σ Option α} {s : σ} {r}
  (h : (x <|> y) s = some r) : x s = some r ∨ y s = some r := by
  change (x s <|> y s) = some r at h
  cases hx : x s with
  | none => right; simpa [hx] using h
  | some a => left; simp [hx] at h; simp [h]

theorem StateT.bind_some {x : StateT σ Option α} {f : α → StateT σ Option β} {s : σ} {r}
  (h : (x >>= f) s = some r) : ∃ a s', x s = some (a, s') ∧ f a s' = some r := by
  change (x s >>= fun p => f p.1 p.2) = some r at h
  cases hx : x s with
  | none => simp [hx] at h
  | some p => exact ⟨p.1, p.2, by simp, by simpa [hx] using h⟩

theorem StateT.failure_some {s : σ} {r} (h : (failure : StateT σ Option α) s = some r) : False := by
  cases h

theorem StateT.pure_some {a : α} {s : σ} {r} (h : (pure a : StateT σ Option α) s = some r) :
    r = (a, s) := by
  change some (a, s) = some r at h
  simp at h
  exact h.symm

theorem List.firstM_some {f : α → StateT σ Option β} {l : List α} {s : σ} {r}
  (h : l.firstM f s = some r) : ∃ a ∈ l, f a s = some r := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases StateT.orElse_some h with h | h
    · exact ⟨a, by simp, h⟩
    · have ⟨b, hb, h⟩ := ih h
      exact ⟨b, by simp [hb], h⟩

theorem Vector.firstM_some {f : α → StateT σ Option β} {n} {xs : Vector α n} {s : σ} {r}
  (h : xs.firstM f s = some r) : ∃ a ∈ xs.toList, f a s = some r := by
  rcases xs with ⟨⟨l⟩, rfl⟩
  simp only [Vector.firstM_mk, List.firstM_toArray] at h
  exact List.firstM_some h

/-- `do let a ← x; pure a` (from early returns) behaves as `x`. -/
theorem StateT.bind_pure_some {x : StateT σ Option α} {s : σ} {r}
  (h : (x >>= fun a => pure a) s = some r) : x s = some r := by
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  rw [StateT.pure_some h₂]
  exact h₁

theorem StateT.get_bind_some {f : σ → StateT σ Option β} {s : σ} {r}
  (h : (get >>= f) s = some r) : f s s = some r := by
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  simp [get, getThe, MonadStateOf.get, StateT.get] at h₁
  obtain ⟨rfl, rfl⟩ := h₁
  exact h₂

theorem List.toVectorDyn_some {xs : List α} {n : Nat} {s s' : σ} {v}
  (h : (xs.toVectorDyn n : StateT σ Option (Vector α n)) s = some (v, s')) :
    ∃ h : xs.length = n, v = xs.toVector.cast h ∧ s' = s := by
  unfold List.toVectorDyn at h
  split at h
  · have := StateT.pure_some h
    simp only [Prod.mk.injEq] at this
    exact ⟨_, this⟩
  · exact (StateT.failure_some h).elim

end StateTOption

variable {Op χ V : Type} [Arity Op] [DecidableEq χ] [Hashable χ]

theorem RewriteM.choose_some {α : Type}
  {cont : AtomicProc Op (RewriteName χ) V → RewriteM Op χ V α}
  {s : RewriteState Op χ V} {r}
  (h : RewriteM.choose cont s = some r) :
    ∃ i : Fin s.aps.length, ↑i ∉ s.matched ∧
      cont s.aps[i] { s with matched := ↑i :: s.matched } = some r := by
  unfold RewriteM.choose at h
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  simp [get, getThe, MonadStateOf.get, StateT.get] at h₁
  obtain ⟨rfl, rfl⟩ := h₁
  have ⟨i, hi, h₃⟩ := List.firstM_some h₂
  simp at hi
  refine ⟨i, hi.2, ?_⟩
  have ⟨_, _, h₄, h₅⟩ := StateT.bind_some h₃
  simp [set, StateT.set] at h₄
  obtain ⟨rfl, rfl⟩ := h₄
  exact h₅

theorem RewriteM.chooseWithNames_some {α : Type}
  {names : List (RewriteName χ)}
  {cont : AtomicProc Op (RewriteName χ) V → RewriteM Op χ V α}
  {s : RewriteState Op χ V} {r}
  (h : RewriteM.chooseWithNames names cont s = some r) :
    ∃ i : Fin s.aps.length, ↑i ∉ s.matched ∧
      cont s.aps[i] { s with matched := ↑i :: s.matched } = some r := by
  unfold RewriteM.chooseWithNames at h
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  simp [get, getThe, MonadStateOf.get, StateT.get] at h₁
  obtain ⟨rfl, rfl⟩ := h₁
  have ⟨ids, _, h₃⟩ := List.firstM_some h₂
  have ⟨i, hi, h₄⟩ := List.firstM_some h₃
  simp at hi
  refine ⟨i, hi.2, ?_⟩
  have ⟨_, _, h₅, h₆⟩ := StateT.bind_some h₄
  simp [set, StateT.set] at h₅
  obtain ⟨rfl, rfl⟩ := h₅
  exact h₆

/-- Variant of `choose_some` with the chosen atom as a variable. -/
theorem RewriteM.choose_some' {α : Type}
  {cont : AtomicProc Op (RewriteName χ) V → RewriteM Op χ V α}
  {s : RewriteState Op χ V} {r}
  (h : RewriteM.choose cont s = some r) :
    ∃ (i : Nat) (ap : AtomicProc Op (RewriteName χ) V), i ∉ s.matched ∧ s.aps[i]? = some ap ∧
      cont ap { s with matched := i :: s.matched } = some r := by
  have ⟨i, hi, h⟩ := RewriteM.choose_some h
  exact ⟨i, _, hi, by simp, h⟩

/-- Variant of `chooseWithNames_some` with the chosen atom as a variable. -/
theorem RewriteM.chooseWithNames_some' {α : Type}
  {names : List (RewriteName χ)}
  {cont : AtomicProc Op (RewriteName χ) V → RewriteM Op χ V α}
  {s : RewriteState Op χ V} {r}
  (h : RewriteM.chooseWithNames names cont s = some r) :
    ∃ (i : Nat) (ap : AtomicProc Op (RewriteName χ) V), i ∉ s.matched ∧ s.aps[i]? = some ap ∧
      cont ap { s with matched := i :: s.matched } = some r := by
  have ⟨i, hi, h⟩ := RewriteM.chooseWithNames_some h
  exact ⟨i, _, hi, by simp, h⟩

theorem RewriteM.assume_some {α : Type} {p : Prop} [Decidable p]
  {cont : p → RewriteM Op χ V α} {s : RewriteState Op χ V} {r}
  (h : RewriteM.assume p cont s = some r) : ∃ hp : p, cont hp s = some r := by
  unfold RewriteM.assume at h
  split at h
  · exact ⟨_, h⟩
  · exact (StateT.failure_some h).elim

theorem RewriteM.apply_some
  {name : String} {res : AtomicProcs Op (RewriteName χ) V}
  {s : RewriteState Op χ V} {r}
  (h : RewriteM.apply name res s = some r) : r = ((name, res), s) := by
  unfold RewriteM.apply at h
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  simp [get, getThe, MonadStateOf.get, StateT.get] at h₁
  obtain ⟨rfl, rfl⟩ := h₁
  split at h₂
  · exact (StateT.failure_some h₂).elim
  · exact StateT.pure_some h₂

/-- Variant of `apply_some` with the components of the result. -/
theorem RewriteM.apply_some'
  {name name' : String} {res res' : AtomicProcs Op (RewriteName χ) V}
  {s s' : RewriteState Op χ V}
  (h : RewriteM.apply name res s = some ((name', res'), s')) :
    name' = name ∧ res' = res ∧ s' = s := by
  have := RewriteM.apply_some h
  simp only [Prod.mk.injEq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Atoms returned by `ctxWithNames` are in the context. -/
theorem RewriteM.ctxWithNames_some
  {names : List (RewriteName χ)} {s : RewriteState Op χ V} {r}
  (h : RewriteM.ctxWithNames names s = some r) :
    r.2 = s ∧ ∀ ap ∈ r.1, ap ∈ s.aps := by
  unfold RewriteM.ctxWithNames at h
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  simp [get, getThe, MonadStateOf.get, StateT.get] at h₁
  obtain ⟨rfl, rfl⟩ := h₁
  have := StateT.pure_some h₂
  subst this
  simp only [List.mem_map, List.mem_flatten, forall_exists_index, and_imp, true_and]
  intro ap l _ _ _ _ _ heq
  subst heq
  exact List.getElem_mem _

/-- `idxCtxWithNames` only reads the state. -/
theorem RewriteM.idxCtxWithNames_some
  {names : List (RewriteName χ)} {s : RewriteState Op χ V} {r}
  (h : RewriteM.idxCtxWithNames names s = some r) : r.2 = s := by
  unfold RewriteM.idxCtxWithNames at h
  have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
  simp [get, getThe, MonadStateOf.get, StateT.get] at h₁
  obtain ⟨rfl, rfl⟩ := h₁
  rw [StateT.pure_some h₂]

theorem RewriteM.assumeFromSameFork_some
  {chan₁ chan₂ : RewriteName χ} {s : RewriteState Op χ V} {r}
  (h : RewriteM.assumeFromSameFork chan₁ chan₂ s = some r) :
    r.2 = s ∧ SameFork s.aps chan₁ chan₂ := by
  unfold RewriteM.assumeFromSameFork at h
  have ⟨aps', s', h₁, h₂⟩ := StateT.bind_some h
  have ⟨hs, hmem⟩ := RewriteM.ctxWithNames_some h₁
  simp only at hs hmem
  subst hs
  have ⟨ap, hap, h₃⟩ := List.firstM_some h₂
  split at h₃
  · split at h₃
    · rename_i hchans
      exact ⟨by rw [StateT.pure_some h₃], _, _, _, hmem _ hap, hchans⟩
    · exact (StateT.failure_some h₃).elim
  · exact (StateT.failure_some h₃).elim

theorem RewriteM.checkFromConst_some [InterpConsts V]
  {chan : RewriteName χ} {s : RewriteState Op χ V} {r}
  (h : RewriteM.checkFromConst chan s = some r) :
    r.2 = s ∧ FromConst s.aps chan r.1 := by
  unfold RewriteM.checkFromConst at h
  have ⟨aps', s', h₁, h₂⟩ := StateT.bind_some h
  have ⟨hs, hmem⟩ := RewriteM.ctxWithNames_some h₁
  simp only at hs hmem
  subst hs
  have ⟨ap, hap, h₃⟩ := List.firstM_some h₂
  split at h₃
  · rename_i inputs outputs
    have ⟨hlen, h₄⟩ := RewriteM.assume_some h₃
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    simp only [List.getElem_cons_zero] at h₄
    split at h₄
    · rename_i hchan
      have ⟨aps'', s'', h₅, h₆⟩ := StateT.bind_some h₄
      have ⟨hs, hmem'⟩ := RewriteM.ctxWithNames_some h₅
      simp only at hs hmem'
      subst hs
      have ⟨ap', hap', h₇⟩ := List.firstM_some h₆
      split at h₇
      · split at h₇
        · rename_i hx
          obtain rfl := StateT.pure_some h₇
          exact ⟨rfl, .fork (hmem _ hap) hchan (hmem' _ hap') hx⟩
        · exact (StateT.failure_some h₇).elim
      · exact (StateT.failure_some h₇).elim
    · exact (StateT.failure_some h₄).elim
  · split at h₃
    · rename_i hchan
      obtain rfl := StateT.pure_some h₃
      exact ⟨rfl, .const (hmem _ hap) hchan⟩
    · exact (StateT.failure_some h₃).elim
  · exact (StateT.failure_some h₃).elim

theorem RewriteM.checkSyncPathTo_some
  {chan : RewriteName χ} {outputs : List (RewriteName χ)} {fuel : Nat} {hist : List Nat}
  {s : RewriteState Op χ V} {r}
  (h : RewriteM.checkSyncPathTo chan outputs fuel hist s = some r) :
    r.2 = s := by
  induction fuel generalizing chan hist with
  | zero =>
    unfold RewriteM.checkSyncPathTo at h
    exact (StateT.failure_some h).elim
  | succ fuel ih =>
    unfold RewriteM.checkSyncPathTo at h
    split at h
    · rw [StateT.pure_some h]
    · have ⟨_, _, h₁, h₂⟩ := StateT.bind_some h
      have hs := RewriteM.idxCtxWithNames_some h₁
      simp only at hs
      subst hs
      have ⟨⟨i, ap⟩, _, h₃⟩ := List.firstM_some h₂
      dsimp only at h₃
      split at h₃
      · exact (StateT.failure_some h₃).elim
      · -- Each case recurses with the same state
        split at h₃ <;> (try split at h₃) <;>
          first
          | exact (StateT.failure_some h₃).elim
          | exact (Vector.firstM_some h₃).elim λ _ ⟨_, h₄⟩ => ih h₄
          | exact (List.firstM_some h₃).elim λ _ ⟨_, h₄⟩ => ih h₄

/-! Variants of the specs above with the components of the result. -/

theorem RewriteM.assumeFromSameFork_some'
  {chan₁ chan₂ : RewriteName χ} {s s' : RewriteState Op χ V} {u : Unit}
  (h : RewriteM.assumeFromSameFork chan₁ chan₂ s = some (u, s')) :
    s' = s ∧ SameFork s.aps chan₁ chan₂ :=
  RewriteM.assumeFromSameFork_some h

theorem RewriteM.checkFromConst_some' [InterpConsts V]
  {chan : RewriteName χ} {s s' : RewriteState Op χ V} {v : V}
  (h : RewriteM.checkFromConst chan s = some (v, s')) :
    s' = s ∧ FromConst s.aps chan v :=
  RewriteM.checkFromConst_some h

theorem RewriteM.checkSyncPathTo_some'
  {chan : RewriteName χ} {outputs : List (RewriteName χ)} {fuel : Nat} {hist : List Nat}
  {s s' : RewriteState Op χ V} {u : Unit}
  (h : RewriteM.checkSyncPathTo chan outputs fuel hist s = some (u, s')) :
    s' = s :=
  RewriteM.checkSyncPathTo_some h

/-- Decomposes the result of `Rewrite.apply`. -/
theorem Rewrite.apply_some
  {rw : Rewrite Op χ V} {proc : Proc Op (RewriteName χ) V m n}
  {disabledRules : List String} {name : String} {proc' : Proc Op (RewriteName χ) V m n}
  (h : rw.apply proc disabledRules = some (name, proc')) :
    ∃ res s,
      rw.run (.init proc.atoms disabledRules) = some ((name, res), s) ∧
      proc' = {
        inputs := proc.inputs.map .rw,
        outputs := proc.outputs.map .rw,
        atoms := AtomicProcs.mapChans .rw (res ++ unmatchedOf s.aps s.matched),
      } := by
  unfold Rewrite.apply at h
  cases hrun : rw.run (.init proc.atoms disabledRules) with
  | none => simp [hrun] at h
  | some p =>
    obtain ⟨⟨name', res⟩, s⟩ := p
    simp [hrun] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨res, s, rfl, ?_⟩
    simp [unmatchedOf]

end Wavelet.Compile
