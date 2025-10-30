import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Wavelet.Data.List

/-! Some lemmas about `Vector` and `Array`. -/

namespace Array

@[simp]
theorem mapM_push [Monad m] [LawfulMonad m] {f : α → m β} {xs : Array α} :
    (xs.push x).mapM f = (return (← xs.mapM f).push (← f x)) := by
  rcases xs with ⟨xs⟩
  simp

end Array

namespace Vector

theorem mapM_toList {α β} {f : α → Option β} {xs : Vector α n} {ys : Vector β n}
  (h : xs.mapM f = some ys):
  xs.toList.mapM f = some ys.toList
:= by
  have : toArray <$> xs.mapM f = toArray <$> some ys := by simp [h]
  simp at this
  simp [Array.mapM_eq_mapM_toList] at this
  have ⟨ys', hmap, hys'⟩ := this
  simp [Vector.toList, hmap, ← hys']

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : Vector α n} {ys : Vector β n}
  (h : xs.mapM f = some ys) :
  (∀ x ∈ xs, ∃ y ∈ ys, f x = some y)
:= by
  simp [← Vector.mem_toList_iff]
  apply List.mapM_some_implies_all_some
  apply mapM_toList h

theorem mapM_push [Monad m] [LawfulMonad m]
  {f : α → m β} {xs : Vector α n} :
  (xs.push x).mapM f = (return (← xs.mapM f).push (← f x))
:= by
  apply map_toArray_inj.mp
  suffices toArray <$> (xs.push x).mapM f = (return (← toArray <$> xs.mapM f).push (← f x)) by
    rw [this]
    simp only [bind_pure_comp, Functor.map_map, bind_map_left, map_bind, toArray_push]
  simp

theorem mem_pop_implies_mem
  {xs : Vector α (n + 1)}
  (h : x ∈ xs.pop) : x ∈ xs
:= by
  simp [Vector.pop, Array.pop] at h
  apply Vector.mem_toList_iff.mp
  simp only [Vector.toList]
  exact List.mem_of_mem_dropLast h

theorem mem_pop_iff
  [NeZero n]
  {xs : Vector α n} :
  x ∈ xs ↔ x ∈ xs.pop ∨ x = xs.back
:= by
  simp [← Vector.mem_toList_iff, Vector.toList_pop]
  constructor
  · intros h
    have ⟨i, hi, hget_i⟩ := List.getElem_of_mem h
    by_cases h₁ : i = n - 1
    · simp [h₁] at hget_i
      simp [← hget_i, Vector.back]
    · left
      simp at hi
      have : x = xs.toList.dropLast[i]'(by simp; omega) := by
        simp [hget_i]
      rw [this]
      apply List.getElem_mem
  · intros h
    cases h <;> rename_i h
    · exact List.mem_of_mem_dropLast h
    · simp [Vector.back] at h
      simp [h]

theorem nodup_implies_pop_nodup
  {xs : Vector α n}
  (h : xs.toList.Nodup) :
  xs.pop.toList.Nodup
:= by
  simp [Vector.toList_pop]
  apply List.Nodup.sublist _ h
  apply List.dropLast_sublist

theorem nodup_implies_back_not_mem_pop
  [NeZero n]
  {xs : Vector α n}
  (h : xs.toList.Nodup) :
  xs.back ∉ xs.pop
:= by
  intros hmem
  simp [Vector.back, ← Vector.mem_toList_iff] at hmem
  have ⟨j, hj, hget_j⟩ := List.getElem_of_mem hmem
  simp at hget_j
  have := (List.Nodup.getElem_inj_iff h).mp hget_j
  simp at hj this
  simp [this] at hj

theorem mem_implies_mem_zip_left
  {xs : Vector α n} {ys : Vector β n}
  (h : x ∈ xs) :
  ∃ y, (x, y) ∈ xs.zip ys
:= by
  have ⟨i, hi, hget_i⟩ := Vector.getElem_of_mem h
  exists ys[i]
  simp [← hget_i, ← Vector.getElem_zip]

@[simp]
theorem back_map
  [NeZero n]
  {f : α → β} {xs : Vector α n} :
  (map f xs).back = f xs.back
:= by
  simp [getElem_map, back_eq_getElem]

@[simp]
theorem back_push
  {xs : Vector α n} :
  (xs.push x).back = x
:= by
  simp [back_eq_getElem]

theorem pop_zip
  [NeZero n]
  {xs : Vector α n} {ys : Vector β n} :
  (xs.zip ys).pop = xs.pop.zip ys.pop
:= by
  grind only [= getElem_zip, getElem_pop, cases Or]

@[simp]
theorem back_zip
  [NeZero n]
  {xs : Vector α n} {ys : Vector β n} :
  (xs.zip ys).back = (xs.back, ys.back)
:= by
  grind only [= getElem_zip, back_eq_getElem]

theorem push_zip
  {xs : Vector α n} {ys : Vector β n} :
    (xs.push x).zip (ys.push y) = (xs.zip ys).push (x, y)
  := by
    apply Vector.ext
    intros i hi
    by_cases h₁ : i = n
    · simp [h₁]
    · have : i < n := by omega
      simp [this]

theorem toList_inj_heq
  {xs : Vector α n} {ys : Vector α m}
  (h : xs.toList = ys.toList) :
    n = m ∧ xs ≍ ys
:= by
  have h₁ : n = xs.toList.length := by simp
  have h₂ : m = ys.toList.length := by simp
  have h₃ : n = m := by rw [h₁, h₂, h]
  subst h₃
  constructor
  · rfl
  · simp
    exact Vector.toList_inj.mp h

theorem inj_map
  {f : α → β}
  (hf : Function.Injective f)
  {xs ys : Vector α n}
  (h : xs.map f = ys.map f) :
    xs = ys
:= by
  apply Vector.ext
  intros i hi
  have : (map f xs)[i] = (map f ys)[i] := by
    simp only [h]
  simp at this
  exact hf this

theorem forall₂_push_toList_to_forall₂
  {α β}
  {xs : Vector α n}
  {ys : Vector β n}
  {x : α} {y : β}
  {R : α → β → Prop}
  (hforall₂ : List.Forall₂ R (xs.push x).toList (ys.push y).toList) :
    List.Forall₂ R xs.toList ys.toList ∧ R x y
:= by
  have ⟨_, hR⟩ := List.forall₂_iff_get.mp hforall₂
  simp [Vector.getElem_push] at hR
  constructor
  · apply List.forall₂_iff_get.mpr
    simp
    intros i hi _
    have := hR i (by omega)
    simp [hi] at this
    exact this
  · have := hR n (by omega)
    simp at this
    exact this

theorem forall₂_to_forall₂_push_toList
  {α β}
  {xs : Vector α n}
  {ys : Vector β n}
  {x : α} {y : β}
  {R : α → β → Prop}
  (hforall₂ : List.Forall₂ R xs.toList ys.toList)
  (hxy : R x y) :
    List.Forall₂ R (xs.push x).toList (ys.push y).toList
:= by
  apply List.forall₂_iff_get.mpr
  simp [Vector.getElem_push]
  intros i hi
  by_cases h₁ : i = n
  · subst h₁
    simp
    exact hxy
  · have : i < n := by omega
    simp [this]
    have ⟨_, h₂⟩ := List.forall₂_iff_get.mp hforall₂
    specialize h₂ i (by simp [this]) (by simp [this])
    simp at h₂
    exact h₂

theorem back_induction
  {motive : ∀ {n}, Vector α n → Prop}
  (empty : motive #v[])
  (push : ∀ {n} (xs : Vector α n) (x : α), motive xs → motive (xs.push x))
  (xs : Vector α n) : motive xs
  := by
  induction n with
  | zero => simp [empty, Vector.eq_empty]
  | succ _ ih =>
    rw [← Vector.push_pop_back xs]
    apply push
    apply ih

theorem forall₂_to_vector
  {α β}
  {xs : Vector α n}
  {ys : List β}
  {R : α → β → Prop}
  (h : List.Forall₂ R xs.toList ys) :
    ∃ ys' : Vector β n,
      ys'.toList = ys ∧
      List.Forall₂ R xs.toList ys'.toList
  := by exists (ys.toVector.cast (by simp [← h.length_eq]))

theorem forall₂_append_to_vector
  {α β}
  {xs₁ : Vector α n₁}
  {xs₂ : Vector α n₂}
  {ys : List β}
  {R : α → β → Prop}
  (h : List.Forall₂ R (xs₁.toList ++ xs₂.toList) ys) :
    ∃ (ys₁' : Vector β n₁)
      (ys₂' : Vector β n₂),
      ys = ys₁'.toList ++ ys₂'.toList ∧
      List.Forall₂ R xs₁.toList ys₁'.toList ∧
      List.Forall₂ R xs₂.toList ys₂'.toList
  := by
  exists (ys.take n₁).toVector.cast (by simp [← h.length_eq])
  exists (ys.drop n₁).toVector.cast (by simp [← h.length_eq])
  simp only [Vector.toList_cast, List.toVector]
  have h₁ := List.forall₂_take n₁ h
  have h₂ := List.forall₂_drop n₁ h
  simp at h₁ h₂
  simp [h₁, h₂]

theorem exists_inverse_to_map
  {f : α → β}
  {xs : Vector β n}
  (h : ∀ x ∈ xs, ∃ y, x = f y) :
    ∃ ys : Vector α n, xs = ys.map f
  := by
  exists xs.attach.map (λ x => (h x.val x.prop).choose)
  apply Vector.ext
  intros i hi
  simp
  exact (h xs[i] (by simp)).choose_spec

theorem forall₂_exists_map
  {α β}
  {xs : Vector α n} {ys : Vector γ n}
  {R : α → γ → Prop}
  {f : β → γ}
  (h : List.Forall₂ R xs.toList ys.toList)
  (hexists : ∀ {x y}, R x y → ∃ z, y = f z) :
    ∃ (ys' : Vector β n), ys = ys'.map f
  := by
  have := h.imp (S := λ x y => ∃ z, y = f z) (by apply hexists)
  have := List.forall₂_implies_all_left this.flip
  simp at this
  apply exists_inverse_to_map
  intros x hmem
  exact (this x hmem).2

end Vector
