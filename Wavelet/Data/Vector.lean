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

end Vector
