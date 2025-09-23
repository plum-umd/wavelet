import Batteries.Data.List.Basic
import Mathlib.Data.List.Infix

namespace List

def toVector (xs : List α) : Vector α xs.length :=
  xs.toArray.toVector

theorem all_some_implies_mapM_some {α β} {f : α → Option β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = some y) →
  ∃ ys, mapM f xs = some ys
:= sorry

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  mapM f xs = some ys →
  (∀ x ∈ xs, ∃ y ∈ ys, f x = some y)
:= sorry

theorem mem_iff_mem_eraseDups [BEq α] {xs : List α}
  : x ∈ xs ↔ x ∈ xs.eraseDups := sorry

theorem mapM_some_iff_forall₂
  {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  mapM f xs = .some ys ↔
  Forall₂ (λ x y => f x = .some y) xs ys
:= sorry

end List

namespace Array

@[simp]
theorem mapM_push [Monad m] [LawfulMonad m] {f : α → m β} {xs : Array α} :
    (xs.push x).mapM f = (return (← xs.mapM f).push (← f x)) := by
  rcases xs with ⟨xs⟩
  simp

end Array

namespace Vector

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : Vector α n} {ys : Vector β n} :
  Vector.mapM f xs = some ys →
  (∀ x ∈ xs, ∃ y ∈ ys, f x = some y)
:= sorry

theorem mapM_toList {α β} {f : α → Option β} {xs : Vector α n} {ys : Vector β n}
  (h : Vector.mapM f xs = some ys):
  List.mapM f xs.toList = some ys.toList
:= sorry

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
  {xs : Vector α (n + 1)} :
  x ∈ xs ↔ x ∈ xs.pop ∨ x = xs.back
:= sorry

theorem nodup_implies_pop_nodup
  {xs : Vector α (n + 1)}
  (h : xs.toList.Nodup) :
  xs.pop.toList.Nodup
:= sorry

theorem nodup_implies_back_not_mem_pop
  {xs : Vector α (n + 1)}
  (h : xs.toList.Nodup) :
  xs.back ∉ xs.pop
:= sorry

end Vector
