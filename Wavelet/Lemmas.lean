import Batteries.Data.List.Basic

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

namespace Vector

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : Vector α n} {ys : Vector β n} :
  Vector.mapM f xs = some ys →
  (∀ x ∈ xs, ∃ y ∈ ys, f x = some y)
:= sorry

theorem mapM_toList {α β} {f : α → Option β} {xs : Vector α n} {ys : Vector β n}
  (h : Vector.mapM f xs = some ys):
  List.mapM f xs.toList = some ys.toList
:= sorry

end Vector
