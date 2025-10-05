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

theorem disjoint_implies_filter_disjoint_left
  {l₁ l₂ : List α}
  (hdisj : Disjoint l₁ l₂) :
  Disjoint (l₁.filter f) l₂
:= by
  intros x h₁ h₂
  have := List.mem_of_mem_filter h₁
  exact hdisj this h₂

theorem to_append_cons
  {l : List α} {i : Nat}
  (hi : i < l.length) :
  l = l.take i ++ l[i] :: l.drop (i + 1)
:= sorry

theorem mem_to_mem_removeAll
  [DecidableEq α]
  {x : α} {l₁ l₂ : List α}
  (h₁ : x ∈ l₁)
  (h₂ : x ∉ l₂) :
  x ∈ (l₁.removeAll l₂)
  := by
  simp [List.removeAll]
  grind

theorem mem_flatten_mapIdx
  {xs : List α} {x : α} {x' : β}
  {f : Nat → α → List β}
  (hmem_x : x ∈ xs)
  (hmem_x' : ∀ i, x' ∈ f i x):
  x' ∈ (xs.mapIdx f).flatten
  := by
  have ⟨i, hlt, hget_x⟩ := List.mem_iff_getElem.mp hmem_x
  apply List.mem_flatten.mpr
  simp
  exists f i xs[i]
  constructor
  · exists i, hlt
  · simp [hget_x, hmem_x']

theorem mem_flatten_map
  {xs : List α} {x : α} {x' : β}
  {f : α → List β}
  (hmem_x : x ∈ xs)
  (hmem_x' : x' ∈ f x):
  x' ∈ (xs.map f).flatten
  := by
  apply List.mem_flatten.mpr
  simp
  exists x

end List
