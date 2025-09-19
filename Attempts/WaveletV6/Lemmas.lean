
namespace List

theorem all_some_implies_mapM_some {α β} {f : α → Option β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = some y) →
  ∃ ys, List.mapM f xs = some ys
:= sorry

theorem mem_iff_mem_eraseDups [BEq α] {xs : List α} : x ∈ xs ↔ x ∈ xs.eraseDups := sorry

end List
