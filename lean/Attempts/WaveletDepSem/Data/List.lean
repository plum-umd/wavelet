import Mathlib.Data.List.Infix
import Mathlib.Data.List.Forall2

/-!
Some proofs are adapted from
https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean/Cedar/Thm/Data/List
-/
namespace List

def toVector (xs : List α) : Vector α xs.length :=
  xs.toArray.toVector

theorem all_some_implies_mapM_some {α β} {f : α → Option β} {xs : List α}
  (h : ∀ x ∈ xs, ∃ y, f x = some y) :
  ∃ ys, mapM f xs = some ys
:= by
  induction xs with
  | nil => exists []
  | cons xhd xtl ih =>
    simp only [mem_cons, forall_eq_or_imp] at h
    replace ⟨⟨yhd, h₁⟩, h₂⟩ := h
    replace ⟨ytl, ih⟩ := ih h₂
    exists yhd :: ytl
    simp [h₁, ih, pure]

theorem mapM_some_iff_forall₂
  {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  mapM f xs = .some ys ↔
  Forall₂ (λ x y => f x = .some y) xs ys
:= by
  constructor
  case mp =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [mapM_nil, pure] at h₁
      injection h₁; rename_i h₁
      subst h₁
      exact List.Forall₂.nil
    case cons xhd xtl ih =>
      simp only [mapM_cons, pure] at h₁
      cases h₂ : f xhd <;>
      simp only [h₂, Option.bind_eq_bind, Option.bind, reduceCtorEq] at h₁
      rename_i yhd
      cases mapM' f xtl
      · split at h₁
        . contradiction
        . simp at h₁
          rename_i a h₂
          rw [← h₁]
          specialize ih h₂
          apply Forall₂.cons
          . rename_i h₃ h₄ h₅
            exact h₃
          . exact ih
      · split at h₁
        . contradiction
        . simp at h₁
          rename_i a h₂
          rw [← h₁]
          specialize ih h₂
          apply Forall₂.cons
          . rename_i h₃ h₄ h₅ h₆
            exact h₃
          . exact ih
  case mpr =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [forall₂_nil_left_iff] at h₁
      simp only [mapM_nil, pure, h₁]
    case cons xhd xtl ih =>
      simp only [mapM_cons, pure]
      replace ⟨yhd, ytl, h₁, h₃, h₄⟩ := forall₂_cons_left_iff.mp h₁
      subst ys
      cases h₂ : f xhd
      case none => simp [h₁] at h₂
      case some y' =>
        simp [h₁] at h₂
        specialize ih h₃
        simp only [ih]
        simp [Option.some.injEq, cons.injEq, and_true]
        rw [h₂]

theorem forall₂_implies_all_left {α β} {R : α → β → Prop} {xs : List α} {ys : List β} :
  List.Forall₂ R xs ys →
  ∀ x ∈ xs, ∃ y ∈ ys, R x y
:= by
  intro h
  induction h
  case nil =>
    simp only [not_mem_nil, false_and, exists_false, imp_self, implies_true]
  case cons xhd yhd xtl ytl hhd _ ih =>
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with hx | hx
    · subst hx
      exists yhd
      simp only [mem_cons, true_or, hhd, and_self]
    · have ⟨y, ih⟩ := ih x hx
      exists y
      simp only [mem_cons, ih, or_true, and_self]

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : List α} {ys : List β}
  (h : mapM f xs = some ys) :
  (∀ x ∈ xs, ∃ y ∈ ys, f x = some y)
:= forall₂_implies_all_left (mapM_some_iff_forall₂.mp h)

theorem mem_implies_mem_eraseDups
  [BEq α] [LawfulBEq α]
  {xs : List α} {x : α}
  (hmem : x ∈ xs) :
  x ∈ xs.eraseDups
:= by
  cases xs with
  | nil => contradiction
  | cons hd tl =>
    simp only [List.eraseDups_cons, List.mem_cons]
    simp only [List.mem_cons] at hmem
    cases hx : x == hd
    · simp only [beq_eq_false_iff_ne, ne_eq] at hx
      apply Or.inr
      simp only [hx, false_or] at hmem
      apply mem_implies_mem_eraseDups
      apply List.mem_filter.mpr
      simp only [hmem, true_and]
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      exact hx
    · apply Or.inl
      simp only [beq_iff_eq] at hx
      exact hx
termination_by xs.length
decreasing_by
  calc
    (List.filter (fun b => !b == hd) tl).length <= tl.length := by
      apply List.length_filter_le
    _ < xs.length := by
      simp [*]

theorem mem_eraseDups_implies_mem
  [BEq α] [LawfulBEq α]
  {xs : List α} {x : α}
  (hmem : x ∈ xs.eraseDups) :
  x ∈ xs
:= by
  cases xs with
  | nil => contradiction
  | cons hd tl =>
    simp only [eraseDups_cons, mem_cons] at hmem
    simp only [mem_cons]
    cases hmem with
    | inl h => exact Or.inl h
    | inr h =>
      apply Or.inr
      have := mem_eraseDups_implies_mem h
      have := List.mem_filter.mp this
      exact this.1
termination_by xs.length
decreasing_by
  calc
    (List.filter (fun b => !b == hd) tl).length <= tl.length := by
      apply List.length_filter_le
    _ < xs.length := by
      simp [*]

theorem mem_iff_mem_eraseDups [BEq α] [LawfulBEq α] {xs : List α}
  : x ∈ xs ↔ x ∈ xs.eraseDups :=
  ⟨mem_implies_mem_eraseDups, mem_eraseDups_implies_mem⟩

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
:= by simp

theorem getElem_of_append_cons
  {l l₁ l₂ : List α} {x : α}
  (h : l = l₁ ++ x :: l₂) :
  l[l₁.length]'(by simp [h]) = x
:= by simp [h]

theorem mem_set_ne
  {l : List α} {i j : Nat} {x y : α}
  (hj : j < l.length)
  (hget₂ : l[j] = y)
  (hne : i ≠ j) : y ∈ l.set i x
:= by
  apply mem_of_getElem (i := j)
  rw [List.getElem_set_ne hne]
  · exact hget₂
  · simp [hj]

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
  simp only [mem_mapIdx, ↓existsAndEq, true_and]
  exists i, hlt
  simp [hget_x, hmem_x']

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

instance Forall₂.instRefl {R : α → α → Prop} [IsRefl α R] :
  IsRefl (List α) (List.Forall₂ R) where
  refl xs := by
    induction xs with
    | nil => simp only [List.Forall₂.nil]
    | cons hd tl ih =>
      simp only [List.Forall₂.cons, IsRefl.refl, ih]

instance Forall₂.instSymm {R : α → α → Prop} [symm : IsSymm α R] :
  IsSymm (List α) (List.Forall₂ R) where
  symm xs ys h := by
    apply List.Forall₂.flip
    apply List.Forall₂.imp _ h
    exact symm.symm

instance Forall₂.instTrans {R : α → α → Prop} [trans : IsTrans α R] :
  IsTrans (List α) (List.Forall₂ R) where
  trans xs ys zs h₁ h₂ := by
    have := trans.trans
    simp [List.forall₂_iff_get] at h₁ h₂ ⊢
    grind only

/-- Produces an index in a flattened list so that updating the index
is the same as updating the corresponding sublist and then flatten. -/
theorem flatten_update_index
  {xs : List (List α)} {x : α}
  {i : Nat} {j : Nat}
  (hi : i < xs.length)
  (hj : j < xs[i].length)
  (hget : xs[i][j] = x) :
    ∃ k : Fin xs.flatten.length,
      xs.flatten[k] = x ∧
      ∀ x', xs.flatten.set k x' = (xs.set i (xs[i].set j x')).flatten
  := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
    simp at hi
    by_cases h₁ : i = 0
    · subst h₁
      simp at hget hj
      exists ⟨j, by simp; omega⟩
      simp [hj, hget]
    · cases i; simp at h₁
      rename_i i'
      simp at hget hi hj
      have ⟨⟨k', hk'⟩, hget_k', hupdate'⟩ := ih hi hj hget
      simp at hk' hget_k' hupdate'
      exists ⟨head.length + k', by simp [hk']⟩
      simp [hget_k']
      exact hupdate'

theorem forall₂_set
  {xs : List α} {ys : List β}
  {x : α} {y : β}
  {R : α → β → Prop}
  (hforall₂ : List.Forall₂ R xs ys)
  (hset : R x y) :
    List.Forall₂ R (xs.set i x) (ys.set i y)
  := by
  apply List.forall₂_iff_get.mpr
  simp [hforall₂.length_eq]
  intros k hk _
  by_cases h₁ : k = i
  · subst h₁
    simp [hset]
  · simp [Ne.symm h₁]
    apply (List.forall₂_iff_get.mp hforall₂).2

theorem forall₂_replicate
  (h : R x y) : List.Forall₂ R (List.replicate k x) (List.replicate k y)
  := by
  apply List.forall₂_iff_get.mpr
  simp [h]

theorem forall₂_append
  {xs₁ xs₂ : List α}
  {ys₁ ys₂ : List β}
  {R : α → β → Prop}
  (h₁ : List.Forall₂ R xs₁ ys₁)
  (h₂ : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  := by
  apply List.forall₂_iff_get.mpr
  simp [h₁.length_eq, h₂.length_eq]
  intros i hi hi'
  simp [List.getElem_append, h₁.length_eq]
  split <;> rename_i h
  · exact (List.forall₂_iff_get.mp h₁).2 i
      (by simp [h₁.length_eq]; exact h) h
  · exact (List.forall₂_iff_get.mp h₂).2 (i - ys₁.length)
      (by simp [h₂.length_eq]; omega)
      (by omega)

end List
