import Batteries.Data.List.Basic
import Batteries.Data.Char.Basic

/-! Basic definitions and lemmas for common data structures that do not depend on mathlib. -/

namespace Fin

@[simp, grind]
abbrev Fin.castPred (k' : Fin (k + 1)) (self : Fin ↑k') : Fin k := self.castLT (by omega)

prefix:max " ↓ " => Fin.castPred _

end Fin

namespace Function

/-- A copy of `Function.update` to avoid dependency on mathlib from executable code. -/
def update' {α : Sort u} {β : α → Sort v} [DecidableEq α]
  (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

end Function

namespace Vector

infixr:65 " ⊗ " => Vector.zip

/-- Dynamically cast a vector and fail if the lengths don't match. -/
def castDyn [Alternative M] (xs : Vector α n) m : M (Vector α m) :=
  if h : n = m then
    pure (xs.cast h)
  else
    failure

end Vector

namespace List

def toVector (xs : List α) : Vector α xs.length :=
  xs.toArray.toVector

/-- Dynamically cast a vector and fail if the lengths don't match the expected length. -/
def toVectorDyn [Alternative M] (xs : List α) n : M (Vector α n) :=
  if h : xs.length = n then
    pure (xs.toVector.cast h)
  else
    failure

def removeDup [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (λ acc x => if x ∈ acc then acc else x :: acc) [] |>.reverse

/-- Same as `List.instMonad` in mathlib, duplicated to remove dependency. -/
instance : Monad List.{u} where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

instance : Alternative List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

instance instDecidableDisjoint [DecidableEq α] {xs ys : List α} : Decidable (xs.Disjoint ys) :=
  match xs with
  | nil => isTrue (by simp [List.Disjoint])
  | cons x xs' =>
    have : Decidable (xs'.Disjoint ys) := instDecidableDisjoint
    if h : x ∉ ys ∧ xs'.Disjoint ys then
      isTrue (by
        simp [h, List.Disjoint]
        intros x' hmem
        simp [List.Disjoint] at h
        exact h.2 hmem)
    else
      isFalse (by
        simp [List.Disjoint] at h ⊢
        exact h)

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

theorem forM_ok_iff_all_ok
  {α ε} {f : α → Except ε PUnit} {xs : List α} :
  (xs.forM f).isOk ↔ ∀ x ∈ xs, (f x).isOk
:= by
  induction xs with
  | nil => simp; rfl
  | cons x xs' ih =>
    simp
    constructor
    · intros h
      simp [bind, Except.bind] at h
      split at h; contradiction
      rename_i h₁
      simp [h₁, Except.isOk, Except.toBool]
      exact ih.mp h
    · intros h
      have ⟨h₁, h₂⟩ := h
      cases h₃ : f x <;> simp [h₃, Except.isOk, Except.toBool] at h₁
      simp [bind, Except.bind]
      exact ih.mpr h₂

theorem Disjoint.symm
  {l₁ l₂ : List α}
  (hdisj : Disjoint l₁ l₂) :
    Disjoint l₂ l₁
  := by
  intros x h₁ h₂
  exact hdisj h₂ h₁

end List

namespace Except

@[simp]
theorem mapError_ok_iff_ok
  {α} {f : ε → ε'} {e : Except ε α} :
    (e.mapError f).isOk = e.isOk
  := by cases e <;> simp [Except.mapError, isOk, Except.toBool]

def unwrapIO {ε α} (e : Except ε α) (msg : String) [ToString ε] : IO α :=
  match e with
  | .ok x => pure x
  | .error err => throw <| IO.userError s!"{msg}: {toString err}"

def context {ε α} (e : Except ε α) (msg : String) [ToString ε] : Except String α :=
  match e with
  | .ok x => .ok x
  | .error err => .error s!"{msg}: {toString err}"

end Except

abbrev ExceptDec ε (p : Prop) := Except (ε × PLift ¬p) (PLift p)

namespace ExceptDec

/-- Dynamically decides a proposition, and returns its proof. -/
def check (p : Prop) [Decidable p] (e : ε) : ExceptDec ε p :=
  if h : p then
    .ok (.up h)
  else
    .error (e, .up h)

/-- Converts one `ExceptDec` to another. -/
def necessary (ed : ExceptDec ε q) (hpq : p → q) : Except (ε × PLift ¬p) (PLift q) :=
  match ed with
  | .ok hq => .ok hq
  | .error (e, h) => .error (e, .up (λ hp => h.down (hpq hp)))

def toDecidable (ed : ExceptDec ε p) : Decidable p :=
  match ed with
  | .ok h => isTrue h.down
  | .error (_, h) => isFalse h.down

def resolve (ed : ExceptDec ε p) : Except ε Unit :=
  match ed with
  | .ok _ => .ok ()
  | .error (e, _) => .error e

end ExceptDec

namespace Option

def toExcept {ε α} (o : Option α) (e : ε) : Except ε α :=
  match o with
  | some x => .ok x
  | none => .error e

def unwrapIO {α} (o : Option α) (msg : String) : IO α :=
  match o with
  | some x => pure x
  | none => throw <| IO.userError msg

end Option

namespace String

def replicateChar (n : Nat) (c : Char) : String := .mk (List.replicate n c)

end String

namespace Lean.Json

def decode [Lean.FromJson α] (src : String) : Except String α :=
  parse src >>= Lean.FromJson.fromJson?

def decodeFile [Lean.FromJson α] (path : String) : IO α := do
  let input ← IO.FS.readFile path
  (decode input).unwrapIO s!"failed to deserialize JSON from {path}"

def encodePretty [Lean.ToJson α] (x : α) : String :=
  pretty (Lean.ToJson.toJson x)

def encodeCompact [Lean.ToJson α] (x : α) : String :=
  compress (Lean.ToJson.toJson x)

def encodeToFilePretty [Lean.ToJson α] (path : String) (x : α) : IO Unit :=
  IO.FS.writeFile path (encodePretty x)

def encodeToFileCompact [Lean.ToJson α] (path : String) (x : α) : IO Unit :=
  IO.FS.writeFile path (encodeCompact x)

end Lean.Json
