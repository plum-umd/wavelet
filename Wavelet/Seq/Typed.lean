import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Wavelet.Seq.Fn

namespace Wavelet.Seq

open Semantics

universe u v w

/-- Base types for l0. Instances of this class
    provide at least a distinguished boolean type. One can extend
    `τ` with further constructors (e.g. integers, units) by
    defining an appropriate instance of `BaseTy`. -/
class BaseTy (τ : Type w) where
  boolTy : τ

/-- Given an operator set `Op`, an `OpTy` instance assigns to each
    operator `o : Op` a vector of input types of length `Arity.ι o`
    and a vector of output types of length `Arity.ω o`. -/
class OpTy (τ : Type w) (Op : Type v) [Arity Op] where
  inputTypes  : (o : Op) → Vector τ (Arity.ι o)
  outputTypes : (o : Op) → Vector τ (Arity.ω o)

abbrev TyEnv (χ : Type u) (τ : Type w) := χ → Option τ

namespace TyEnv

variable {χ : Type u} {τ : Type w}

/-- The empty type environment with no bindings. -/
def empty : TyEnv χ τ := λ _ => none

/-- Insert a vector of variables together with a vector of types into
    an existing environment. -/
def insertVars [DecidableEq χ]
    {n : Nat} (vars : Vector χ n) (tys : Vector τ n)
    (Γ : TyEnv χ τ) : TyEnv χ τ :=
  λ v =>
    ((vars.zip tys).toList.find? (·.1 = v)).map (·.2) <|> Γ v

/-- Remove a single variable from the environment. -/
def removeVar [DecidableEq χ] (x : χ) (Γ : TyEnv χ τ) : TyEnv χ τ :=
  λ y => if y = x then none else Γ y

/-- Remove a list of variables from the environment. -/
def removeVars [DecidableEq χ] (xs : List χ) (Γ : TyEnv χ τ) : TyEnv χ τ :=
  λ y => if y ∈ xs then none else Γ y

/-- Lookup the type of a variable in the environment. -/
def getVar (Γ : TyEnv χ τ) (x : χ) : Option τ := Γ x

/-- Well-typed variables -/
def wellTypedVars [DecidableEq χ]
    (vars : Vector χ n) (tys : Vector τ n) (Γ : TyEnv χ τ) : Prop :=
  List.Forall₂ (λ v ty => Γ.getVar v = some ty) vars.toList tys.toList

end TyEnv

/-- Typing judgement for expressions. -/
inductive Expr.Typed
    [Arity Op] [BaseTy τ] [OpTy τ Op] [DecidableEq χ] :
    TyEnv χ τ → Expr Op χ m n → Vector τ m → Vector τ n → Prop
  | ret
      {vars : Vector χ n} {inTys: Vector τ m} {outTys : Vector τ n}:
      Γ.wellTypedVars vars outTys →
      Expr.Typed Γ (.ret vars) inTys outTys
  | tail
      {vars : Vector χ m} {inTys: Vector τ m} {outTys : Vector τ n}:
      Γ.wellTypedVars vars inTys →
      Expr.Typed Γ (.tail vars) inTys outTys
  | op
      {args : Vector χ (Arity.ι o)} {rets : Vector χ (Arity.ω o)}
      {inTys : Vector τ m} {outTys : Vector τ n}:
      Γ.wellTypedVars args (OpTy.inputTypes o) →
      Expr.Typed (Γ.insertVars rets (OpTy.outputTypes o)) cont inTys outTys →
      Expr.Typed Γ (.op o args rets cont) inTys outTys
  | br {cond : χ}
      {inTys : Vector τ m} {outTys : Vector τ n}:
      TyEnv.getVar Γ cond = some (BaseTy.boolTy) →
      Expr.Typed Γ left inTys outTys →
      Expr.Typed Γ right inTys outTys →
      Expr.Typed Γ (.br cond left right) inTys outTys

def Fn.Typed
    [BaseTy τ] [Arity Op] [OpTy τ Op] [DecidableEq χ] :
    Fn Op χ V m n → Vector τ m → Vector τ n → Prop
  | ⟨params, body⟩, inTys, outTys =>
      let Γ₀ := TyEnv.insertVars params inTys TyEnv.empty
      Expr.Typed Γ₀ body inTys outTys

/-- A capability annotates an array with two finite sets of indices.
    The set `shrd` tracks indices for which shared (read‑only)
    permissions are available; the set `uniq` tracks indices for
    which unique (read/write) permissions are available.  The
    `disjoint` proof ensures that these regions do not overlap. -/
structure Capability where
  shrd : Finset ℕ
  uniq : Finset ℕ
  disjoint : Disjoint shrd uniq

namespace Capability

/-- The empty capability grants no permissions. -/
def empty : Capability :=
  { shrd := ∅, uniq := ∅, disjoint := by simp }

/-- Remove a single index from the unique region of a capability. -/
def removeUniq (i : ℕ) (c : Capability) : Capability :=
  { shrd := c.shrd,
    uniq := c.uniq.erase i,
    disjoint := by
      have h : Disjoint c.shrd c.uniq := c.disjoint
      -- Erasing an element from `uniq` preserves disjointness.
      exact h.mono_right (Finset.erase_subset _ _) }

/-- Compose two capabilities when they are compatible.  Composition
    merges the shared and unique regions if no conflict arises:
    unique regions must be pairwise disjoint, and no unique region
    may overlap with a shared region from the other side. -/
def compose (c₁ c₂ : Capability) : Option Capability :=
  if h₁ : Disjoint c₁.uniq c₂.uniq ∧ Disjoint c₁.uniq c₂.shrd ∧ Disjoint c₂.uniq c₁.shrd then
    some
      { shrd := c₁.shrd ∪ c₂.shrd,
        uniq := c₁.uniq ∪ c₂.uniq,
        disjoint := by
          obtain ⟨h₁₁, h₁₂, h₁₃⟩ := h₁
          apply Finset.disjoint_union_left.mpr
          constructor
          · apply Finset.disjoint_union_right.mpr
            exact ⟨c₁.disjoint, h₁₃.symm⟩
          · apply Finset.disjoint_union_right.mpr
            exact ⟨h₁₂.symm, c₂.disjoint⟩
      }
  else
    none

/-- Capability ordering: `c₁ ≤ c₂` iff every read permission in
    `c₁` is available as either a read or a write permission in `c₂`
    and every write permission in `c₁` is available as a write
    permission in `c₂`. -/
def le (c₁ c₂ : Capability) : Prop :=
  c₁.shrd ⊆ (c₂.shrd ∪ c₂.uniq) ∧ c₁.uniq ⊆ c₂.uniq

instance : LE Capability := ⟨le⟩

instance {c₁ c₂ : Capability} : Decidable (c₁ ≤ c₂) :=
  inferInstanceAs (Decidable (c₁.shrd ⊆ (c₂.shrd ∪ c₂.uniq) ∧ c₁.uniq ⊆ c₂.uniq))

/-- Minus operation: `c₁ - c₂` is defined if `c₂ ≤ c₁`, and removes the shared
  and unique permissions in `c₂` from `c₁`'s unique permissions, while moving
  the shared permissions in `c₂` to `c₁`'s shared permissions. -/
def minus (c₁ c₂ : Capability) : Option Capability :=
  if h : c₂ ≤ c₁ then
    some
      { shrd := c₁.shrd ∪ c₂.shrd,
        uniq := c₁.uniq \ (c₂.shrd ∪ c₂.uniq),
        disjoint := by
          apply Finset.disjoint_union_left.mpr
          constructor
          · -- c₁.shrd is disjoint from the result's uniq (subset of c₁.uniq)
            exact c₁.disjoint.mono_right Finset.sdiff_subset
          · -- c₂.shrd is disjoint from the result's uniq (which excludes c₂.shrd)
            simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_union, not_and, not_or]
            intros x hx _ h_not_in
            exact (h_not_in hx).elim
      }
  else
    none

@[ext]
theorem ext (c₁ c₂ : Capability) (h₁ : c₁.shrd = c₂.shrd) (h₂ : c₁.uniq = c₂.uniq) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

/-- instance for PartialOrder -/
instance : PartialOrder Capability where
  le := le
  le_refl c := ⟨Finset.subset_union_left, subset_refl _⟩
  le_trans c₁ c₂ c₃ h₁ h₂ := by
    obtain ⟨h₁₁, h₁₂⟩ := h₁
    obtain ⟨h₂₁, h₂₂⟩ := h₂
    constructor
    · -- c₁.shrd ⊆ (c₃.shrd ∪ c₃.uniq)
      calc c₁.shrd
        _ ⊆ c₂.shrd ∪ c₂.uniq     := h₁₁
        _ ⊆ c₃.shrd ∪ c₃.uniq     := Finset.union_subset h₂₁ (subset_trans h₂₂ Finset.subset_union_right)
    · -- c₁.uniq ⊆ c₃.uniq
      exact subset_trans h₁₂ h₂₂
  le_antisymm c₁ c₂ h₁ h₂ := by
    obtain ⟨h₁₁, h₁₂⟩ := h₁
    obtain ⟨h₂₁, h₂₂⟩ := h₂
    have uniq_eq : c₁.uniq = c₂.uniq := subset_antisymm h₁₂ h₂₂
    have shrd_eq : c₁.shrd = c₂.shrd := by
      apply subset_antisymm
      · -- c₁.shrd ⊆ c₂.shrd
        intro x hx
        have : x ∈ c₂.shrd ∪ c₂.uniq := h₁₁ hx
        rw [Finset.mem_union] at this
        rcases this with h_shrd | h_uniq
        · exact h_shrd
        · -- Contradiction with disjointness
          rw [←uniq_eq] at h_uniq
          exact absurd (Finset.mem_inter.mpr ⟨hx, h_uniq⟩) (Finset.disjoint_iff_inter_eq_empty.mp c₁.disjoint ▸ Finset.notMem_empty x)
      · -- c₂.shrd ⊆ c₁.shrd
        intro x hx
        have : x ∈ c₁.shrd ∪ c₁.uniq := h₂₁ hx
        rw [Finset.mem_union] at this
        rcases this with h_shrd | h_uniq
        · exact h_shrd
        · rw [uniq_eq] at h_uniq
          exact absurd (Finset.mem_inter.mpr ⟨hx, h_uniq⟩) (Finset.disjoint_iff_inter_eq_empty.mp c₂.disjoint ▸ Finset.notMem_empty x)
    ext <;> simp [shrd_eq, uniq_eq]

end Capability

/-- A capability environment for arrays. -/
abbrev CapEnv (χ : Type u) := χ → Option Capability

namespace CapEnv

def empty : CapEnv χ := λ _ => none

def get (Δ : CapEnv χ) (A : χ) : Option Capability := Δ A

def update [DecidableEq χ] (Δ : CapEnv χ) (A : χ) (cap : Capability) : CapEnv χ :=
  λ B => if B = A then some cap else Δ B

/-- Pointwise comparison on capability environments. -/
def le (Δ₁ Δ₂ : CapEnv χ) : Prop :=
  ∀ A c₁, Δ₁ A = some c₁ → (∃ c₂, Δ₂ A = some c₂ ∧ c₁ ≤ c₂)

instance : LE (CapEnv χ) := ⟨CapEnv.le⟩

def leCheck [DecidableEq χ] (vars : List χ) (Δ₁ Δ₂ : CapEnv χ) : Bool :=
  vars.all fun A =>
    match Δ₁ A with
    | none => true
    | some c₁ =>
      match Δ₂ A with
      | none => false
      | some c₂ => decide (c₁ ≤ c₂)

/-- If leCheck returns true for all variables in scope, then Δ₁ ≤ Δ₂. -/
theorem leCheck_sound [DecidableEq χ] (vars : List χ)
    (h_complete : ∀ A c₁, Δ₁ A = some c₁ → A ∈ vars) :
    leCheck vars Δ₁ Δ₂ = true → Δ₁ ≤ Δ₂ := by
  intro h A c₁ h₁
  have : A ∈ vars := h_complete A c₁ h₁
  simp [leCheck, List.all_eq_true] at h
  have := h A this
  simp [h₁] at this
  cases h₂ : Δ₂ A
  · simp [h₂] at this
  · rename_i c₂
    simp [h₂] at this
    exact ⟨c₂, rfl, this⟩

def minus [DecidableEq χ] (Δ₁ Δ₂ : CapEnv χ) (vars : List χ) : Option (CapEnv χ) :=
  if leCheck vars Δ₂ Δ₁ then
    some (λ A =>
      match Δ₁ A, Δ₂ A with
      | some c₁, some c₂ => Capability.minus c₁ c₂
      | some c₁, none   => some c₁
      | none, _         => none)
  else
    none

end CapEnv

/-- A proposition context together with an entailment relation.  To
    instantiate this class one must specify the type of propositions
    and define what it means for a context to entail a proposition. -/
class PropCtx (PCxt : Type) where
  entails : PCxt → Prop → Prop

class IntBaseTy (τ : Type w) extends BaseTy τ where
  intTy : τ

structure ArrayDecl (χ : Type u) where
  name : χ
  size : Nat

structure FnSig (Op : Type v) (χ : Type u) (τ : Type w) [Arity Op] where
  params : Vector χ m
  paramTypes : Vector τ m
  retTypes : Vector τ n
  initCap : Vector χ m → CapEnv χ
  body : Expr Op χ m n

/-- Specification of primitive operators including resource usage. -/
class OpSpec (τ : Type w) (Op : Type v) (PCxt : Type)
  [Arity Op] [PropCtx PCxt] extends OpTy τ Op where
  haveCap : (o : Op) → Vector χ (Arity.ι o) → CapEnv χ → PCxt → Prop
  updateCap : (o : Op) → Vector χ (Arity.ι o) → CapEnv χ → CapEnv χ
  updatePhi : (o : Op) → Vector χ (Arity.ι o) → PCxt → PCxt

-- Θ; Γ; Δ; Φ ⊨ e: Θ.retTypes
inductive Expr.TypedMem [Arity Op] [IntBaseTy τ] [OpTy τ Op]
    [DecidableEq χ] {PCxt : Type} [PropCtx PCxt] [OpSpec τ Op PCxt]:
    FnSig Op χ τ → TyEnv χ τ → CapEnv χ → PCxt → Expr Op χ m n → Prop
  | ret
      {Θ : FnSig Op χ τ} {Γ : TyEnv χ τ} {Δ : CapEnv χ} {Φ : PCxt}
      {xs : Vector χ n} :
      Γ.wellTypedVars xs Θ.retTypes →
      Expr.TypedMem Θ Γ Δ Φ (.ret xs)
  | tail
      {Θ : FnSig Op χ τ} {Γ : TyEnv χ τ} {Δ : CapEnv χ} {Φ : PCxt}
      {xs : Vector χ m} :
      Γ.wellTypedVars xs Θ.paramTypes →
      -- current capability in Δ should include needed capability
      Θ.initCap xs ≤ Δ →
      Expr.TypedMem Θ Γ Δ Φ (.tail xs)
  | op
      {Θ : FnSig Op χ τ} {Γ : TyEnv χ τ} {Δ : CapEnv χ} {Φ : PCxt}
      {o : Op} {args : Vector χ (Arity.ι o)} {rets : Vector χ (Arity.ω o)}
      {cont : Expr Op χ m n} :
      Γ.wellTypedVars args (OpTy.inputTypes o) →
      @OpSpec.haveCap τ Op PCxt _ _ _ _ o args Δ Φ →
      (let Γ' := Γ.insertVars rets (OpTy.outputTypes o)
      let Δ' := @OpSpec.updateCap τ Op PCxt _ _ _ _ o args Δ
      let Φ' := @OpSpec.updatePhi τ Op PCxt _ _ _ _ o args Φ
      Expr.TypedMem Θ Γ' Δ' Φ' cont) →
      Expr.TypedMem Θ Γ Δ Φ (.op o args rets cont)
  | br
      {Θ : FnSig Op χ τ} {Γ : TyEnv χ τ} {Δ : CapEnv χ} {Φ : PCxt}
      {b : χ} {eₗ eᵣ : Expr Op χ m n} :
      TyEnv.getVar Γ b = some BaseTy.boolTy →
      Expr.TypedMem Θ Γ Δ Φ eₗ →
      Expr.TypedMem Θ Γ Δ Φ eᵣ →
      Expr.TypedMem Θ Γ Δ Φ (.br b eₗ eᵣ)
end Wavelet.Seq
