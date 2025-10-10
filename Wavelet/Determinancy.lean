import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Reasoning about the determinancy of semantics. -/

namespace Wavelet.Semantics

open Semantics

abbrev CompatRel V := ∀ {n m}, Vector V n → Vector V m → Prop

/-- Any yielding transitions from the same state commute,
if a certain compatibility constraint holds on the inputs. -/
def CommYields
  [Arity Op]
  (Compat : CompatRel V)
  (sem : Semantics Op V m n)
  : Prop :=
  ∀ s s₁ s₂
    op₁ inputs₁ outputs₁
    op₂ inputs₂ outputs₂,
    sem.lts.Step s (.yield op₁ inputs₁ outputs₁) s₁ →
    sem.lts.Step s (.yield op₂ inputs₂ outputs₂) s₂ →
    Compat inputs₁ inputs₂ →
    ∃ s',
      sem.lts.Step s₁ (.yield op₂ inputs₂ outputs₂) s' ∧
      sem.lts.Step s₂ (.yield op₁ inputs₁ outputs₁) s'

def OpInterp.Determinant
  [Arity Op]
  (Compat : CompatRel V)
  (interp : OpInterp Op V)
  : Prop :=
  ∀ s s₁ s₂
    op₁ inputs₁ outputs₁
    op₂ inputs₂ outputs₂,
    interp.interp op₁ inputs₁ s outputs₁ s₁ →
    interp.interp op₂ inputs₂ s outputs₂ s₂ →
    Compat inputs₁ inputs₂ →
    ∃ s',
      interp.interp op₁ inputs₁ s₂ outputs₁ s' ∧
      interp.interp op₂ inputs₂ s₁ outputs₂ s'

/-
Three pieces:
- A state invariant `P : S → Prop` on each semantics
- A guarded transition that enforces the invariant on the base transition
- Proof obligations
  - Simulation between guarded transitions
  - Invariant implies compatibility relation of values (obligation of the semantics)
  - Compatibility relation implies commutative operators (obligation of op interp)
  - Typing in Seq implies progress in the guarded transition

Maybe just specialize to PCMs?

class WithToken V where
  token : V → PCM

State invariant on Seq: for any two values v₁ v₂ in the config, token v₁ ⊥ token v₂
-/

inductive GuardedLts {S} (Inv : S → Prop) (lts : Lts S E) : Lts S E where
  | step : Inv s → Inv s' → lts.Step s e s' → GuardedLts Inv lts s e s'

/-- Guard the transition of a semantics with the given invariant. -/
def guard [Arity Op]
  (sem : Semantics Op V m n)
  (Inv : sem.S → Prop) : Semantics Op V m n :=
  {
    S := sem.S,
    init := sem.init,
    lts := GuardedLts Inv sem.lts,
    -- TODO: this is actually not true,
    -- maybe remove this requirement?
    yields_functional := sorry
  }

class PCM (C : Type u) where
  add : C → C → C
  zero : C
  valid : C → Prop
  eq : C → C → Prop

infixl:60 " ⬝ " => PCM.add
infix:50 " ≡ " => PCM.eq
prefix:40 "✓ " => PCM.valid

def PCM.disjoint {C : Type u} [PCM C] (a b : C) : Prop := ✓ a ⬝ b

/-- TODO: Implement some type class for partial order. -/
def PCM.le {C : Type u} [PCM C] (a b : C) : Prop := ∃ c, b ≡ a ⬝ c

def PCM.framePreserving {C : Type u} [PCM C] (a b : C) : Prop :=
  ∀ c, ✓ a ⬝ c → ✓ b ⬝ c

infix:50 " ⊥ " => PCM.disjoint
infix:50 " ≤ " => PCM.le
infix:50 " ⟹ " => PCM.framePreserving

class LawfulPCM (R : Type u) [inst : PCM R] where
  add_comm : ∀ a b : R, a ⬝ b ≡ b ⬝ a
  add_assoc : ∀ a b c : R, (a ⬝ b) ⬝ c ≡ a ⬝ (b ⬝ c)
  add_ident : ∀ a : R, a ⬝ inst.zero ≡ a
  valid_add : ∀ a b : R, ✓ a ⬝ b → ✓ a
  valid_zero : ✓ inst.zero
  valid_eq : ∀ a b : R, a ≡ b → ✓ a → ✓ b
  eq_refl : ∀ a : R, a ≡ a
  eq_symm : ∀ a b : R, a ≡ b → b ≡ a
  eq_trans : ∀ a b c : R, a ≡ b → b ≡ c → a ≡ c

/-- Uses only the LHS `InterpConsts` of a sum for constants. -/
instance instInterpConstsSum [left : InterpConsts V] : InterpConsts (V ⊕ V') where
  junkVal := .inl (left.junkVal)
  toBool
    | .inl v => left.toBool v
    | .inr _ => none
  fromBool := .inl ∘ left.fromBool
  unique_fromBool_toBool b := left.unique_fromBool_toBool b
  unique_toBool_fromBool b v hv := by
    split at hv
    · rename_i v'
      have := left.unique_toBool_fromBool b v' hv
      simp [this]
    · contradiction

end Wavelet.Semantics

namespace Wavelet.Seq

open Semantics Compile

def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  ∀ x₁ x₂ t₁ t₂,
    x₁ ≠ x₂ →
    c.vars.getVar x₁ = some (.inr t₁) →
    c.vars.getVar x₂ = some (.inr t₂) →
    t₁ ⊥ t₂

end Wavelet.Seq

namespace Wavelet.Dataflow

open Semantics

def Config.DisjointTokens
  [Arity Op] [PCM T]
  (c : Config Op χ (V ⊕ T) m n) : Prop :=
  ∀ x₁ x₂
    (buf₁ buf₂ : List (V ⊕ T))
    (i : Fin buf₁.length) (j : Fin buf₂.length)
    t₁ t₂,
    x₁ ≠ x₂ ∨ i.val ≠ j.val →
    c.chans x₁ = some buf₁ →
    c.chans x₂ = some buf₂ →
    buf₁[i] = .inr t₁ →
    buf₂[j] = .inr t₂ →
    t₁ ⊥ t₂

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Seq Dataflow

theorem sim_compile_fn'
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  (fn : Fn Op χ (V ⊕ T) m n)
  (hnz : m > 0 ∧ n > 0)
  (hwf : fn.AffineVar) :
  fn.semantics.guard (Config.DisjointTokens)
    ≲ᵣ (compileFn hnz fn).semantics.guard (Config.DisjointTokens)
  := sorry

-- theorem fn_progress
--   [Arity Op]
--   [InterpConsts V]
--   [WithToken V T]
--   [PCM T]
--   [DecidableEq χ]
--   (fn : Fn Op χ V m n)
--   (hnz : m > 0 ∧ n > 0)
--   (hwf : fn.AffineVar)
--   (hwell_typed : sorry) :
--   fn.semantics -- Maybe even add the tokens here?
--     ≲ᵣ fn.semantics.guard (Config.DisjointTokens T)
--   := sorry

end Wavelet.Compile
