import Wavelet.Semantics
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Reasoning about the determinancy of semantics. -/

namespace Wavelet.Semantics

open Semantics

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

/-
Maybe easier to directly do the Label translation in `GuardedLts`?
-/

/-- Restricts an LTS by imposing a state invariant,
and also transforms the label. -/
inductive Lts.Guard {S} (InvS : S → Prop) (InvE : E → E' → Prop) (lts : Lts S E) : Lts S E' where
  | step :
    InvS s → InvE e e' → InvS s' →
    lts.Step s e s' →
    Guard InvS InvE lts s e' s'

/-- Guard the transition of a semantics with the given invariant. -/
def guard
  [Arity Op] [Arity Op']
  (sem : Semantics Op V m n)
  (InvS : sem.S → Prop)
  (InvE : Label Op V m n → Label Op' V' m' n' → Prop) :
  Semantics Op' V' m' n' :=
  {
    S := sem.S,
    init := sem.init,
    lts := sem.lts.Guard InvS InvE,
    -- TODO: this is actually not true,
    -- maybe remove this requirement?
    yields_functional := sorry
  }

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

/-- PCM specification of an operator set -/
structure OpSpec Op V T [Arity Op] [PCM T] where
  requires : (op : Op) → Vector V (Arity.ι op) → T
  ensures : (op : Op) → Vector V (Arity.ι op) → T
  frame_preserving : ∀ op inputs, requires op inputs ⟹ ensures op inputs

/-- Augments the operator set with an additional ghost argument
to pass a PCM token, as well as two operators to split and join PCMs. -/
inductive WithSpec (Op : Type u) [Arity Op] [PCM T] (spec : OpSpec Op V T) where
  | op (op : Op)
  | split (left : T)
  | join

instance instArityWithSpec
  [arity : Arity Op] [PCM T]
  {spec : OpSpec Op V T} :
  Arity (WithSpec Op spec) where
  ι | .op o => arity.ι o + 1
    | .split _ => 1
    | .join => 2
  ω | .op o => arity.ω o + 1
    | .split _ => 2
    | .join => 1

/-- Semantics of the base operators instrumented
with the dynamic checks for `OpSpec`. -/
instance OpInterp.withSpec
  [Arity Op] [inst : OpInterp Op V] [PCM T]
  (spec : OpSpec Op V T) :
  OpInterp (WithSpec Op spec) (V ⊕ T) where
  S := inst.S
  init := inst.init
  /-
  Checks the ghost tokens against the spec,
  then pass through the inputs/outputs to
  the base interpretation.
  -/
  interp
    | .op op, inputs, state, outputs, s' =>
        ∃ tok₁ tok₂ inputs' outputs',
          inputs.back = .inr tok₁ ∧
          outputs.back = .inr tok₂ ∧
          inputs'.map .inl = inputs.pop ∧
          outputs'.map .inl = outputs.pop ∧
          tok₁ ≡ spec.requires op inputs' ∧
          tok₂ ≡ spec.ensures op inputs' ∧
          inst.interp op inputs' state outputs' s'
    | .split left, inputs, state, outputs, s' =>
        ∃ inputTok outputTok₂,
          inputs[0]'(by simp [Arity.ι]) = .inr inputTok ∧
          outputs[0]'(by simp [Arity.ω]) = .inr left ∧
          outputs[1]'(by simp [Arity.ω]) = .inr outputTok₂ ∧
          inputTok ≡ left ⊔ outputTok₂
    | .join, inputs, state, outputs, s' =>
        ∃ inputTok₁ inputTok₂ outputTok,
          inputs[0]'(by simp [Arity.ι]) = .inr inputTok₁ ∧
          inputs[1]'(by simp [Arity.ι]) = .inr inputTok₂ ∧
          outputs[0]'(by simp [Arity.ω]) = .inr outputTok ∧
          outputTok ≡ inputTok₁ ⊔ inputTok₂

/-- Stucks if a ghost token is received as opposed to an actual value. -/
instance OpInterp.withGhost
  [Arity Op] [inst : OpInterp Op V] :
  OpInterp Op (V ⊕ T) where
  S := inst.S
  init := inst.init
  interp op inputs state outputs s' :=
    ∃ inputs' outputs',
      inputs'.map .inl = inputs ∧
      outputs'.map .inl = outputs ∧
      inst.interp op inputs' state outputs' s'

def translateLabel
  [Arity Op₁] [Arity Op₂]
  (sem : Semantics Op₁ V₁ m₁ n₁)
  (LMap : Label Op₁ V₁ m₁ n₁ → Label Op₂ V₂ m₂ n₂ → Prop) :
  Semantics Op₂ V₂ m₂ n₂ := sorry

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
  {spec : Semantics.OpSpec Op V T}
  (fn : Fn (WithSpec Op spec) χ (V ⊕ T) m n)
  (hnz : m > 0 ∧ n > 0)
  (hwf : fn.AffineVar) :
  fn.semantics.guard Config.DisjointTokens (λ _ => True)
    ≲ᵣ (compileFn hnz fn).semantics.guard Config.DisjointTokens (λ _ => True)
  := sorry

theorem sim_compile_prog'
  [Arity Op]
  [InterpConsts V]
  [PCM T]
  [DecidableEq χ]
  {spec : Semantics.OpSpec Op V T}
  (sigs : Vector Sig k)
  (prog : Prog (WithSpec Op spec) χ (V ⊕ T) sigs)
  (i : Nat)
  (hlt : i < k)
  (hnz : ∀ (i : Fin k), sigs[i].ι > 0 ∧ sigs[i].ω > 0)
  (hwf : ∀ i, (prog i).AffineVar)
  (haff : prog.AffineInrOp) :
  prog.semantics ⟨i, hlt⟩ ≲ᵣ (compileProg sigs prog hnz ⟨i, hlt⟩).semantics
  := sorry

-- def eraseGhost
--   [Arity Op]
--   [PCM T]
--   {spec : OpSpec' Op V T}
--   (proc : Proc (WithSpec Op spec) χ (V ⊕ T) m n) : Proc Op χ V m n
--   := sorry

-- def attachToken
--   [Arity Op]
--   (fn : Fn Op χ V m n) : Fn Op χ (V ⊕ T) m n := {
--     params := fn.params
--     body := fn.body
--   }

-- theorem fn_progress
--   [Arity Op]
--   [InterpConsts V]
--   [PCM T]
--   [DecidableEq χ]
--   {spec : OpSpec' Op V T}
--   (fn : Fn Op χ V m n)
--   {fn' : Fn (WithSpec Op spec) χ (V ⊕ T) m n}
--   (hnz : m > 0 ∧ n > 0)
--   (hwf : fn.AffineVar)
--   (hwt : sorry) -- Well-typedness: generates the elaborated `fn'` from `fn`
--   (interp : OpInterp Op V) :
--   (attachToken fn).semantics.interpret interp.withGhost
--     ≲ᵣ (fn'.semantics.guard Config.DisjointTokens (λ _ => True)).interpret
--         (interp.withSpec spec)
--   := sorry

end Wavelet.Compile
