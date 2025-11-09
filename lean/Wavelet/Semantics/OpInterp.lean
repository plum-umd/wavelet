import Mathlib.Logic.Function.Basic

import Wavelet.Semantics.Defs

/-! Interpretations for operators. -/

namespace Wavelet.Semantics

/-- The empty operator set -/
inductive Empty : Type

def Empty.elim {α} (e : Empty) : α := by cases e

instance : Arity Empty where
  ι e := e.elim
  ω e := e.elim

instance : NeZeroArity Empty where
  neZeroᵢ e := e.elim
  neZeroₒ e := e.elim

/-- The dual action of `Label.yield`. -/
inductive RespLabel (Op : Type u) (V : Type v) [Arity Op] : Type (max u v) where
  | respond (op : Op) (inputs : Vector V (Arity.ι op)) (outputs : Vector V (Arity.ω op))

def RespLabel.MatchLabel
  [Arity Op]
  {V : Type v} : RespLabel Op V → Label Op V m n → Prop
  | .respond op₁ inputs₁ outputs₁, .yield op₂ inputs₂ outputs₂ =>
    op₁ = op₂ ∧ inputs₁ ≍ inputs₂ ∧ outputs₁ ≍ outputs₂
  | _, _ => False

/-- Parallel composition of `sem` and `interp`. -/
inductive Lts.InterpStep
  [Arity Op]
  (base : Lts S₁ (Label Op V m n))
  (interp : Lts S₂ (RespLabel Op V)) : Lts (S₁ × S₂) (Label Empty V m n) where
  | step_tau :
    base.Step s .τ s' →
    InterpStep base interp (s, t) .τ (s', t)
  | step_input :
    base.Step s (.input inputVals) s' →
    InterpStep base interp (s, t) (.input inputVals) (s', t)
  | step_output :
    base.Step s (.output outputVals) s' →
    InterpStep base interp (s, t) (.output outputVals) (s', t)
  | step_yield :
    base.Step s (.yield op inputs outputs) s' →
    interp.Step t (.respond op inputs outputs) t' →
    InterpStep base interp (s, t) .τ (s', t')

/-- Similar to `Interp`, but allowing additional indices in the base LTS. -/
inductive Lts.IndexedInterpStep
  {Op : Type u} {V : Type v}
  {S₁ : Type w₁} {S₂ : Type w₂}
  [Arity Op] {I : Type}
  (base : Lts S₁ (I × Label Op V m n))
  (interp : Lts S₂ (RespLabel Op V)) : Lts (S₁ × S₂) (I × Label Empty V m n) where
  | step_tau :
    base.Step s (i, .τ) s' →
    IndexedInterpStep base interp (s, t) (i, .τ) (s', t)
  | step_input :
    base.Step s (i, .input inputVals) s' →
    IndexedInterpStep base interp (s, t) (i, .input inputVals) (s', t)
  | step_output :
    base.Step s (i, .output outputVals) s' →
    IndexedInterpStep base interp (s, t) (i, .output outputVals) (s', t)
  | step_yield :
    base.Step s (i, .yield op inputs outputs) s' →
    interp.Step t (.respond op inputs outputs) t' →
    IndexedInterpStep base interp (s, t) (i, .τ) (s', t')

/-- Base semantics interprets all of the operators in the same LTS
with potentially shared states.

TODO: The fact that we need two definitions of semantics (`OpInterp`
and `Semantics`) is a bit unfortunate. Try unify?
-/
class OpInterp.{u, v, w} (Op : Type u) (V : Type v) [Arity Op] : Type (max u v (w + 1)) where
  S : Type w
  init : S
  lts : Lts S (RespLabel Op V)

/-- Fully interpret all operators using a `OpInterp` to get
a transition system with only input/output/silent events. -/
def interpret.{u, v, w₁, w₂}
  {Op : Type u} {V : Type v}
  [Arity Op]
  (sem : Semantics.{_, _, w₁} Op V m n)
  (interp : OpInterp.{_, _, w₂} Op V)
  : Semantics.{_, _, max w₁ w₂} Empty V m n
  := {
    S := sem.S × interp.S,
    init := (sem.init, interp.init),
    lts := Lts.InterpStep sem.lts interp.lts,
  }

/-- Deterministic operator set. -/
def OpInterp.Deterministic
  [Arity Op]
  (interp : OpInterp Op V) : Prop :=
  ∀ {s s₁' s₂' op inputs outputs₁ outputs₂},
    interp.lts.Step s (.respond op inputs outputs₁) s₁' →
    interp.lts.Step s (.respond op inputs outputs₂) s₂' →
    s₁' = s₂' ∧ outputs₁ = outputs₂

/-- No operator can execute and block another operator's execution
(although the result might change). -/
def OpInterp.NonBlocking
  [Arity Op]
  (interp : OpInterp Op V) : Prop :=
  ∀ {s s₁ s₂ l op inputs outputs},
    interp.lts.Step s l s₁ →
    interp.lts.Step s (.respond op inputs outputs) s₂ →
    ∃ outputs' s₂',
      interp.lts.Step s₁ (.respond op inputs outputs') s₂'

def Lts.InterpStep.map_step
  [Arity Op] {S S'}
  {lts₁ lts₂ : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hmap : ∀ {s s' l}, lts₁.Step s l s' → lts₂.Step s l s')
  (hstep : (Lts.InterpStep lts₁ lts').Step s l s') :
    (Lts.InterpStep lts₂ lts').Step s l s'
  := by
  cases hstep with
  | step_tau hstep => exact .step_tau (hmap hstep)
  | step_input hstep => exact .step_input (hmap hstep)
  | step_output hstep => exact .step_output (hmap hstep)
  | step_yield hbase hinterp => exact .step_yield (hmap hbase) hinterp

def Lts.InterpStep.output_eq_state
  [Arity Op] {S S'}
  {lts : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hstep : (Lts.InterpStep lts lts').Step s (.output vals) s') :
    s.2 = s'.2
  := by cases hstep; rfl

def Lts.InterpStep.to_base_step
  [Arity Op] {S S'}
  {lts : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {l : Label Empty V m n}
  {s s' : S × S'}
  (hsteps : (Lts.InterpStep lts lts').Step s l s') :
    ∃ l', lts.Step s.1 l' s'.1
  := by
  cases hsteps with
  | step_tau hstep => exact ⟨_, hstep⟩
  | step_input hstep => exact ⟨_, hstep⟩
  | step_output hstep => exact ⟨_, hstep⟩
  | step_yield hbase hinterp => exact ⟨_, hbase⟩

def Lts.InterpStep.star_to_base_star
  [Arity Op] {S S'}
  {lts : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {tr : Trace (Label Empty V m n)}
  {s s' : S × S'}
  (hsteps : (Lts.InterpStep lts lts').Star s tr s') :
    ∃ tr', lts.Star s.1 tr' s'.1
  := by
  induction hsteps with
  | refl => exact ⟨_, .refl⟩
  | tail pref tail ih =>
    have ⟨_, tail'⟩ := tail.to_base_step
    have ⟨_, ih'⟩ := ih
    exact ⟨_, .tail ih' tail'⟩

def Lts.InterpStep.from_base_tau_star
  [Arity Op] {S S'}
  {lts : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S}
  {t : S'}
  (hsteps : lts.TauStar .τ s s') :
    (Lts.InterpStep lts lts').TauStar .τ (s, t) (s', t)
  := by
  induction hsteps with
  | refl => exact .refl
  | tail _ tail ih => exact .tail ih (.step_tau tail)

def Lts.IndexedInterpStep.map_step
  [Arity Op] {S S'}
  {lts₁ lts₂ : Lts S (Nat × Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hmap : ∀ {s s' l}, lts₁.Step s l s' → lts₂.Step s l s')
  (hstep : (lts₁.IndexedInterpStep lts').Step s l s') :
    (lts₂.IndexedInterpStep lts').Step s l s'
  := by
  cases hstep with
  | step_tau hstep => exact .step_tau (hmap hstep)
  | step_input hstep => exact .step_input (hmap hstep)
  | step_output hstep => exact .step_output (hmap hstep)
  | step_yield hbase hinterp => exact .step_yield (hmap hbase) hinterp

def Lts.IndexedInterpStep.to_interp
  [Arity Op] {S S'}
  {lts₁ : Lts S (Nat × Label Op V m n)}
  {lts₂ : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hmap : ∀ {s s' i l}, lts₁.Step s (i, l) s' → lts₂.Step s l s')
  (hstep : (lts₁.IndexedInterpStep lts').Step s (i, l) s') :
    (lts₂.InterpStep lts').Step s l s'
  := by
  cases hstep with
  | step_tau hstep => exact .step_tau (hmap hstep)
  | step_input hstep => exact .step_input (hmap hstep)
  | step_output hstep => exact .step_output (hmap hstep)
  | step_yield hbase hinterp => exact .step_yield (hmap hbase) hinterp

def Lts.InterpStep.to_indexed_interp_tau
  [Arity Op] {S S'}
  {lts₁ : Lts S (Label Op V m n)}
  {lts₂ : Lts S (Nat × Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s s' : S × S'}
  (hmap : ∀ {s s' l},
    l.isYield ∨ l.isSilent →
    lts₁.Step s l s' → ∃ i, lts₂.Step s (i, l) s')
  (hstep : (lts₁.InterpStep lts').Step s .τ s') :
    ∃ i, (lts₂.IndexedInterpStep lts').Step s (i, .τ) s'
  := by
  cases hstep with
  | step_tau hstep =>
    have ⟨i, hstep'⟩ := hmap (by simp) hstep
    exact ⟨i, .step_tau hstep'⟩
  | step_yield hbase hinterp =>
    have ⟨i, hbase'⟩ := hmap (by simp) hbase
    exact ⟨i, .step_yield hbase' hinterp⟩

def Lts.InterpStep.map_inv
  [Arity Op] {S S'}
  {lts : Lts S (Label Op V m n)}
  {lts' : Lts S' (RespLabel Op V)}
  {s : S × S'}
  {Inv : S → Prop}
  (hinv : lts.IsInvariantAt Inv s.1) :
    (Lts.InterpStep lts lts').IsInvariantAt (Inv ·.1) s
  := by
  intros s' tr hsteps
  have ⟨_, hsteps'⟩ := Lts.InterpStep.star_to_base_star hsteps
  exact hinv hsteps'

def InterpSim
  [Arity Op]
  [interp : OpInterp.{_, _, w₂} Op V]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : sem₁ ≲ᵣ[R] sem₂)
  (s₁ : sem₁.S × interp.S) (s₂ : sem₂.S × interp.S) : Prop
  := hsim.Sim s₁.1 s₂.1 ∧ s₁.2 = s₂.2

/-- `interp` preserves IO-restricted simulation. -/
theorem sim_interp
  [Arity Op]
  [InterpConsts V]
  [interp : OpInterp.{_, _, w₂} Op V]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : sem₁ ≲ᵣ[R] sem₂) :
    sem₁.interpret interp ≲ᵣ[λ s₁ s₂ => R s₁.1 s₂.1 ∧ s₁.2 = s₂.2] sem₂.interpret interp
  := by
  apply Lts.SimilaritySt.intro (InterpSim hsim)
  · constructor
    · simp [InterpSim, Semantics.interpret]
      exact hsim.sim_init
    · intros s₁ s₂ l s₁' h hstep
      rcases s₁ with ⟨s₁₁, s₁₂⟩
      rcases s₂ with ⟨s₂₁, s₂₂⟩
      have ⟨h₁, h₂⟩ := h
      simp at h₁ h₂
      simp [Semantics.interpret] at hstep
      cases hstep with
      | step_tau hstep =>
        have ⟨_, hstep', h₁'⟩ := hsim.sim_step _ _ _ _ h₁ hstep
        cases hstep' with | step_tau hstep' =>
        have hstep'' : (sem₂.interpret interp).lts.IORestrictedStep.Step (_, s₂₂) _ _ :=
          Lts.IORestrictedStep.step_tau
            (Lts.InterpStep.from_base_tau_star hstep')
        exact ⟨_, hstep'', by simp [InterpSim, h₁', h₂]⟩
      | step_input hstep =>
        have ⟨_, hstep', h₁'⟩ := hsim.sim_step _ _ _ _ h₁ hstep
        cases hstep' with | step_input hstep' htau' =>
        rename_i s₃
        have htau'' : (sem₂.interpret interp).lts.TauStar .τ (_, s₂₂) _ :=
          Lts.InterpStep.from_base_tau_star htau'
        exact ⟨_,
          .step_input (.step_input hstep') htau'',
          by simp [InterpSim, h₁', h₂]⟩
      | step_output hstep =>
        have ⟨_, hstep', h₁'⟩ := hsim.sim_step _ _ _ _ h₁ hstep
        cases hstep' with | step_output htau' hstep' =>
        rename_i s₃
        have htau'' : (sem₂.interpret interp).lts.TauStar .τ (_, s₂₂) _ :=
          Lts.InterpStep.from_base_tau_star htau'
        exact ⟨_,
          .step_output htau'' (.step_output hstep'),
          by simp [InterpSim, h₁', h₂]⟩
      | step_yield hstep hinterp =>
        have ⟨_, hstep', h₁'⟩ := hsim.sim_step _ _ _ _ h₁ hstep
        cases hstep' with | step_yield hstep' =>
        subst h₂
        exact ⟨_, .step_tau (.single (.step_yield hstep' hinterp)),
          by simp [InterpSim, h₁']⟩
  · simp [InterpSim]
    intros s₁ _ s₂ h
    exact hsim.sim_prop _ _ h

/-- A monad interpretation of operators (mostly used in executing dataflow graphs) -/
class OpInterpM.{u, v, w}
  (Op : Type u) (V : Type v) (M : Type v → Type w) [Arity Op] : Type (max u v w) where
  interp : (op : Op) → Vector V (Arity.ι op) → M (Vector V (Arity.ω op))

end Wavelet.Semantics
