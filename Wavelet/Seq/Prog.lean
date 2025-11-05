import Wavelet.Semantics.Defs
import Wavelet.Semantics.Link
import Wavelet.Seq.Fn

/-! Syntax and semantics of programs (a list of `Fn`s with a acyclic call graph). -/

/-- TODO: move this to a better place. -/
@[simp, grind]
abbrev Fin.castPred (k' : Fin (k + 1)) (self : Fin ↑k') : Fin k := self.castLT (by omega)

prefix:max " ↓ " => Fin.castPred _

namespace Wavelet.Seq

open Semantics

structure Sig where
  ι : Nat
  ω : Nat

abbrev Sigs k := Fin k → Sig

/-- Signatures with non-zero arities. -/
class NeZeroSigs (sigs : Sigs k) where
  neZeroᵢ : ∀ i : Fin k, NeZero (sigs i).ι
  neZeroₒ : ∀ i : Fin k, NeZero (sigs i).ω

instance {sigs : Sigs k} [NeZeroSigs sigs] (i : Fin k) : NeZero (sigs i).ι := NeZeroSigs.neZeroᵢ i
instance {sigs : Sigs k} [NeZeroSigs sigs] (i : Fin k) : NeZero (sigs i).ω := NeZeroSigs.neZeroₒ i

inductive SigOps (sigs : Sigs k) (k' : Fin (k + 1)) where
  | call (i : Fin k')
  deriving DecidableEq

@[simp]
def SigOps.toFin' {sigs : Sigs k} {k' : Fin (k + 1)} : SigOps sigs k' → Fin k'
  | .call i => i

@[simp]
def SigOps.toFin {sigs : Sigs k} {k' : Fin (k + 1)} : SigOps sigs k' → Fin k
  | .call i => i.castLT (by omega)

def SigOps.elim0 : SigOps sigs ⟨0, by simp⟩ → α
  | .call i => i.elim0

instance : Arity (SigOps sigs k') where
  ι | .call i => (sigs ↓i).ι
  ω | .call i => (sigs ↓i).ω

instance [NeZeroSigs sigs] : NeZeroArity (SigOps sigs k') where
  neZeroᵢ | .call i => by apply NeZeroSigs.neZeroᵢ
  neZeroₒ | .call i => by apply NeZeroSigs.neZeroₒ

abbrev Prog (Op : Type u) χ V [Arity Op] (sigs : Sigs k) :=
  (i : Fin k) → Fn (Op ⊕ SigOps sigs i.castSucc) χ V (sigs i).ι (sigs i).ω

/-- Semantics of programs by semantically linking dependencies. -/
def Prog.semantics.{u, v, w}
  {Op : Type u} {χ : Type v} {V : Type w}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  (prog : Prog Op χ V sigs)
  (i : Fin k) : Semantics.{u, w, max u v w} Op V (sigs i).ι (sigs i).ω
  := Semantics.link (prog i).semantics (Prog.semantics prog ·.toFin)

-- /-- (Strong) induction principal for proving `motive (prog i)` for all `i`. -/
-- theorem Prog.semantics_induction
--   [Arity Op] [DecidableEq χ] [InterpConsts V]
--   {sigs : Sigs k}
--   {prog : Prog Op χ V sigs}
--   {motive : (i' : Fin k) → Semantics Op V (sigs i').ι (sigs i').ω → Prop}
--   (ind : (i : Fin k) →
--     (∀ (j : Fin i), motive ⟨j, by omega⟩ (prog.semantics _)) →
--     motive i (prog.semantics i))
--   (i : Fin k) :
--     motive i (prog.semantics i)
--   := sorry

theorem Prog.semantics_state
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    (prog.semantics i).S = LinkState (prog i).semantics (Prog.semantics prog ·.toFin)
  := by
  rw [Prog.semantics]
  rfl

@[simp]
def Prog.unfoldState
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    (prog.semantics i).S → LinkState (prog i).semantics (Prog.semantics prog ·.toFin)
  := cast Prog.semantics_state

@[simp]
def Prog.foldState
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    LinkState (prog i).semantics (Prog.semantics prog ·.toFin) → (prog.semantics i).S
  := cast Prog.semantics_state.symm

/-- Unfold a `Prog` state to a `LinkState`. -/
instance
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    Coe ((prog.semantics i).S) (LinkState (prog i).semantics (Prog.semantics prog ·.toFin)) where
  coe := Prog.unfoldState

/-- Fold a `LinkState` into a `Prog` state. -/
instance
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    Coe (LinkState (prog i).semantics (Prog.semantics prog ·.toFin)) ((prog.semantics i).S) where
  coe := Prog.foldState

@[simp]
theorem Prog.state_fold_unfold_eq
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  (s : (prog.semantics i).S) :
    Prog.foldState (Prog.unfoldState s) = s
  := by simp

@[simp]
theorem Prog.state_unfold_fold_eq
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  (s : LinkState (prog i).semantics (Prog.semantics prog ·.toFin)) :
    ↑(↑s : (prog.semantics i).S) = s
  := by simp

theorem Prog.unfold_init_heq
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    (prog.semantics i).init ≍
      LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin)
  := by
  rw [Prog.semantics]
  rfl

theorem Prog.unfold_init
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    ↑(prog.semantics i).init =
      LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin)
  := by
  apply cast_eq_iff_heq.mpr
  exact Prog.unfold_init_heq

theorem Prog.fold_init
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    ↑(LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin)) =
      (prog.semantics i).init
  := by
  apply cast_eq_iff_heq.mpr
  exact Prog.unfold_init_heq.symm

theorem Prog.unfold_lts
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    (prog.semantics i).lts ≍
      ((prog i).semantics.link (Prog.semantics prog ·.toFin)).lts
  := by rw [Prog.semantics]

theorem Prog.unfold_step
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {s s' : (prog.semantics i).S}
  {l : Label Op V (sigs i).ι (sigs i).ω}
  (hsteps : (prog.semantics i).lts.Step s l s') :
    ((prog i).semantics.link (Prog.semantics prog ·.toFin)).lts.Step
      (Prog.unfoldState s) l (Prog.unfoldState s')
  := by
  apply Lts.Step.heq_lts
  · rw [Prog.semantics]
  · exact Prog.unfold_lts
  · exact hsteps

theorem Prog.fold_step
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {s s' : (prog.semantics i).S}
  {l : Label Op V (sigs i).ι (sigs i).ω}
  (hsteps : ((prog i).semantics.link (Prog.semantics prog ·.toFin)).lts.Step
    (Prog.unfoldState s) l (Prog.unfoldState s')) :
    (prog.semantics i).lts.Step s l s'
  := by
  rw [← Prog.state_fold_unfold_eq s,
    ← Prog.state_fold_unfold_eq s']
  apply Lts.Step.heq_lts
  · rw [Prog.semantics, link]
  · exact Prog.unfold_lts.symm
  · exact hsteps

theorem Prog.unfold_star
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {tr : Trace (Label Op V (sigs i).ι (sigs i).ω)}
  {s : (prog.semantics i).S}
  (hsteps : (prog.semantics i).lts.Star (prog.semantics i).init tr s) :
    ((prog i).semantics.link (Prog.semantics prog ·.toFin)).lts.Star
      (LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin))
      tr (Prog.unfoldState s)
  := by
  rw [← Prog.unfold_init]
  apply hsteps.map_step_state
  apply Prog.unfold_step

theorem Prog.fold_star
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {tr : Trace (Label Op V (sigs i).ι (sigs i).ω)}
  {s : (prog.semantics i).S}
  (hsteps : ((prog i).semantics.link (Prog.semantics prog ·.toFin)).lts.Star
    (LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin))
      tr (Prog.unfoldState s)) :
    (prog.semantics i).lts.Star (prog.semantics i).init tr s
  := by
  rw [← Prog.fold_init,
    ← Prog.state_fold_unfold_eq s]
  apply hsteps.map_step_state
  intros s₁ s₂ l hstep
  apply Prog.fold_step
  simp
  exact hstep

theorem Prog.unfold_is_invariant
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  {Inv : (prog.semantics i).S → Prop}
  (h : ((prog i).semantics.link (Prog.semantics prog ·.toFin)).IsInvariant (Inv ∘ Prog.foldState)) :
    (prog.semantics i).IsInvariant Inv
  := by
  intros s tr hsteps
  rw [← Prog.state_fold_unfold_eq s] at hsteps ⊢
  replace hsteps := Prog.unfold_star hsteps
  have := h hsteps
  simp at this
  simp [this]

end Wavelet.Seq
