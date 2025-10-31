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

theorem Prog.semantics_init_heq
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    (prog.semantics i).init ≍
      LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin)
  := by
  rw [Prog.semantics]
  rfl

theorem Prog.semantics_init
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  {prog : Prog Op χ V sigs}
  {i : Fin k} :
    ↑(prog.semantics i).init =
      LinkState.init (prog i).semantics (Prog.semantics prog ·.toFin)
  := by
  apply cast_eq_iff_heq.mpr
  exact Prog.semantics_init_heq

end Wavelet.Seq
