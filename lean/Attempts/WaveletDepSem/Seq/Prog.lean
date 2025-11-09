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

/-- Semantics of programs by semantically linking dependent functions. -/
def Prog.semantics.{u, v, w}
  {Op : Type u} {χ : Type v} {V : Type w}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k}
  (prog : Prog Op χ V sigs)
  (i : Fin k)
  : (S : Type (max u v w)) × Semantics S Op V (sigs i).ι (sigs i).ω
  := ⟨_, Semantics.link (prog i).semantics (λ op =>
    Prog.semantics prog op.toFin)⟩

end Wavelet.Seq
