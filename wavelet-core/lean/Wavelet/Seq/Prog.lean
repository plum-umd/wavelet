import Wavelet.Data.Basic
import Wavelet.Semantics.Defs
import Wavelet.Semantics.Link
import Wavelet.Seq.Fn

/-! Syntax and semantics of programs (a list of `Fn`s with a acyclic call graph). -/

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

end Wavelet.Seq
