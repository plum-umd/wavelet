import Wavelet.Op
import Wavelet.Lts
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

namespace Wavelet.Call

open Op Lts Seq Dataflow Compile

structure Sig where
  ι : Nat
  ω : Nat

/-- TODO: can't refer to the last signature? -/
inductive SigOps (sigs : Vector Sig k) (k' : Fin k) where
  | call (i : Fin k')
  deriving DecidableEq

def SigOps.toFin {k' : Fin k} : SigOps sigs k' → Fin k'
  | .call i => i

def SigOps.elim0 {hlt : 0 < k} : SigOps sigs ⟨0, hlt⟩ → α
  | .call i => i.elim0

instance : Arity (SigOps sigs k') where
  ι | .call i => sigs[i].ι
  ω | .call i => sigs[i].ω

abbrev Prog (Op : Type u) χ {k} [Arity Op] (sigs : Vector Sig k) :=
  (i : Fin k) → Fn (Op ⊕ SigOps sigs i) χ sigs[i].ι sigs[i].ω

def Prog.semantics
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Vector Sig k}
  (prog : Prog Op χ sigs)
  : (i : Fin k) → Semantics Op V sigs[i].ι sigs[i].ω
  -- Nothing more to interpret
  | ⟨0, hlt⟩ => (prog ⟨0, hlt⟩).semantics.link (·.elim0)
  -- Interpret all previous semantics, then link
  | ⟨i + 1, hlt⟩ =>
    (prog ⟨i + 1, hlt⟩).semantics.link
      (λ op => Prog.semantics prog ⟨op.toFin, by omega⟩)

end Wavelet.Call
