import Wavelet.Compile.Prog

import Wavelet.Thm.Determinacy.DisjointTokens

/-! Lemmas that `compileProg` and related compilers produces
a dataflow graph satisfying the `HasNoTokenConst` requirement. -/

namespace Wavelet.Determinacy

open Semantics Compile Seq Dataflow

variable {Op T : Type u} {χ χ' : Type v} {V : Type w} {m n : Nat}

theorem compile_fn_has_no_token_const
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {fn : Fn Op χ (V ⊕ T) m n} :
    (compileFn fn).HasNoTokenConst
  := by sorry

theorem map_chans_has_no_token_const
  [Arity Op]
  {f : χ → χ'}
  {proc : Proc Op χ (V ⊕ T) m n}
  (hntok : proc.HasNoTokenConst) :
    (proc.mapChans f).HasNoTokenConst
  := by sorry

theorem link_procs_has_no_token_const
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) (V ⊕ T) (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) (V ⊕ T) m n}
  (hntok_dep : ∀ i, (procs i).HasNoTokenConst)
  (hntok_main : main.HasNoTokenConst) :
    (linkProcs k' procs main).HasNoTokenConst
  := by sorry

end Wavelet.Determinacy
