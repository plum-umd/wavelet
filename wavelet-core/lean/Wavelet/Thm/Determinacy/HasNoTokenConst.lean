import Wavelet.Compile.Prog

import Wavelet.Thm.Determinacy.DisjointTokens

/-! Lemmas that `compileProg` and related compilers produces
a dataflow graph satisfying the `HasNoTokenConst` requirement. -/

namespace Wavelet.Determinacy

open Semantics Compile Seq Dataflow

variable {Op T : Type u} {χ χ' : Type v} {V : Type w} {m n : Nat}

private theorem compile_expr_has_no_token_const
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {definedVars : List χ}
  {pathConds : List (Bool × ChanName χ)}
  (expr : Expr Op χ m n)
  {ap : AtomicProc Op (ChanName χ) (V ⊕ T)}
  (hmem : ap ∈ compileExpr (V := V ⊕ T) definedVars pathConds expr) :
    ap.HasNoTokenConst :=
  match expr with
  | .ret vars => by
    simp only [compileExpr, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · simp only [AtomicProc.forwardc, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
      intro v hv
      rw [Vector.mem_append] at hv
      rcases hv with hv | hv
      · rw [Vector.mem_replicate] at hv; rw [hv.2]; rfl
      · rw [Vector.mem_singleton] at hv; rw [hv]; rfl
    · simp only [AtomicProc.sink]
      split <;> simp [AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
  | .tail vars => by
    simp only [compileExpr, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · simp only [AtomicProc.forwardc, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
      intro v hv
      rw [Vector.mem_append] at hv
      rcases hv with hv | hv
      · rw [Vector.mem_replicate] at hv; rw [hv.2]; rfl
      · rw [Vector.mem_singleton] at hv; rw [hv]; rfl
    · simp only [AtomicProc.sink]
      split <;> simp [AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
  | .op o args rets cont => by
    simp only [compileExpr, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact trivial
    · exact compile_expr_has_no_token_const cont hmem
  | .br cond left right => by
    simp only [compileExpr] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · rw [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          rcases hmem with rfl | rfl
          · simp [AtomicProc.fork, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
          · simp [AtomicProc.switch, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
        · exact compile_expr_has_no_token_const left hmem
      · exact compile_expr_has_no_token_const right hmem
    · simp only [List.mem_singleton] at hmem
      subst hmem
      simp [compileExpr.branchMerge, AtomicProc.merge, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]

theorem compile_fn_has_no_token_const
  [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]
  {fn : Fn Op χ (V ⊕ T) m n} :
    (compileFn fn).HasNoTokenConst
  := by
  intro ap hmem
  simp only [compileFn, List.mem_cons, List.mem_append] at hmem
  rcases hmem with rfl | (hmem | hmem)
  · simp [compileFn.initCarry, AtomicProc.carry, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
  · exact compile_expr_has_no_token_const fn.body hmem
  · simp only [compileFn.resultSteers, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · simp [AtomicProc.fork, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
    · simp [AtomicProc.steer, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
    · simp [AtomicProc.steer, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]

theorem map_chans_has_no_token_const
  [Arity Op]
  {f : χ → χ'}
  {proc : Proc Op χ (V ⊕ T) m n}
  (hntok : proc.HasNoTokenConst) :
    (proc.mapChans f).HasNoTokenConst
  := by
  intro ap hmem
  simp [Proc.mapChans, AtomicProcs.mapChans] at hmem
  obtain ⟨ap', hmem', rfl⟩ := hmem
  cases ap' with
  | op o ins outs => simp [AtomicProc.mapChans, AtomicProc.HasNoTokenConst]
  | async aop ins outs =>
    simp [AtomicProc.mapChans, AtomicProc.HasNoTokenConst]
    exact hntok _ hmem'

theorem link_procs_has_no_token_const
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) (V ⊕ T) (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) (V ⊕ T) m n}
  (hntok_dep : ∀ i, (procs i).HasNoTokenConst)
  (hntok_main : main.HasNoTokenConst) :
    (linkProcs k' procs main).HasNoTokenConst
  := by
  intro ap hmem
  simp only [linkProcs] at hmem
  rw [List.mem_flatten] at hmem
  obtain ⟨l, hl_mem, hap_mem⟩ := hmem
  rw [List.mem_map] at hl_mem
  obtain ⟨atom, hatom_mem, rfl⟩ := hl_mem
  cases atom with
  | op o ins outs =>
    cases o with
    | inl o =>
      simp [linkAtomicProc] at hap_mem
      subst hap_mem
      simp [AtomicProc.HasNoTokenConst]
    | inr op =>
      simp only [linkAtomicProc] at hap_mem
      rw [List.mem_append] at hap_mem
      rcases hap_mem with hap_mem | hap_mem
      · rw [List.mem_append] at hap_mem
        rcases hap_mem with hap_mem | hap_mem
        · simp only [List.mem_singleton] at hap_mem
          subst hap_mem
          simp [AtomicProc.forward, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
        · simp [AtomicProcs.mapChans] at hap_mem
          obtain ⟨ap', hap'_mem, rfl⟩ := hap_mem
          cases ap' with
          | op o' ins' outs' =>
            simp [AtomicProc.mapChans, AtomicProc.HasNoTokenConst]
          | async aop' ins' outs' =>
            simp [AtomicProc.mapChans, AtomicProc.HasNoTokenConst]
            exact hntok_dep op.toFin' _ hap'_mem
      · simp only [List.mem_singleton] at hap_mem
        subst hap_mem
        simp [AtomicProc.forward, AtomicProc.HasNoTokenConst, AsyncOp.HasNoTokenConst]
  | async aop ins outs =>
    simp only [linkAtomicProc, List.mem_singleton] at hap_mem
    subst hap_mem
    simp only [AtomicProc.HasNoTokenConst]
    exact hntok_main _ hatom_mem

end Wavelet.Determinacy
