import Wavelet.Seq.AffineVar
import Wavelet.Dataflow.AffineChan
import Wavelet.Compile.Fn.Defs
import Wavelet.Compile.Prog.Defs

/-! Compiling a function/program satisfying `AffineVar`
results in a graph satisfying `AffineChan`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

theorem expr_aff_var_to_aff_chan
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [NeZero m] [NeZero n]
  {usedVars : List χ}
  {definedVars : List χ}
  {pathConds : List (Bool × ChanName χ)}
  (hnodup : definedVars.Nodup)
  (expr : Expr Op χ m n)
  (haff : expr.AffineVar usedVars definedVars)
  {aps : AtomicProcs Op (ChanName χ) V}
  (hcomp : aps = compileExpr (V := V) definedVars pathConds expr) :
    aps.AffineChan
  := by
  subst aps
  cases haff with
  | wf_ret hnodup_rets =>
    rename_i retVars
    simp [compileExpr]
    constructor
    · simp
      intros i
      cases i
      rename_i i hlt
      simp
      if h₁ : i = 0 then
        subst h₁
        simp [AtomicProc.inputs, AtomicProc.outputs, AtomicProc.forwardc,
          compileExpr.exprOutputs]
        -- TODO: should be doable
        sorry
      else if h₂ : i = 1 then
        subst h₂
        if h₃ : definedVars.removeAll retVars.toList = [] then
          simp [AtomicProc.inputs, AtomicProc.outputs, AtomicProc.sink,
            compileExpr.exprOutputs, h₃]
        else
          simp [AtomicProc.inputs, AtomicProc.outputs, AtomicProc.sink,
            compileExpr.exprOutputs, h₃]
          sorry
      else
        omega
    · simp
      intros i j hne
      simp [AtomicProc.forwardc, AtomicProc.sink, compileExpr.exprOutputs]
      if h₁ : i = 0 ∧ j = 1 then
        if h₃ : definedVars.removeAll retVars.toList = [] then
          simp [h₁, h₃, AtomicProc.inputs, AtomicProc.outputs]
        else
          simp [h₁, h₃, AtomicProc.inputs, AtomicProc.outputs,
            compileExpr.allVarsExcept]
          sorry
      else if h₂ : i = 1 ∧ j = 0 then
        if h₄ : definedVars.removeAll retVars.toList = [] then
          simp [h₂, h₄, AtomicProc.inputs, AtomicProc.outputs]
        else
          simp [h₂, h₄, AtomicProc.inputs, AtomicProc.outputs,
            compileExpr.allVarsExcept]
          sorry
      else
        omega
  | wf_op hnodup_args hnodup_rets hdisj_used hdisj_defined hdefined hcont =>
    sorry
  | _ => sorry

end Wavelet.Compile
