import Wavelet.Thm.Data

import Wavelet.Compile.Fn
import Wavelet.Seq.AffineVar
import Wavelet.Dataflow.AffineChan

/-! Compiling a function with `AffineVar` produces a process with `AffineChan`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

variable {Op : Type} {χ : Type} {V : Type} {m n : Nat}
variable [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]

theorem compileExpr_no_input_chan
  {definedVars : List χ}
  {pathConds : List (Bool × ChanName χ)} :
    {expr : Expr Op χ m n} →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ∀ name ∈ ap.outputs, ∀ var, name ≠ .input var
  | .ret _
  | .tail _ => by
    intros ap hmem_ap name hmem_name var hname
    subst hname
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.forwardc,
        compileExpr.exprOutputs, compileExpr.tailExprOutputs] at hmem_name
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.sink] at hmem_name
      split_ifs at hmem_name
      · simp at hmem_name
      · simp at hmem_name
  | .op _ _ _ _ => by
    intros ap hmem_ap name hmem_name var hname
    subst hname
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs] at hmem_name
    · apply compileExpr_no_input_chan _ hmem_ap _ hmem_name
      rfl
  | .br _ _ _ => by
    intros ap hmem_ap name hmem_name var hname
    subst hname
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.fork] at hmem_name
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, compileExpr.allVarsExcept, AtomicProc.switch] at hmem_name
    cases hmem_ap <;> rename_i hmem_ap
    · apply compileExpr_no_input_chan _ hmem_ap _ hmem_name
      rfl
    cases hmem_ap <;> rename_i hmem_ap
    · apply compileExpr_no_input_chan _ hmem_ap _ hmem_name
      rfl
    · subst hmem_ap
      simp [AtomicProc.outputs, compileExpr.branchMerge, compileExpr.exprOutputs, AtomicProc.merge] at hmem_name

theorem compileExpr_no_final_dest_chan
  {definedVars : List χ}
  {pathConds : List (Bool × ChanName χ)} :
    {expr : Expr Op χ m n} →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ∀ name ∈ ap.inputs, ∀ i, name ≠ .final_dest i
  | .ret _
  | .tail _ => by
    intros ap hmem_ap name hmem_name var hname
    subst hname
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.forwardc,
        compileExpr.exprOutputs, compileExpr.tailExprOutputs] at hmem_name
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.sink] at hmem_name
      split_ifs at hmem_name
      · simp at hmem_name
      · simp [compileExpr.allVarsExcept] at hmem_name
  | .op _ _ _ _ => by
    intros ap hmem_ap name hmem_name var hname
    subst hname
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs] at hmem_name
    · apply compileExpr_no_final_dest_chan _ hmem_ap _ hmem_name
      rfl
  | .br _ _ _ => by
    intros ap hmem_ap name hmem_name var hname
    subst hname
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.fork] at hmem_name
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, compileExpr.allVarsExcept, AtomicProc.switch] at hmem_name
    cases hmem_ap <;> rename_i hmem_ap
    · apply compileExpr_no_final_dest_chan _ hmem_ap _ hmem_name
      rfl
    cases hmem_ap <;> rename_i hmem_ap
    · apply compileExpr_no_final_dest_chan _ hmem_ap _ hmem_name
      rfl
    · subst hmem_ap
      simp [AtomicProc.inputs, compileExpr.branchMerge, compileExpr.exprOutputs, AtomicProc.merge] at hmem_name

theorem compileExpr_nodup_io
  {definedVars usedVars : List χ}
  {pathConds : List (Bool × ChanName χ)}
  (hdef_nodup : definedVars.Nodup) :
    {expr : Expr Op χ m n} →
    expr.AffineVar usedVars definedVars →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ap.inputs.Nodup ∧ ap.outputs.Nodup
  | .ret _ | .tail _ => by
    intros haff ap hmem_ap
    cases haff with | _ hnodup =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.forwardc, AtomicProc.inputs, AtomicProc.outputs,
        Vector.toList_map, Vector.toList_append, Vector.toList_push, Vector.toList_range,
        compileExpr.exprOutputs, compileExpr.tailExprOutputs]
      constructor
      · exact List.Nodup.map (by simp [Function.Injective]) hnodup
      · apply List.Nodup.append
        · exact List.Nodup.map (by simp [Function.Injective]) List.nodup_range
        · apply List.Nodup.append
          · exact List.Nodup.map (by simp [Function.Injective]) List.nodup_range
          · simp
          · simp
        · simp
          intros name hmem₁ hmem₂
          simp at hmem₁ hmem₂
          have ⟨_, _, hname₁⟩ := hmem₁
          have ⟨_, _, hname₂⟩ := hmem₂
          subst hname₁
          simp at hname₂
    · subst hmem_ap
      constructor
      · simp [AtomicProc.sink, AtomicProc.inputs]
        split_ifs
        · simp
        · simp [compileExpr.allVarsExcept, List.toVector]
          apply List.Nodup.map (by simp [Function.Injective])
          apply List.removeAll_nodup hdef_nodup
      · simp [AtomicProc.sink, AtomicProc.outputs]
        split_ifs <;> simp
  | .op _ _ _ _ => by
    intros haff ap hmem_ap
    cases haff with | wf_op hargs_nodup hrets_nodup _ hdisj _ haff' =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
      constructor
      · exact List.Nodup.map (by simp [Function.Injective]) hargs_nodup
      · exact List.Nodup.map (by simp [Function.Injective]) hrets_nodup
    · apply compileExpr_nodup_io _ haff' _ hmem_ap
      apply List.Nodup.append
      · exact List.removeAll_nodup hdef_nodup
      · exact hrets_nodup
      · exact List.removeAll_disjoint hdisj
  | .br _ _ _ => by
    intros haff ap hmem_ap
    cases haff with | wf_br _ haff₁ haff₂ =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.fork, AtomicProc.inputs, AtomicProc.outputs]
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.switch, compileExpr.allVarsExcept, AtomicProc.inputs,
        AtomicProc.outputs, List.toVector]
      constructor
      · apply List.Nodup.map (by simp [Function.Injective])
        exact List.removeAll_nodup hdef_nodup
      · apply List.Nodup.append
        · apply List.Nodup.map (by simp [Function.Injective])
          exact List.removeAll_nodup hdef_nodup
        · apply List.Nodup.map (by simp [Function.Injective])
          exact List.removeAll_nodup hdef_nodup
        · intros name hmem₁ hmem₂
          simp at hmem₁ hmem₂
          have ⟨_, _, hname₁⟩ := hmem₁
          have ⟨_, _, hname₂⟩ := hmem₂
          subst hname₁
          simp at hname₂
    cases hmem_ap <;> rename_i hmem_ap
    · apply compileExpr_nodup_io _ haff₁ _ hmem_ap
      exact List.removeAll_nodup hdef_nodup
    cases hmem_ap <;> rename_i hmem_ap
    · apply compileExpr_nodup_io _ haff₂ _ hmem_ap
      exact List.removeAll_nodup hdef_nodup
    · subst hmem_ap
      simp [AtomicProc.merge, compileExpr.branchMerge, compileExpr.exprOutputs,
        AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map, Vector.toList_append,
        Vector.toList_push, Vector.toList_cast]
      constructor
      · apply List.Nodup.append
        · apply List.Nodup.map (by simp [Function.Injective])
          simp [Vector.toList_range]
          exact List.nodup_range
        · apply List.Nodup.append
          · apply List.Nodup.map (by simp [Function.Injective])
            simp [Vector.toList_range]
            exact List.nodup_range
          · apply List.Nodup.cons (by simp)
            apply List.Nodup.append
            · apply List.Nodup.map (by simp [Function.Injective])
              simp [Vector.toList_range]
              exact List.nodup_range
            · apply List.Nodup.append
              · apply List.Nodup.map (by simp [Function.Injective])
                simp [Vector.toList_range]
                exact List.nodup_range
              · simp
              · simp
            · simp
              intros name hmem₁ hmem₂
              simp at hmem₁ hmem₂
              have ⟨_, _, hname₁⟩ := hmem₁
              have ⟨_, _, hname₂⟩ := hmem₂
              subst hname₁
              simp at hname₂
          · simp
            constructor <;> {
              intros name hmem₁ hmem₂
              simp at hmem₁ hmem₂
              have ⟨_, _, hname₁⟩ := hmem₁
              have ⟨_, _, hname₂⟩ := hmem₂
              subst hname₁
              simp at hname₂
            }
        · simp
          constructor
          · intros name hmem₁ hmem₂
            simp at hmem₁ hmem₂
            have ⟨_, _, hname₁⟩ := hmem₁
            have ⟨_, _, hname₂⟩ := hmem₂
            subst hname₁
            simp at hname₂
          constructor <;> {
            intros name hmem₁ hmem₂
            simp at hmem₁ hmem₂
            have ⟨_, _, hname₁⟩ := hmem₁
            have ⟨_, _, hname₂⟩ := hmem₂
            subst hname₁
            simp at hname₂
          }
      · apply List.Nodup.append
        · apply List.Nodup.map (by simp [Function.Injective])
          simp [Vector.toList_range]
          exact List.nodup_range
        · apply List.Nodup.append
          · apply List.Nodup.map (by simp [Function.Injective])
            simp [Vector.toList_range]
            exact List.nodup_range
          · simp
          · simp
        · intros name hmem₁ hmem₂
          simp at hmem₁ hmem₂
          cases hmem₂ <;> rename_i hmem₂
          · have ⟨_, _, hname₂⟩ := hmem₂
            subst hname₂
            simp at hmem₁
          · subst hmem₂
            simp at hmem₁

theorem compileFn_inputs_disj_atom_outputs
  (fn : Fn Op χ V m n)
  (ap : AtomicProc Op (ChanName χ) V)
  (hmem_ap : ap ∈ (compileFn fn).atoms) :
    ap.outputs.Disjoint (compileFn fn).inputs.toList
  := by
  simp [compileFn, compileFn.inputs, Vector.toList_map] at hmem_ap ⊢
  cases hmem_ap <;> rename_i hmem_ap
  · subst hmem_ap
    apply List.disjoint_iff_ne.mpr
    simp [compileFn.initCarry, AtomicProc.outputs, AtomicProc.carry, Vector.toList_map]
  cases hmem_ap <;> rename_i hmem_ap
  · simp [compileFn.bodyComp] at hmem_ap
    apply List.disjoint_iff_ne.mpr
    intros name₁ hmem_name₁ name₂ hmem_name₂
    simp at hmem_name₂
    have ⟨_, _, hname₂⟩ := hmem_name₂
    subst hname₂
    apply compileExpr_no_input_chan _ hmem_ap _ hmem_name₁
  · apply List.disjoint_iff_ne.mpr
    simp [compileFn.resultSteers] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.fork]
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.steer]
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.steer]

theorem compileFn_outputs_disj_atom_inputs
  (fn : Fn Op χ V m n)
  (ap : AtomicProc Op (ChanName χ) V)
  (hmem_ap : ap ∈ (compileFn fn).atoms) :
    ap.inputs.Disjoint (compileFn fn).outputs.toList
  := by
  simp [compileFn, compileFn.outputs, Vector.toList_map] at hmem_ap ⊢
  cases hmem_ap <;> rename_i hmem_ap
  · subst hmem_ap
    apply List.disjoint_iff_ne.mpr
    simp [compileFn.initCarry, compileFn.inputs, AtomicProc.inputs, AtomicProc.carry, Vector.toList_map]
    grind only [= List.nodup_iff_count, =_ Vector.toList_toArray,
      = List.nodup_iff_pairwise_ne, cases Or]
  cases hmem_ap <;> rename_i hmem_ap
  · simp [compileFn.bodyComp] at hmem_ap
    apply List.disjoint_iff_ne.mpr
    intros name₁ hmem_name₁ name₂ hmem_name₂
    simp at hmem_name₂
    have ⟨_, _, hname₂⟩ := hmem_name₂
    subst hname₂
    apply compileExpr_no_final_dest_chan _ hmem_ap _ hmem_name₁
  · apply List.disjoint_iff_ne.mpr
    simp [compileFn.resultSteers] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.fork]
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.steer]
    · subst hmem_ap
      simp [AtomicProc.inputs, AtomicProc.steer]

theorem compileFn_affine_var_imp_atoms_affine_chan
  (fn : Fn Op χ V m n)
  (haff : fn.AffineVar) :
    (compileFn fn).atoms.AffineChan
  := by
  have ⟨haff_param, haff_body⟩ := haff
  constructor
  · intros ap hmem_ap
    simp [compileFn, compileFn.bodyComp] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [compileFn.initCarry, compileFn.inputs,
        AtomicProc.carry, AtomicProc.inputs, AtomicProc.outputs,
        Vector.toList_cast, Vector.toList_map, Vector.toList_append,
        Vector.toList_range]
      constructor
      · apply List.Nodup.append
        · exact List.Nodup.map (by simp [Function.Injective]) haff_param
        · exact List.Nodup.map (by simp [Function.Injective]) List.nodup_range
        · -- TODO: This chunk of argument occurs multiple times in this file,
          -- maybe factor it out.
          intros name hmem₁ hmem₂
          simp at hmem₁ hmem₂
          have ⟨_, _, hname₁⟩ := hmem₁
          have ⟨_, _, hname₂⟩ := hmem₂
          subst hname₁
          simp at hname₂
      · exact List.Nodup.map (by simp [Function.Injective]) haff_param
    cases hmem_ap <;> rename_i hmem_ap
    · exact compileExpr_nodup_io (m := m) (n := n) haff_param haff_body _ hmem_ap
    · simp [compileFn.resultSteers] at hmem_ap
      cases hmem_ap <;> rename_i hmem_ap
      · subst hmem_ap
        simp [AtomicProc.fork, AtomicProc.inputs, AtomicProc.outputs]
      cases hmem_ap <;> rename_i hmem_ap
      · subst hmem_ap
        simp [AtomicProc.steer, AtomicProc.inputs, AtomicProc.outputs,
          Vector.toList_map, Vector.toList_range, Vector.toList_append]
        constructor <;> exact List.Nodup.map (by simp [Function.Injective]) List.nodup_range
      · subst hmem_ap
        simp [AtomicProc.steer, AtomicProc.inputs, AtomicProc.outputs,
          Vector.toList_map, Vector.toList_range, Vector.toList_append]
        constructor <;> exact List.Nodup.map (by simp [Function.Injective]) List.nodup_range
  · sorry

/-- A function with affine variable usage is compiled to a process
with affine channel usage. -/
theorem compileFn_affine_var_imp_affine_chan
  (fn : Fn Op χ V m n)
  (haff : fn.AffineVar) :
    (compileFn fn).AffineChan
  := by
  have ⟨haff_param, haff_body⟩ := haff
  constructor
  -- Disjoint input channels
  · simp [compileFn, compileFn.inputs, Vector.toList_map]
    exact List.Nodup.map (by simp [Function.Injective]) haff_param
  constructor
  -- Disjoint output channels
  · simp [compileFn, compileFn.outputs, Vector.toList_map]
    apply List.Nodup.map (by simp [Function.Injective])
    simp [Vector.toList_range]
    exact List.nodup_range
  constructor
  · exact compileFn_affine_var_imp_atoms_affine_chan fn haff
  -- Global inputs are disjoint from each atom's outputs;
  -- global outputs are disjoint from each atom's inputs.
  constructor
  · exact compileFn_inputs_disj_atom_outputs fn
  · exact compileFn_outputs_disj_atom_inputs fn

end Wavelet.Compile
