import Wavelet.Thm.Data

import Wavelet.Compile.Fn
import Wavelet.Seq.AffineVar
import Wavelet.Dataflow.AffineChan

/-! Compiling a function with `AffineVar` produces a process with `AffineChan`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

variable {Op : Type} {χ : Type} {V : Type} {m n : Nat}
variable [Arity Op] [InterpConsts V] [DecidableEq χ] [NeZero m] [NeZero n]

private theorem compileExpr_no_input_chan
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

private theorem compileExpr_no_final_dest_chan
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

private theorem compileExpr_nodup_io
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

/-- Overapproximates the input channels of `compileExpr ...`. -/
private def IsCompileExprInput
  (pathConds : List (Bool × ChanName χ)) :
    ChanName χ → Prop
  | .var _ pathConds' =>
    pathConds.IsSuffix pathConds'
  | .switch_cond (.var _ pathConds')
  | .merge_cond (.var _ pathConds') =>
    pathConds.IsSuffix pathConds'
  | .dest _ pathConds'
  | .tail_arg _ pathConds'
  | .tail_cond pathConds' =>
    pathConds.length < pathConds'.length ∧ pathConds.IsSuffix pathConds'
  | _ => False

omit [DecidableEq χ] in
private theorem IsCompileExprInput.weaken
  {pathConds pathConds' : List (Bool × ChanName χ)}
  {name : ChanName χ}
  (hsuff : pathConds'.IsSuffix pathConds)
  (h : IsCompileExprInput pathConds name) :
    IsCompileExprInput pathConds' name := by
  cases name with
  | var _ _ => exact hsuff.trans h
  | switch_cond inner =>
    cases inner <;> simp [IsCompileExprInput] at h ⊢
    exact hsuff.trans h
  | merge_cond inner =>
    cases inner <;> simp [IsCompileExprInput] at h ⊢
    exact hsuff.trans h
  | dest _ _ => exact ⟨Nat.lt_of_le_of_lt hsuff.length_le h.1, hsuff.trans h.2⟩
  | tail_arg _ _ => exact ⟨Nat.lt_of_le_of_lt hsuff.length_le h.1, hsuff.trans h.2⟩
  | tail_cond _ => exact ⟨Nat.lt_of_le_of_lt hsuff.length_le h.1, hsuff.trans h.2⟩
  | input _ => exact h.elim
  | tail_cond_carry => exact h.elim
  | tail_cond_steer_dests => exact h.elim
  | tail_cond_steer_tail_args => exact h.elim
  | final_dest _ => exact h.elim
  | final_tail_arg _ => exact h.elim

/-- Overapproximates the output channels `compileExpr ...`. -/
private def IsCompiledExprOutput
  (pathConds : List (Bool × ChanName χ)) :
    ChanName χ → Prop
  | .var _ pathConds'
  | .switch_cond (.var _ pathConds')
  | .merge_cond (.var _ pathConds')
  | .dest _ pathConds'
  | .tail_arg _ pathConds'
  | .tail_cond pathConds' =>
    pathConds.IsSuffix pathConds'
  | _ => False

omit [DecidableEq χ] in
private theorem IsCompiledExprOutput.weaken
  {pathConds pathConds' : List (Bool × ChanName χ)}
  {name : ChanName χ}
  (hsuff : pathConds'.IsSuffix pathConds)
  (h : IsCompiledExprOutput pathConds name) :
    IsCompiledExprOutput pathConds' name := by
  cases name with
  | var _ _ => exact hsuff.trans h
  | switch_cond inner =>
    cases inner <;> simp [IsCompiledExprOutput] at h ⊢
    exact hsuff.trans h
  | merge_cond inner =>
    cases inner <;> simp [IsCompiledExprOutput] at h ⊢
    exact hsuff.trans h
  | dest _ _ => exact hsuff.trans h
  | tail_arg _ _ => exact hsuff.trans h
  | tail_cond _ => exact hsuff.trans h
  | input _ => exact h.elim
  | tail_cond_carry => exact h.elim
  | tail_cond_steer_dests => exact h.elim
  | tail_cond_steer_tail_args => exact h.elim
  | final_dest _ => exact h.elim
  | final_tail_arg _ => exact h.elim

private theorem compileExpr_inputs_overapprox
  {definedVars usedVars : List χ}
  {pathConds : List (Bool × ChanName χ)} :
    {expr : Expr Op χ m n} →
    expr.AffineVar usedVars definedVars →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ∀ name ∈ ap.inputs, IsCompileExprInput pathConds name
  | .ret _ | .tail _ => by
    intros haff ap hmem_ap name hmem_name
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.forwardc, AtomicProc.inputs] at hmem_name
      have ⟨_, _, hname⟩ := hmem_name
      subst hname
      simp [IsCompileExprInput]
    · subst hmem_ap
      simp [AtomicProc.sink, AtomicProc.inputs] at hmem_name
      split_ifs at hmem_name
      · simp at hmem_name
      · simp [compileExpr.allVarsExcept] at hmem_name
        have ⟨_, _, hname⟩ := hmem_name
        subst hname
        simp [IsCompileExprInput]
  | .op _ _ _ _ => by
    intros haff ap hmem_ap name hmem_name
    cases haff with | wf_op _ _ _ _ _ haff' =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, Vector.toList_map] at hmem_name
      have ⟨_, _, hname⟩ := hmem_name
      subst hname
      simp [IsCompileExprInput]
    · exact compileExpr_inputs_overapprox haff' _ hmem_ap _ hmem_name
  | .br _ _ _ => by
    intros haff ap hmem_ap name hmem_name
    cases haff with | wf_br hmem_cond haff₁ haff₂ =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.fork, AtomicProc.inputs] at hmem_name
      subst hmem_name
      simp [IsCompileExprInput]
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.switch, compileExpr.allVarsExcept, AtomicProc.inputs,
        List.toVector] at hmem_name
      cases hmem_name with
      | inl h => subst h; simp [IsCompileExprInput]
      | inr h =>
        have ⟨_, _, hname⟩ := h
        subst hname
        simp [IsCompileExprInput]
    cases hmem_ap <;> rename_i hmem_ap
    · apply IsCompileExprInput.weaken (List.suffix_cons _ _)
      exact compileExpr_inputs_overapprox haff₁ _ hmem_ap _ hmem_name
    cases hmem_ap <;> rename_i hmem_ap
    · apply IsCompileExprInput.weaken (List.suffix_cons _ _)
      exact compileExpr_inputs_overapprox haff₂ _ hmem_ap _ hmem_name
    · subst hmem_ap
      simp [AtomicProc.inputs, compileExpr.branchMerge, compileExpr.exprOutputs,
        AtomicProc.merge, Vector.toList_map, Vector.toList_append, Vector.toList_push,
        Vector.toList_range] at hmem_name
      rcases hmem_name with
        h | ⟨_, _, h⟩ | ((⟨_, _, h⟩ | h) | (⟨_, _, h⟩ | (⟨_, _, h⟩ | h)))
      <;> subst h
      <;> simp [IsCompileExprInput, List.suffix_cons]

private theorem compileExpr_outputs_overapprox
  {definedVars usedVars : List χ}
  {pathConds : List (Bool × ChanName χ)} :
    {expr : Expr Op χ m n} →
    expr.AffineVar usedVars definedVars →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ∀ name ∈ ap.outputs, IsCompiledExprOutput pathConds name
  | .ret _ | .tail _ => by
    intros haff ap hmem_ap name hmem_name
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.forwardc, AtomicProc.outputs,
        compileExpr.exprOutputs, compileExpr.tailExprOutputs,
        Vector.toList_map, Vector.toList_append, Vector.toList_push,
        Vector.toList_range] at hmem_name
      rcases hmem_name with ⟨_, _, h⟩ | (⟨_, _, h⟩ | h)
      <;> subst h
      <;> simp [IsCompiledExprOutput]
    · subst hmem_ap
      simp [AtomicProc.sink, AtomicProc.outputs] at hmem_name
      split_ifs at hmem_name <;> simp at hmem_name
  | .op _ _ _ _ => by
    intros haff ap hmem_ap name hmem_name
    cases haff with | wf_op _ _ _ _ _ haff' =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, Vector.toList_map] at hmem_name
      have ⟨_, _, hname⟩ := hmem_name
      subst hname
      simp [IsCompiledExprOutput]
    · exact compileExpr_outputs_overapprox haff' _ hmem_ap _ hmem_name
  | .br _ _ _ => by
    intros haff ap hmem_ap name hmem_name
    cases haff with | wf_br hmem_cond haff₁ haff₂ =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.fork, AtomicProc.outputs] at hmem_name
      rcases hmem_name with h | h
      <;> subst h
      <;> simp [IsCompiledExprOutput]
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.switch, compileExpr.allVarsExcept, AtomicProc.outputs,
        List.toVector] at hmem_name
      rcases hmem_name with ⟨_, _, h⟩ | ⟨_, _, h⟩
      <;> subst h
      <;> simp [IsCompiledExprOutput, List.suffix_cons]
    cases hmem_ap <;> rename_i hmem_ap
    · apply IsCompiledExprOutput.weaken (List.suffix_cons _ _)
      exact compileExpr_outputs_overapprox haff₁ _ hmem_ap _ hmem_name
    cases hmem_ap <;> rename_i hmem_ap
    · apply IsCompiledExprOutput.weaken (List.suffix_cons _ _)
      exact compileExpr_outputs_overapprox haff₂ _ hmem_ap _ hmem_name
    · subst hmem_ap
      simp [AtomicProc.outputs, compileExpr.branchMerge, compileExpr.exprOutputs,
        AtomicProc.merge, Vector.toList_map, Vector.toList_append, Vector.toList_push,
        Vector.toList_range] at hmem_name
      rcases hmem_name with ⟨_, _, h⟩ | (⟨_, _, h⟩ | h)
      <;> subst h
      <;> simp [IsCompiledExprOutput]

/-- Outputs of compileExpr never produce `.var v pathConds` when `v ∈ definedVars` or `v ∈ usedVars`. -/
private theorem compileExpr_no_definedVar_var_output
  {definedVars usedVars : List χ}
  {pathConds : List (Bool × ChanName χ)} :
    {expr : Expr Op χ m n} →
    expr.AffineVar usedVars definedVars →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ∀ v, ChanName.var v pathConds ∈ ap.outputs →
    v ∉ definedVars ∧ v ∉ usedVars
  | .ret _ | .tail _ => by
    intros haff ap hmem_ap v hvar
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.forwardc,
        compileExpr.exprOutputs, compileExpr.tailExprOutputs,
        Vector.toList_map, Vector.toList_append, Vector.toList_push,
        Vector.toList_range] at hvar
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.sink] at hvar
      split_ifs at hvar <;> simp at hvar
  | .op _ _ _ _ => by
    intros haff ap hmem_ap v hvar
    cases haff with | wf_op _ _ hdisj_used hdisj_def _ haff' =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp only [AtomicProc.outputs, Vector.toList_map] at hvar
      simp only [List.mem_map] at hvar
      obtain ⟨w, hmem_w, hw⟩ := hvar
      simp at hw; subst hw
      constructor
      · exact fun h => hdisj_def h hmem_w
      · exact fun h => hdisj_used h hmem_w
    · have ih := compileExpr_no_definedVar_var_output haff' _ hmem_ap v hvar
      obtain ⟨hndef', hnused'⟩ := ih
      simp only [List.mem_append] at hndef' hnused'
      push_neg at hndef' hnused'
      exact ⟨fun h => hndef'.1 (List.mem_to_mem_removeAll h hnused'.2), fun h => hnused'.1 h⟩
  | .br _ _ _ => by
    intros haff ap hmem_ap v hvar
    cases haff with | wf_br _ haff₁ haff₂ =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, AtomicProc.fork] at hvar
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.outputs, compileExpr.allVarsExcept, AtomicProc.switch,
        List.toVector] at hvar
    cases hmem_ap <;> rename_i hmem_ap
    · have happrox := compileExpr_outputs_overapprox haff₁ _ hmem_ap _ hvar
      simp [IsCompiledExprOutput] at happrox
      exact absurd happrox (by intro h; have := h.length_le; simp at this; omega)
    cases hmem_ap <;> rename_i hmem_ap
    · have happrox := compileExpr_outputs_overapprox haff₂ _ hmem_ap _ hvar
      simp [IsCompiledExprOutput] at happrox
      exact absurd happrox (by intro h; have := h.length_le; simp at this; omega)
    · subst hmem_ap
      simp [AtomicProc.outputs, compileExpr.branchMerge, compileExpr.exprOutputs,
        AtomicProc.merge, Vector.toList_map, Vector.toList_append, Vector.toList_push,
        Vector.toList_range] at hvar

/-- If a variable `v` is not in `definedVars` but is in `usedVars`,
then `.var v pathConds` never appears as an input to any compiled atom.
This captures the affine property: once consumed, a variable is not read again. -/
private theorem compileExpr_no_used_var_input
  {definedVars usedVars : List χ}
  {pathConds : List (Bool × ChanName χ)} :
    {expr : Expr Op χ m n} →
    expr.AffineVar usedVars definedVars →
    ∀ v, v ∉ definedVars → v ∈ usedVars →
    ∀ ap ∈ compileExpr (V := V) definedVars pathConds expr,
    ChanName.var v pathConds ∉ ap.inputs
  | .ret _ | .tail _ => by
    intros haff v hv_not_def _ ap hmem_ap hmem_input
    cases haff with | _ hnodup hsub =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.forwardc, AtomicProc.inputs, Vector.toList_map] at hmem_input
      exact hv_not_def (hsub (Vector.mem_toList_iff.mpr hmem_input))
    · subst hmem_ap
      simp only [AtomicProc.sink] at hmem_input
      split_ifs at hmem_input
      · simp [AtomicProc.inputs, compileExpr.allVarsExcept, Vector.toList_map,
          List.mem_map] at hmem_input
        replace hmem_input := Vector.mem_toList_iff.mpr hmem_input
        simp [List.toVector] at hmem_input
        exact hv_not_def (List.mem_removeAll_to_mem hmem_input)
      · simp [AtomicProc.inputs] at hmem_input
  | .op _ _ _ _ => by
    intros haff v hv_not_def hv_in_used ap hmem_ap hmem_input
    cases haff with | wf_op hargs_nodup hrets_nodup hdisj_used hdisj_def hsub haff' =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.inputs, Vector.toList_map] at hmem_input
      exact hv_not_def (hsub (Vector.mem_toList_iff.mpr hmem_input))
    · apply compileExpr_no_used_var_input haff' v _ _ ap hmem_ap hmem_input
      · simp only [List.mem_append, not_or]
        exact ⟨fun h => hv_not_def (List.mem_removeAll_to_mem h),
               fun h => hdisj_used hv_in_used h⟩
      · exact List.mem_append_left _ hv_in_used
  | .br _ _ _ => by
    intros haff v hv_not_def _ ap hmem_ap hmem_input
    cases haff with | wf_br hmem_cond haff₁ haff₂ =>
    simp [compileExpr] at hmem_ap
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.fork, AtomicProc.inputs] at hmem_input
      subst hmem_input; exact hv_not_def hmem_cond
    cases hmem_ap <;> rename_i hmem_ap
    · subst hmem_ap
      simp [AtomicProc.switch, AtomicProc.inputs, compileExpr.allVarsExcept,
        Vector.toList_map, Vector.toList_append] at hmem_input
      replace hmem_input := Vector.mem_toList_iff.mpr hmem_input
      simp [List.toVector] at hmem_input
      exact hv_not_def (List.mem_removeAll_to_mem hmem_input)
    cases hmem_ap <;> rename_i hmem_ap
    · have h := compileExpr_inputs_overapprox haff₁ ap hmem_ap _ hmem_input
      simp [IsCompileExprInput] at h
      exact absurd h (by intro hsuff; have := hsuff.length_le; simp at this; omega)
    cases hmem_ap <;> rename_i hmem_ap
    · have h := compileExpr_inputs_overapprox haff₂ ap hmem_ap _ hmem_input
      simp [IsCompileExprInput] at h
      exact absurd h (by intro hsuff; have := hsuff.length_le; simp at this; omega)
    · subst hmem_ap
      simp [AtomicProc.inputs, compileExpr.branchMerge, compileExpr.exprOutputs,
        AtomicProc.merge, Vector.toList_map, Vector.toList_append, Vector.toList_push,
        Vector.toList_range] at hmem_input

private theorem compileExpr_pairwise_disj_io
  {definedVars usedVars : List χ}
  {pathConds : List (Bool × ChanName χ)}
  (hdef_nodup : definedVars.Nodup) :
    {expr : Expr Op χ m n} →
    (haff : expr.AffineVar usedVars definedVars) →
    (compileExpr (V := V) definedVars pathConds expr).Pairwise
      λ ap₁ ap₂ => ap₁.inputs.Disjoint ap₂.inputs ∧ ap₁.outputs.Disjoint ap₂.outputs
  | .ret _ | .tail _ => by
    intros haff
    cases haff with | _ hnodup hsub =>
    simp only [compileExpr]
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intros ap hmem
    simp at hmem; subst hmem
    constructor
    · apply List.disjoint_iff_ne.mpr
      intros name₁ hmem₁ name₂ hmem₂
      simp [AtomicProc.forwardc, AtomicProc.inputs] at hmem₁
      simp [AtomicProc.sink, AtomicProc.inputs] at hmem₂
      split_ifs at hmem₂
      · simp at hmem₂
      · simp [compileExpr.allVarsExcept] at hmem₂
        obtain ⟨v₁, hv₁_mem, rfl⟩ := hmem₁
        obtain ⟨v₂, hv₂_mem, rfl⟩ := hmem₂
        simp only [ne_eq, ChanName.var.injEq, not_and]
        intro heq _; subst heq
        replace hv₂_mem := Vector.mem_toList_iff.mpr hv₂_mem
        simp [List.toVector] at hv₂_mem
        simp [List.removeAll, List.mem_filter] at hv₂_mem
        exact absurd hv₁_mem hv₂_mem.2
    · simp [AtomicProc.sink, AtomicProc.outputs]
      split_ifs <;> simp
  | .op _ _ _ _ => by
    intro haff
    cases haff with | wf_op hargs_nodup hrets_nodup hdisj_used hdisj_def hsub haff' =>
    simp [compileExpr]
    constructor
    · intros ap hmem_ap
      constructor
      · intros x hmem_x₁ hmem_x₂
        simp [AtomicProc.inputs, Vector.toList_map] at hmem_x₁
        obtain ⟨a, ha_mem, rfl⟩ := hmem_x₁
        apply compileExpr_no_used_var_input haff' a _ _ ap hmem_ap hmem_x₂
        · simp only [List.mem_append, not_or]
          constructor
          · intro h
            simp [List.removeAll, List.mem_filter] at h
            exact absurd ha_mem h.2
          · intro h
            exact hdisj_def (hsub (Vector.mem_toList_iff.mpr ha_mem)) h
        · exact List.mem_append_right _ (Vector.mem_toList_iff.mpr ha_mem)
      · intros x hmem_x₁ hmem_x₂
        simp [AtomicProc.outputs, Vector.toList_map] at hmem_x₁
        obtain ⟨r, hr_mem, rfl⟩ := hmem_x₁
        have h := compileExpr_no_definedVar_var_output haff' ap hmem_ap r hmem_x₂
        exact h.1 (List.mem_append_right _ (Vector.mem_toList_iff.mpr hr_mem))
    · exact compileExpr_pairwise_disj_io (List.Nodup.append (List.removeAll_nodup hdef_nodup) hrets_nodup (List.removeAll_disjoint hdisj_def)) haff'
  | .br _ _ _ => by
    sorry

private theorem compileFn_inputs_disj_atom_outputs
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

private theorem compileFn_outputs_disj_atom_inputs
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

private theorem compileFn_affine_var_imp_atoms_nodup_io
  (fn : Fn Op χ V m n)
  (haff : fn.AffineVar) :
    ∀ ap ∈ (compileFn fn).atoms, ap.inputs.Nodup ∧ ap.outputs.Nodup
  := by
  have ⟨haff_param, haff_body⟩ := haff
  intros ap hmem_ap
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

private theorem compileFn_affine_var_imp_atoms_pairwise_disj_io
  (fn : Fn Op χ V m n)
  (haff : fn.AffineVar) :
    (compileFn fn).atoms.Pairwise λ ap₁ ap₂ =>
      ap₁.inputs.Disjoint ap₂.inputs ∧
      ap₁.outputs.Disjoint ap₂.outputs
  := by
  have ⟨haff_param, haff_body⟩ := haff
  simp only [compileFn]
  constructor
  · intros ap hmem_ap
    simp [compileFn.bodyComp] at hmem_ap
    rcases hmem_ap with hmem_ap | hmem_ap
    · constructor
      · apply List.disjoint_iff_ne.mpr
        intros name₁ hmem₁ name₂ hmem₂
        simp [compileFn.initCarry, AtomicProc.carry, AtomicProc.inputs,
          Vector.toList_map, compileFn.inputs] at hmem₁
        have h₂ := compileExpr_inputs_overapprox haff_body _ hmem_ap _ hmem₂
        rcases hmem₁ with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
        <;> cases name₂ <;> simp_all [IsCompileExprInput]
      · apply List.disjoint_iff_ne.mpr
        intros name₁ hmem₁ name₂ hmem₂
        simp [compileFn.initCarry, AtomicProc.carry, AtomicProc.outputs,
          Vector.toList_map, compileFn.inputs] at hmem₁
        obtain ⟨p, hp_mem, rfl⟩ := hmem₁
        intro heq; subst heq
        exact (compileExpr_no_definedVar_var_output haff_body ap hmem_ap p hmem₂).1 (by simp [hp_mem])
    · simp [compileFn.resultSteers] at hmem_ap
      rcases hmem_ap with rfl | rfl | rfl
      <;> (constructor <;> intros x h₁ h₂ <;>
           simp [compileFn.initCarry, AtomicProc.carry, AtomicProc.inputs, AtomicProc.outputs,
             Vector.toList_map, compileFn.inputs,
             AtomicProc.fork, AtomicProc.steer] at h₁ h₂ <;>
           cases x <;> simp_all)
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · simp only [compileFn.bodyComp]
      exact compileExpr_pairwise_disj_io haff_param haff_body
    · simp only [compileFn.resultSteers]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
      · intros ap hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        cases hmem <;> rename_i hmem <;> subst hmem
        <;> constructor
        <;> apply List.disjoint_iff_ne.mpr
        <;> simp [AtomicProc.fork, AtomicProc.steer, AtomicProc.inputs, AtomicProc.outputs,
              Vector.toList_map, Vector.toList_range, Vector.toList_append]
      · intros ap hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        constructor
        <;> apply List.disjoint_iff_ne.mpr
        <;> simp [AtomicProc.steer, AtomicProc.inputs, AtomicProc.outputs,
              Vector.toList_map, Vector.toList_range, Vector.toList_append]
    · intros ap₁ hmem₁ ap₂ hmem₂
      simp [compileFn.bodyComp] at hmem₁
      have hinputs := compileExpr_inputs_overapprox haff_body _ hmem₁
      have houtputs := compileExpr_outputs_overapprox haff_body _ hmem₁
      simp [compileFn.resultSteers] at hmem₂
      constructor
      · apply List.disjoint_iff_ne.mpr
        intros name₁ hmem_name₁ name₂ hmem_name₂
        have h₁ := hinputs _ hmem_name₁
        rcases hmem₂ with h | h | h
        <;> subst h
        <;> simp [AtomicProc.fork, AtomicProc.steer, AtomicProc.inputs,
              Vector.toList_map, Vector.toList_range, Vector.toList_append] at hmem_name₂
        · subst hmem_name₂
          cases name₁ <;> simp_all [IsCompileExprInput]
          exact List.ne_nil_of_length_pos h₁
        all_goals {
          rcases hmem_name₂ with h | ⟨_, _, h⟩
          <;> subst h
          <;> cases name₁ <;> simp_all [IsCompileExprInput]
          intros
          exact List.ne_nil_of_length_pos h₁
        }
      · intros x hmem_x₁ hmem_x₂
        have hx := houtputs _ hmem_x₁
        rcases hmem₂ with h | h | h <;> subst h
        <;> simp [AtomicProc.fork, AtomicProc.steer, AtomicProc.outputs,
              Vector.toList_map, Vector.toList_range, Vector.toList_append] at hmem_x₂
        <;> (first | (rcases hmem_x₂ with h | h | h <;> subst h) | obtain ⟨_, _, rfl⟩ := hmem_x₂)
        <;> simp [IsCompiledExprOutput] at hx

private theorem compileFn_affine_var_imp_atoms_affine_chan
  (fn : Fn Op χ V m n)
  (haff : fn.AffineVar) :
    (compileFn fn).atoms.AffineChan
  := by
  constructor
  · exact compileFn_affine_var_imp_atoms_nodup_io fn haff
  · exact compileFn_affine_var_imp_atoms_pairwise_disj_io fn haff

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
