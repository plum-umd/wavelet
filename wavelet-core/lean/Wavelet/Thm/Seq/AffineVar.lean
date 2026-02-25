import Wavelet.Thm.Data
import Wavelet.Seq.AffineVar

/-! Some auxiliary lemmas about `Expr.AffineVar`. -/

namespace Wavelet.Seq

/-- The `wf_br` case of `Expr.AffineVar` preserves the disjointness of `usedvars` and `definedVars`. -/
theorem Expr.AffineVar.wf_br_preserves_disjoint
  [DecidableEq χ]
  {usedVars definedVars : List χ} {c : χ}
  (hdisj : usedVars.Disjoint definedVars)
  (_hmem : c ∈ definedVars) :
  (c :: usedVars).Disjoint (definedVars.removeAll [c]) := by
  rw [List.disjoint_cons_left]
  constructor
  · simp [List.removeAll, List.mem_filter]
  · intro x hx hrem
    simp [List.removeAll, List.mem_filter] at hrem
    exact hdisj hx hrem.1

/-- The `wf_op` case of `Expr.AffineVar` preserves the disjointness of `usedvars` and `definedVars`. -/
theorem Expr.AffineVar.wf_op_preserves_disjoint
  [DecidableEq χ]
  {usedVars definedVars args rets : List χ}
  (hdisj : usedVars.Disjoint definedVars)
  (hdisj_used : usedVars.Disjoint rets)
  (hdisj_def : definedVars.Disjoint rets)
  (hsub : args ⊆ definedVars) :
  (usedVars ++ args).Disjoint ((definedVars.removeAll args) ++ rets) := by
  rw [List.disjoint_append_left, List.disjoint_append_right, List.disjoint_append_right]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro x hx hrem
    simp [List.removeAll, List.mem_filter] at hrem
    exact hdisj hx hrem.1
  · exact hdisj_used
  · intro x hx hrem
    simp [List.removeAll, List.mem_filter] at hrem
    exact hrem.2 hx
  · intro x hx hret
    exact hdisj_def (hsub hx) hret

end Wavelet.Seq
