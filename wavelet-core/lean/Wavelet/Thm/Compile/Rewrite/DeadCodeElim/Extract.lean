import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Simple
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Steer
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Order
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract.Merge

/-! Every successful run of `deadCodeElim` is described by `DCEMatch`. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

theorem deadCodeElim_some
  {Op χ V : Type} [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V] [DecidableEq V]
  {aps : AtomicProcs Op (RewriteName χ) V} {disabledRules : List String}
  {name : String} {res : AtomicProcs Op (RewriteName χ) V} {s : RewriteState Op χ V}
  (h : (deadCodeElim (Op := Op) (χ := χ) (V := V)).run (.init aps disabledRules) =
    some ((name, res), s)) :
    s.aps = aps ∧ DCEMatch aps s.matched name res
  := by
  unfold deadCodeElim StateT.run at h
  replace ⟨i₁, ap, _, hap, h⟩ := RewriteM.choose_some' h
  -- One case per top-level branch of `deadCodeElim`
  split at h
  case h_1 => exact Extract.branch_op_some rfl rfl hap h
  case h_2 => exact Extract.branch_forward_some rfl rfl hap h
  case h_3 => exact Extract.branch_switch_some rfl rfl hap h
  case h_4 => exact Extract.branch_steer_some rfl rfl hap h
  case h_5 => exact Extract.branch_fork_zero_some rfl rfl hap h
  case h_6 => exact Extract.branch_fork_one_some rfl rfl hap h
  case h_7 => exact Extract.branch_fork_some rfl rfl hap h
  case h_8 => exact Extract.branch_order_one_some rfl rfl hap h
  case h_9 => exact Extract.branch_order_some rfl rfl hap h
  case h_10 => exact Extract.branch_const_some rfl rfl hap h
  case h_11 => exact Extract.branch_inact_some rfl rfl hap h
  case h_12 => exact Extract.branch_carry_left_some rfl rfl hap h
  case h_13 => exact Extract.branch_carry_right_some rfl rfl hap h
  case h_14 => exact Extract.branch_merge_some rfl rfl hap h
  case h_15 => exact (StateT.failure_some h).elim

end Wavelet.Compile.DeadCodeElim
