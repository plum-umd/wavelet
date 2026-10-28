import Wavelet.Thm.Compile.MapChans
import Wavelet.Thm.Compile.Rewrite.Sim
import Wavelet.Thm.Compile.Rewrite.Monad
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Extract
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SyncOrderOrder
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.FoldForward
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SwitchSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SteerConst
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.SteerSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ParSteerSteer
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstSteer
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Fork0
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Fork1
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ForkSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ForkFork
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.Order1
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.OrderOrder
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.OrderSyncPath
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.OrderSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.OrderConst
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.OrderSteerSteer
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.ConstSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.InactSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.CarryForkSteerToInv
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.CarryConst
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.MergeSink
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.MergeConst
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.CarrySteerCycle
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.MergeSteer
import Wavelet.Thm.Compile.Rewrite.DeadCodeElim.MergeDedup

/-! Main theorems for one application of `deadCodeElim`. -/

namespace Wavelet.Compile.DeadCodeElim

open Semantics Dataflow

/-- Rules of `deadCodeElim` that produce n-ary sinks, which may leave unconsumed values. -/
def naryRules : List String := [
  "carry-steer-cycle-to-sink",
  "carry-order-steer-cycle-to-sink",
  "merge-steer-true",
  "merge-steer-false",
  "merge-dedup",
]

theorem rename_not_mem_allNames
  [Arity Op] {proc : Proc Op χ V m n} {i : Nat} {x : RewriteName χ} :
    RewriteName.rename i x ∉ (proc.mapChans RewriteName.base).allNames := by
  simp [Proc.allNames, Proc.mapChans, AtomicProcs.inputNames, AtomicProcs.outputNames,
    AtomicProcs.mapChans]

theorem dce_match_ok
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {I : List Nat} {name : String}
  {res : AtomicProcs Op (RewriteName χ) V}
  (haff : (proc.mapChans RewriteName.base).AffineChan)
  (h : DCEMatch (proc.mapChans RewriteName.base).atoms I name res)
  (hname : name ∉ excludedRules)
  (hnary : name ∉ naryRules) :
    RuleOK (proc.mapChans RewriteName.base) I res := by
  cases h with
  | sync_order_order h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hlen₁ hlen₂ hmem₁ hmem₂ =>
    exact sync_order_order_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hlen₁ hlen₂ hmem₁ hmem₂
  | fold_forward_aop_receiver h₁ h₂ hne hmem =>
    exact fold_forward_aop_receiver_ok haff h₁ h₂ hne hmem
  | fold_forward_aop_sender h₁ h₂ hne hnmem hmem =>
    exact fold_forward_aop_sender_ok haff h₁ h₂ hne hnmem hmem
  | fold_forward_op_receiver h₁ h₂ hne hmem =>
    exact fold_forward_op_receiver_ok haff h₁ h₂ hne hmem
  | fold_forward_op_sender h₁ h₂ hne hnmem hmem =>
    exact fold_forward_op_sender_ok haff h₁ h₂ hne hnmem hmem
  | switch_sink_left h₁ h₂ hne =>
    exact switch_sink_left_ok haff h₁ h₂ hne
  | switch_sink_right h₁ h₂ hne hne' =>
    exact switch_sink_right_ok haff h₁ h₂ hne hne'
  | steer_const_true h₁ hconst hbool =>
    exact steer_const_true_ok haff h₁ hconst hbool
  | steer_const_false h₁ hconst hbool hne =>
    exact steer_const_false_ok haff h₁ hconst hbool hne
  | steer_sink h₁ h₂ hne =>
    exact steer_sink_ok haff h₁ h₂ hne
  | par_steer_steer h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hlen hfork₁ hfork₂ =>
    exact par_steer_steer_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hlen hfork₁ hfork₂
      rename_not_mem_allNames
  | const_steer h₁ h₂ hne =>
    exact const_steer_ok haff h₁ h₂ hne rename_not_mem_allNames
  | fork_0 h₁ =>
    exact fork_0_ok h₁
  | fork_1 h₁ =>
    exact fork_1_ok h₁
  | fork_sink h₁ h₂ hne hlen hmem =>
    exact fork_sink_ok haff h₁ h₂ hne hlen hmem
  | fork_fork h₁ h₂ hne hlen hlen' hmem =>
    exact fork_fork_ok haff h₁ h₂ hne hlen hlen' hmem
  | order_1 h₁ =>
    exact order_1_ok h₁
  | order_order h₁ h₂ hne hk₁ hlen _ hlen' hmem hnew =>
    exact order_order_ok haff h₁ h₂ hne hk₁ hlen hlen' hmem hnew
  | order_sync_path h₁ h₂ hne _ hlen hlen' hmem₁ hmem₂ =>
    exact order_sync_path_ok haff h₁ h₂ hne hlen hlen' hmem₁ hmem₂
  | order_sink h₁ h₂ hne _ _ _ hmem =>
    exact order_sink_ok haff h₁ h₂ hne hmem
  | order_const h₁ h₂ hne _ hlen hmem hne' =>
    exact order_const_ok haff h₁ h₂ hne hlen hmem hne'
  | order_const_head h₁ h₂ hne _ hlen =>
    exact order_const_head_ok haff h₁ h₂ hne hlen
  | order_steer_steer h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork =>
    exact order_steer_steer_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork
  | const_sink h₁ h₂ hne =>
    exact const_sink_ok haff h₁ h₂ hne
  | inact_sink h₁ h₂ hne _ _ _ hndisj =>
    exact inact_sink_ok haff h₁ h₂ hne hndisj
  | carry_fork_steer_to_inv_left h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork =>
    exact carry_fork_steer_to_inv_left_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork
  | carry_fork_steer_to_inv_right h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ _ hfork =>
    exact carry_fork_steer_to_inv_right_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork
  | carry_steer_cycle_to_sink => simp [naryRules] at hnary
  | carry_order_steer_cycle_to_sink => simp [naryRules] at hnary
  | carry_false h₁ hconst hbool =>
    exact carry_false_ok haff h₁ hconst hbool
  | carry_true h₁ hconst hbool =>
    exact carry_true_ok haff h₁ hconst hbool
  | merge_sink h₁ h₂ hne _ hmem =>
    exact merge_sink_ok haff h₁ h₂ hne hmem
  | merge_steer_true => simp [naryRules] at hnary
  | merge_steer_false => simp [naryRules] at hnary
  | merge_dedup => simp [naryRules] at hnary
  | merge_same_const h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ =>
    exact merge_same_const_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ rename_not_mem_allNames
  | merge_true_false_const h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hbool₁ hbool₂ =>
    exact merge_true_false_const_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hbool₁ hbool₂
  | excluded h => exact absurd h hname

theorem dce_match_ok_nary
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {proc : Proc Op χ V m n} {I : List Nat} {name : String}
  {res : AtomicProcs Op (RewriteName χ) V}
  (haff : (proc.mapChans RewriteName.base).AffineChan)
  (h : DCEMatch (proc.mapChans RewriteName.base).atoms I name res)
  (hnary : name ∈ naryRules) :
    RuleOKNoInit (proc.mapChans RewriteName.base) I res := by
  cases h
  case carry_steer_cycle_to_sink h₁ h₂ hne _ =>
    exact carry_steer_cycle_to_sink_ok haff h₁ h₂ hne
  case carry_order_steer_cycle_to_sink h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ _ hmem _ =>
    exact carry_order_steer_cycle_to_sink_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hmem
  case merge_steer_true h₁ h₂ hne hfork =>
    exact merge_steer_true_ok haff h₁ h₂ hne hfork
  case merge_steer_false h₁ h₂ hne hfork =>
    exact merge_steer_false_ok haff h₁ h₂ hne hfork
  case merge_dedup h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork₁ hfork₂ hfork₃ =>
    exact merge_dedup_ok haff h₁ h₂ h₃ hne₂₁ hne₃₁ hne₃₂ hfork₁ hfork₂ hfork₃
      rename_not_mem_allNames
  case excluded h =>
    exfalso
    simp only [excludedRules, naryRules, List.mem_cons, List.not_mem_nil, or_false] at h hnary
    rcases h with rfl | rfl | rfl <;> simp at hnary
  all_goals simp [naryRules] at hnary

private theorem base_injective : Function.Injective (RewriteName.base (χ := χ)) := by
  intro x y h; cases h; rfl

private theorem rw_injective : Function.Injective (RewriteName.rw (χ := χ)) := by
  intro x y h; cases h; rfl

/-- Decomposes `deadCodeElim.apply` into a `DCEMatch` and a renaming. -/
private theorem dead_code_elim_apply_some
  [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V] [DecidableEq V]
  {proc : Proc Op χ V m n} {proc' : Proc Op (RewriteName χ) V m n}
  {disabledRules : List String} {rwName : String}
  (hrw : deadCodeElim.apply (proc.mapChans .base) disabledRules = some (rwName, proc')) :
    ∃ I res,
      DCEMatch (proc.mapChans .base).atoms I rwName res ∧
      proc' = ({ proc.mapChans .base with
        atoms := res ++ unmatchedOf (proc.mapChans .base).atoms I
      } : Proc Op (RewriteName χ) V m n).mapChans .rw := by
  obtain ⟨res, s, hrun, rfl⟩ := Rewrite.apply_some hrw
  obtain ⟨haps, hmatch⟩ := deadCodeElim_some hrun
  refine ⟨s.matched, res, hmatch, ?_⟩
  rw [haps]
  rfl

/-- One application of `deadCodeElim` is a forward simulation, except for the rules in
`excludedRules` and `naryRules`. -/
theorem dead_code_elim_sim_preserves_init
  [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V] [DecidableEq V]
  {proc : Proc Op χ V m n} {proc' : Proc Op (RewriteName χ) V m n}
  {disabledRules : List String} {rwName : String}
  (haff : proc.AffineChan)
  (hrw : deadCodeElim.apply (proc.mapChans .base) disabledRules = some (rwName, proc'))
  (hname : rwName ∉ excludedRules)
  (hnary : rwName ∉ naryRules) :
    (proc.semantics ≲ᵣ[PreservesInit] proc'.semantics) ∧ proc'.AffineChan := by
  have haff₀ := map_chans_preserves_aff_var base_injective haff
  obtain ⟨I, res, hmatch, rfl⟩ := dead_code_elim_apply_some hrw
  have hok := dce_match_ok haff₀ hmatch hname hnary
  constructor
  · apply IORestrictedSimilaritySt.trans_preserves_init
      (sim_map_chans_inj_preserves_init base_injective).to_restricted_sim
    apply IORestrictedSimilaritySt.trans_preserves_init
      (sim_rewrite_preserves_init haff₀ hok)
    exact (sim_map_chans_inj_preserves_init rw_injective).to_restricted_sim
  · exact map_chans_preserves_aff_var rw_injective (rewrite_affine_chan haff₀ hok.1)

/-- The rules in `naryRules` are forward simulations, but without `PreservesInit`. -/
theorem dead_code_elim_sim_nary
  [Arity Op] [DecidableEq χ] [Hashable χ] [InterpConsts V] [DecidableEq V]
  {proc : Proc Op χ V m n} {proc' : Proc Op (RewriteName χ) V m n}
  {disabledRules : List String} {rwName : String}
  (haff : proc.AffineChan)
  (hrw : deadCodeElim.apply (proc.mapChans .base) disabledRules = some (rwName, proc'))
  (hnary : rwName ∈ naryRules) :
    (proc.semantics ≲ᵣ proc'.semantics) ∧ proc'.AffineChan := by
  have haff₀ := map_chans_preserves_aff_var base_injective haff
  obtain ⟨I, res, hmatch, rfl⟩ := dead_code_elim_apply_some hrw
  have hok := dce_match_ok_nary haff₀ hmatch hnary
  constructor
  · apply IORestrictedSimilarity.trans
      (StrongSimilaritySt.to_restricted_sim (sim_map_chans_inj base_injective))
    apply IORestrictedSimilarity.trans (sim_rewrite haff₀ hok)
    exact StrongSimilaritySt.to_restricted_sim (sim_map_chans_inj rw_injective)
  · exact map_chans_preserves_aff_var rw_injective (rewrite_affine_chan haff₀ hok.1)

end Wavelet.Compile.DeadCodeElim
