import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

/-! Add (non-recursive) function calls by interpreting a function as an operator. -/

namespace Wavelet.Seq

open Op

/-- Interprets a function as an operator in the sequential semantics. -/
inductive Fn.OpStep
  [Arity Op] [InterpConsts V] [InterpOp Op V S] [DecidableEq χ]
  (fn : Fn Op χ m n) (args : Vector V m) :
  S × Option (Seq.Config Op χ V S m n) →
  (S × Option (Seq.Config Op χ V S m n)) × Option (Vector V n) → Prop where
  | step_fn_init :
    Fn.OpStep fn args (state, none) ((state, Seq.Config.init fn state args), none)
  | step_fn_cont :
    Seq.Config.Step { c with state } c' →
    Fn.OpStep fn args (state, some c) ((c'.state, some c'), none)
  | step_fn_ret :
    c.expr = .ret retVals →
    Fn.OpStep fn args (state, some c) ((state, none), some retVals)

end Wavelet.Seq

namespace Wavelet.Dataflow

open Op Seq

/-- Interprets a process as an operator in the dataflow semantics. -/
inductive Proc.OpStep
  [Arity Op] [InterpConsts V] [InterpOp Op V S] [DecidableEq χ]
  (proc : Proc Op (ChanName χ) V m n) (args : Vector V m) :
  S × Option (Dataflow.Config Op (ChanName χ) V S m n) →
  (S × Option (Dataflow.Config Op (ChanName χ) V S m n)) × Option (Vector V n) → Prop where
  | step_proc_init :
    Proc.OpStep proc args (state, none)
      ((state, some (Dataflow.Config.init proc state args)), none)
  | step_proc_cont :
    Dataflow.Config.Step { c with state } c' →
    Proc.OpStep proc args (state, some c) ((c'.state, some c'), none)
  | step_proc_ret :
    c.chans.popVals ((Vector.range n).map ChanName.final_dest) = some (retVals, chans') →
    Proc.OpStep proc args (state, some c)
      ((state, none), some retVals)

end Wavelet.Dataflow

namespace Wavelet.Seq

open Op

structure EncapFn Op χ [Arity Op] where
  ι : Nat
  ω : Nat
  fn : Fn Op χ ι ω

structure EncapConfig Op χ V S [Arity Op] where
  ι : Nat
  ω : Nat
  config : Seq.Config Op χ V S ι ω

def EncapConfig.init {Op χ V S}
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V S]
  [DecidableEq χ]
  (ef : EncapFn Op χ)
  (state : S)
  (args : Vector V ef.ι) :
  EncapConfig Op χ V S :=
  ⟨ef.ι, ef.ω, Seq.Config.init ef.fn state args⟩

/-- Augments the operator set with one custom function. -/
inductive WithFns Op [Arity Op] {χ k} (fns : Vector (EncapFn Op χ) k)
  | op (o : Op)
  | call (k : Fin k)

/-- States for the additional `k` functions. -/
structure WithFns.State
  Op χ V S
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapFn Op χ) k) where
  innerState : S
  fnStates : Vector (Option (EncapConfig Op χ V S)) k
  inv_matching_io {i : Fin k} :
    fnStates[i] = some ec → ec.ι = fns[i].ι ∧ ec.ω = fns[i].ω

instance
  [Arity Op]
  {fns : Vector (EncapFn Op χ) k} : Arity (WithFns Op fns) where
  ι | .op o => Arity.ι o
    | .call i => fns[i].ι
  ω | .op o => Arity.ω o
    | .call i => fns[i].ω

inductive WithFns.Step
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapFn Op χ) k) :
  (op : WithFns Op fns) →
  Vector V (Arity.ι op) →
  WithFns.State Op χ V S fns →
  WithFns.State Op χ V S fns × Option (Vector V (Arity.ω op)) →
  Prop where
  | step_op :
    InterpOp.Step o inputVals state.innerState (innerState', outputVals) →
    WithFns.Step fns (.op o) inputVals state
      ({ state with innerState := innerState' }, outputVals)
  /-- Initialize call state without producing any outputs. -/
  | step_call_init :
    state.fnStates[i] = none →
    WithFns.Step fns (.call i) inputVals
      state
      ({
        state with
        fnStates := state.fnStates.set i
          (some (EncapConfig.init fns[i] state.innerState inputVals))
        -- Preserve that the invariant is preserved.
        inv_matching_io := by
          intros ec j hec
          simp [Vector.getElem_set] at hec
          split at hec <;> rename_i hj
          · simp [EncapConfig.init] at hec
            simp [← hec, hj]
          · apply state.inv_matching_io hec
      }, none)
  | step_call_cont :
    state.fnStates[i] = some ec →
    Seq.Config.Step ec.config config' →
    WithFns.Step fns (.call i) inputVals
      state
      ({ state with
        fnStates := state.fnStates.set i (some { ec with config := config' })
        inv_matching_io := by sorry
      }, none)
  | step_call_ret :
    (hec : state.fnStates[i] = some ec) →
    ec.config.expr = .ret retVals →
    WithFns.Step fns (.call i) inputVals
      state
      (
        { state with
          fnStates := state.fnStates.set i none
          inv_matching_io := by sorry
        },
        some (cast (by
          congr 1
          simp [Arity.ω]
          apply (state.inv_matching_io hec).2
        ) retVals),
      )

instance
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapFn Op χ) k)
  : InterpOp (WithFns Op fns) V (WithFns.State Op χ V S fns) where
  Step := WithFns.Step fns

end Wavelet.Seq
