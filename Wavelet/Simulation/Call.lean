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

def Fn.encap [Arity Op] (fn : Fn Op χ m n) : EncapFn Op χ := ⟨m, n, fn⟩

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

/-- Augments the operator set with a list of custom functions. -/
inductive WithFns Op [Arity Op] {χ k} (fns : Vector (EncapFn Op χ) k) where
  | op (o : Op)
  | call (k : Fin k)

inductive WithFn (Op : Type u) [Arity Op] {χ} (fn : EncapFn Op χ) : Type u where
  | op (o : Op)
  | call

infixl:65 " w/ " => WithFns
infixl:65 " w/ " => WithFn

/-- States for the additional `k` functions. -/
structure WithFns.State
  Op χ V S
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapFn Op χ) k) where
  innerState : S
  fnStates : Vector (Option (EncapConfig Op χ V S)) k

structure WithFn.State
  Op χ V S
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fn : EncapFn Op χ) where
  innerState : S
  config : Option (Seq.Config Op χ V S fn.ι fn.ω)

instance
  [Arity Op]
  {fns : Vector (EncapFn Op χ) k} : Arity (WithFns Op fns) where
  ι | .op o => Arity.ι o
    | .call i => fns[i].ι
  ω | .op o => Arity.ω o
    | .call i => fns[i].ω

instance
  [Arity Op]
  {fn : EncapFn Op χ} : Arity (WithFn Op fn) where
  ι | .op o => Arity.ι o
    | .call => fn.ι
  ω | .op o => Arity.ω o
    | .call => fn.ω

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
      }, none)
  | step_call_cont :
    state.fnStates[i] = some ec →
    Seq.Config.Step ec.config config' →
    WithFns.Step fns (.call i) inputVals
      state
      ({ state with
        fnStates := state.fnStates.set i (some { ec with config := config' })
      }, none)
  | step_call_ret :
    state.fnStates[i] = some ec →
    (_ : ec.ω = fns[i].ω) →
    ec.config.expr = .ret retVals →
    WithFns.Step fns (.call i) inputVals
      state
      (
        { state with fnStates := state.fnStates.set i none },
        some (cast (by congr) retVals),
      )

inductive WithFn.Step
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fn : EncapFn Op χ) :
  (op : WithFn Op fn) →
  Vector V (Arity.ι op) →
  WithFn.State Op χ V S fn →
  WithFn.State Op χ V S fn × Option (Vector V (Arity.ω op)) →
  Prop where
  | step_op :
    InterpOp.Step o inputVals state.innerState (innerState', outputVals) →
    WithFn.Step fn (.op o) inputVals state
      ({ state with innerState := innerState' }, outputVals)
  /-- Initialize call state without producing any outputs. -/
  | step_call_init :
    state.config = none →
    WithFn.Step fn .call inputVals
      state
      ({
        state with
        config := some (Seq.Config.init fn.fn state.innerState inputVals)
      }, none)
  | step_call_cont :
    state.config = some config →
    Seq.Config.Step config config' →
    WithFn.Step fn .call inputVals
      state
      ({ state with config := config' }, none)
  | step_call_ret :
    state.config = some config →
    config.expr = .ret retVals →
    WithFn.Step fn .call inputVals
      state
      ({ state with config := none }, some retVals)

instance
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapFn Op χ) k)
  : InterpOp (WithFns Op fns) V (WithFns.State Op χ V S fns) where
  Step := WithFns.Step fns

instance
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fn : EncapFn Op χ)
  : InterpOp (WithFn Op fn) V (WithFn.State Op χ V S fn) where
  Step := WithFn.Step fn

example
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapFn Op χ) k)
  (main : Fn (Op w/ fns) χ m n)
  : Dataflow.Proc Op χ V m n := sorry

example
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fn : EncapFn Op χ)
  (main : Fn (Op w/ fn) χ m n)
  : Dataflow.Proc Op χ V m n := sorry

example
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns₁ : Vector (EncapFn Op χ) k)
  (fns₂ : Vector (EncapFn (Op w/ fns₁) χ) k)
  (main : Fn (Op w/ fns₁ w/ fns₂) χ m n)
  : Dataflow.Proc Op χ V m n := sorry

example
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fn₁ : EncapFn Op χ)
  (fn₂ : EncapFn (Op w/ fn₁) χ)
  (fn₃ : EncapFn (Op w/ fn₁ w/ fn₂) χ)
  (main : Fn (Op w/ fn₁ w/ fn₂ w/ fn₃) χ m n)
  : Dataflow.Proc Op χ V m n := sorry

inductive Fns (χ : Type v) (V : Type w) (S : Type x) : Type u → Type (max (u + 1) v w x) where
  | empty : Fns χ V S Op
  | decl [Arity Op]
    (rest : Fns χ V S Op)
    (fn : EncapFn Op χ)
    : Fns χ V S (Op w/ fn)

section Example

variable (Op χ V S : Type*)
variable [Arity Op]

def efn₁ : EncapFn Op χ := sorry
def efn₂ : EncapFn (Op w/ (efn₁ Op χ)) χ := sorry
def fns : Fns χ V S (Op w/ (efn₁ Op χ) w/ (efn₂ Op χ))
  := .decl (.decl .empty (efn₁ Op χ)) (efn₂ Op χ)

end Example

end Wavelet.Seq

namespace Wavelet.Dataflow

open Op Seq

structure EncapProc Op χ V [Arity Op] where
  ι : Nat
  ω : Nat
  proc : Proc Op χ V ι ω

structure EncapConfig Op χ V S [Arity Op] where
  ι : Nat
  ω : Nat
  config : Dataflow.Config Op χ V S ι ω

def EncapConfig.init {Op χ V S}
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V S]
  [DecidableEq χ]
  (ef : EncapProc Op χ V)
  (state : S)
  (args : Vector V ef.ι) :
  EncapConfig Op χ V S :=
  ⟨ef.ι, ef.ω, Dataflow.Config.init ef.proc state args⟩

/-- Augments the operator set with a vector of custom processes. -/
inductive WithProcs Op [Arity Op] {χ V k} (procs : Vector (EncapProc Op χ V) k) where
  | op (o : Op)
  | proc (k : Fin k)

infixl:65 " w/ " => WithProcs

structure WithProcs.State
  Op χ V S
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : Vector (EncapProc Op χ V) k) where
  innerState : S
  procStates : Vector (Option (EncapConfig Op χ V S)) k

instance
  [Arity Op]
  {procs : Vector (EncapProc Op χ V) k} : Arity (WithProcs Op procs) where
  ι | .op o => Arity.ι o
    | .proc i => procs[i].ι
  ω | .op o => Arity.ω o
    | .proc i => procs[i].ω

inductive WithProcs.Step
  [Arity Op] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (procs : Vector (EncapProc Op χ V) k) :
  (op : WithProcs Op procs) →
  Vector V (Arity.ι op) →
  WithProcs.State Op χ V S procs →
  WithProcs.State Op χ V S procs × Option (Vector V (Arity.ω op)) →
  Prop where
  | step_op :
    InterpOp.Step o inputVals state.innerState (innerState', outputVals) →
    WithProcs.Step procs (.op o) inputVals state
      ({ state with innerState := innerState' }, outputVals)
  | step_proc_init :
    state.procStates[i] = none →
    WithProcs.Step procs (.proc i) inputVals
      state
      ({
        state with
        procStates := state.procStates.set i
          (some (EncapConfig.init procs[i] state.innerState inputVals))
      }, none)
  | step_proc_cont :
    state.procStates[i] = some pc →
    Dataflow.Config.Step pc.config config' →
    WithProcs.Step procs (.proc i) inputVals
      state
      ({ state with
        procStates := state.procStates.set i (some { pc with config := config' })
      }, none)
  | step_proc_ret :
    state.procStates[i] = some pc →
    pc.config.chans.popVals procs[i].proc.outputs = some (retVals, chans') →
    WithProcs.Step procs (.proc i) inputVals
      state
      (
        { state with procStates := state.procStates.set i none },
        some retVals,
      )

/-- Flatten the use of nested processes to get a single dataflow graph. -/
def flatten
  [Arity Op]
  (procs : Vector (EncapProc Op χ V) k)
  (main : Proc (Op w/ procs) χ V m n)
  : Proc Op χ V m n := sorry

end Wavelet.Dataflow
