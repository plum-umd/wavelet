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

/-- Augments the operator set with an uninterpreted set of function names. -/
inductive WithFns Op (F : Type u) [Arity Op] where
  | op (o : Op)
  | call (f : F)

infixl:65 " w/ " => WithFns

abbrev WithFns.Interp Op F χ [Arity Op] [Arity F] :=
  (f : F) → Fn Op χ (Arity.ι f) (Arity.ω f)

/-- States for the additional `k` functions. -/
structure WithFns.State
  Op χ V S
  [Arity Op] [Arity F] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : WithFns.Interp Op F χ) where
  innerState : S
  fnStates : (f : F) → Option (Config Op χ V S (Arity.ι f) (Arity.ω f))

instance [Arity Op] [Arity F] : Arity (WithFns Op F) where
  ι | .op o => Arity.ι o
    | .call f => Arity.ι f
  ω | .op o => Arity.ω o
    | .call f => Arity.ω f

/-- Instantiate the function names with a list of functions -/
inductive WithFns.Step
  [Arity Op] [Arity F] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : WithFns.Interp Op F χ) :
  (op : WithFns Op F) →
  Vector V (Arity.ι op) →
  WithFns.State Op χ V S fns →
  WithFns.State Op χ V S fns × Option (Vector V (Arity.ω op)) →
  Prop where
  | step_op :
    InterpOp.Step o inputVals state.innerState (innerState', outputVals) →
    WithFns.Step fns (.op o) inputVals state
      ({ state with innerState := innerState' }, outputVals)
  -- /-- Initialize call state without producing any outputs. -/
  -- | step_call_init :
  --   state.fnStates i = none →
  --   WithFns.Step fns (.call i) inputVals
  --     state
  --     ({
  --       state with
  --       fnStates := state.fnStates.set i
  --         (some (EncapConfig.init fns[i] state.innerState inputVals))
  --     }, none)
  -- | step_call_cont :
  --   state.fnStates[i] = some ec →
  --   Seq.Config.Step ec.config config' →
  --   WithFns.Step fns (.call i) inputVals
  --     state
  --     ({ state with
  --       fnStates := state.fnStates.set i (some { ec with config := config' })
  --     }, none)
  -- | step_call_ret :
  --   state.fnStates[i] = some ec →
  --   (_ : ec.ω = fns[i].ω) →
  --   ec.config.expr = .ret retVals →
  --   WithFns.Step fns (.call i) inputVals
  --     state
  --     (
  --       { state with fnStates := state.fnStates.set i none },
  --       some (cast (by congr) retVals),
  --     )

instance
  [Arity Op] [Arity F] [InterpConsts V]
  [InterpOp Op V S] [DecidableEq χ]
  (fns : WithFns.Interp Op F χ)
  : InterpOp (WithFns Op F) V (WithFns.State Op χ V S fns) where
  Step := WithFns.Step fns

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

end Wavelet.Dataflow

namespace Wavelet.Compile

open Op Seq Dataflow

-- /-- Flatten the use of nested processes to get a single dataflow graph. -/
-- def linkProcs
--   [Arity Op]
--   (procs : Vector (EncapProc Op χ V) k)
--   (main : Proc (Op w/ procs) χ V m n)
--   : Proc Op χ V m n := sorry

-- def linkFn
--   [Arity Op] [Arity F] [InterpConsts V]
--   [DecidableEq χ]
--   (fn : Fn (Op w/ F) χ m n)
--   (compiled : (f : F) → Proc Op χ V (Arity.ι f) (Arity.ω f))
--   : Proc (Op w/ F) χ V m n := sorry

end Wavelet.Compile

namespace Wavelet.Op

instance instAritySum [l : Arity Op₁] [r : Arity Op₂] : Arity (Op₁ ⊕ Op₂) where
  ι | .inl o => Arity.ι o
    | .inr o => Arity.ι o
  ω | .inl o => Arity.ω o
    | .inr o => Arity.ω o

instance [Arity Op₁] [Arity Op₂]
  [InterpOp Op₁ V S] [InterpOp Op₂ V S]
  : InterpOp (Op₁ ⊕ Op₂) V S where
  Step op inputs state res :=
    match op with
    | .inl o => InterpOp.Step o inputs state res
    | .inr o => InterpOp.Step o inputs state res

end Wavelet.Op

namespace Wavelet.Compile

open Op Seq Dataflow

/-- Interpretation of symbols in `F` as sequential functions. -/
abbrev FnInterps Op (F : Type u) χ [Arity Op] [Arity F] := (f : F) → Fn Op χ (Arity.ι f) (Arity.ω f)

/-- Interpretation of symbols in `F` as dataflow processes. -/
abbrev ProcInterps Op (F : Type u) χ V [Arity Op] [Arity F] := (f : F) → Proc Op χ V (Arity.ι f) (Arity.ω f)

structure FnInterps.State
  Op χ V S [Arity Op] [Arity F]
  (fns : FnInterps Op F χ) where
  state : S
  configs : (f : F) → Option (Seq.Config Op χ V S (Arity.ι f) (Arity.ω f))

structure ProcInterps.State
  Op χ V S [Arity Op] [Arity F]
  (procs : ProcInterps Op F χ V) where
  state : S
  configs : (f : F) → Option (Dataflow.Config Op χ V S (Arity.ι f) (Arity.ω f))

instance instArityFin [inst : Arity (Fin k)] {k' : Fin k} : Arity (Fin k') where
  ι i := inst.ι (i.castLT (by omega))
  ω i := inst.ω (i.castLT (by omega))

instance [inst : Arity (Fin (k + 1))] : Arity (Fin k) where
  ι i := inst.ι (i.castLT (by omega))
  ω i := inst.ω (i.castLT (by omega))

abbrev Prog Op χ k [Arity Op] [sig : Arity (Fin k)] :=
  (i : Fin k) → Fn (Op ⊕ Fin i) χ (Arity.ι i) (Arity.ω i)

abbrev exampleSig : Arity (Fin 2) := {
    ι | 0 => 2
      | 1 => 3,
    ω | 0 => 1
      | 1 => 2,
  }

def exampleProg [Arity Op] : Prog (sig := exampleSig) Op String 2
  | 0 =>
    let : Arity (Fin 0) := _
    {
      params := #v["a", "b"],
      body := .ret #v["a"],
      : Fn (Op ⊕ Fin 0) _ _ _
    }
  | 1 =>
    let : Arity (Fin 1) := _
    {
      params := #v["a", "b", "c"],
      body :=
        .op (.inr 0)
          (cast (by rfl) #v["b", "c"])
          (cast (by rfl) #v["d"])
          (.ret #v["a", "d"]),
      : Fn (Op ⊕ Fin 1) _ _ _
    }

/-- Channel name prefixes to disambiguate names during linking. -/
inductive LinkName (χ : Type u) where
  | base (name : χ)
  | main (name : LinkName χ)
  | dep (i : Nat) (name : LinkName χ)

def linkAtomicProc
  [Arity Op] [Arity (Fin k)]
  (procs : (i : Fin k) → Proc Op (LinkName χ) V (Arity.ι i) (Arity.ω i))
  (idx : Nat) -- Index of the atomic proc
  (atom : AtomicProc (Op ⊕ Fin k) (LinkName χ) V) : AtomicProcs Op (LinkName χ) V :=
  match atom with
  | .op (.inl o) inputs outputs =>
    [.op o (inputs.map .main) (outputs.map .main)]
  | .op (.inr i) inputs outputs =>
    [ .forward (inputs.map .main) ((procs i).inputs.map (LinkName.dep idx)) ] ++
    (procs i).atoms.mapChans (LinkName.dep idx) ++
    [ .forward ((procs i).outputs.map (LinkName.dep idx)) (outputs.map .main) ]
  | .switch decider inputs outputs₁ outputs₂ =>
    [.switch (.main decider) (inputs.map .main) (outputs₁.map .main) (outputs₂.map .main)]
  | .steer flavor decider inputs outputs =>
    [.steer flavor (.main decider) (inputs.map .main) (outputs.map .main)]
  | .carry inLoop decider inputs₁ inputs₂ outputs =>
    [.carry inLoop (.main decider) (inputs₁.map .main) (inputs₂.map .main) (outputs.map .main)]
  | .merge decider inputs₁ inputs₂ outputs =>
    [.merge (.main decider) (inputs₁.map .main) (inputs₂.map .main) (outputs.map .main)]
  | .forward inputs outputs => [.forward (inputs.map .main) (outputs.map .main)]
  | .fork input outputs => [.fork (.main input) (outputs.map .main)]
  | .const c act outputs => [.const c act (outputs.map .main)]
  | .forwardc inputs consts outputs => [.forwardc (inputs.map .main) consts (outputs.map .main)]
  | .sink inputs => [.sink (inputs.map .main)]

/-- Inline calls to the given `k` processes while preserving a forward simulation. -/
def linkProcs
  [Arity Op] [Arity (Fin k)]
  (procs : (i : Fin k) → Proc Op (LinkName χ) V (Arity.ι i) (Arity.ω i))
  (main : Proc (Op ⊕ Fin k) (LinkName χ) V m n)
  : Proc Op (LinkName χ) V m n := {
    inputs := main.inputs.map LinkName.main,
    outputs := main.outputs.map LinkName.main,
    atoms := (main.atoms.mapIdx (linkAtomicProc procs)).flatten,
  }

/-- Given a program (a list of functions that non-recursively call each other),
compile the `i`-th function to a process without any dependencies. -/
def compileProg
  [Arity Op] [sig : Arity (Fin k)]
  [DecidableEq χ] [InterpConsts V]
  (prog : Prog Op χ k)
  (hnz : ∀ i : Fin k, sig.ι i > 0 ∧ sig.ω i > 0)
  (i : Fin k) : Proc Op (LinkName (ChanName χ)) V (sig.ι i) (sig.ω i) :=
  -- Compile the current function
  let proc : Proc (Op ⊕ Fin i) (LinkName (ChanName χ)) V _ _ :=
    compileFn (by apply hnz) (prog i) |>.mapChans LinkName.base
  -- Compile dependencies
  let deps : (j : Fin i) → Proc Op (LinkName (ChanName χ)) V (Arity.ι j) (Arity.ω j) :=
    λ j => compileProg prog hnz (j.castLT (by omega))
  -- Link everything into one dataflow graph
  linkProcs deps proc

abbrev ProgConfig Op χ V S k [Arity Op] [sig : Arity (Fin k)] :=
  (i : Fin k) → Seq.Config (Op ⊕ Fin k) χ V S (Arity.ι i) (Arity.ω i)

/-- Lifts an interpretation across different universe for the state type. -/
instance [Arity Op] [InterpOp Op V S] : InterpOp Op V (ULift S) where
  Step o inputs state res := InterpOp.Step o inputs state.down ⟨res.1.down, res.2⟩

inductive Prog.StepFn
  [Arity Op] [InterpConsts V]
  [inst : InterpOp Op V S] [DecidableEq χ] :
  (fn : Fn Op χ m n) →
  Vector V m →
  S × Option (Seq.Config Op χ V S m n) →
  (S × Option (Seq.Config Op χ V S m n)) × Option (Vector V n) →
  Prop where
  | step_fn_init :
    Prog.StepFn fn args (state, none) ((state, some (Seq.Config.init fn state args)), none)
  | step_fn_cont :
    Seq.Config.Step { c with state } c' →
    Prog.StepFn fn args (state, some c) ((c'.state, some c'), none)
  | step_fn_ret :
    c.expr = .ret retVals →
    Prog.StepFn fn args (state, some c) ((state, none), some retVals)

/--
Given the base semantics of `Op` wrt. value type `V`
and state type `S`, generates a semantics for `Op ⊕ Fin i`
by interpreting the first `i` functions.
-/
def Prog.AsInterpOp
  {Op : Type u₁} {χ : Type u₂}
  (V : Type u₃) (S : Type u₄)
  [Arity Op] [sig : Arity (Fin k)]
  [DecidableEq χ] [InterpConsts V]
  [InterpOp Op V S]
  (prog : Prog Op χ k)
  : (i : Fin k) →
    (S' : Type (max u₁ u₂ u₃ u₄)) ×
    (S → S') ×
    InterpOp (Op ⊕ Fin i) V S'
  | ⟨0, _⟩ =>
    let : Arity (Fin 0) := _
    ⟨
      ULift S,
      ULift.up,
      {
        Step
          | .inl o => InterpOp.Step o
          | .inr f => Fin.elim0 f
      },
    ⟩
  | ⟨i' + 1, _⟩ =>
    let i'fin := ⟨i', by omega⟩
    let ⟨S', init, inst'⟩ := prog.AsInterpOp V S i'fin
    let fn := prog i'fin
    let : Arity (Fin (i' + 1)) := _
    ⟨
      S' × Option (Seq.Config (Op ⊕ Fin i') χ V S' (Arity.ι i'fin) (Arity.ω i'fin)),
      λ s => (init s, none),
      {
        Step
          | .inl o, inputs, state, res =>
            inst'.Step (.inl o) inputs state.1 ⟨res.1.1, res.2⟩
          | .inr f, inputs, state, res =>
            if h : f.val = i' then
              Prog.StepFn
                (inst := inst')
                fn
                (cast (by simp [← h, i'fin]; rfl) inputs)
                (cast (by simp [← h, i'fin]) state)
                (cast (by simp [← h, i'fin]; rfl) res)
            else
              inst'.Step (.inr ⟨↑f, by simp [i'fin]; omega⟩) inputs state.1 ⟨res.1.1, res.2⟩
      }
    ⟩

/-- Generates a transition relation for the `i`th function,
which depends on the `InterpOp` for the previous functions
generated by `Prog.AsInterpOp`. -/
def Prog.Step
  {Op : Type u₁} {χ : Type u₂}
  (V : Type u₃) (S : Type u₄)
  [Arity Op] [Arity (Fin k)]
  [InterpConsts V]
  [InterpOp Op V S]
  [DecidableEq χ]
  (prog : Prog Op χ k)
  (i : Fin k) :
  (S' : Type (max u₁ u₂ u₃ u₄)) ×
  (S → S') ×
  (
    Seq.Config (Op ⊕ Fin i) χ V S' (Arity.ι i) (Arity.ω i) →
    Seq.Config (Op ⊕ Fin i) χ V S' (Arity.ι i) (Arity.ω i) →
    Prop
  ) :=
  let ⟨S', init, _⟩ := prog.AsInterpOp V S i
  ⟨S', init, Seq.Config.Step⟩

def Prog.init
  {Op : Type u₁} {χ : Type u₂}
  (V : Type u₃) (S : Type u₄)
  [Arity Op] [Arity (Fin k)]
  [InterpConsts V]
  [InterpOp Op V S]
  [DecidableEq χ]
  (prog : Prog Op χ k)
  (i : Fin k)
  (state : S)
  (args : Vector V (Arity.ι i)) :
  (S' : Type (max u₁ u₂ u₃ u₄)) ×
  Seq.Config (Op ⊕ Fin i) χ V S' (Arity.ι i) (Arity.ω i) :=
  let ⟨S', init, _⟩ := prog.AsInterpOp V S i
  ⟨S', Seq.Config.init (prog i) (init state) args⟩

end Wavelet.Compile
