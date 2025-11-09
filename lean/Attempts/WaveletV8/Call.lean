import Wavelet.Op
import Wavelet.LTS
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

import Wavelet.Simulation

/-! Add (non-recursive) function calls by interpreting a function as an operator. -/

-- namespace Wavelet.Seq

-- open Op

-- /-- Interprets a function as an operator in the sequential semantics. -/
-- inductive Fn.OpStep
--   [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
--   (fn : Fn Op χ m n) (args : Vector V m) :
--   S × Option (Seq.Config Op χ V S m n) →
--   Trace E →
--   (S × Option (Seq.Config Op χ V S m n)) × Option (Vector V n) → Prop where
--   | step_fn_init :
--     Fn.OpStep fn args (state, none) .ε ((state, Seq.Config.init fn state args), none)
--   | step_fn_cont :
--     Seq.Config.Step { c with state } tr c' →
--     Fn.OpStep fn args (state, some c) tr ((c'.state, some c'), none)
--   | step_fn_ret :
--     c.expr = .ret retVals →
--     Fn.OpStep fn args (state, some c) .ε ((state, none), some retVals)

-- end Wavelet.Seq

-- namespace Wavelet.Dataflow

-- open Op Seq

-- /-- Interprets a process as an operator in the dataflow semantics. -/
-- inductive Proc.OpStep
--   [Arity Op] [InterpConsts V] [InterpOp Op V E S] [DecidableEq χ]
--   (proc : Proc Op (ChanName χ) V m n) (args : Vector V m) :
--   S × Option (Dataflow.Config Op (ChanName χ) V S m n) →
--   Trace E →
--   (S × Option (Dataflow.Config Op (ChanName χ) V S m n)) × Option (Vector V n) → Prop where
--   | step_proc_init :
--     Proc.OpStep proc args (state, none) .ε
--       ((state, some (Dataflow.Config.init proc state args)), none)
--   | step_proc_cont :
--     Dataflow.Config.Step { c with state } tr c' →
--     Proc.OpStep proc args (state, some c) tr ((c'.state, some c'), none)
--   | step_proc_ret :
--     c.chans.popVals ((Vector.range n).map ChanName.final_dest) = some (retVals, chans') →
--     Proc.OpStep proc args (state, some c)
--       .ε ((state, none), some retVals)

-- end Wavelet.Dataflow

-- namespace Wavelet.Seq

-- open Op

-- /-- Augments the operator set with an uninterpreted set of function names. -/
-- inductive WithFns Op (F : Type u) [Arity Op] where
--   | op (o : Op)
--   | call (f : F)

-- infixl:65 " w/ " => WithFns

-- abbrev WithFns.Interp Op F χ [Arity Op] [Arity F] :=
--   (f : F) → Fn Op χ (Arity.ι f) (Arity.ω f)

-- /-- States for the additional `k` functions. -/
-- structure WithFns.State
--   Op χ V E S
--   [Arity Op] [Arity F] [InterpConsts V]
--   [InterpOp Op V E S] [DecidableEq χ]
--   (fns : WithFns.Interp Op F χ) where
--   innerState : S
--   fnStates : (f : F) → Option (Config Op χ V S (Arity.ι f) (Arity.ω f))

-- instance [Arity Op] [Arity F] : Arity (WithFns Op F) where
--   ι | .op o => Arity.ι o
--     | .call f => Arity.ι f
--   ω | .op o => Arity.ω o
--     | .call f => Arity.ω f

-- /-- Instantiate the function names with a list of functions -/
-- inductive WithFns.Step
--   [Arity Op] [Arity F] [InterpConsts V]
--   [InterpOp Op V E S] [DecidableEq χ]
--   (fns : WithFns.Interp Op F χ) :
--   (op : WithFns Op F) →
--   Vector V (Arity.ι op) →
--   WithFns.State Op χ V E S fns →
--   Trace E →
--   WithFns.State Op χ V E S fns × Option (Vector V (Arity.ω op)) →
--   Prop where
--   | step_op :
--     InterpOp.Step o inputVals state.innerState tr (innerState', outputVals) →
--     WithFns.Step fns (.op o) inputVals state tr
--       ({ state with innerState := innerState' }, outputVals)
--   -- /-- Initialize call state without producing any outputs. -/
--   -- | step_call_init :
--   --   state.fnStates i = none →
--   --   WithFns.Step fns (.call i) inputVals
--   --     state
--   --     ({
--   --       state with
--   --       fnStates := state.fnStates.set i
--   --         (some (EncapConfig.init fns[i] state.innerState inputVals))
--   --     }, none)
--   -- | step_call_cont :
--   --   state.fnStates[i] = some ec →
--   --   Seq.Config.Step ec.config config' →
--   --   WithFns.Step fns (.call i) inputVals
--   --     state
--   --     ({ state with
--   --       fnStates := state.fnStates.set i (some { ec with config := config' })
--   --     }, none)
--   -- | step_call_ret :
--   --   state.fnStates[i] = some ec →
--   --   (_ : ec.ω = fns[i].ω) →
--   --   ec.config.expr = .ret retVals →
--   --   WithFns.Step fns (.call i) inputVals
--   --     state
--   --     (
--   --       { state with fnStates := state.fnStates.set i none },
--   --       some (cast (by congr) retVals),
--   --     )

-- instance
--   [Arity Op] [Arity F] [InterpConsts V]
--   [InterpOp Op V S] [DecidableEq χ]
--   (fns : WithFns.Interp Op F χ)
--   : InterpOp (WithFns Op F) V (WithFns.State Op χ V S fns) where
--   Step := WithFns.Step fns

-- end Wavelet.Seq

-- namespace Wavelet.Dataflow

-- open Op Seq

-- structure EncapProc Op χ V [Arity Op] where
--   ι : Nat
--   ω : Nat
--   proc : Proc Op χ V ι ω

-- structure EncapConfig Op χ V S [Arity Op] where
--   ι : Nat
--   ω : Nat
--   config : Dataflow.Config Op χ V S ι ω

-- def EncapConfig.init {Op χ V S}
--   [Arity Op]
--   [InterpConsts V]
--   [InterpOp Op V S]
--   [DecidableEq χ]
--   (ef : EncapProc Op χ V)
--   (state : S)
--   (args : Vector V ef.ι) :
--   EncapConfig Op χ V S :=
--   ⟨ef.ι, ef.ω, Dataflow.Config.init ef.proc state args⟩

-- /-- Augments the operator set with a vector of custom processes. -/
-- inductive WithProcs Op [Arity Op] {χ V k} (procs : Vector (EncapProc Op χ V) k) where
--   | op (o : Op)
--   | proc (k : Fin k)

-- infixl:65 " w/ " => WithProcs

-- structure WithProcs.State
--   Op χ V S
--   [Arity Op] [InterpConsts V]
--   [InterpOp Op V E S] [DecidableEq χ]
--   (fns : Vector (EncapProc Op χ V) k) where
--   innerState : S
--   procStates : Vector (Option (EncapConfig Op χ V S)) k

-- instance
--   [Arity Op]
--   {procs : Vector (EncapProc Op χ V) k} : Arity (WithProcs Op procs) where
--   ι | .op o => Arity.ι o
--     | .proc i => procs[i].ι
--   ω | .op o => Arity.ω o
--     | .proc i => procs[i].ω

-- inductive WithProcs.Step
--   [Arity Op] [InterpConsts V]
--   [InterpOp Op V S] [DecidableEq χ]
--   (procs : Vector (EncapProc Op χ V) k) :
--   (op : WithProcs Op procs) →
--   Vector V (Arity.ι op) →
--   WithProcs.State Op χ V S procs →
--   WithProcs.State Op χ V S procs × Option (Vector V (Arity.ω op)) →
--   Prop where
--   | step_op :
--     InterpOp.Step o inputVals state.innerState (innerState', outputVals) →
--     WithProcs.Step procs (.op o) inputVals state
--       ({ state with innerState := innerState' }, outputVals)
--   | step_proc_init :
--     state.procStates[i] = none →
--     WithProcs.Step procs (.proc i) inputVals
--       state
--       ({
--         state with
--         procStates := state.procStates.set i
--           (some (EncapConfig.init procs[i] state.innerState inputVals))
--       }, none)
--   | step_proc_cont :
--     state.procStates[i] = some pc →
--     Dataflow.Config.Step pc.config config' →
--     WithProcs.Step procs (.proc i) inputVals
--       state
--       ({ state with
--         procStates := state.procStates.set i (some { pc with config := config' })
--       }, none)
--   | step_proc_ret :
--     state.procStates[i] = some pc →
--     pc.config.chans.popVals procs[i].proc.outputs = some (retVals, chans') →
--     WithProcs.Step procs (.proc i) inputVals
--       state
--       (
--         { state with procStates := state.procStates.set i none },
--         some retVals,
--       )

-- end Wavelet.Dataflow

namespace Wavelet.Compile

open Op LTS Seq Dataflow
open Simulation Simulation.Defs

structure Sig where
  ι : Nat
  ω : Nat

/-- Operators ⊕ first `k'` signatures in `sigs` -/
inductive WithSigs Op (sigs : Vector Sig k) (k' : Fin k) where
  | op (o : Op)
  | call (i : Fin k')

instance [Arity Op] {sigs : Vector Sig k} : Arity (WithSigs Op sigs k') where
  ι | .op o => Arity.ι o
    | .call i => sigs[i].ι
  ω | .op o => Arity.ω o
    | .call i => sigs[i].ω

-- /-- Lifts an interpretation across different universe for the state type. -/
-- instance instOpULift [Arity Op] [InterpOp Op V E S] : InterpOp Op V E (ULift S) where
--   Step o inputs state tr res := InterpOp.Step o inputs state.down tr ⟨res.1.down, res.2⟩

-- instance instOpSumFin0 [Arity Op] [inst : InterpOp Op V E S] : InterpOp (Op ⊕ Fin 0) V E S where
--   Step
--     | .inl o, inputs, state, tr, res =>
--       InterpOp.Step o inputs state tr res
--     | .inr f, _, _, _, _ => Fin.elim0 f

abbrev Prog (Op : Type u) χ {k} [Arity Op] (sigs : Vector Sig k) :=
  (i : Fin k) → Fn (WithSigs Op sigs i) χ sigs[i].ι sigs[i].ω

abbrev exampleSigs : Vector Sig 2 :=
  #v[
    { ι := 2, ω := 1 },
    { ι := 3, ω := 2 },
  ]

example [Arity Op] : Prog (sigs := exampleSigs) Op String
  | 0 =>
    {
      params := #v["a", "b"],
      body := .ret #v["a"],
    }
  | 1 =>
    {
      params := #v["a", "b", "c"],
      body :=
        -- let d = call 0 (b, c)
        -- return (a, d)
        .op (.call ⟨0, by omega⟩)
          (cast (by rfl) #v["b", "c"])
          (cast (by rfl) #v["d"])
          (.ret #v["a", "d"]),
    }

/-- Channel name prefixes to disambiguate names during linking. -/
inductive LinkName (χ : Type u) where
  | base (name : χ)
  | main (name : LinkName χ)
  | dep (i : Nat) (name : LinkName χ)

/-- TODO: should be auto-derived -/
instance [inst : DecidableEq χ] : DecidableEq (LinkName χ) := sorry

def linkAtomicProc
  [Arity Op]
  (sigs : Vector Sig k)
  (k' : Fin k)
  (procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω)
  (idx : Nat) -- Index of the atomic proc
  (atom : AtomicProc (WithSigs Op sigs k') (LinkName χ) V) : AtomicProcs Op (LinkName χ) V :=
  match atom with
  | .op (.op o) inputs outputs =>
    [.op o (inputs.map .main) (outputs.map .main)]
  | .op (.call i) inputs outputs =>
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
  [Arity Op]
  (sigs : Vector Sig k)
  (k' : Fin k)
  (procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω)
  (main : Proc (WithSigs Op sigs k') (LinkName χ) V m n)
  : Proc Op (LinkName χ) V m n := {
    inputs := main.inputs.map LinkName.main,
    outputs := main.outputs.map LinkName.main,
    atoms := (main.atoms.mapIdx (linkAtomicProc sigs k' procs)).flatten,
  }

/-- Given a program (a list of functions that non-recursively call each other),
compile the `i`-th function to a process without any dependencies. -/
def compileProg
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (sigs : Vector Sig k)
  (prog : Prog Op χ sigs)
  (hnz : ∀ i : Fin k, sigs[i].ι > 0 ∧ sigs[i].ω > 0)
  (i : Fin k) : Proc Op (LinkName (ChanName χ)) V sigs[i].ι sigs[i].ω :=
  -- Compile the current function
  let proc : Proc (WithSigs Op sigs i) (LinkName (ChanName χ)) V _ _ :=
    compileFn (by apply hnz) (prog i) |>.mapChans LinkName.base
  -- Compile dependencies
  let deps : (j : Fin i) → Proc Op (LinkName (ChanName χ)) V sigs[j].ι sigs[j].ω :=
    λ j => compileProg sigs prog hnz (j.castLT (by omega))
  -- Link everything into one dataflow graph
  linkProcs sigs i deps proc

inductive Prog.StepFn
  [Arity Op] [InterpConsts V]
  [inst : InterpOp Op V E S] [DecidableEq χ] :
  (fn : Fn Op χ m n) →
  Vector V m →
  S × Option (Seq.Config Op χ V S m n) →
  Trace E →
  (S × Option (Seq.Config Op χ V S m n)) × Option (Vector V n) →
  Prop where
  | step_fn_init :
    Prog.StepFn fn args (state, none) .ε ((state, some (Seq.Config.init fn state args)), none)
  | step_fn_cont :
    Seq.Config.Step { c with state } tr c' →
    Prog.StepFn fn args (state, some c) tr ((c'.state, some c'), none)
  | step_fn_ret :
    c.expr = .ret retVals →
    Prog.StepFn fn args (state, some c) .ε ((state, none), some retVals)

/--
State type for interpreting the first `i` functions as operators.

It's essentially a stack of configurations, but formulated in a
way that can be directly used with the existing stepping relation.
-/
abbrev Prog.InterpStack
  (Op : Type u₁) (χ : Type u₂) (V : Type u₃) (S : Type u₄)
  [Arity Op]
  (sigs : Vector Sig k)
  : Fin k → Type (max u₁ u₂ u₃ u₄)
  | ⟨0, _⟩ => ULift S
  | ⟨i + 1, _⟩ =>
    let i' : Fin k := ⟨i, by omega⟩
    let S' := InterpStack Op χ V S sigs i'
    S' × Option (Seq.Config (WithSigs Op sigs i') χ V S' sigs[i'].ι sigs[i'].ω)

theorem Prog.InterpStack.unfold0
  (Op : Type u₁) (χ : Type u₂) (V : Type u₃) (S : Type u₄)
  [Arity Op]
  {sigs : Vector Sig k}
  : Prog.InterpStack Op χ V S sigs ⟨0, hnz⟩ = ULift S
  := by rfl

def Prog.InterpStack.inj
  [Arity Op]
  {sigs : Vector Sig k}
  (s : S)
  : {i : Fin k} → Prog.InterpStack Op χ V S sigs i
  | ⟨0, _⟩ => ULift.up s
  | ⟨_ + 1, _⟩ => (inj s, none)

/-- Extracts the current state from the stack. -/
def Prog.InterpStack.base
  [Arity Op]
  {sigs : Vector Sig k}
  {i : Fin k}
  (stack : Prog.InterpStack Op χ V S sigs i) : S
  := match i with
    | ⟨0, _⟩ => stack.down
    | ⟨_ + 1, _⟩ => InterpStack.base stack.1

instance Prog.instFnAsOp0
  [Arity Op] [InterpConsts V]
  [baseInst : InterpOp Op V E S]
  : InterpOp
    (WithSigs Op sigs ⟨0, hnz⟩) V E
    (Prog.InterpStack Op χ V S sigs ⟨0, hnz⟩)
  := {
    Step
      | .op o, inputs, state, tr, res =>
        baseInst.Step o inputs state.base tr ⟨res.1.base, res.2⟩
      | .call f, _, _, _, _ => Fin.elim0 f
  }

/-- Generate an `InterpOp` of the first `i` functions over `Prog.InterpStack`. -/
instance Prog.instFnAsOp
  {Op χ V S}
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [baseInst : InterpOp Op V E S]
  {sigs : Vector Sig k}
  (prog : Prog Op χ sigs)
  (i : Fin k)
  : InterpOp (WithSigs Op sigs i) V E (Prog.InterpStack Op χ V S sigs i)
  := match i with
  | ⟨0, _⟩ => instFnAsOp0
  | ⟨i + 1, _⟩ =>
    let i' : Fin k := ⟨i, by omega⟩
    let inst := instFnAsOp prog i'
    {
      Step
        -- Operators in `Op` are interpreted in the original semantics (`baseInst`).
        | .op o, inputs, state, tr, res =>
          inst.Step (.op o) inputs state.1 tr ⟨res.1.1, res.2⟩
        -- Function calls are either interpreted by the IH `inst`
        -- or by the current function `prog i'`.
        | .call f, inputs, state, tr, res =>
          if h₁ : i = f.val then
            have h₂ : instArityWithSigs.ω (WithSigs.call f) = sigs[i'].ω
              := by simp [i', h₁]; rfl
            Prog.StepFn
              (inst := inst)
              (prog i')
              (cast (by simp [i', h₁]; rfl) inputs)
              (cast (by simp [i']; rfl) state)
              tr
              (cast (by simp [i']; rw [h₂]; rfl) res)
          else
            inst.Step (.call ⟨↑f, by simp [i']; omega⟩) inputs state.1 tr ⟨res.1.1, res.2⟩
    }

/-- Generates a transition relation for the `i`th function,
which depends on the `InterpOp` for the previous functions
generated by `Prog.AsInterpOp`. -/
def Prog.Step
  {Op χ} (V S)
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  (sigs : Vector Sig k)
  (prog : Prog Op χ sigs)
  (i : Fin k) :
  (
    Seq.Config (WithSigs Op sigs i) χ V (Prog.InterpStack Op χ V S sigs i) sigs[i].ι sigs[i].ω →
    Trace E →
    Seq.Config (WithSigs Op sigs i) χ V (Prog.InterpStack Op χ V S sigs i) sigs[i].ι sigs[i].ω →
    Prop
  ) := Seq.Config.Step (interp := Prog.instFnAsOp prog i)

def Prog.init
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  (sigs : Vector Sig k)
  (prog : Prog Op χ sigs) (i : Fin k)
  (state : S)
  (args : Vector V sigs[i].ι) :
  Seq.Config (WithSigs Op sigs i) χ V (Prog.InterpStack Op χ V S sigs i) sigs[i].ι sigs[i].ω :=
  Seq.Config.init (prog i) (.inj state) args

instance [Arity Op] {i : Fin k}
  : GetState (Seq.Config (WithSigs Op sigs i) χ V (Prog.InterpStack Op χ V S sigs i) sigs[i].ι sigs[i].ω) S where
  getState config := config.state.base

abbrev Proc.InterpStack
  (Op : Type u₁) (χ : Type u₂) (V : Type u₃) (S : Type u₄)
  [Arity Op]
  (sigs : Vector Sig k)
  : Fin k → Type (max u₁ u₂ u₃ u₄)
  | ⟨0, _⟩ => ULift S
  | ⟨i + 1, _⟩ =>
    let i' : Fin k := ⟨i, by omega⟩
    let S' := InterpStack Op χ V S sigs i'
    S' × Option (Dataflow.Config (WithSigs Op sigs i') χ V S' sigs[i'].ι sigs[i'].ω)

def Proc.InterpStack.inj
  [Arity Op]
  {sigs : Vector Sig k}
  (s : S)
  : {i : Fin k} → Proc.InterpStack Op χ V S sigs i
  | ⟨0, _⟩ => ULift.up s
  | ⟨_ + 1, _⟩ => (inj s, none)

/-- Extracts the current state from the stack. -/
def Proc.InterpStack.base
  [Arity Op]
  {sigs : Vector Sig k}
  {i : Fin k}
  (stack : InterpStack Op χ V S sigs i) : S
  := match i with
    | ⟨0, _⟩ => stack.down
    | ⟨_ + 1, _⟩ => InterpStack.base stack.1

instance Proc.instFnAsOp0
  [Arity Op] [InterpConsts V]
  [baseInst : InterpOp Op V E S]
  : InterpOp
    (WithSigs Op sigs ⟨0, hnz⟩) V E
    (InterpStack Op χ V S sigs ⟨0, hnz⟩)
  := {
    Step
      | .op o, inputs, state, tr, res =>
        baseInst.Step o inputs state.base tr ⟨res.1.base, res.2⟩
      | .call f, _, _, _, _ => Fin.elim0 f
  }

inductive Proc.StepProc
  [Arity Op] [InterpConsts V]
  [inst : InterpOp Op V E S] [DecidableEq χ]
  (proc : Proc Op χ V m n) :
  Vector V m →
  S × Option (Dataflow.Config Op χ V S m n) →
  Trace E →
  (S × Option (Dataflow.Config Op χ V S m n)) × Option (Vector V n) →
  Prop where
  | step_proc_init :
    StepProc proc args (state, none) .ε
      ((state, some (Dataflow.Config.init proc state args)), none)
  | step_proc_cont :
    Dataflow.Config.Step { c with state } tr c' →
    StepProc proc args (state, some c) tr ((c'.state, some c'), none)
  | step_proc_ret :
    c.chans.popVals proc.outputs = some (outputVals, chans') →
    StepProc proc args (state, some c) .ε ((state, none), some outputVals)

instance Proc.instProcAsOp
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  [baseInst : InterpOp Op V E S]
  {sigs : Vector Sig k}
  (procs : (i : Fin k) → Proc (WithSigs Op sigs i) χ V sigs[i].ι sigs[i].ω)
  (i : Fin k)
  : InterpOp (WithSigs Op sigs i) V E (InterpStack Op χ V S sigs i)
  := match i with
  | ⟨0, _⟩ => instFnAsOp0
  | ⟨i + 1, _⟩ =>
    let i' : Fin k := ⟨i, by omega⟩
    let inst := instProcAsOp procs i'
    {
      Step
        -- Operators in `Op` are interpreted in the original semantics (`baseInst`).
        | .op o, inputs, state, tr, res =>
          inst.Step (.op o) inputs state.1 tr ⟨res.1.1, res.2⟩
        -- Function calls are either interpreted by the IH `inst`
        -- or by the current function `prog i'`.
        | .call f, inputs, state, tr, res =>
          if h₁ : i = f.val then
            have h₂ : instArityWithSigs.ω (WithSigs.call f) = sigs[i'].ω
              := by simp [i', h₁]; rfl
            Proc.StepProc
              (inst := inst)
              (procs i')
              (cast (by simp [i', h₁]; rfl) inputs)
              (cast (by simp [i']; rfl) state)
              tr
              (cast (by simp [i']; rw [h₂]; rfl) res)
          else
            inst.Step (.call ⟨↑f, by simp [i']; omega⟩) inputs state.1 tr ⟨res.1.1, res.2⟩
    }

/-- Converts a simulation result with initial setup steps to a simulation. -/
theorem sim_with_init_to_sim
  (c₁ : C₁) (c₂ : C₂)
  (Step₁ : LTS C₁ E)
  (Step₂ : LTS C₂ E)
  [LTS.Transitive Step₂]
  (R : C₁ → C₂ → Prop)
  (hsim_init : ∃ c₂', Step₂ c₂ .ε c₂' ∧ Simulation c₁ c₂' R Step₁ Step₂)
  : Simulation c₁ c₂ (λ a b => (a = c₁ ∧ b = c₂) ∨ R a b) Step₁ Step₂
  := by
  have ⟨c₂', hstep_c₂, hsim⟩ := hsim_init
  constructor
  · simp
  · intros d₁ d₂ d₁' tr hr hstep
    cases hr with
    | inl hr =>
      simp [hr] at hstep ⊢
      have ⟨d₂', hstep_c₂', hr⟩ := hsim.coind c₁ c₂' d₁' tr (hsim.base) hstep
      exists d₂'
      constructor
      · have := LTS.Transitive.trans hstep_c₂ hstep_c₂'
        simp at this
        exact this
      · simp [hr]
    | inr hr =>
      have ⟨d₂', hstep_d₂, hr⟩ := hsim.coind d₁ d₂ d₁' tr hr hstep
      exists d₂'
      constructor
      · exact hstep_d₂
      · right
        exact hr

theorem sim_trans
  {c₁ : C₁} {c₂ : C₂} {c₃ : C₃}
  {Step₁ : LTS C₁ E}
  {Step₂ : LTS C₂ E}
  {Step₃ : LTS C₃ E}
  (R₁₂ : C₁ → C₂ → Prop)
  (R₂₃ : C₂ → C₃ → Prop)
  (hsim₁₂ : Simulation c₁ c₂ R₁₂ Step₁ Step₂)
  (hsim₂₃ : Simulation c₂ c₃ R₂₃ Step₂ Step₃)
  : Simulation c₁ c₃ (Relation.Comp R₁₂ R₂₃) Step₁ Step₃
  := sorry

theorem similarity_trans
  {c₁ : C₁} {c₂ : C₂} {c₃ : C₃}
  {Step₁ : LTS C₁ E}
  {Step₂ : LTS C₂ E}
  {Step₃ : LTS C₃ E}
  (hsim₁₂ : ∃ R, Simulation c₁ c₂ R Step₁ Step₂)
  (hsim₂₃ : ∃ R, Simulation c₂ c₃ R Step₂ Step₃)
  : ∃ R, Simulation c₁ c₃ R Step₁ Step₃
  := sorry

def Expr.castWithSigs0
  [Arity Op]
  {sigs : Vector Sig k}
  {hnz : 0 < k} :
  Expr (WithSigs Op sigs ⟨0, hnz⟩) χ m n → Expr Op χ m n
  | .ret vars => .ret vars
  | .tail vars => .tail vars
  | .op (.op o) inputs outputs cont =>
    .op o inputs outputs (castWithSigs0 cont)
  | .op (.call f) .. => Fin.elim0 f
  | .br cond left right => .br cond (castWithSigs0 left) (castWithSigs0 right)

def Fn.castWithSigs0
  [Arity Op]
  {sigs : Vector Sig k}
  {hnz : 0 < k}
  (fn : Fn (WithSigs Op sigs ⟨0, hnz⟩) χ m n) :
  Fn Op χ m n := {
    params := fn.params,
    body := Expr.castWithSigs0 fn.body,
  }

def AtomicProc.castWithSigs0
  [Arity Op]
  {sigs : Vector Sig k}
  {hnz : 0 < k}
  : AtomicProc (WithSigs Op sigs ⟨0, hnz⟩) χ V → AtomicProc Op χ V
  | _ => sorry

def Proc.castWithSigs0
  [Arity Op]
  {sigs : Vector Sig k}
  {hnz : 0 < k}
  (proc : Proc (WithSigs Op sigs ⟨0, hnz⟩) χ V m n)
  : Proc Op χ V m n := {
    inputs := proc.inputs,
    outputs := proc.outputs,
    atoms := proc.atoms.map (AtomicProc.castWithSigs0),
  }

theorem lemma₀
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  {sigs : Vector Sig k}
  {hz : 0 < k}
  (fn : Fn (WithSigs Op sigs ⟨0, hz⟩) χ m n) :
  ∃ R,
    Simulation (E := E)
      -- (Seq.Config.init fn { down := state : ULift S} args)
      (Seq.Config.init fn (Prog.InterpStack.inj state) args)
      (Seq.Config.init (Fn.castWithSigs0 fn) state args)
      R
      (Seq.Config.Step (interp := Prog.instFnAsOp0 (χ := χ)))
      (Seq.Config.Step (V := V) (S := S))
  := sorry

theorem cast_sigs0_preserves_wf
  [Arity Op]
  [DecidableEq χ]
  {fn : Fn (WithSigs Op sigs ⟨0, hnz⟩) χ m n}
  (h : fn.WellFormed) :
  (Fn.castWithSigs0 fn).WellFormed := sorry

theorem sim_compile_fn'
  [Arity Op] [InterpConsts V]
  [interp : InterpOp Op V E S] [DecidableEq χ]
  (fn : Fn Op χ m n)
  (hnz : m > 0 ∧ n > 0)
  (hwf : fn.WellFormed)
  : ∃ R,
    Simulation (E := E)
      (Seq.Config.init fn state args)
      (Dataflow.Config.init (compileFn hnz fn) state args)
      R
      (Seq.Config.Step (V := V) (S := S))
      Dataflow.Config.StepPlus
  := by
  constructor
  apply sim_with_init_to_sim
  apply sim_compile_fn fn args state hnz
  apply hwf

theorem lemma₁
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  {sigs : Vector Sig k}
  {hz : 0 < k}
  (fn : Fn (WithSigs Op sigs ⟨0, hz⟩) χ m n)
  (hnz : m > 0 ∧ n > 0)
  (hwf : fn.WellFormed) :
  ∃ R,
    Simulation (E := E)
      -- (Seq.Config.init fn { down := state : ULift S} args)
      (Seq.Config.init (Fn.castWithSigs0 fn) state args)
      (Dataflow.Config.init (compileFn hnz (Fn.castWithSigs0 fn)) state args)
      R
      (Seq.Config.Step (V := V) (S := S))
      Dataflow.Config.StepPlus
  := by apply sim_compile_fn' _ hnz (cast_sigs0_preserves_wf hwf)

theorem compile_prog_0
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (sigs : Vector Sig k)
  (prog : Prog Op χ sigs)
  {hz : 0 < k}
  (hnz : ∀ (i : Fin k), sigs[i].ι > 0 ∧ sigs[i].ω > 0) :
  compileProg sigs prog hnz ⟨0, hz⟩
    = (compileFn (V := V) (by apply hnz) (Fn.castWithSigs0 (prog ⟨0, hz⟩))).mapChans
      (LinkName.main ∘ LinkName.base)
  := sorry

theorem sim_dataflow_chan_inj
  {χ₁ χ₂ : Type u}
  [Arity Op]
  [InterpConsts V]
  [interp : InterpOp Op V E S]
  [DecidableEq χ₁]
  [DecidableEq χ₂]
  {proc : Proc Op χ₁ V m n}
  (r : χ₁ → χ₂)
  (hinj : Function.Injective r)
  : ∃ R,
    Simulation (E := E)
      (Dataflow.Config.init proc state args)
      (Dataflow.Config.init (proc.mapChans r) state args)
      R
      (Dataflow.Config.StepPlus (S := S))
      Dataflow.Config.StepPlus
  := sorry

/-- Defines when two `InterpOp`s form a simulation. -/
abbrev InterpOpSimulation
  [Arity Op]
  (R : S₁ → S₂ → Prop)
  (s₁ : S₁) (s₂ : S₂)
  (interp₁ : InterpOp Op V E S₁)
  (interp₂ : InterpOp Op V E S₂)
  : Prop :=
  R s₁ s₂ ∧
  ∀ o inputs s₁ s₂ s₁' tr res,
    R s₁ s₂ →
    interp₁.Step o inputs s₁ tr (s₁', res) →
    ∃ s₂' ,
      interp₂.Step o inputs s₂ tr (s₂', res) ∧
      R s₁' s₂'

theorem sim_interp_to_sim_proc
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (proc : Proc Op χ V m n)
  (state₁ : S₁) (state₂ : S₂)
  (interp₁ : InterpOp Op V E S₁)
  (interp₂ : InterpOp Op V E S₂)
  (hsim : ∃ R, InterpOpSimulation R state₁ state₂ interp₁ interp₂) :
  ∃ R,
    Simulation (E := E)
      (Dataflow.Config.init proc state₁ args)
      (Dataflow.Config.init proc state₂ args)
      R
      (Dataflow.Config.StepPlus (S := S₁))
      (Dataflow.Config.StepPlus (S := S₂))
  := sorry

theorem sim_interp_to_sim_fn
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (fn : Fn Op χ m n)
  (state₁ : S₁) (state₂ : S₂)
  (interp₁ : InterpOp Op V E S₁)
  (interp₂ : InterpOp Op V E S₂)
  (hsim : ∃ R, InterpOpSimulation R state₁ state₂ interp₁ interp₂) :
  ∃ R,
    Simulation (E := E)
      (Seq.Config.init fn state₁ args)
      (Seq.Config.init fn state₂ args)
      R
      (Seq.Config.StepPlus (V := V) (S := S₁))
      (Seq.Config.StepPlus (V := V) (S := S₂))
  := sorry

theorem sim_interp_fn_to_proc
  [Arity Op] [DecidableEq χ₁] [DecidableEq χ₂] [InterpConsts V]
  [InterpOp Op V E S]
  {sigs : Vector Sig k}
  (init : S)
  (prog : Prog Op χ₁ sigs)
  (procs : (i : Fin k) → Proc (WithSigs Op sigs i) χ₂ V sigs[i].ι sigs[i].ω)
  (i : Fin k)
  (hsim : ∀ i args,
    ∃ R, Simulation (E := E)
      (Seq.Config.init (prog i) (.inj init) args)
      (Dataflow.Config.init (procs i) (.inj init) args)
      R
      (Seq.Config.Step (interp := Prog.instFnAsOp prog i))
      (Dataflow.Config.StepPlus (interp := Proc.instProcAsOp procs i))) :
  ∃ R, InterpOpSimulation (E := E) R
    (.inj init) (.inj init)
    (Prog.instFnAsOp prog i)
    (Proc.instProcAsOp procs i)
:= sorry

/-- TODO: need to strengthen to SPSimulation. -/
theorem really?
  -- {Op : Type u₁} {χ : Type u₂} {V : Type u₃} {S : Type u₄}
  [Arity Op]
  [InterpConsts V]
  [baseInst : InterpOp Op V E S]
  [DecidableEq χ]
  (sigs : Vector Sig k)
  (prog : Prog Op χ sigs)
  (i : Fin k)
  (state : S)
  (args : Vector V sigs[i].ι)
  (hnz : ∀ (i : Fin k), sigs[i].ι > 0 ∧ sigs[i].ω > 0)
  (hwf : ∀ i, (prog i).WellFormed) :
  ∃ R,
    Simulation
      (Prog.init (E := E) sigs prog i state args)
      (Dataflow.Config.init (compileProg sigs prog hnz i) state args)
      R
      (Prog.Step V S sigs prog i)
      (Dataflow.Config.StepPlus (E := E))
  := by
  have ⟨i', hi⟩ := i
  induction i' with
  | zero =>
    simp [Prog.init, Prog.Step, Prog.instFnAsOp]
    simp [compile_prog_0]
    generalize hfn : prog ⟨0, hi⟩ = fn
    have hwf : fn.WellFormed := by simp [← hfn]; apply hwf
    apply similarity_trans (lemma₀ fn)
    apply similarity_trans (lemma₁ fn (by apply hnz) hwf)
    apply sim_dataflow_chan_inj
    simp [Function.Injective]
  | succ i'' =>
    unfold compileProg
    simp [Prog.init, Prog.Step]
    generalize hfn : prog ⟨i'' + 1, hi⟩ = fn
    apply similarity_trans (sim_compile_fn'
      (interp := Prog.instFnAsOp prog ⟨i'' + 1, hi⟩)
      fn
      (by apply hnz ⟨i'' + 1, hi⟩)
      (by simp [← hfn]; apply hwf))
    simp
    apply similarity_trans (sim_dataflow_chan_inj
      (interp := Prog.instFnAsOp prog ⟨i'' + 1, hi⟩)
      LinkName.base (by simp [Function.Injective]))
    apply similarity_trans
    · apply sim_interp_to_sim_proc
        _
        (Prog.InterpStack.inj state)
        (Proc.InterpStack.inj state)
        (Prog.instFnAsOp (S := S) (E := E) (sigs := sigs) (baseInst := baseInst) prog ⟨i'' + 1, hi⟩)
        (Proc.instProcAsOp (S := S) (E := E) (sigs := sigs) (baseInst := baseInst)
          (λ j : Fin k => (compileFn (by apply hnz) (prog j)).mapChans LinkName.base)
          ⟨i'' + 1, hi⟩)
      apply sim_interp_fn_to_proc (V := V)
        (sigs := sigs)
        state prog _
        ⟨i'' + 1, hi⟩
        (by
          intros i args
          apply similarity_trans
          · apply sim_compile_fn' (interp := Prog.instFnAsOp prog i) _
              (by apply hnz)
              (by apply hwf)
          ·
            sorry)
    sorry

end Wavelet.Compile

namespace Wavelet.Op

instance [Arity Op₁] [Arity Op₂] : Arity (Op₁ ⊕ Op₂) where
  ι | .inl o => Arity.ι o
    | .inr o => Arity.ι o
  ω | .inl o => Arity.ω o
    | .inr o => Arity.ω o

def InterpTransformer Op Op' V E S S' [Arity Op] [Arity Op'] :=
  InterpOp Op V E S →
  InterpOp (Op ⊕ Op') V E (S × S')

end Wavelet.Op

/-
Plan:

More flattened structure:

Program := (i : Fin k) → Fn (WithSigs Op sigs) χ sigs[i].ι sigs[i].ω

==> compiled to (i : Fin k) → Proc (WithSigs Op sigs) χ V sigs[i].ι sigs[i].ω

Linking at the program level:
  Configuration: {
    stack : List Seq.Config (encap m and n?)
  }

Linking at the proc level:
  Configuration: {
    stack : List Dataflow.Config (encap m and n?)
  }

-/

-- /-! Version 2... -/
-- namespace Wavelet.Compile

-- open Op Seq Dataflow

-- -- structure EncapFn Op [Arity Op] χ where
-- --   Op' : Type u
-- --   instArity : Arity Op'
-- --   m : Nat
-- --   n : Nat
-- --   fn : Fn (Op ⊕ Op') χ m n

-- -- abbrev EncapFns Op [Arity Op] χ k := Vector (EncapFn Op χ) k

-- -- inductive WithFns Op [Arity Op] (fns : EncapFns Op χ k) where
-- --   | op (o : Op) : WithFns Op fns
-- --   | call (i : Fin k) : WithFns Op fns

-- -- instance [Arity Op] {fns : EncapFns Op χ k} : Arity (WithFns Op fns) where
-- --   ι | .op o => Arity.ι o
-- --     | .call i => fns[i].m
-- --   ω | .op o => Arity.ω o
-- --     | .call i => fns[i].n

-- -- abbrev Prog' Op [Arity Op] χ m n :=
-- --   (k : Nat) × (fns : EncapFns Op χ k) × Fn (WithFns Op fns) χ m n

-- structure EncapFn Op [Arity Op] χ V E S where
--   Op' : Type u
--   instArity : Arity Op'
--   instInterp : InterpOp Op' V E S
--   m : Nat
--   n : Nat
--   fn : Fn (Op ⊕ Op') χ m n

-- inductive EncapFns (Op : Type u) (χ : Type v) [Arity Op] : Nat → Type (max u v) where
--   | leaf m n : Fn Op χ m n → EncapFns Op χ 1
--   | par_cons m n : EncapFns Op χ k → Fn Op χ m n → EncapFns Op χ (k + 1)
--   | dep_cons :
--       (fns : EncapFns Op χ k) →
--       (m n : Nat) →
--       (fn : Fn sorry χ m n) →
--       EncapFns Op χ 1

-- end Wavelet.Compile

-- namespace Wavelet.Op

-- inductive Empty

-- def Empty.elim {α} (e : Empty) : α := by cases e

-- instance : Arity Empty where
--   ι e := e.elim
--   ω e := e.elim

-- /-- TODO: We can maybe unify `Yield` and `Step` into one LTS
-- with three types of labels:
-- - yield
-- - output
-- - silent -/
-- class Semantics Op V E [Arity Op] m n where
--   S : Type*
--   init : Vector V m → S
--   Yield : S → (op : Op) → Vector V (Arity.ι op) → Vector V (Arity.ω op) → S → Prop
--   Step : S → Trace E → S → Option (Vector V n) → Prop
--   IsYield s op inputs := ∃ outputs s', Yield s op inputs outputs s'

-- structure Semantics.Simulates
--   [Arity Op]
--   (sem₁ sem₂ : Semantics Op V E m n)
--   (R : sem₁.S → sem₂.S → Prop) : Prop where
--   init : ∀ args, R (sem₁.init args) (sem₂.init args)
--   sim_yield : ∀ s₁ s₂ op inputs outputs s₁',
--     R s₁ s₂ →
--     sem₁.Yield s₁ op inputs outputs s₁' →
--     ∃ s₂' ,
--       sem₂.Yield s₂ op inputs outputs s₂' ∧
--       R s₁' s₂'
--   sim_step : ∀ s₁ s₂ tr s₁' retVals,
--     R s₁ s₂ →
--     sem₁.Step s₁ tr s₁' retVals →
--     ∃ s₂' ,
--       sem₂.Step s₂ tr s₂' retVals ∧
--       R s₁' s₂'

-- abbrev PartInterp Op₀ Op V E [Arity Op₀] [Arity Op] :=
--   (op : Op) → Semantics Op₀ V E (Arity.ι op) (Arity.ω op)

-- abbrev FullInterp Op V E [Arity Op] := PartInterp Empty Op V E

-- structure LinkState
--   [Arity Op₀] [Arity Op₁]
--   [DecidableEq Op₁]
--   (deps : PartInterp Op₀ Op₁ V E)
--   (main : Semantics (Op₀ ⊕ Op₁) V E m n) where
--   mainState : main.S
--   depStates : (op : Op₁) → Option (deps op).S

-- def LinkState.init
--   [Arity Op₀] [Arity Op₁]
--   [DecidableEq Op₁]
--   {deps : PartInterp Op₀ Op₁ V E}
--   {main : Semantics (Op₀ ⊕ Op₁) V E m n}
--   (args : Vector V m) : LinkState deps main := {
--     mainState := main.init args,
--     depStates := λ _ => none,
--   }

-- inductive LinkYield
--   [Arity Op₀] [Arity Op₁]
--   [DecidableEq Op₁]
--   (deps : PartInterp Op₀ Op₁ V E)
--   (main : Semantics (Op₀ ⊕ Op₁) V E m n)
--   : LinkState deps main →
--     (op : Op₀) → Vector V (Arity.ι op) → Vector V (Arity.ω op) →
--     LinkState deps main → Prop where
--   /-- Main semantics making a yield -/
--   | yield_main :
--     main.Yield s.mainState (.inl op) inputs outputs mainState' →
--     LinkYield deps main s op inputs outputs { s with mainState := mainState' }
--   /-- One of the dependencies making a yield -/
--   | yield_dep {depState depState' : (deps depOp).S} :
--     s.depStates depOp = some depState →
--     (deps depOp).Yield depState op inputs outputs depState' →
--     LinkYield deps main s op inputs outputs
--       { s with depStates := Function.update s.depStates depOp (some depState') }

-- inductive LinkStep
--   [Arity Op₀] [Arity Op₁]
--   [DecidableEq Op₁]
--   (deps : PartInterp Op₀ Op₁ V E)
--   (main : Semantics (Op₀ ⊕ Op₁) V E m n)
--   : LinkState deps main →
--     Trace E →
--     LinkState deps main →
--     Option (Vector V n) →
--     Prop where
--   /-- Main semantics making a step -/
--   | step_main :
--     main.Step s.mainState tr mainState' retVals →
--     LinkStep deps main s tr { s with mainState := mainState' } retVals
--   /-- Main semantics yielding to a dependency -/
--   | step_yield_to_dep {depState : (deps depOp).S} :
--     main.IsYield s.mainState (.inr depOp) inputVals →
--     s.depStates depOp = none → -- No parallel yields to the same dependency
--     LinkStep deps main s .ε
--       { s with depStates :=
--         Function.update s.depStates depOp (some ((deps depOp).init inputVals)) }
--       none
--   /-- One of the dependencies making a step without returning -/
--   | step_dep_no_ret {depState depState' : (deps depOp).S} :
--     s.depStates depOp = some depState →
--     (deps depOp).Step depState tr depState' none →
--     LinkStep deps main s tr
--       { s with depStates := Function.update s.depStates depOp (some depState') }
--       none
--   /-- One of the dependencies making a step and returning to the main semantics -/
--   | step_dep_with_ret
--     {depState depState' : (deps depOp).S} :
--     s.depStates depOp = some depState →
--     (deps depOp).Step depState tr depState' (some outputVals) →
--     main.Yield s.mainState (.inr depOp) inputVals outputVals mainState' →
--     LinkStep deps main s tr
--       { s with
--         mainState := mainState',
--         depStates := Function.update s.depStates depOp none }
--       none

-- /-- Link a partial interpretation of a subset of operators. -/
-- def link
--   [Arity Op₀] [Arity Op₁]
--   [DecidableEq Op₁]
--   (deps : PartInterp Op₀ Op₁ V E)
--   (main : Semantics (Op₀ ⊕ Op₁) V E m n)
--   : Semantics Op₀ V E m n
--   := {
--     S := LinkState deps main,
--     init := LinkState.init,
--     Yield := LinkYield deps main,
--     Step := LinkStep deps main,
--   }

-- end Wavelet.Op

namespace Wavelet.Op

inductive Empty

def Empty.elim {α} (e : Empty) : α := by cases e

instance : Arity Empty where
  ι e := e.elim
  ω e := e.elim

abbrev Lts (C : Type u) (E : Type v) := C → E → C → Prop

abbrev Lts.Step (lts : Lts C E) := lts

/-- Zero or more steps with the given label -/
inductive Lts.TauStar (lts : Lts C E) (τ : E) : C → C → Prop
  | refl : lts.TauStar τ c c
  | tail (c₁ c₂ c₃ : C) :
      lts.TauStar τ c₁ c₂ → lts c₂ τ c₃ → lts.TauStar τ c₁ c₃

/-- A non-tau step preceded and followed by zero or more tau steps. -/
inductive Lts.StepModTau (lts : Lts C E) (τ : E) : Lts C E where
  | mk :
      lts.TauStar τ c₁ c₂ →
      lts c₂ e c₃ →
      e ≠ τ →
      lts.TauStar τ c₃ c₄ →
      lts.StepModTau τ c₁ e c₄

/-- Introduces a single step without any τ events -/
def Lts.StepModTau.single
  {lts : Lts C E} {τ : E}
  (hstep : lts.Step c₁ l c₂) (hne : l ≠ τ)
  : lts.StepModTau τ c₁ l c₂ := ⟨.refl, hstep, hne, .refl⟩

structure Lts.Simulates
  (lts₁ : Lts C₁ E)
  (lts₂ : Lts C₂ E)
  (R : C₁ → C₂ → Prop)
  (c₁ : C₁) (c₂ : C₂) : Prop where
  init : R c₁ c₂
  coind : ∀ c₁ l c₁',
    R c₁ c₂ →
    lts₁.Step c₁ l c₁' →
    ∃ c₂',
      lts₂.Step c₂ l c₂' ∧
      R c₁' c₂'

inductive Label (Op : Type u) V n [Arity Op] where
  | yield (o : Op) (inputs : Vector V (Arity.ι o)) (outputs : Vector V (Arity.ω o))
  | output (vals : Vector V n)
  | τ

class Semantics Op V [Arity Op] m n where
  S : Type*
  init : Vector V m → S
  lts : Lts S (Label Op V n)

/-- Whether the given state can potentially yield. -/
def Semantics.HasYield
  [Arity Op]
  (sem : Semantics Op V m n)
  (s : sem.S) (op : Op) (inputs : Vector V (Arity.ι op)) : Prop :=
  ∃ outputs s', sem.lts.Step s (.yield op inputs outputs) s'

abbrev Semantics.Simulates
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := ∀ args, Lts.Simulates
    (sem₁.lts.StepModTau .τ) (sem₂.lts.StepModTau .τ)
    R
    (sem₁.init args) (sem₂.init args)

abbrev PartInterp Op₀ Op V [Arity Op₀] [Arity Op] :=
  (op : Op) → Semantics Op₀ V (Arity.ι op) (Arity.ω op)

abbrev FullInterp Op V [Arity Op] := PartInterp Empty Op V

structure LinkState
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (deps : PartInterp Op₀ Op₁ V)
  (main : Semantics (Op₀ ⊕ Op₁) V m n) where
  mainState : main.S
  depStates : (op : Op₁) → Option (deps op).S

def LinkState.init
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {deps : PartInterp Op₀ Op₁ V}
  {main : Semantics (Op₀ ⊕ Op₁) V m n}
  (args : Vector V m) : LinkState deps main := {
    mainState := main.init args,
    depStates := λ _ => none,
  }

inductive LinkStep
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (deps : PartInterp Op₀ Op₁ V)
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  : Lts (LinkState deps main) (Label Op₀ V n) where
  | step_main_tau :
    main.lts.Step s.mainState .τ mainState' →
    LinkStep deps main s .τ { s with mainState := mainState' }
  | step_main_yield :
    main.lts.Step s.mainState (.yield (.inl op) inputs outputs) mainState' →
    LinkStep deps main s (.yield op inputs outputs) { s with mainState := mainState' }
  | step_main_output :
    main.lts.Step s.mainState (.output outputVals) mainState' →
    LinkStep deps main s (.output outputVals) { s with mainState := mainState' }
  | step_dep_tau {depState depState' : (deps depOp).S} :
    s.depStates depOp = some depState →
    (deps depOp).lts.Step depState .τ depState' →
    LinkStep deps main s .τ
      { s with depStates := Function.update s.depStates depOp (some depState') }
  | step_dep_yield {depState depState' : (deps depOp).S} :
    s.depStates depOp = some depState →
    (deps depOp).lts.Step depState (.yield op inputs outputs) depState' →
    LinkStep deps main s (.yield op inputs outputs)
      { s with depStates := Function.update s.depStates depOp (some depState') }
  -- Semantics to yield and return to the partial interpretation
  | step_spawn :
    main.HasYield s.mainState (.inr depOp) inputVals →
    s.depStates depOp = none → -- No parallel yields to the same dependency
    LinkStep deps main s .τ
      { s with depStates :=
        Function.update s.depStates depOp (some ((deps depOp).init inputVals)) }
  | step_join
    {depState : (deps depOp).S} :
    s.depStates depOp = some depState →
    (deps depOp).lts.Step depState (.output outputVals) depState' →
    main.lts.Step s.mainState (.yield (.inr depOp) inputVals outputVals) mainState' →
    LinkStep deps main s .τ
      { s with
        mainState := mainState',
        depStates := Function.update s.depStates depOp none }

/-- Link a partial interpretation of a subset of operators. -/
def link
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  (deps : PartInterp Op₀ Op₁ V)
  (main : Semantics (Op₀ ⊕ Op₁) V m n)
  : Semantics Op₀ V m n
  := {
    S := LinkState deps main,
    init := LinkState.init,
    lts := LinkStep deps main,
  }

end Wavelet.Op
