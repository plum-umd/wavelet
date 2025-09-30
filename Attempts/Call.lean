import Wavelet.Op
import Wavelet.LTS
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

import Wavelet.Simulation.Defs

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
open Simulation.Defs

instance instAritySum [l : Arity Op₁] [r : Arity Op₂] : Arity (Op₁ ⊕ Op₂) where
  ι | .inl o => Arity.ι o
    | .inr o => Arity.ι o
  ω | .inl o => Arity.ω o
    | .inr o => Arity.ω o

instance instArityFinMem [inst : Arity (Fin k)] {k' : Fin k} : Arity (Fin k') where
  ι i := inst.ι (i.castLT (by omega))
  ω i := inst.ω (i.castLT (by omega))

instance instArityFinPred [inst : Arity (Fin (k + 1))] : Arity (Fin k) where
  ι i := inst.ι (i.castLT (by omega))
  ω i := inst.ω (i.castLT (by omega))

instance instArityFin0 : Arity (Fin 0) where
  ι := Fin.elim0
  ω := Fin.elim0

/-- Lifts an interpretation across different universe for the state type. -/
instance instOpULift [Arity Op] [InterpOp Op V E S] : InterpOp Op V E (ULift S) where
  Step o inputs state tr res := InterpOp.Step o inputs state.down tr ⟨res.1.down, res.2⟩

instance instOpSumFin0 [Arity Op] [inst : InterpOp Op V E S] : InterpOp (Op ⊕ Fin 0) V E S where
  Step
    | .inl o, inputs, state, tr, res =>
      InterpOp.Step o inputs state tr res
    | .inr f, _, _, _, _ => Fin.elim0 f

abbrev Prog Op χ k [Arity Op] [sig : Arity (Fin k)] :=
  (i : Fin k) → Fn (Op ⊕ Fin i) χ (Arity.ι i) (Arity.ω i)

-- structure EncapFn Op χ [Arity Op] where
--   ι : Nat
--   ω : Nat
--   fn : Fn Op χ ι ω

-- def EncapFn.fromFn {Op χ m n} [Arity Op] (fn : Fn Op χ m n) : EncapFn Op χ := ⟨m, n, fn⟩

-- inductive WithFn (Op : Type u) {χ : Type v} [Arity Op] (fn : EncapFn Op χ) where
--   | op (o : Op)
--   | call

-- infix:65 " w/ " => WithFn

-- instance instArityWithFn [Arity Op] (fn : EncapFn Op χ) : Arity (Op w/ fn) where
--   ι | .op o => Arity.ι o
--     | .call => fn.ι
--   ω | .op o => Arity.ω o
--     | .call => fn.ω

-- structure Sig where
--   ι : Nat
--   ω : Nat

-- inductive Prog' : (Op : Type u) → (χ : Type v) → [Arity Op] → Type (max (u + 1) (v + 1)) where
--   | nil [Arity Op] : Prog' Op χ
--   | cons [Arity Op] (prog : Prog' Op χ) (fn : EncapFn Op χ) : Prog' (Op w/ fn) χ

-- example {Op} [Arity Op] : Prog' Op String
--   := sorry
--   where
--     fn₁ : EncapFn Op String := .fromFn {
--       params := #v["a", "b"],
--       body := .ret #v["a"],
--     }
--     fn₂ : EncapFn (Op w/ fn₁) String := .fromFn {
--       params := #v["a", "b", "c"],
--       body :=
--         .op (.inr .call)
--           (cast (by rfl) #v["b", "c"])
--           (cast (by rfl) #v["d"])
--           (.ret #v["a", "d"]),
--     }

abbrev exampleSig : Arity (Fin 2) := {
    ι | 0 => 2
      | 1 => 3,
    ω | 0 => 1
      | 1 => 2,
  }

example [Arity Op] : Prog (sig := exampleSig) Op String 2
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

/-- TODO: should be auto-derived -/
instance [inst : DecidableEq χ] : DecidableEq (LinkName χ) := sorry

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

-- def compileProg₀
--   [Arity Op] [sig : Arity (Fin k)]
--   [DecidableEq χ] [InterpConsts V]
--   (fns : (i : Fin k) → Fn Op χ (Arity.ι i) (Arity.ω i))
--   (main : Fn (Op ⊕ Fin k) χ m n)
--   : Proc Op (LinkName (ChanName χ)) V (sig.ι i) (sig.ω i)
--   := sorry

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
  (Op : Type u₁) (χ : Type u₂) (V : Type u₃) (S : Type u₄) k
  [Arity Op]
  [sig : Arity (Fin k)]
  : Fin k → Type (max u₁ u₂ u₃ u₄)
  | ⟨0, _⟩ => ULift S
  | ⟨i + 1, _⟩ =>
    let i' : Fin k := ⟨i, by omega⟩
    let S' := InterpStack Op χ V S k i'
    let : Arity (Fin i') := instArityFinMem
    S' × Option (Seq.Config (Op ⊕ Fin i') χ V S' (Arity.ι i') (Arity.ω i'))

def Prog.InterpStack.inj
  {Op χ V S k}
  [Arity Op] [sig : Arity (Fin k)]
  (s : S)
  : {i : Fin k} → Prog.InterpStack Op χ V S k i
  | ⟨0, _⟩ => ULift.up s
  | ⟨_ + 1, _⟩ => (inj s, none)

/-- Extracts the current state from the stack. -/
def Prog.InterpStack.base
  {Op χ V S k}
  [Arity Op] [Arity (Fin k)]
  {i : Fin k}
  (stack : Prog.InterpStack Op χ V S k i) : S
  := match i with
    | ⟨0, _⟩ => stack.down
    | ⟨_ + 1, _⟩ => InterpStack.base stack.1

/-- Generate an `InterpOp` of the first `i` functions over `Prog.InterpStack`. -/
instance Prog.instFnAsOp
  {Op χ} (V S)
  [Arity Op] [sig : Arity (Fin k)]
  [DecidableEq χ] [InterpConsts V]
  [baseInst : InterpOp Op V E S]
  (prog : Prog Op χ k)
  : (i : Fin k) → InterpOp (Op ⊕ Fin i) V E (Prog.InterpStack Op χ V S k i)
  | ⟨0, _⟩ =>
    let : Arity (Fin 0) := _
    {
      Step
        | .inl o, inputs, state, tr, res =>
          baseInst.Step o inputs state.base tr ⟨res.1.base, res.2⟩
        | .inr f, inputs, state, tr, res => Fin.elim0 f
    }
  | ⟨i + 1, _⟩ =>
    let i' : Fin k := ⟨i, by omega⟩
    let inst := instFnAsOp V S prog i'
    let : Arity (Fin (i + 1)) := _
    {
      Step
        -- Operators in `Op` are interpreted in the original semantics (`baseInst`).
        | .inl o, inputs, state, tr, res =>
          inst.Step (.inl o) inputs state.1 tr ⟨res.1.1, res.2⟩
        -- Function calls are either interpreted by the IH `inst`
        -- or by the current function `prog i'`.
        | .inr f, inputs, state, tr, res =>
          if h₁ : f.val = i then
            have h₂ : Arity.ι (Sum.inr (α := Op) f) = Arity.ι i'
              := by simp [← h₁, i']; rfl
            have h₃ : Arity.ω (Sum.inr (α := Op) f) = Arity.ω i'
              := by simp [← h₁, i']; rfl
            Prog.StepFn
              (inst := inst)
              (prog i')
              (cast (by congr) inputs)
              (cast (by simp [i']; rfl) state)
              tr
              (cast (by simp [i', h₃]; rfl) res)
          else
            inst.Step (.inr ⟨↑f, by simp [i']; omega⟩) inputs state.1 tr ⟨res.1.1, res.2⟩
    }

/-- Generates a transition relation for the `i`th function,
which depends on the `InterpOp` for the previous functions
generated by `Prog.AsInterpOp`. -/
def Prog.Step
  {Op χ} (V S)
  [Arity Op] [Arity (Fin k)]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  (prog : Prog Op χ k)
  (i : Fin k) :
  (
    Seq.Config (Op ⊕ Fin i) χ V (Prog.InterpStack Op χ V S k i) (Arity.ι i) (Arity.ω i) →
    Trace E →
    Seq.Config (Op ⊕ Fin i) χ V (Prog.InterpStack Op χ V S k i) (Arity.ι i) (Arity.ω i) →
    Prop
  ) := Seq.Config.Step (interp := Prog.instFnAsOp V S prog i)

def Prog.init
  [Arity Op] [Arity (Fin k)]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  (prog : Prog Op χ k) (i : Fin k)
  (state : S)
  (args : Vector V (Arity.ι i)) :
  Seq.Config (Op ⊕ Fin i) χ V (Prog.InterpStack Op χ V S k i) (Arity.ι i) (Arity.ω i) :=
  Seq.Config.init (prog i) (.inj state) args

instance [Arity Op] [Arity (Fin k)] {i : Fin k}
  : GetState (Seq.Config (Op ⊕ Fin i) χ V (Prog.InterpStack Op χ V S k i) (Arity.ι i) (Arity.ω i)) S where
  getState config := config.state.base

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

-- theorem linkAtomicProc₀_equals_mapChans
--   [Arity Op] [Arity (Fin 0)]
--   (procs : (i : Fin 0) → Proc Op (LinkName χ) V (Arity.ι i) (Arity.ω i))
--   (idx : Nat) -- Index of the atomic proc
--   (atom : AtomicProc (Op ⊕ Fin 0) (LinkName χ) V) :
--   linkAtomicProc procs idx atom = atom.mapChans LinkName.main := sorry

def Expr.castSumFin0
  [Arity Op] [Arity (Fin 0)] :
  Expr (Op ⊕ Fin 0) χ m n → Expr Op χ m n
  | .ret vars => .ret vars
  | .tail vars => .tail vars
  | .op (.inl o) inputs outputs cont => .op o inputs outputs (Expr.castSumFin0 cont)
  | .op (.inr f) .. => Fin.elim0 f
  | .br cond left right => .br cond (Expr.castSumFin0 left) (Expr.castSumFin0 right)

def Fn.castSumFin0
  [Arity Op] [Arity (Fin 0)]
  (fn : Fn (Op ⊕ Fin 0) χ m n) :
  Fn Op χ m n := {
    params := fn.params,
    body := Expr.castSumFin0 fn.body,
  }

theorem lemma₀
  [Arity Op]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  (fn : Fn (Op ⊕ Fin 0) χ m n) :
  ∃ R,
    Simulation (E := E)
      (Seq.Config.init fn { down := state : ULift S} args)
      (Seq.Config.init (Fn.castSumFin0 fn) state args)
      R
      Seq.Config.Step
      (Seq.Config.Step (V := V))
  := sorry

/-- TODO: need to strengthen to SPSimulation. -/
theorem really?
  [Arity Op] [Arity (Fin k)]
  [InterpConsts V]
  [InterpOp Op V E S]
  [DecidableEq χ]
  (prog : Prog Op χ k)
  (i : Fin k)
  (state : S)
  (args : Vector V (Arity.ι i))
  (hnz : ∀ (i : Fin k), Arity.ι i > 0 ∧ Arity.ω i > 0) :
  ∃ R,
    Simulation
      (Prog.init (E := E) prog i state args)
      (Dataflow.Config.init (compileProg prog hnz i) state args)
      R
      (Prog.Step V S prog i)
      (Dataflow.Config.Step (E := E))
  := by
  have ⟨i', hi⟩ := i
  induction i' with
  | zero =>
    unfold compileProg
    simp [Prog.init, Prog.InterpStack.inj]
    simp [linkProcs, Proc.mapChans]
    generalize hfn : prog ⟨0, hi⟩ = fn
    -- let : Arity (Fin 0) := instArityFin
    -- let : Arity (Op ⊕ Fin 0) := instAritySum
    let : Arity (Fin ↑(⟨0, hi⟩ : Fin k)) := instArityFinMem
    -- have :
    --   Simulation (E := E)
    --     (Seq.Config.init fn { down := state : ULift S } args)
    --     (Dataflow.Config.init (compileFn (by apply hnz) fn) { down := state : ULift S } args)
    --     sorry
    --     sorry
    --     sorry
    --   := sorry
    sorry
  | succ => sorry

end Wavelet.Compile
