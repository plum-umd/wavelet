import Wavelet.Op
import Wavelet.Lts
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile

import Wavelet.Simulation.Lemmas

namespace Wavelet.Call

open Op Lts Seq Dataflow Compile
open Simulation.Lemmas

structure Sig where
  ι : Nat
  ω : Nat

inductive SigOps (sigs : Vector Sig k) (k' : Fin (k + 1)) where
  | call (i : Fin k')
  deriving DecidableEq

def SigOps.toFin {k' : Fin (k + 1)} : SigOps sigs k' → Fin k'
  | .call i => i

def SigOps.elim0 : SigOps sigs ⟨0, by simp⟩ → α
  | .call i => i.elim0

instance : Arity (SigOps sigs k') where
  ι | .call i => sigs[i].ι
  ω | .call i => sigs[i].ω

abbrev Prog (Op : Type u) χ V [Arity Op] (sigs : Vector Sig k) :=
  (i : Fin k) → Fn (Op ⊕ SigOps sigs i.castSucc) χ V sigs[i].ι sigs[i].ω

def Prog.semantics
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Vector Sig k}
  (prog : Prog Op χ V sigs)
  (i : Fin k)
  : Semantics Op V sigs[i].ι sigs[i].ω
  := (prog i).semantics.link (λ op =>
    Prog.semantics prog ⟨op.toFin, by omega⟩)

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
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω)
  (idx : Nat) -- Index of the atomic proc
  (atom : AtomicProc (Op ⊕ (SigOps sigs k')) (LinkName χ) V)
  : AtomicProcs Op (LinkName χ) V :=
  match atom with
  | .op (.inl o) inputs outputs =>
    [.op o (inputs.map .main) (outputs.map .main)]
  | .op (.inr (.call i)) inputs outputs =>
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
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω)
  (main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n)
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
  (prog : Prog Op χ V sigs)
  (hnz : ∀ i : Fin k, sigs[i].ι > 0 ∧ sigs[i].ω > 0)
  (i : Fin k) : Proc Op (LinkName (ChanName χ)) V sigs[i].ι sigs[i].ω :=
  -- Compile the current function
  let proc : Proc (Op ⊕ SigOps sigs i.castSucc) (LinkName (ChanName χ)) V _ _ :=
    compileFn (by apply hnz) (prog i) |>.mapChans LinkName.base
  -- Compile dependencies
  let deps : (j : Fin i) → Proc Op (LinkName (ChanName χ)) V sigs[j].ι sigs[j].ω :=
    λ j => compileProg sigs prog hnz (j.castLT (by omega))
  -- Link everything into one dataflow graph
  linkProcs sigs i.castSucc deps proc

/-- TODO: Migrate the proofs of the older version over. -/
theorem sim_compile_fn
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (hnz : m > 0 ∧ n > 0)
  (fn : Fn Op χ V m n)
  (hwf : fn.WellFormed) :
  fn.semantics ≲ (compileFn hnz fn).semantics
  := sorry

theorem sim_congr_link
  [Arity Op₀] [Arity Op₁]
  [DecidableEq Op₁]
  {main main' : Semantics (Op₀ ⊕ Op₁) V m n}
  {deps deps' : PartInterp Op₀ Op₁ V}
  (hsim_deps : ∀ i, deps i ≲ deps' i)
  (hsim_main : main ≲ main')
  : main.link deps ≲ main'.link deps'
  := sorry

theorem sim_map_chans_inj
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f) :
  proc.semantics ≲ (proc.mapChans f).semantics := sorry

def Sim.getDepOp
  [Arity Op]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  : AtomicProc (Op ⊕ SigOps sigs k') χ V → Option (SigOps sigs k')
  | .op (.inr depOp) _ _ => some depOp
  | _ => none

/-- Ghost states/invariants about the current activated dependency operator. -/
structure Sim.GhostFrame
  [Arity Op]
  [DecidableEq χ]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  (mainState : Dataflow.Config (Op ⊕ SigOps sigs k') (LinkName χ) V m n)
  (depOp : SigOps sigs k') where
  depIdx : Fin mainState.proc.atoms.length
  inputs : Vector (LinkName χ) sigs[depOp.toFin].ι
  inputVals : Vector V sigs[depOp.toFin].ι
  outputs : Vector (LinkName χ) sigs[depOp.toFin].ω
  chans' : ChanMap (LinkName χ) V
  -- Some facts required to run `Dataflow.Config.Step.step_op` after returning
  get_op : mainState.proc.atoms[depIdx] = .op (.inr depOp) inputs outputs
  pop_inputs : mainState.chans.popVals inputs = some (inputVals, chans')

/-- Linked dataflow channel states when no dependency is currently activated -/
def Sim.linkChansMain
  (mainChans : ChanMap (LinkName χ) V) : ChanMap (LinkName χ) V :=
  λ name =>
    match name with
    | .main name' => mainChans name'
    | _ => []

/-- Linked dataflow channel states when a dependency operator is activated -/
def Sim.linkChansDep
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  {mainState : Dataflow.Config (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {depOp : SigOps sigs k'}
  (frame : Sim.GhostFrame mainState depOp)
  (depChans : ChanMap (LinkName χ) V)
  : ChanMap (LinkName χ) V :=
  λ name =>
    match name with
    | .base _ => []
    | .main name' => mainState.chans name'
    | .dep i name' => if i = frame.depIdx then depChans name' else []

def Sim
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (config₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics))
  (config₂ : Dataflow.Config Op (LinkName χ) V m n) : Prop
  :=
  config₂.proc = linkProcs sigs k'
    (λ i => (config₁.depStates (.call i)).proc)
    config₁.mainState.proc ∧
  (config₁.curSem = none → config₂.chans = Sim.linkChansMain config₁.mainState.chans) ∧
  (∀ depOp, config₁.curSem = some depOp →
    ∃ frame : Sim.GhostFrame config₁.mainState depOp,
      config₂.chans = Sim.linkChansDep frame (config₁.depStates depOp).chans)

-- ChanMap.pushVals (Vector.map (LinkName.dep idx) (procs depOp.toFin).inputs) inputVals
--     (Sim.linkChans
--       { curSem := s₁.curSem, mainState := { proc := s₁.mainState.proc, chans := chans' }, depStates := s₁.depStates }) =
--   Sim.linkChans
--     { curSem := some depOp, mainState := s₁.mainState,
--       depStates :=
--         Function.update s₁.depStates depOp
--           { proc := (s₁.depStates depOp).proc,
--             chans := ChanMap.pushVals (s₁.depStates depOp).proc.inputs inputVals (s₁.depStates depOp).chans } }

-- /-- `pushVals` on main channels commutes with `linkChans`. -/
-- theorem sim_link_procs_push_vals
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {sigs : Vector Sig k}
--   {k' : Fin (k + 1)}
--   {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
--   {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
--   {s₁ s₁' : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
--   (curDep curDep' : Option (Fin main.atoms.length))
--   (hpush : chans.pushVals names vals = chans') :
--   (Sim.linkChans (main := main)
--     { s₁ with mainState := { s₁.mainState with chans := chans } }).pushVals
--     (names.map LinkName.main) vals =
--     Sim.linkChans (main := main)
--       { s₁ with mainState := { s₁.mainState with chans := chans' } }
--   := by
--   sorry

-- /-- `pushVals` on main channels commutes with `linkChans`. -/
-- theorem sim_link_procs_push_vals_main
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {sigs : Vector Sig k}
--   {k' : Fin (k + 1)}
--   {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
--   {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
--   {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
--   (hpush : chans.pushVals names vals = chans') :
--   (Sim.linkChans (main := main)
--     { s₁ with mainState := { s₁.mainState with chans := chans } }).pushVals
--     (names.map LinkName.main) vals =
--     Sim.linkChans (main := main)
--       { s₁ with mainState := { s₁.mainState with chans := chans' } }
--   := by
--   simp [← hpush]
--   funext name
--   simp [Sim.linkChans]
--   cases name with
--   | base _ =>
--     simp
--     rw [push_vals_disjoint]
--     rotate_left
--     · simp
--     simp [Sim.linkChans]
--   | main name' =>
--     simp
--     rw [push_vals_map]
--     · simp [Function.Injective]
--     simp [Sim.linkChans]
--   | dep =>
--     simp
--     rw [push_vals_disjoint]
--     rotate_left
--     · simp
--     simp [Sim.linkChans]

-- /-- `popVals` on main channels commutes with linkChans. -/
-- theorem sim_link_procs_pop_vals_main
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {sigs : Vector Sig k}
--   {k' : Fin (k + 1)}
--   {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
--   {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
--   {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
--   (hpop : chans.popVals names = some (outputVals, chans')) :
--   (Sim.linkChans (main := main)
--     { s₁ with mainState := { s₁.mainState with chans := chans } }).popVals
--     (names.map LinkName.main) =
--     some (
--       outputVals,
--       Sim.linkChans (main := main)
--         { s₁ with mainState := { s₁.mainState with chans := chans' } },
--     )
--   := by
--   sorry

theorem mem_flatten_mapIdx
  {xs : List α} {x : α} {x' : β}
  {f : Nat → α → List β}
  (hmem_x : x ∈ xs)
  (hmem_x' : ∀ i, x' ∈ f i x):
  x' ∈ (xs.mapIdx f).flatten
  := by
  have ⟨i, hlt, hget_x⟩ := List.mem_iff_getElem.mp hmem_x
  apply List.mem_flatten.mpr
  simp
  exists f i xs[i]
  constructor
  · exists i, hlt
  · simp [hget_x, hmem_x']

-- theorem sim_link_procs_step_main
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {sigs : Vector Sig k}
--   {k' : Fin (k + 1)}
--   {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
--   {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
--   {mainState' : main.semantics.S}
--   {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
--   {s₂ : Dataflow.Config Op (LinkName χ) V m n}
--   {l : Label (Op ⊕ SigOps sigs k') V m n}
--   {l' : Label Op V m n}
--   (hsim : Sim s₁ s₂)
--   -- Assumptions of `.LinkStep.step_main`
--   (hcur : s₁.curSem = none)
--   (hlabel : Semantics.MainLabelPassthrough l l')
--   (hstep_main : main.semantics.lts.Step s₁.mainState l mainState')
--   : ∃ s₂',
--     Dataflow.Config.Step.StepModTau Label.τ s₂ l' s₂' ∧
--     Sim { s₁ with mainState := mainState' } s₂' := by
--   have ⟨hsim_proc, hsim_chans⟩ := hsim
--   simp [Proc.semantics, Lts.Step] at hstep_main
--   cases hstep_main with
--   | step_init =>
--     rename_i args
--     cases hlabel
--     have hstep_s₂ : Dataflow.Config.Step s₂ (.input args) _
--       := Dataflow.Config.Step.step_init
--     replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
--     exists s₂'
--     constructor
--     · exact .single hstep_s₂
--     · and_intros
--       · simp [hs₂', hsim_proc]
--       · simp [hs₂', hsim_proc, hsim_chans, linkProcs]
--         apply sim_link_procs_push_vals_main
--         rfl
--   | step_output hpop =>
--     rename_i chans' outputVals
--     cases hlabel
--     have hstep_s₂ : Dataflow.Config.Step s₂ (.output outputVals) _
--       := Dataflow.Config.Step.step_output
--         (by
--           simp [hsim_proc, hsim_chans, linkProcs]
--           apply sim_link_procs_pop_vals_main hpop)
--     replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
--     exists s₂'
--     constructor
--     · exact .single hstep_s₂
--     · and_intros
--       · simp [hs₂', hsim_proc]
--       · simp [hs₂']
--   | step_op hmem_op hpop =>
--     cases hlabel
--     rename_i chans' op inputVals outputVals inputs outputs
--     have hstep_s₂ : Dataflow.Config.Step s₂ (.yield op inputVals outputVals) _
--       := Dataflow.Config.Step.step_op
--         (op := op)
--         (inputs := inputs.map LinkName.main)
--         (outputs := outputs.map LinkName.main)
--         (by
--           simp [hsim_proc, linkProcs]
--           apply mem_flatten_mapIdx hmem_op
--           simp [linkAtomicProc])
--         (by
--           simp [hsim_chans]
--           apply sim_link_procs_pop_vals_main hpop)
--     replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
--     exists s₂'
--     constructor
--     · exact .single hstep_s₂
--     · and_intros
--       · simp [hs₂', hsim_proc]
--       · simp [hs₂', hsim_proc, linkProcs]
--         apply sim_link_procs_push_vals_main
--         rfl
--   | _ => sorry

-- theorem sim_link_procs_step_dep
--   [Arity Op]
--   [DecidableEq χ]
--   [InterpConsts V]
--   {sigs : Vector Sig k}
--   {k' : Fin (k + 1)}
--   {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
--   {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
--   {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
--   {s₂ : Dataflow.Config Op (LinkName χ) V m n}
--   {depOp : SigOps sigs k'}
--   {depState' : (procs depOp.toFin).semantics.S}
--   {l : Label Op V sigs[depOp.toFin].ι sigs[depOp.toFin].ω}
--   {l' : Label Op V m n}
--   (hsim : Sim s₁ s₂)
--   -- Assumptions of `.LinkStep.step_dep`
--   (hcur : s₁.curSem = some depOp)
--   (hlabel : Semantics.DepLabelPassthrough l l')
--   (hstep_dep : (procs depOp.toFin).semantics.lts.Step (s₁.depStates depOp) l depState')
--   : ∃ s₂',
--     Dataflow.Config.Step.StepModTau Label.τ s₂ l' s₂' ∧
--     Sim { s₁ with
--       depStates := Function.update s₁.depStates depOp depState' } s₂'
--   := by
--   have ⟨hsim_proc, hsim_chans⟩ := hsim
--   simp [Proc.semantics, Lts.Step] at hstep_dep
--   cases hstep_dep with
--   | step_init =>
--     rename_i args
--     cases hlabel
--   | step_op hmem_op hpop =>
--     cases hlabel
--     rename_i op inputVals outputVals inputs outputs chans'
--     sorry
--   | _ => sorry

theorem sim_link_procs_step_dep_spawn
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {depOp : SigOps sigs k'}
  {depState' : (procs depOp.toFin).semantics.S}
  {inputVals : Vector V sigs[depOp.toFin].ι}
  (hsim : Sim s₁ s₂)
  -- Assumptions of `.LinkStep.step_dep`
  (hcur : s₁.curSem = none)
  (hyield : main.semantics.HasYield s₁.mainState (.inr depOp) inputVals)
  (hstep_dep :
    (procs depOp.toFin).semantics.lts.Step
      (s₁.depStates depOp) (.input inputVals) depState')
  : ∃ s₂',
    Dataflow.Config.Step.StepModTau .τ s₂ .τ s₂' ∧
    Sim { s₁ with
      curSem := some depOp,
      depStates := Function.update s₁.depStates depOp depState' } s₂'
  := by
  have ⟨hsim_proc, hsim_chans⟩ := hsim
  have ⟨outputVals, mainState', hstep_main⟩ := hyield
  simp [Proc.semantics, Lts.Step] at hstep_dep hstep_main
  cases hstep_dep with | step_init =>
  cases hstep_main with | step_op hmem_op hpop =>
  rename_i chans' inputs outputs
  -- | .op (.inr (.call i)) inputs outputs =>
  --   [ .forward (inputs.map .main) ((procs i).inputs.map (LinkName.dep idx)) ] ++
  --   (procs i).atoms.mapChans (LinkName.dep idx) ++
  --   [ .forward ((procs i).outputs.map (LinkName.dep idx)) (outputs.map .main) ]
  have ⟨idx, hidx, hget_op⟩ := List.mem_iff_getElem.mp hmem_op
  have hmem_forward :
    .forward
      (inputs.map .main)
      ((procs depOp.toFin).inputs.map (LinkName.dep idx))
    ∈ s₂.proc.atoms
    := sorry
  sorry
  -- have hstep_s₂ : Dataflow.Config.Step s₂ .τ _
  --   := Dataflow.Config.Step.step_forward
  --     hmem_forward
  --     (by
  --       simp [hsim_chans]
  --       apply sim_link_procs_pop_vals_main hpop)
  -- replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
  -- exists s₂'
  -- constructor
  -- · exact .single hstep_s₂
  -- · and_intros
  --   · -- TODO: clean this up
  --     simp [hs₂', hsim_proc, linkProcs]
  --     cases depOp with | call i =>
  --     congr
  --     funext i'
  --     if h : i' = i then
  --       subst h
  --       simp
  --     else
  --       simp [Function.update, h]
  --   · simp [hs₂']
  --     -- Need suitably generalized `sim_link_procs_push_vals_main`
  --     sorry

theorem sim_link_procs_step_dep_ret
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {depOp : SigOps sigs k'}
  {depState' : (procs depOp.toFin).semantics.S}
  {mainState' : main.semantics.S}
  {inputVals : Vector V sigs[depOp.toFin].ι}
  {outputVals : Vector V sigs[depOp.toFin].ω}
  (hsim : Sim s₁ s₂)
  -- Assumptions of `.LinkStep.step_dep`
  (hcur : s₁.curSem = some depOp)
  (hstep_dep :
    (procs depOp.toFin).semantics.lts.Step
      (s₁.depStates depOp) (.output outputVals) depState')
  (hyield :
    main.semantics.lts.Step s₁.mainState
      (Label.yield (.inr depOp) inputVals outputVals) mainState')
  : ∃ s₂',
    Dataflow.Config.Step.StepModTau .τ s₂ .τ s₂' ∧
    Sim { s₁ with
      curSem := none,
      mainState := mainState',
      depStates := Function.update s₁.depStates depOp depState' } s₂'
  := sorry

/-- Linking syntactically simulates linking semantically. -/
theorem sim_link_procs
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
  {deps : PartInterp Op (SigOps sigs k') V}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (hdeps : ∀ op, deps op = (procs (op.toFin)).semantics) :
  main.semantics.link deps ≲ (linkProcs sigs k' procs main).semantics
  := by
  replace hdeps :
    deps = λ op : SigOps sigs k' => (procs (op.toFin)).semantics := by
    funext op
    apply hdeps
  simp only [hdeps]
  apply Lts.SimilarBy.mk Sim
  apply Semantics.SimulatedBy.alt
  · -- Sim holds at initial states
    simp [Sim, Proc.semantics, Semantics.link,
      Semantics.LinkState.init, Dataflow.Config.init]
    sorry
  · intros s₁ s₂ l s₁' hsim hstep_s₁
    simp [Semantics.link, Lts.Step] at hstep_s₁
    simp [Proc.semantics]
    cases hstep_s₁ with
    | step_main hcur hlabel hstep_main =>
      sorry
      -- exact sim_link_procs_step_main hsim hcur hlabel hstep_main
    | step_dep hcur hlabel hstep_dep =>
      sorry
      -- exact sim_link_procs_step_dep hsim hcur hlabel hstep_dep
    | step_dep_spawn hcur hyield hstep_dep =>
      exact sim_link_procs_step_dep_spawn hsim hcur hyield hstep_dep
    | step_dep_ret hcur hstep_dep hyield =>
      exact sim_link_procs_step_dep_ret hsim hcur hstep_dep hyield

theorem sim_compile_prog
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (sigs : Vector Sig k)
  (prog : Prog Op χ V sigs)
  (i : Nat)
  (hlt : i < k)
  (hnz : ∀ (i : Fin k), sigs[i].ι > 0 ∧ sigs[i].ω > 0)
  (hwf : ∀ i, (prog i).WellFormed) :
  prog.semantics ⟨i, hlt⟩ ≲ (compileProg sigs prog hnz ⟨i, hlt⟩).semantics
  := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    unfold Prog.semantics
    unfold compileProg
    simp
    apply Semantics.SimilarBy.trans
    apply sim_congr_link
    · intros j
      apply ih
      omega
    · apply Semantics.SimilarBy.trans
        (sim_compile_fn
          (by apply hnz ⟨i, by omega⟩) _
          (by apply hwf))
        (sim_map_chans_inj (f := LinkName.base) (by simp [Function.Injective]))
    apply sim_link_procs
    intros op
    rfl

end Wavelet.Call
