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

@[simp]
def SigOps.toFin {k' : Fin (k + 1)} : SigOps sigs k' → Fin k'
  | .call i => i

@[simp]
theorem SigOps.inj_to_fin {i j : SigOps sigs k'} :
  i.toFin = j.toFin ↔ i = j
  := by
  constructor
  · intros h
    cases i
    cases j
    simp at h
    simp [h]
  · intros h
    simp [h]

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
  | dep (op : Nat) (name : LinkName χ)

/-- TODO: should be auto-derived -/
instance [inst : DecidableEq χ] : DecidableEq (LinkName χ) := sorry

def linkAtomicProc
  [Arity Op]
  (sigs : Vector Sig k)
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω)
  (atom : AtomicProc (Op ⊕ (SigOps sigs k')) (LinkName χ) V)
  : AtomicProcs Op (LinkName χ) V :=
  match atom with
  | .op (.inl o) inputs outputs =>
    [.op o (inputs.map .main) (outputs.map .main)]
  | .op (.inr op) inputs outputs =>
    [ .forward (inputs.map .main) ((procs op.toFin).inputs.map (LinkName.dep op.toFin)) ] ++
    (procs op.toFin).atoms.mapChans (LinkName.dep op.toFin) ++
    [ .forward ((procs op.toFin).outputs.map (LinkName.dep op.toFin)) (outputs.map .main) ]
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

/--
Inline calls to the given `k` processes while preserving a forward simulation.

This procedure is a bit more subtle than one might expect.
In order to preserve simulation (e.g., see `sim_link_procs`),
we have to assume one of the following properties about the dependent processes:
1. Either that no dependent process is called twice, or
2. The depdenent processes are "good-behaving" in the sense that
   if they emit the `.output` label, then they can always continue
   to a state identical to the initial state.

They are required because if the main process makes two separate calls
to the same dependent process, we have to make sure there is a schedule
where one call does not interfere with the other.

Property 1 is harder to prove without determinancy. Because we have
to prove that for **any trace** that produces the `.output` label at
the end, something good happens. But determinancy might be dependent
on, e.g., lack of data races.

Therefore, in the theorems below, we assume property 1.
-/
def linkProcs
  [Arity Op]
  (sigs : Vector Sig k)
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω)
  (main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n)
  : Proc Op (LinkName χ) V m n := {
    inputs := main.inputs.map LinkName.main,
    outputs := main.outputs.map LinkName.main,
    atoms := (main.atoms.map (linkAtomicProc sigs k' procs)).flatten,
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

def Sim.AffineDepOp
  [Arity Op]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  (proc : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n) : Prop
  := ∀ depOp inputs inputs' outputs outputs',
    .op (.inr depOp) inputs outputs ∈ proc.atoms →
    .op (.inr depOp) inputs' outputs' ∈ proc.atoms →
    inputs = inputs' ∧ outputs = outputs'

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

/-- Corresponds channel states -/
def Sim.linkChans
  (mainChans : ChanMap (LinkName χ) V)
  (depChans : Fin k' → ChanMap (LinkName χ) V)
  : ChanMap (LinkName χ) V :=
  λ name => match name with
    | .main name' => mainChans name'
    | .dep i name' => if _ : i < k' then depChans ⟨i, by assumption⟩ name' else []
    | _ => []

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
  -- Inputs/outputs of dependencies remain the same
  (∀ depOp, (config₁.depStates depOp).proc.inputs = (procs depOp.toFin).inputs) ∧
  (∀ depOp, (config₁.depStates depOp).proc.outputs = (procs depOp.toFin).outputs) ∧
  Sim.AffineDepOp config₁.mainState.proc ∧
  -- Linking
  config₂.proc = linkProcs sigs k'
    (λ i => (config₁.depStates (.call i)).proc)
    config₁.mainState.proc ∧
  -- Channel maps in two cases
  let depChans := (λ i => (config₁.depStates (.call i)).chans)
  (config₁.curSem = none → config₂.chans = Sim.linkChans config₁.mainState.chans depChans) ∧
  -- Some ghost states for spawn/return
  (∀ {depOp}, config₁.curSem = some depOp →
    ∃ frame : Sim.GhostFrame config₁.mainState depOp,
      config₂.chans = Sim.linkChans frame.chans' depChans)

/-- `pushVals` on main channels commutes with `linkChans`. -/
theorem sim_link_procs_push_vals_main
  [DecidableEq χ]
  {chans : ChanMap (LinkName χ) V} :
  (Sim.linkChans chans depChans).pushVals
    (names.map LinkName.main) vals = Sim.linkChans
    (chans.pushVals names vals) depChans
  := by
  funext name
  simp [Sim.linkChans]
  cases name with
  | base _ =>
    simp
    rw [push_vals_disjoint]
    rotate_left
    · simp
    simp [Sim.linkChans]
  | main name' =>
    simp
    rw [push_vals_map]
    · simp [Function.Injective]
    simp [Sim.linkChans]
  | dep =>
    simp
    rw [push_vals_disjoint]
    rotate_left
    · simp
    simp [Sim.linkChans]

/-- `pushVals` on dep channels commutes with `linkChans`. -/
theorem sim_link_procs_push_vals_dep
  [DecidableEq χ]
  {chans : ChanMap (LinkName χ) V}
  {depChans : Fin k' → ChanMap (LinkName χ) V}
  {i : Fin k'} :
  (Sim.linkChans chans depChans).pushVals
    (names.map (.dep i))
    vals
    (.dep i name') =
    (depChans i).pushVals names vals name'
  := by
  by_cases h : name' ∈ names
  · apply push_vals_map
    · simp [Function.Injective]
    simp [Sim.linkChans]
  · rw [push_vals_disjoint]
    rotate_left
    · simp [h]
    rw [push_vals_disjoint]
    rotate_left
    · simp [h]
    simp [Sim.linkChans]

/-- `popVals` on main channels commutes with `linkChansMain`. -/
theorem sim_link_procs_pop_vals_main
  [DecidableEq χ]
  {chans chans' : ChanMap (LinkName χ) V}
  (hpop : chans.popVals names = some (outputVals, chans')) :
  (Sim.linkChans chans depChans).popVals
    (names.map LinkName.main) =
    some (outputVals, Sim.linkChans chans' depChans)
  := by
  sorry

theorem sim_link_procs_pop_vals_dep
  [DecidableEq χ]
  {chans : ChanMap (LinkName χ) V}
  {depChans : Fin k' → ChanMap (LinkName χ) V}
  {i : Fin k'}
  (hpop : (depChans i).popVals names = some (outputVals, chans')) :
  (Sim.linkChans chans depChans).popVals (names.map (.dep i)) =
    some (outputVals, Sim.linkChans chans (Function.update depChans i chans'))
  := by
  sorry

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
  have ⟨hsim_proc_inputs, hsim_proc_outputs, hsim_aff, hsim_proc, hsim_main, hsim_dep⟩ := hsim
  have hsim_chans := hsim_main hcur
  have ⟨outputVals, mainState', hstep_main⟩ := hyield
  simp [Proc.semantics, Lts.Step] at hstep_dep hstep_main
  cases hstep_dep with | step_init =>
  cases hstep_main with | step_op hmem_op hpop =>
  rename_i chans' inputs outputs
  have ⟨idx, hidx, hget_op⟩ := List.mem_iff_getElem.mp hmem_op
  have hmem_forward :
    .forward
      (inputs.map .main)
      ((procs depOp.toFin).inputs.map (LinkName.dep depOp.toFin))
    ∈ s₂.proc.atoms
    := by
    simp [hsim_proc, linkProcs]
    have := List.mem_of_getElem hget_op
    exists AtomicProc.op (Sum.inr depOp) inputs outputs
    simp [this, linkAtomicProc, hsim_proc_inputs]
  have hstep_s₂ : Dataflow.Config.Step s₂ .τ _
    := Dataflow.Config.Step.step_forward
      (inputVals := inputVals)
      hmem_forward
      (by
        simp [hsim_chans]
        apply sim_link_procs_pop_vals_main hpop)
  replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
  exists s₂'
  constructor
  · exact .single hstep_s₂
  · and_intros
    · simp
      intros depOp'
      by_cases hdep : depOp = depOp'
      · subst hdep
        simp [hsim_proc_inputs]
      · rw [Function.update_of_ne (Ne.symm hdep) _ _]
        simp [hsim_proc_inputs]
    · simp
      intros depOp'
      by_cases hdep : depOp = depOp'
      · subst hdep
        simp [hsim_proc_outputs]
      · rw [Function.update_of_ne (Ne.symm hdep) _ _]
        simp [hsim_proc_outputs]
    · exact hsim_aff
    · simp [hs₂', hsim_proc, linkProcs]
      congr
      cases depOp with | call i =>
      funext i'
      by_cases h : i' = i
      · subst h
        simp
      · simp [Function.update, h]
    · simp [hs₂']
    · simp [hs₂']
      exists {
        depIdx := ⟨idx, hidx⟩,
        inputs := inputs,
        inputVals := inputVals,
        outputs := outputs,
        chans' := chans',
        get_op := hget_op,
        pop_inputs := hpop,
      }
      funext name
      simp [Sim.linkChans]
      cases name with
      | base _ =>
        simp
        rw [push_vals_disjoint]
        rotate_left; simp
        simp [Sim.linkChans]
      | main name' =>
        simp
        rw [push_vals_disjoint]
        rotate_left; simp
        simp [Sim.linkChans]
      | dep i name' =>
        simp
        split <;> rename_i h₁
        · simp [hsim_proc_inputs]
          by_cases h₂ : i = depOp.toFin
          · cases depOp with | call i' =>
            simp at h₂
            subst h₂
            rw [Function.update_self]
            simp
            apply sim_link_procs_push_vals_dep
          · simp at h₂
            rw [Function.update_of_ne (by
              intros h
              simp [← h] at h₂) _ _]
            rw [push_vals_disjoint]
            rotate_left; simp [Ne.symm h₂]
            simp [Sim.linkChans, h₁]
        · rw [push_vals_disjoint]
          rotate_left
          · simp only [Vector.mem_map]
            intros h₂
            have ⟨_, _, h₃⟩ := h₂
            simp at h₃
            omega
          simp [Sim.linkChans, h₁]

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
  := by
  have ⟨hsim_proc_inputs, hsim_proc_outputs, hsim_aff, hsim_proc, hsim_main, hsim_dep⟩ := hsim
  have ⟨frame, hsim_chans⟩ := hsim_dep hcur
  have ⟨
    depIdx,
    inputs',
    inputVals',
    outputs',
    chans₁,
    hget_op,
    hpop_inputs',
  ⟩ := frame
  simp [Proc.semantics, Lts.Step] at hstep_dep hyield
  cases hyield with | step_op hmem_op hpop_inputs =>
  rename_i chans₁' inputs outputs
  -- Prove that `hyield` must be the same as the previous
  -- `HasYield` call by affine usage of dependencies
  have ⟨h₁, h₂⟩ := hsim_aff depOp inputs inputs' outputs outputs'
    hmem_op (List.mem_of_getElem hget_op)
  subst h₁ h₂
  simp [hpop_inputs] at hpop_inputs'
  have ⟨h₁, h₂⟩ := hpop_inputs'
  subst h₁ h₂
  clear hpop_inputs'
  simp at hsim_chans
  cases hstep_dep with | step_output hpop_outputs =>
  rename_i chans'
  have ⟨idx, hidx, hget_op⟩ := List.mem_iff_getElem.mp hmem_op
  have hmem_forward_inputs :
    .forward
      (inputs.map .main)
      ((procs depOp.toFin).inputs.map (LinkName.dep depOp.toFin))
    ∈ s₂.proc.atoms
    := by
    simp [hsim_proc, linkProcs]
    have := List.mem_of_getElem hget_op
    exists AtomicProc.op (Sum.inr depOp) inputs outputs
    simp [this, linkAtomicProc, hsim_proc_inputs]
  have hmem_forward_outputs :
    .forward
      ((procs depOp.toFin).outputs.map (LinkName.dep depOp.toFin))
      (outputs.map .main)
    ∈ s₂.proc.atoms
    := by
    simp [hsim_proc, linkProcs]
    have := List.mem_of_getElem hget_op
    exists AtomicProc.op (Sum.inr depOp) inputs outputs
    simp [this, linkAtomicProc, hsim_proc_outputs]
  have hstep_s₂ : Dataflow.Config.Step s₂ .τ _
    := Dataflow.Config.Step.step_forward
      (inputVals := outputVals)
      (chans' :=
        Sim.linkChans chans₁'
          (Function.update (λ i => (s₁.depStates (SigOps.call i)).chans) depOp.1 chans'))
      hmem_forward_outputs
      (by
        simp [hsim_chans]
        simp [hsim_proc_outputs] at hpop_outputs
        rw [sim_link_procs_pop_vals_dep hpop_outputs])
  replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
  exists s₂'
  constructor
  · exact .single hstep_s₂
  · and_intros
    · simp
      intros depOp'
      by_cases hdep : depOp = depOp'
      · subst hdep
        simp [hsim_proc_inputs]
      · rw [Function.update_of_ne (Ne.symm hdep) _ _]
        simp [hsim_proc_inputs]
    · simp
      intros depOp'
      by_cases hdep : depOp = depOp'
      · subst hdep
        simp [hsim_proc_outputs]
      · rw [Function.update_of_ne (Ne.symm hdep) _ _]
        simp [hsim_proc_outputs]
    · exact hsim_aff
    · simp [hs₂', hsim_proc, linkProcs]
      congr
      cases depOp with | call i =>
      funext i'
      by_cases h : i' = i
      · subst h
        simp
      · simp [Function.update, h]
    · simp [hs₂']
      rw [sim_link_procs_push_vals_main]
      congr
      funext i
      by_cases h : i = depOp.1
      · rw [h]
        simp
      · simp [h]
        rw [Function.update_of_ne (by
          intros h'
          simp [← h'] at h) _ _]
    · simp [hs₂']

theorem sim_link_procs_step_main
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Vector Sig k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V sigs[i].ι sigs[i].ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {mainState' : main.semantics.S}
  {s₁ : Semantics.LinkState main.semantics (λ op => (procs (op.toFin)).semantics)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {l : Label (Op ⊕ SigOps sigs k') V m n}
  {l' : Label Op V m n}
  (hsim : Sim s₁ s₂)
  -- Assumptions of `.LinkStep.step_main`
  (hcur : s₁.curSem = none)
  (hlabel : Semantics.MainLabelPassthrough l l')
  (hstep_main : main.semantics.lts.Step s₁.mainState l mainState')
  : ∃ s₂',
    Dataflow.Config.Step.StepModTau Label.τ s₂ l' s₂' ∧
    Sim { s₁ with mainState := mainState' } s₂' := by
  have ⟨hsim_proc_inputs, hsim_proc_outputs, hsim_aff, hsim_proc, hsim_main, hsim_dep⟩ := hsim
  have hsim_chans := hsim_main hcur
  simp [Proc.semantics, Lts.Step] at hstep_main
  cases hstep_main with
  | step_init =>
    rename_i args
    cases hlabel
    have hstep_s₂ : Dataflow.Config.Step s₂ (.input args) _
      := Dataflow.Config.Step.step_init
    replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
    exists s₂'
    constructor
    · exact .single hstep_s₂
    · and_intros
      · exact hsim_proc_inputs
      · exact hsim_proc_outputs
      · exact hsim_aff
      · simp [hs₂', hsim_proc]
      · simp [hs₂', hsim_chans, hsim_proc, linkProcs]
        intros
        simp [sim_link_procs_push_vals_main]
      · simp [hs₂', hcur]
  | step_output hpop =>
    rename_i chans' outputVals
    cases hlabel
    have hstep_s₂ : Dataflow.Config.Step s₂ (.output outputVals) _
      := Dataflow.Config.Step.step_output
        (by
          simp [hsim_proc, hsim_chans, linkProcs]
          apply sim_link_procs_pop_vals_main hpop)
    replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
    exists s₂'
    constructor
    · exact .single hstep_s₂
    · and_intros
      · exact hsim_proc_inputs
      · exact hsim_proc_outputs
      · exact hsim_aff
      · simp [hs₂', hsim_proc]
      · simp [hs₂', hsim_proc, linkProcs]
      · simp [hs₂', hcur]
  | step_op hmem_op hpop =>
    cases hlabel
    rename_i chans' op inputVals outputVals inputs outputs
    have hstep_s₂ : Dataflow.Config.Step s₂ (.yield op inputVals outputVals) _
      := Dataflow.Config.Step.step_op
        (op := op)
        (inputs := inputs.map LinkName.main)
        (outputs := outputs.map LinkName.main)
        (by
          simp [hsim_proc, linkProcs]
          apply List.mem_flatten_map hmem_op
          simp [linkAtomicProc])
        (by
          simp [hsim_chans]
          apply sim_link_procs_pop_vals_main hpop)
    replace ⟨s₂', hs₂', hstep_s₂⟩ := exists_eq_left.mpr hstep_s₂
    exists s₂'
    constructor
    · exact .single hstep_s₂
    · and_intros
      · exact hsim_proc_inputs
      · exact hsim_proc_outputs
      · exact hsim_aff
      · simp [hs₂', hsim_proc]
      · simp [hs₂', hsim_proc, linkProcs]
        intros
        simp [sim_link_procs_push_vals_main]
      · simp [hs₂', hcur]
  | _ => sorry

theorem sim_link_procs_step_dep
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
  {l : Label Op V sigs[depOp.toFin].ι sigs[depOp.toFin].ω}
  {l' : Label Op V m n}
  (hsim : Sim s₁ s₂)
  -- Assumptions of `.LinkStep.step_dep`
  (hcur : s₁.curSem = some depOp)
  (hlabel : Semantics.DepLabelPassthrough l l')
  (hstep_dep : (procs depOp.toFin).semantics.lts.Step (s₁.depStates depOp) l depState')
  : ∃ s₂',
    Dataflow.Config.Step.StepModTau Label.τ s₂ l' s₂' ∧
    Sim { s₁ with
      depStates := Function.update s₁.depStates depOp depState' } s₂'
  := by
  have ⟨hsim_proc, hsim_chans⟩ := hsim
  simp [Proc.semantics, Lts.Step] at hstep_dep
  cases hstep_dep with
  | step_init =>
    rename_i args
    cases hlabel
  | step_op hmem_op hpop =>
    cases hlabel
    rename_i op inputVals outputVals inputs outputs chans'
    sorry
  | _ => sorry

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
      exact sim_link_procs_step_main hsim hcur hlabel hstep_main
    | step_dep hcur hlabel hstep_dep =>
      exact sim_link_procs_step_dep hsim hcur hlabel hstep_dep
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
