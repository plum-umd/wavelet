import Wavelet.Compile.Prog.Defs
import Wavelet.Compile.MapChans
import Wavelet.Compile.Fn.Simulation
import Wavelet.Compile.AffineOp

/-! SimRelulation proofs for `compileProg`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

/-- Ghost states/invariants about the current activated dependency operator. -/
private structure SimRel.GhostFrame
  [Arity Op]
  [DecidableEq χ]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  (mainState : Dataflow.Config (Op ⊕ SigOps sigs k') (LinkName χ) V m n)
  (depOp : SigOps sigs k') where
  depIdx : Fin mainState.proc.atoms.length
  inputs : Vector (LinkName χ) (sigs depOp.toFin).ι
  inputVals : Vector V (sigs depOp.toFin).ι
  outputs : Vector (LinkName χ) (sigs depOp.toFin).ω
  chans' : ChanMap (LinkName χ) V
  -- Some facts required to run `Dataflow.Config.Step.step_op` after returning
  get_op : mainState.proc.atoms[depIdx] = .op (.inr depOp) inputs outputs
  pop_inputs : mainState.chans.popVals inputs = some (inputVals, chans')

/-- Corresponds channel states -/
private def SimRel.linkChans
  (mainChans : ChanMap (LinkName χ) V)
  (depChans : Fin k' → ChanMap (LinkName χ) V) :
    ChanMap (LinkName χ) V
  := λ name => match name with
    | .main name' => mainChans name'
    | .dep i name' => if _ : i < k' then depChans ⟨i, by assumption⟩ name' else []
    | _ => []

/-- Simulation relation for `linkProcs`. -/
private def SimRel
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (config₁ : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩))
  (config₂ : Dataflow.Config Op (LinkName χ) V m n) : Prop
  :=
  -- Inputs/outputs of dependencies remain the same
  (∀ depOp, (config₁.depStates depOp).proc.inputs = (procs depOp.toFin').inputs) ∧
  (∀ depOp, (config₁.depStates depOp).proc.outputs = (procs depOp.toFin').outputs) ∧
  config₁.mainState.proc.AffineInrOp ∧
  -- Linking
  config₂.proc = linkProcs sigs k'
    (λ i => (config₁.depStates (.call i)).proc)
    config₁.mainState.proc ∧
  -- Channel maps in two cases
  let depChans := (λ i => (config₁.depStates (.call i)).chans)
  (config₁.curSem = none → config₂.chans = SimRel.linkChans config₁.mainState.chans depChans) ∧
  -- Some ghost states for spawn/return
  (∀ {depOp}, config₁.curSem = some depOp →
    ∃ frame : SimRel.GhostFrame config₁.mainState depOp,
      config₂.chans = SimRel.linkChans frame.chans' depChans)

/-- `pushVals` on main channels commutes with `linkChans`. -/
theorem sim_link_procs_push_vals_main
  [DecidableEq χ]
  {chans : ChanMap (LinkName χ) V} :
    (SimRel.linkChans chans depChans).pushVals
      (names.map .main) vals = SimRel.linkChans
      (chans.pushVals names vals) depChans
  := by
  funext name
  simp [SimRel.linkChans]
  cases name with
  | base _ =>
    simp
    rw [push_vals_disjoint]
    rotate_left
    · simp
    simp [SimRel.linkChans]
  | main name' =>
    simp
    rw [push_vals_map]
    · simp [Function.Injective]
    simp [SimRel.linkChans]
  | dep =>
    simp
    rw [push_vals_disjoint]
    rotate_left
    · simp
    simp [SimRel.linkChans]

/-- `pushVals` on dep channels commutes with `linkChans`. -/
private theorem sim_link_procs_push_vals_dep
  [DecidableEq χ]
  {chans : ChanMap (LinkName χ) V}
  {depChans : Fin k' → ChanMap (LinkName χ) V}
  {i : Fin k'} :
    (SimRel.linkChans chans depChans).pushVals
      (names.map (.dep i))
      vals
      (.dep i name') =
      (depChans i).pushVals names vals name'
  := by
  by_cases h : name' ∈ names
  · apply push_vals_map
    · simp [Function.Injective]
    simp [SimRel.linkChans]
  · rw [push_vals_disjoint]
    rotate_left
    · simp [h]
    rw [push_vals_disjoint]
    rotate_left
    · simp [h]
    simp [SimRel.linkChans]

/-- `pushVals` on dep channels commutes with `linkChans`. -/
private theorem sim_link_procs_push_vals_dep_alt
  [DecidableEq χ]
  {chans : ChanMap (LinkName χ) V}
  {depChans : Fin k' → ChanMap (LinkName χ) V}
  {i : Fin k'} :
    (SimRel.linkChans chans depChans).pushVals
      (names.map (.dep i)) vals =
      (SimRel.linkChans chans (Function.update depChans i ((depChans i).pushVals names vals)))
  := by
  funext name
  cases name with
  | base =>
    rw [push_vals_disjoint]
    rotate_left
    · simp
    simp [SimRel.linkChans]
  | main =>
    rw [push_vals_disjoint]
    rotate_left
    · simp
    simp [SimRel.linkChans]
  | dep i' name' =>
    simp [SimRel.linkChans]
    split <;> rename_i h₁
    · by_cases h₂ : i' = i
      · simp [h₂]
        rw [push_vals_map]
        · simp [Function.Injective]
        · simp [SimRel.linkChans]
      · rw [Function.update_of_ne (by
          intros h₃
          simp [← h₃] at h₂) _ _]
        rw [push_vals_disjoint]
        rotate_left
        · simp [Ne.symm h₂]
        simp [SimRel.linkChans, h₁]
    · rw [push_vals_disjoint]
      rotate_left
      · simp; omega
      · simp [SimRel.linkChans]
        simp [h₁]

/-- `popVal` on a main channel commutes with `linkChans`. -/
private theorem sim_link_procs_pop_val_main
  [DecidableEq χ]
  {chans chans' : ChanMap (LinkName χ) V}
  {name : LinkName χ}
  (hpop : chans.popVal name = some (val, chans')) :
    (SimRel.linkChans chans depChans).popVal (.main name) =
      some (val, SimRel.linkChans chans' depChans)
  := by
  simp [ChanMap.popVal] at hpop ⊢
  split at hpop <;> rename_i h₁
  contradiction
  simp at hpop
  simp [SimRel.linkChans, h₁, hpop]
  funext name
  cases name with
  | base => simp [SimRel.linkChans]
  | main => simp [SimRel.linkChans, ← hpop.2]
  | dep => simp [SimRel.linkChans]

/-- `popVals` on main channels commutes with `linkChans`. -/
private theorem sim_link_procs_pop_vals_main
  [DecidableEq χ]
  {chans chans' : ChanMap (LinkName χ) V}
  {names : Vector (LinkName χ) n}
  (hpop : chans.popVals names = some (outputVals, chans')) :
    (SimRel.linkChans chans depChans).popVals (names.map .main) =
      some (outputVals, SimRel.linkChans chans' depChans)
  := by
  induction n generalizing chans chans' with
  | zero =>
    simp [Vector.eq_empty, ChanMap.popVals] at hpop ⊢
    simp [hpop]
  | succ n' ih =>
    simp [pop_vals_unfold] at hpop ⊢
    simp [Option.bind] at hpop
    split at hpop <;> rename_i h₁
    contradiction
    simp at hpop
    split at hpop <;> rename_i h₂
    contradiction
    simp at hpop
    simp [← Vector.map_pop, ih h₁]
    simp [sim_link_procs_pop_val_main h₂, hpop]

/-- `popVal` on a dep channel commutes with `linkChans`. -/
private theorem sim_link_procs_pop_val_dep
  [DecidableEq χ]
  {mainChans chans' : ChanMap (LinkName χ) V}
  {name : LinkName χ}
  {depChans : Fin k' → ChanMap (LinkName χ) V}
  {i : Fin k'}
  (hpop : (depChans i).popVal name = some (val, chans')) :
    (SimRel.linkChans mainChans depChans).popVal (.dep i name) =
      some (val, SimRel.linkChans mainChans (Function.update depChans i chans'))
  := by
  simp [ChanMap.popVal] at hpop ⊢
  split at hpop <;> rename_i h₁
  contradiction
  simp at hpop
  simp [SimRel.linkChans, h₁, hpop]
  funext name
  cases name with
  | base => simp [SimRel.linkChans]
  | main => simp [SimRel.linkChans]
  | dep i' name' =>
    simp [SimRel.linkChans]
    by_cases h₁ : i = i'
    · simp [h₁]
      by_cases h₂ : name' = name
      · simp [h₂, ← h₁, ← hpop.2]
      · simp [h₂]
        split
        · simp [← h₁, ← hpop.2, h₂]
        · rfl
    · simp [Ne.symm h₁]
      split
      · rw [Function.update_of_ne (by
          intros h₂; simp [← h₂] at h₁) _ _]
      · rfl

private theorem sim_link_procs_pop_vals_dep
  [DecidableEq χ]
  {mainChans chans' : ChanMap (LinkName χ) V}
  {names : Vector (LinkName χ) n}
  {depChans : Fin k' → ChanMap (LinkName χ) V}
  {i : Fin k'}
  (hpop : (depChans i).popVals names = some (outputVals, chans')) :
  (SimRel.linkChans mainChans depChans).popVals (names.map (.dep i)) =
    some (outputVals, SimRel.linkChans mainChans (Function.update depChans i chans'))
  := by
  induction n generalizing chans' with
  | zero =>
    simp [ChanMap.popVals] at hpop ⊢
    simp [← hpop]
  | succ n' ih =>
    simp [pop_vals_unfold] at hpop ⊢
    simp [Option.bind] at hpop
    split at hpop <;> rename_i pops h₁
    contradiction
    simp at hpop
    split at hpop <;> rename_i pop h₂
    contradiction
    simp at hpop
    simp [← Vector.map_pop, ih h₁]
    have : pops.snd = Function.update depChans i pops.snd i := by simp
    rw [this] at h₂
    simp [sim_link_procs_pop_val_dep (χ := χ) h₂, hpop]

private theorem sim_link_procs_step_dep_spawn
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {s₁ : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {depOp : SigOps sigs k'}
  {depState' : (procs depOp.toFin').semantics.State}
  {inputVals : Vector V (sigs depOp.toFin).ι}
  (hsim : SimRel s₁ s₂)
  -- Assumptions of `.LinkStep.step_dep`
  (hcur : s₁.curSem = none)
  (hyield : main.semantics.HasYield s₁.mainState (.inr depOp) inputVals)
  (hstep_dep :
    (procs depOp.toFin').semantics.lts.Step
      (s₁.depStates depOp) (.input inputVals) depState') :
    ∃ s₂',
      Dataflow.Config.Step.IORestrictedStep s₂ .τ s₂' ∧
      SimRel { s₁ with
        curSem := some depOp,
        depStates := Function.update s₁.depStates depOp depState'
        : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩) } s₂'
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
      ((procs depOp.toFin').inputs.map (LinkName.dep depOp.toFin))
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
      simp [SimRel.linkChans]
      cases name with
      | base _ =>
        simp
        rw [push_vals_disjoint]
        rotate_left; simp
        simp [SimRel.linkChans]
      | main name' =>
        simp
        rw [push_vals_disjoint]
        rotate_left; simp
        simp [SimRel.linkChans]
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
            simp [SimRel.linkChans, h₁]
        · rw [push_vals_disjoint]
          rotate_left
          · simp only [Vector.mem_map]
            intros h₂
            have ⟨_, _, h₃⟩ := h₂
            simp at h₃
            omega
          simp [SimRel.linkChans, h₁]

private theorem sim_link_procs_step_dep_ret
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {s₁ : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {depOp : SigOps sigs k'}
  {depState' : (procs depOp.toFin').semantics.State}
  {mainState' : main.semantics.State}
  {inputVals : Vector V (sigs depOp.toFin).ι}
  {outputVals : Vector V (sigs depOp.toFin).ω}
  (hsim : SimRel s₁ s₂)
  -- Assumptions of `.LinkStep.step_dep`
  (hcur : s₁.curSem = some depOp)
  (hstep_dep :
    (procs depOp.toFin').semantics.lts.Step
      (s₁.depStates depOp) (.output outputVals) depState')
  (hyield :
    main.semantics.lts.Step s₁.mainState
      (Label.yield (.inr depOp) inputVals outputVals) mainState') :
    ∃ s₂',
      Dataflow.Config.Step.IORestrictedStep s₂ .τ s₂' ∧
      SimRel { s₁ with
        curSem := none,
        mainState := mainState',
        depStates := Function.update s₁.depStates depOp depState'
        : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩) } s₂'
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
  have ⟨h₁, h₂⟩ := hsim_aff.of_mem hmem_op (List.mem_of_getElem hget_op)
  subst h₁ h₂
  simp [hpop_inputs] at hpop_inputs'
  have ⟨h₁, h₂⟩ := hpop_inputs'
  subst h₁ h₂
  clear hpop_inputs'
  simp at hsim_chans
  cases hstep_dep with | step_output hpop_outputs =>
  rename_i chans'
  have ⟨idx, hidx, hget_op⟩ := List.mem_iff_getElem.mp hmem_op
  have hmem_forward_outputs :
    .forward
      ((procs depOp.toFin').outputs.map (LinkName.dep depOp.toFin))
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
        SimRel.linkChans chans₁'
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

/-- Async op interpretation is preserved by any injective map. -/
private theorem aop_interp_map_inj
  [DecidableEq χ] [InterpConsts V]
  {aop aop' : AsyncOp V}
  {k₁ k₂ : Nat}
  {inputs : Vector (LinkName χ) k₁}
  {inputVals : Vector V k₁}
  {outputs : Vector (LinkName χ) k₂}
  {outputVals : Vector V k₂}
  (f : LinkName χ → LinkName χ)
  (hinterp : aop.Interp (.mk
    allInputs allOutputs
    inputs.toList inputVals.toList
    outputs.toList outputVals.toList) aop') :
    aop.Interp
      (.mk
        (allInputs.map f)
        (allOutputs.map f)
        (inputs.map f).toList
        inputVals.toList
        (outputs.map f).toList
        outputVals.toList)
      aop'
  := by
  generalize hinputs' : inputs.toList = inputs'
  generalize hinput_vals' : inputVals.toList = inputVals'
  generalize houtputs' : outputs.toList = outputs'
  generalize houtput_vals' : outputVals.toList = outputVals'
  rw [hinputs', hinput_vals', houtputs', houtput_vals'] at hinterp
  cases hinterp with
  | interp_switch h₁ h₂ h₃ =>
    rename Bool => deciderBool
    simp [Vector.toList_map, hinputs', houtputs']
    cases deciderBool <;> simp
    · exact .interp_switch (deciderBool := false)
        (by simp [h₁]) (by simp [h₂]) (by simp [h₃])
    · exact .interp_switch (deciderBool := true)
        (by simp [h₁]) (by simp [h₂]) (by simp [h₃])
  | interp_steer_true h₁ h₂ h₃ h₄ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_steer_true (by simp [h₁]) (by simp [h₂]) h₃ h₄
  | interp_steer_false h₁ h₂ h₃ h₄ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_steer_false (by simp [h₁]) (by simp [h₂]) h₃ h₄
  | interp_merge_left h₁ h₂ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_merge_left (by simp [h₁]) (by simp [h₂])
  | interp_merge_right h₁ h₂ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_merge_right (by simp [h₁]) (by simp [h₂])
  | interp_merge_decider h₁ h₂ h₃ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_merge_decider (by simp [h₁]) (by simp [h₂]) h₃
  | interp_forward h₁ h₂ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_forward (by simp [h₁]) (by simp [h₂])
  | interp_fork h₁ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_fork (by simp [h₁])
  | interp_const h₁ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_const (by simp [h₁])
  | interp_forwardc h₁ h₂ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_forwardc (by simp [h₁]) (by simp [h₂])
  | interp_sink h₁ =>
    simp [Vector.toList_map, hinputs', houtputs']
    exact .interp_sink (by simp [h₁])

private theorem sim_link_procs_step_main
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {mainState' : main.semantics.State}
  {s₁ : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {l : Label (Op ⊕ SigOps sigs k') V m n}
  {l' : Label Op V m n}
  (hsim : SimRel s₁ s₂)
  -- Assumptions of `.LinkStep.step_main`
  (hcur : s₁.curSem = none)
  (hlabel : Semantics.MainLabelPassthrough l l')
  (hstep_main : main.semantics.lts.Step s₁.mainState l mainState') :
    ∃ s₂',
      Dataflow.Config.Step.IORestrictedStep s₂ l' s₂' ∧
      SimRel { s₁ with mainState := mainState'
      : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩) } s₂' := by
  have ⟨hsim_proc_inputs, hsim_proc_outputs, hsim_aff, hsim_proc, hsim_main, hsim_dep⟩ := hsim
  have hsim_chans := hsim_main hcur
  simp [Proc.semantics, Lts.Step] at hstep_main
  cases hstep_main with
  | step_init =>
    rename_i args
    cases hlabel
    have hstep_s₂ : Dataflow.Config.Step s₂ (.input args) _
      := Dataflow.Config.Step.step_init
    exact ⟨_, .single hstep_s₂,
      by
        and_intros
        · exact hsim_proc_inputs
        · exact hsim_proc_outputs
        · exact hsim_aff
        · simp [hsim_proc]
        · simp [hsim_chans, hsim_proc, linkProcs]
          intros
          simp [sim_link_procs_push_vals_main]
        · simp [hcur]
    ⟩
  | step_output hpop =>
    cases hlabel
    have hstep_s₂ : Dataflow.Config.Step s₂ (.output _) _
      := Dataflow.Config.Step.step_output
        (by
          simp [hsim_proc, hsim_chans, linkProcs]
          apply sim_link_procs_pop_vals_main hpop)
    exact ⟨_, .single hstep_s₂,
      by
        and_intros
        · exact hsim_proc_inputs
        · exact hsim_proc_outputs
        · exact hsim_aff
        · simp [hsim_proc]
        · simp
        · simp [hcur]
    ⟩
  | step_op hmem_op hpop =>
    cases hlabel
    rename_i chans' op inputVals outputVals inputs outputs
    have hstep_s₂ : Dataflow.Config.Step s₂ (.yield op inputVals outputVals) _
      := Dataflow.Config.Step.step_op
        (op := op)
        (inputs := inputs.map LinkName.main)
        (outputs := outputs.map LinkName.main)
        (by
          simp [hsim_proc]
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
  | step_async hi hget hinterp hpops =>
    rename_i aop aop' allInputs allOutputs inputs inputVals outputs outputVals chans' i
    cases hlabel
    have := List.flatten_update_index
      (i := i) (j := 0)
      (xs := List.map
        (linkAtomicProc sigs k' fun i => (s₁.depStates (SigOps.call i)).proc)
        s₁.mainState.proc.atoms)
      (by simp [hi]) (by simp [hget, linkAtomicProc])
      (by
        simp [hget, linkAtomicProc]
        rfl)
    have ⟨i', hget', hupdate⟩ := this
    rcases i' with ⟨i', hi'⟩
    simp at hget'
    simp [hget] at hupdate
    have hstep_s₂ : Dataflow.Config.Step s₂ _ _
      := .step_async
        (aop := aop)
        (aop' := aop')
        (allInputs := allInputs.map .main)
        (allOutputs := allOutputs.map .main)
        (inputs := inputs.map .main)
        (outputs := outputs.map .main)
        (by simp only [hsim_proc, linkProcs]; exact hi')
        (by simp [hsim_proc, linkProcs]; exact hget')
        (aop_interp_map_inj .main hinterp)
        (by
          simp [hsim_chans]
          apply sim_link_procs_pop_vals_main hpops)
    exact ⟨_, .single hstep_s₂,
      by
        and_intros
        · exact hsim_proc_inputs
        · exact hsim_proc_outputs
        · simp [Proc.AffineInrOp]
          intros
          rename_i hne hi hj hget₁ hget₂
          simp [List.getElem_set] at hget₁ hget₂
          split at hget₁ <;> split at hget₂
          any_goals contradiction
          exact hsim_aff hne hi hj hget₁ hget₂
        · simp [hsim_proc, linkProcs]
          rw [hupdate]
          congr
        · simp
          intros
          rw [sim_link_procs_push_vals_main]
        · simp [hcur]
    ⟩

private theorem sim_link_procs_step_dep
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  {s₁ : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩)}
  {s₂ : Dataflow.Config Op (LinkName χ) V m n}
  {depOp : SigOps sigs k'}
  {depState' : (procs depOp.toFin').semantics.State}
  {l : Label Op V (sigs depOp.toFin).ι (sigs depOp.toFin).ω}
  {l' : Label Op V m n}
  (hsim : SimRel s₁ s₂)
  -- Assumptions of `.LinkStep.step_dep`
  (hcur : s₁.curSem = some depOp)
  (hlabel : Semantics.DepLabelPassthrough l l')
  (hstep_dep : (procs depOp.toFin').semantics.lts.Step (s₁.depStates depOp) l depState') :
    ∃ s₂',
      Dataflow.Config.Step.IORestrictedStep s₂ l' s₂' ∧
      SimRel { s₁ with
        depStates := Function.update s₁.depStates depOp depState'
        : Semantics.LinkState main.semantics (λ op => ⟨_, (procs op.toFin').semantics⟩) } s₂'
  := by
  have ⟨hsim_proc_inputs, hsim_proc_outputs, hsim_aff, hsim_proc, hsim_main, hsim_dep⟩ := hsim
  have ⟨frame, hsim_chans⟩ := hsim_dep hcur
  simp [Proc.semantics, Lts.Step] at hstep_dep
  cases hstep_dep with
  | step_init | step_output => cases hlabel
  | step_op hmem_op hpop =>
    cases hlabel
    rename_i op inputs outputs inputVals outputVals chans'
    have hstep_s₂ : Dataflow.Config.Step s₂ (.yield op inputVals outputVals) _
      := Dataflow.Config.Step.step_op
        (op := op)
        (inputs := inputs.map (.dep depOp.toFin))
        (outputs := outputs.map (.dep depOp.toFin))
        (chans' :=
          SimRel.linkChans frame.chans'
            (Function.update (λ i => (s₁.depStates (SigOps.call i)).chans) depOp.1 chans'))
        (by
          simp [hsim_proc]
          apply List.mem_flatten_map (List.mem_of_getElem frame.get_op)
          simp [linkAtomicProc, AtomicProcs.mapChans, AtomicProc.forward]
          exists AtomicProc.op op inputs outputs)
        (by
          simp [hsim_chans]
          rw [sim_link_procs_pop_vals_dep hpop])
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
        · simp [Ne.symm hdep]
          simp [hsim_proc_inputs]
      · simp
        intros depOp'
        by_cases hdep : depOp = depOp'
        · subst hdep
          simp [hsim_proc_outputs]
        · simp [Ne.symm hdep]
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
      · simp [hs₂', hcur]
      · simp [hs₂', hcur]
        exists frame
        rw [sim_link_procs_push_vals_dep_alt]
        congr
        funext i
        simp
        by_cases h : i = depOp.1
        · rw [h]
          simp
        · simp [h]
          rw [Function.update_of_ne (by
            intros h'
            simp [← h'] at h) _ _]
  | step_async hi hget hinterp hpops =>
    rename_i aop aop' allInputs allOutputs inputs inputVals outputs outputVals chans' i
    cases hlabel
    have hget_dep := frame.get_op
    simp at hget_dep
    have := List.flatten_update_index
      (i := frame.depIdx) (j := i + 1)
      (xs := List.map
        (linkAtomicProc sigs k' fun i => (s₁.depStates (SigOps.call i)).proc)
        s₁.mainState.proc.atoms)
      (by simp) (by
        simp [hget_dep, linkAtomicProc, AtomicProcs.mapChans]
        trans
        · exact hi
        · simp)
      (by
        simp [linkAtomicProc]
        rfl)
    have ⟨i', hget', hupdate⟩ := this
    rcases i' with ⟨i', hi'⟩
    simp [hget_dep] at hget' hupdate
    have hstep_s₂ : Dataflow.Config.Step s₂ _ _
      := .step_async
        (aop := aop)
        (aop' := aop')
        (allInputs := allInputs.map (.dep depOp.toFin))
        (allOutputs := allOutputs.map (.dep depOp.toFin))
        (inputs := inputs.map (.dep depOp.toFin))
        (outputs := outputs.map (.dep depOp.toFin))
        (by simp only [hsim_proc, linkProcs]; exact hi')
        (by
          simp [hsim_proc, linkProcs]
          rw [hget']
          simp [AtomicProcs.mapChans, AtomicProc.mapChans, hi, hget])
        (aop_interp_map_inj (.dep depOp.toFin) hinterp)
        (by
          simp [hsim_chans]
          apply sim_link_procs_pop_vals_dep hpops)
    exact ⟨_, .single hstep_s₂,
      by
        and_intros
        · simp
          intros depOp'
          by_cases hdep : depOp = depOp'
          · subst hdep
            simp [hsim_proc_inputs]
          · simp [Ne.symm hdep]
            simp [hsim_proc_inputs]
        · simp
          intros depOp'
          by_cases hdep : depOp = depOp'
          · subst hdep
            simp [hsim_proc_outputs]
          · simp [Ne.symm hdep]
            simp [hsim_proc_outputs]
        · exact hsim_aff
        · simp [hsim_proc, linkProcs]
          rw [hupdate]
          congr
          apply List.ext_get
          · simp
          · simp
            intros j hj₁ hj₂
            rw [List.getElem_set]
            split <;> rename_i hij
            · subst hij
              simp [linkAtomicProc, hget_dep, AtomicProcs.mapChans,
                AtomicProc.mapChans, hi]
            · simp [linkAtomicProc]
              cases hget_j : s₁.mainState.proc.atoms[j] with
              | op op =>
                cases op with
                | inl => rfl
                | inr depOp' =>
                  have hne_dep : depOp' ≠ depOp := by
                    symm
                    exact hsim_aff hij frame.depIdx.2 hj₂ hget_dep hget_j
                  simp [hne_dep]
              | async => rfl
        · simp [hcur]
        · simp [hcur]
          exists frame
          rw [sim_link_procs_push_vals_dep_alt]
          congr
          funext i
          simp
          by_cases h : i = depOp.1
          · rw [h]
            simp
          · simp [h]
            rw [Function.update_of_ne (by
              intros h'
              simp [← h'] at h) _ _]
    ⟩

/-- Linking syntactically simulates linking semantically. -/
theorem sim_link_procs
  [Arity Op]
  [DecidableEq χ]
  [InterpConsts V]
  {sigs : Sigs k}
  {k' : Fin (k + 1)}
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {deps : PartInterp Op (SigOps sigs k') V}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (hdeps : ∀ op, deps op = ⟨_, (procs op.toFin').semantics⟩)
  (haff : main.AffineInrOp) :
    main.semantics.link deps ≲ᵣ (linkProcs sigs k' procs main).semantics
  := by
  replace hdeps :
    deps = λ op : SigOps sigs k' => ⟨_, (procs op.toFin').semantics⟩ := by
    funext op
    apply hdeps
  rw [hdeps]
  apply Lts.Similarity.intro SimRel
  constructor
  · -- SimRel holds at initial states
    simp [SimRel, Proc.semantics, Semantics.link,
      Semantics.LinkState.init, Dataflow.Config.init]
    constructor
    · exact haff
    · funext name
      simp [SimRel.linkChans, ChanMap.empty]
      cases name <;> rfl
  · -- SimRel holds after every step
    intros s₁ s₂ l s₁' hsim hstep_s₁
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

theorem sim_compile_prog.{u₁, u₂, u₃}
  {Op : Type u₁}
  {χ : Type u₂}
  {V : Type u₃}
  [Arity Op]
  [InterpConsts V]
  [DecidableEq χ]
  (sigs : Sigs k)
  (prog : Prog Op χ V sigs)
  (i : Nat)
  (hlt : i < k)
  (hwf : ∀ i, (prog i).AffineVar)
  (haff : prog.AffineInrOp) :
    (prog.semantics ⟨i, hlt⟩).2 ≲ᵣ (compileProg sigs prog ⟨i, hlt⟩).semantics
  := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases h : prog.semantics ⟨i, hlt⟩ with ⟨_, progSem⟩
    simp [Prog.semantics] at h
    have ⟨h₁, h₂⟩ := h
    subst h₁ h₂
    unfold Prog.semantics
    unfold compileProg
    simp
    apply IORestrictedSimilarity.trans
    apply sim_congr_link
    · intros j
      apply ih
      omega
    · apply IORestrictedSimilarity.trans
        (sim_compile_fn _
          (by apply hwf))
        (sim_map_chans_inj (f := LinkName.base) (by simp [Function.Injective]))
    apply sim_link_procs
    · intros op
      rfl
    · apply map_chans_preserves_aff_op
      apply compile_fn_preserves_aff_op
      apply haff

end Wavelet.Compile
