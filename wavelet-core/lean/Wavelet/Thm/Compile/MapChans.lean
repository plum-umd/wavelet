import Wavelet.Compile.MapChans

import Wavelet.Thm.Semantics.Simulation
import Wavelet.Thm.Dataflow.ChanMap
import Wavelet.Thm.Dataflow.AffineChan

/-! Simulation and other utility lemmas about `Proc.mapChans`. -/

namespace Wavelet.Dataflow

open Semantics

@[simp]
theorem map_chans_comm_inputs [Arity Op]
  (f : χ → χ') (ap : AtomicProc Op χ V) :
    (ap.mapChans f).inputs = ap.inputs.map f := by
  cases ap <;> simp [AtomicProc.mapChans, AtomicProc.inputs, Vector.toList_map]

@[simp]
theorem map_chans_comm_outputs [Arity Op]
  (f : χ → χ') (ap : AtomicProc Op χ V) :
    (ap.mapChans f).outputs = ap.outputs.map f := by
  cases ap <;> simp [AtomicProc.mapChans, AtomicProc.outputs, Vector.toList_map]

section Simulation

private def SimRel
  [Arity Op] {χ χ' : Type u}
  [DecidableEq χ] [DecidableEq χ']
  (f : χ → χ')
  (s₁ : Config Op χ V m n)
  (s₂ : Config Op χ' V m n) : Prop :=
  s₂.proc = s₁.proc.mapChans f ∧
  s₁.chans = s₂.chans ∘ f ∧
  -- No other names other than those in the image of `f`
  s₂.chans.AllNames (∃ n', f n' = ·)

theorem async_op_interp_map_chans
  [InterpConsts V]
  {aop : AsyncOp V}
  (f : χ → χ')
  (hinterp : AsyncOp.Interp aop
    (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop') :
    AsyncOp.Interp aop
      (.mk (allInputs.map f) (allOutputs.map f) (inputs.map f) inputVals (outputs.map f) outputVals)
      aop'
  := by
  cases hinterp with
  | interp_switch h₁ h₂ h₃ =>
    rename Bool => deciderBool
    cases deciderBool <;> {
      simp
      rw [← List.length_map f] at h₁ h₂
      exact .interp_switch h₁ h₂ h₃
    }
  | interp_steer_true h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_steer_true h₁ h₂ h₃ h₄
  | interp_steer_false h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_steer_false h₁ h₂ h₃ h₄
  | interp_merge_left h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    simp
    exact .interp_merge_left h₁ h₂
  | interp_merge_right h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    simp
    exact .interp_merge_right h₁ h₂
  | interp_merge_decider h₁ h₂ h₃ =>
    rw [← List.length_map f] at h₁ h₂
    simp
    exact .interp_merge_decider h₁ h₂ h₃
  | interp_forward h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_forward h₁ h₂
  | interp_fork h₁ h₂ =>
    rw [← List.length_map f] at h₁
    exact .interp_fork h₁ h₂
  | interp_order h₁ h₂ =>
    rw [← List.length_map f] at h₁
    exact .interp_order h₁ h₂
  | interp_const h₁ =>
    rw [← List.length_map f] at h₁
    exact .interp_const h₁
  | interp_forwardc h₁ h₂ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_forwardc h₁ h₂
  | interp_sink h₁ =>
    rw [← List.length_map f] at h₁
    exact .interp_sink h₁
  | interp_inv_init h₁ h₂ h₃ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_inv_init h₁ h₂ h₃
  | interp_inv_true h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_inv_true h₁ h₂ h₃ h₄
  | interp_inv_false h₁ h₂ h₃ h₄ =>
    rw [← List.length_map f] at h₁ h₂
    exact .interp_inv_false h₁ h₂ h₃ h₄

theorem sim_map_chans_inj_preserves_init
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f) :
    proc.semantics ≲ₛ[PreservesInit] (proc.mapChans f).semantics
  := by
  apply Lts.SimilaritySt.intro (SimRel f)
  · constructor
    · constructor
      · rfl
      · simp [Proc.semantics, Config.init, ChanMap.empty, ChanMap.AllNames]
    · intros s₁ s₂ l s₁' hsim hstep
      have ⟨hsim_proc, hsim_chans, hsim_emp⟩ := hsim
      cases hstep with
      | step_init =>
        exact ⟨_,
          .step_init,
          by
            and_intros
            · exact hsim_proc
            · simp [hsim_proc, hsim_chans, Proc.mapChans]
              rw [push_vals_map_chans hf]
            · simp [hsim_proc, Proc.mapChans]
              apply push_vals_preserves_all_names hsim_emp
              simp,
        ⟩
      | step_output hpop =>
        simp [hsim_chans] at hpop
        have ⟨map', heq', hpop'⟩ := pop_vals_map_chans hf hpop
        subst heq'
        exact ⟨_,
          .step_output (by
            simp [hsim_proc, Proc.mapChans]
            exact hpop'),
          by
            and_intros
            · exact hsim_proc
            · simp
            · with_reducible
              exact pop_vals_preserves_all_names hsim_emp hpop',
        ⟩
      | step_op hmem hpop =>
        simp [hsim_chans] at hmem hpop
        have ⟨_, heq', hpop'⟩ := pop_vals_map_chans hf hpop
        subst heq'
        exact ⟨_,
          .step_op
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans]
              exact ⟨_, hmem, by simp [AtomicProc.mapChans]; constructor <;> rfl⟩)
            (by exact hpop'),
          by
            and_intros
            · exact hsim_proc
            · simp
              rw [push_vals_map_chans hf]
            · with_reducible
              simp
              apply push_vals_preserves_all_names
              · exact pop_vals_preserves_all_names hsim_emp hpop'
              · simp,
        ⟩
      | step_async hi hget hinterp hpop =>
        simp [hsim_chans] at hget hpop
        have ⟨_, heq', hpop'⟩ := pop_vals_map_chans hf hpop
        subst heq'
        exact ⟨_,
          .step_async
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans]
              exact hi)
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans, hget,
                AtomicProc.mapChans]
              and_intros <;> rfl)
            (by
              have := async_op_interp_map_chans f hinterp
              simp only [← Vector.toList_map] at this
              exact this)
            (by exact hpop'),
          by
            and_intros
            · simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans,
                AtomicProc.mapChans]
            · simp
              rw [push_vals_map_chans hf]
            · with_reducible
              simp
              apply push_vals_preserves_all_names
              · exact pop_vals_preserves_all_names hsim_emp hpop'
              · simp,
        ⟩
  · intros s₁ s₂ hsim hinit
    subst hinit
    rcases s₂ with ⟨proc₂, chans₂⟩
    have ⟨hsim_proc, hsim_chans, hsim_emp⟩ := hsim
    simp [Proc.semantics, Config.init] at hsim_proc hsim_chans hsim_emp
    simp [Proc.semantics, Config.init, hsim_proc]
    funext n
    by_cases hemp : chans₂ n = []
    · simp [hemp, ChanMap.empty]
    · have ⟨n', hfn'⟩ := hsim_emp hemp
      simp [← hfn']
      have : (chans₂ ∘ f) n' = [] := by
        rw [← hsim_chans, ChanMap.empty]
      simp at this
      simp [this, ChanMap.empty]

theorem sim_map_chans_inj
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f) :
    proc.semantics ≲ₛ (proc.mapChans f).semantics
  := (sim_map_chans_inj_preserves_init hf).weaken (by simp)

/-! Variants of the lemmas above where `f` is only injective on names satisfying `P`. -/

theorem push_val_map_chans_on
  [DecidableEq χ] [DecidableEq χ']
  {map₁ : ChanMap χ V} {map₂ : ChanMap χ' V}
  {name : χ} {val : V}
  {f : χ → χ'} {P : χ → Prop}
  (hf : ∀ x y, P x → P y → f x = f y → x = y)
  (hname : P name)
  (hmap : ∀ x, P x → map₁ x = map₂ (f x)) :
    ∀ x, P x → map₁.pushVal name val x = map₂.pushVal (f name) val (f x)
  := by
  intros x hx
  by_cases h : x = name
  · subst h
    simp [ChanMap.pushVal, hmap x hx]
  · have : f x ≠ f name := λ h' => h (hf _ _ hx hname h')
    simp [ChanMap.pushVal, h, this, hmap x hx]

theorem push_vals_map_chans_on
  [DecidableEq χ] [DecidableEq χ']
  {map₁ : ChanMap χ V} {map₂ : ChanMap χ' V}
  {names : Vector χ n} {vals : Vector V n}
  {f : χ → χ'} {P : χ → Prop}
  (hf : ∀ x y, P x → P y → f x = f y → x = y)
  (hnames : ∀ name ∈ names, P name)
  (hmap : ∀ x, P x → map₁ x = map₂ (f x)) :
    ∀ x, P x → map₁.pushVals names vals x = map₂.pushVals (names.map f) vals (f x)
  := by
  induction names using Vector.back_induction
    generalizing map₁ map₂ with
  | empty =>
    intros x hx
    simp [hmap x hx]
  | push names' name ih =>
    rw [push_vals_unfold, push_vals_unfold]
    simp only [Vector.map_push, Vector.pop_push, Vector.back_push]
    apply push_val_map_chans_on hf (hnames name (by simp))
    exact ih (λ name' h => hnames name' (by simp [h])) hmap

theorem pop_val_map_chans_on
  [DecidableEq χ] [DecidableEq χ']
  {map₁ map₁' : ChanMap χ V} {map₂ : ChanMap χ' V}
  {name : χ} {val : V}
  {f : χ → χ'} {P : χ → Prop}
  (hf : ∀ x y, P x → P y → f x = f y → x = y)
  (hname : P name)
  (hmap : ∀ x, P x → map₁ x = map₂ (f x))
  (hpop : map₁.popVal name = some (val, map₁')) :
    ∃ map₂',
      map₂.popVal (f name) = some (val, map₂') ∧
      ∀ x, P x → map₁' x = map₂' (f x)
  := by
  simp only [ChanMap.popVal] at hpop
  split at hpop; contradiction
  rename_i rest heq
  simp only [Option.some.injEq, Prod.mk.injEq] at hpop
  have ⟨h₁, h₂⟩ := hpop
  subst h₁ h₂
  refine ⟨λ n => if n = f name then rest else map₂ n, ?_, ?_⟩
  · simp [ChanMap.popVal, ← hmap name hname, heq]
  · intros x hx
    by_cases h : x = name
    · subst h; simp
    · have : f x ≠ f name := λ h' => h (hf _ _ hx hname h')
      simp [h, this, hmap x hx]

theorem pop_vals_map_chans_on
  [DecidableEq χ] [DecidableEq χ']
  {map₁ map₁' : ChanMap χ V} {map₂ : ChanMap χ' V}
  {names : Vector χ n} {vals : Vector V n}
  {f : χ → χ'} {P : χ → Prop}
  (hf : ∀ x y, P x → P y → f x = f y → x = y)
  (hnames : ∀ name ∈ names, P name)
  (hmap : ∀ x, P x → map₁ x = map₂ (f x))
  (hpop : map₁.popVals names = some (vals, map₁')) :
    ∃ map₂',
      map₂.popVals (names.map f) = some (vals, map₂') ∧
      ∀ x, P x → map₁' x = map₂' (f x)
  := by
  induction names using Vector.back_induction
    generalizing map₁ map₁' map₂ with
  | empty =>
    simp only [pop_vals_zero, Option.some.injEq, Prod.mk.injEq] at hpop
    have ⟨h₁, h₂⟩ := hpop
    subst h₁ h₂
    exact ⟨map₂, by simp, hmap⟩
  | push names' name ih =>
    simp only [pop_vals_unfold, Vector.pop_push, Vector.back_push] at hpop
    simp only [Option.bind_eq_bind, Option.bind] at hpop
    split at hpop; contradiction
    rename_i res₁ heq₁
    rcases res₁ with ⟨vals', map''⟩
    simp only at hpop
    split at hpop; contradiction
    rename_i res₂ heq₂
    rcases res₂ with ⟨val, map'''⟩
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpop
    have ⟨h₁, h₂⟩ := hpop
    subst h₁ h₂
    have ⟨m₂, hpop₁, hmap₁⟩ := ih (λ name' h => hnames name' (by simp [h])) hmap heq₁
    have ⟨m₂', hpop₂, hmap₂⟩ := pop_val_map_chans_on hf (hnames name (by simp)) hmap₁ heq₂
    refine ⟨m₂', ?_, hmap₂⟩
    rw [pop_vals_unfold]
    simp [hpop₁, hpop₂]

private def SimRelOn
  [Arity Op] {χ χ' : Type u}
  [DecidableEq χ] [DecidableEq χ']
  (P : χ → Prop)
  (f : χ → χ')
  (s₁ : Config Op χ V m n)
  (s₂ : Config Op χ' V m n) : Prop :=
  s₂.proc = s₁.proc.mapChans f ∧
  (∀ x ∈ s₁.proc.inputs, P x) ∧
  (∀ x ∈ s₁.proc.outputs, P x) ∧
  (∀ ap ∈ s₁.proc.atoms, ∀ x, x ∈ ap.inputs ∨ x ∈ ap.outputs → P x) ∧
  (∀ x, P x → s₁.chans x = s₂.chans (f x)) ∧
  s₂.chans.AllNames (λ y => ∃ x, P x ∧ f x = y)

/-- Same as `sim_map_chans_inj_preserves_init`, but `f` only needs
to be injective on the channel names of `proc` (in `P`). -/
theorem sim_map_chans_inj_on_preserves_init
  {χ χ' : Type u}
  [Arity Op]
  [DecidableEq χ]
  [DecidableEq χ']
  [InterpConsts V]
  {f : χ → χ'}
  {proc : Proc Op χ V m n}
  {P : χ → Prop}
  (hinputs : ∀ x ∈ proc.inputs, P x)
  (houtputs : ∀ x ∈ proc.outputs, P x)
  (hatoms : ∀ ap ∈ proc.atoms, ∀ x, x ∈ ap.inputs ∨ x ∈ ap.outputs → P x)
  (hf : ∀ x y, P x → P y → f x = f y → x = y) :
    proc.semantics ≲ₛ[PreservesInit] (proc.mapChans f).semantics
  := by
  apply Lts.SimilaritySt.intro (SimRelOn P f)
  · constructor
    · exact ⟨rfl, hinputs, houtputs, hatoms,
        by simp [Proc.semantics, Config.init, ChanMap.empty],
        by simp [Proc.semantics, Config.init, ChanMap.empty, ChanMap.AllNames]⟩
    · intros s₁ s₂ l s₁' hsim hstep
      have ⟨hsim_proc, hsim_ins, hsim_outs, hsim_atoms, hsim_chans, hsim_names⟩ := hsim
      cases hstep with
      | step_init =>
        exact ⟨_,
          .step_init,
          by
            refine ⟨hsim_proc, hsim_ins, hsim_outs, hsim_atoms, ?_, ?_⟩
            · simp only [hsim_proc, Proc.mapChans]
              exact push_vals_map_chans_on hf hsim_ins hsim_chans
            · simp only [hsim_proc, Proc.mapChans]
              apply push_vals_preserves_all_names hsim_names
              simp only [Vector.mem_map]
              rintro _ ⟨x, hx, rfl⟩
              exact ⟨x, hsim_ins x hx, rfl⟩,
        ⟩
      | step_output hpop =>
        have ⟨_, hpop', hchans'⟩ := pop_vals_map_chans_on hf hsim_outs hsim_chans hpop
        refine ⟨_,
          .step_output (by
            simp only [hsim_proc, Proc.mapChans]
            exact hpop'),
          ?_⟩
        exact ⟨hsim_proc, hsim_ins, hsim_outs, hsim_atoms, hchans',
          pop_vals_preserves_all_names hsim_names hpop'⟩
      | step_op hmem hpop =>
        have hnames := hsim_atoms _ hmem
        have hnames_in : ∀ x ∈ _, P x :=
          λ x hx => hnames x (.inl (by simpa [AtomicProc.inputs] using hx))
        have hnames_out : ∀ x ∈ _, P x :=
          λ x hx => hnames x (.inr (by simpa [AtomicProc.outputs] using hx))
        have ⟨_, hpop', hchans'⟩ := pop_vals_map_chans_on hf hnames_in hsim_chans hpop
        refine ⟨_,
          .step_op
            (by
              simp only [hsim_proc, Proc.mapChans, AtomicProcs.mapChans, List.mem_map]
              exact ⟨_, hmem, rfl⟩)
            hpop',
          ?_⟩
        refine ⟨hsim_proc, hsim_ins, hsim_outs, hsim_atoms, ?_, ?_⟩
        · exact push_vals_map_chans_on hf hnames_out hchans'
        · apply push_vals_preserves_all_names
            (pop_vals_preserves_all_names hsim_names hpop')
          simp only [Vector.mem_map]
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨x, hnames_out x hx, rfl⟩
      | step_async hi hget hinterp hpop =>
        have hnames := hsim_atoms _ (hget ▸ List.getElem_mem hi)
        have hnames_in : ∀ x ∈ _, P x :=
          λ x hx => hnames x (.inl (by
            simp only [AtomicProc.inputs]
            exact hinterp.input_sublist.subset (by simpa using hx)))
        have hnames_out : ∀ x ∈ _, P x :=
          λ x hx => hnames x (.inr (by
            simp only [AtomicProc.outputs]
            exact hinterp.output_sublist.subset (by simpa using hx)))
        have ⟨_, hpop', hchans'⟩ := pop_vals_map_chans_on hf hnames_in hsim_chans hpop
        exact ⟨_,
          .step_async
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans]
              exact hi)
            (by
              simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans, hget,
                AtomicProc.mapChans]
              and_intros <;> rfl)
            (by
              have := async_op_interp_map_chans f hinterp
              simp only [← Vector.toList_map] at this
              exact this)
            hpop',
          by
            refine ⟨?_, hsim_ins, hsim_outs, ?_, ?_, ?_⟩
            · simp [hsim_proc, Proc.mapChans, AtomicProcs.mapChans,
                AtomicProc.mapChans]
            · intros ap hap
              rcases List.mem_or_eq_of_mem_set hap with hap | hap
              · exact hsim_atoms ap hap
              · subst hap
                exact hnames
            · exact push_vals_map_chans_on hf hnames_out hchans'
            · apply push_vals_preserves_all_names
                (pop_vals_preserves_all_names hsim_names hpop')
              simp only [Vector.mem_map]
              rintro _ ⟨x, hx, rfl⟩
              exact ⟨x, hnames_out x hx, rfl⟩,
        ⟩
  · intros s₁ s₂ hsim hinit
    subst hinit
    rcases s₂ with ⟨proc₂, chans₂⟩
    have ⟨hsim_proc, _, _, _, hsim_chans, hsim_names⟩ := hsim
    simp [Proc.semantics, Config.init] at hsim_proc hsim_chans hsim_names
    simp [Proc.semantics, Config.init, hsim_proc]
    funext y
    by_cases hemp : chans₂ y = []
    · simp [hemp, ChanMap.empty]
    · have ⟨x, hx, hfx⟩ := hsim_names hemp
      subst hfx
      have := hsim_chans x hx
      simp [ChanMap.empty] at this
      exact absurd this hemp

end Simulation

section RenameM

variable {χ χ' : Type u} [DecidableEq χ] [Hashable χ]

/-- Indices in a renaming state are distinct and less than its size. -/
private def RenameM.Inv (σ : Std.HashMap χ Nat) : Prop :=
  (∀ (x : χ) (i : Nat), σ[x]? = some i → i < σ.size) ∧
  (∀ (x y : χ) (i : Nat), σ[x]? = some i → σ[y]? = some i → x = y)

/-- `σ'` extends `σ`. -/
private def RenameM.Le (σ σ' : Std.HashMap χ Nat) : Prop :=
  ∀ (x : χ) (i : Nat), σ[x]? = some i → σ'[x]? = some i

/-- The renaming function given by a renaming state. -/
private def RenameM.toFun (renamer : Nat → χ → χ') (σ : Std.HashMap χ Nat) (x : χ) : χ' :=
  renamer (σ[x]?.getD 0) x

private theorem RenameM.mapName_spec
  {renamer : Nat → χ → χ'} {x : χ} {σ : Std.HashMap χ Nat}
  (hinv : RenameM.Inv σ) :
    RenameM.Inv ((RenameM.mapName renamer x).run σ).2 ∧
    RenameM.Le σ ((RenameM.mapName renamer x).run σ).2 ∧
    ∃ i, ((RenameM.mapName renamer x).run σ).2[x]? = some i ∧
      ((RenameM.mapName renamer x).run σ).1 = renamer i x
  := by
  have ⟨hbound, hinj⟩ := hinv
  cases h : σ[x]? with
  | some idx =>
    simp [RenameM.mapName, h]
    simp only [pure]
    exact ⟨hinv, λ _ _ h => h, idx, h, rfl⟩
  | none =>
    simp [RenameM.mapName, h]
    simp only [pure]
    have hnmem : x ∉ σ := by
      simp [Std.HashMap.mem_iff_isSome_getElem?, h]
    have hsize : (σ.insert x σ.size).size = σ.size + 1 := by
      simp [Std.HashMap.size_insert, hnmem]
    have hget : ∀ y, (σ.insert x σ.size)[y]? = if x = y then some σ.size else σ[y]? := by
      intro y
      simp [Std.HashMap.getElem?_insert]
    refine ⟨⟨?_, ?_⟩, ?_, σ.size, by simp, rfl⟩
    · intros y i hy
      rw [hget] at hy
      rw [hsize]
      split at hy
      · simp at hy
        omega
      · have := hbound y i hy
        omega
    · intros y z i hy hz
      rw [hget] at hy hz
      split at hy <;> split at hz
      · subst_vars
        rfl
      · simp at hy
        subst hy
        have := hbound z _ hz
        omega
      · simp at hz
        subst hz
        have := hbound y _ hy
        omega
      · exact hinj y z i hy hz
    · intros y i hy
      rw [hget]
      have : x ≠ y := by
        rintro rfl
        simp [h] at hy
      simp [this, hy]

private theorem RenameM.run_bind₂
  {α β γ : Type u}
  (x : RenameM χ α) (y : RenameM χ β) (f : α → β → γ) (σ : Std.HashMap χ Nat) :
    (do let a ← x; let b ← y; pure (f a b) : RenameM χ γ).run σ =
      (f (x.run σ).1 (y.run (x.run σ).2).1, (y.run (x.run σ).2).2)
  := rfl

private theorem RenameM.run'_bind₃
  {α β γ δ : Type u}
  (x : RenameM χ α) (y : RenameM χ β) (z : RenameM χ γ) (f : α → β → γ → δ)
  (σ : Std.HashMap χ Nat) :
    (do let a ← x; let b ← y; let c ← z; pure (f a b c) : RenameM χ δ).run' σ =
      f (x.run σ).1 (y.run (x.run σ).2).1 (z.run (y.run (x.run σ).2).2).1
  := rfl

private theorem RenameM.mapM_cons_run
  {α : Type v} {β : Type u}
  (g : α → RenameM χ β) (a : α) (xs : List α) (σ : Std.HashMap χ Nat) :
    ((a :: xs).mapM g).run σ =
      (((g a).run σ).1 :: ((xs.mapM g).run ((g a).run σ).2).1,
        ((xs.mapM g).run ((g a).run σ).2).2)
  := by
  rw [List.mapM_cons]
  rfl

private theorem RenameM.vector_mapM_run
  {α : Type v} {β : Type u}
  (g : α → RenameM χ β) (xs : Vector α k) (σ : Std.HashMap χ Nat) :
    ((xs.mapM g).run σ).1.toList = ((xs.toList.mapM g).run σ).1 ∧
    ((xs.mapM g).run σ).2 = ((xs.toList.mapM g).run σ).2
  := by
  have h : Vector.toList <$> xs.mapM g = xs.toList.mapM g := by
    show Vector.toList <$> xs.mapM g = List.mapM g xs.toArray.toList
    rw [← Array.toList_mapM, ← Vector.toArray_mapM, Functor.map_map]
    rfl
  have h' := congrArg (λ c => StateT.run c σ) h
  simp only [StateT.run_map] at h'
  rw [← h']
  exact ⟨rfl, rfl⟩

private theorem RenameM.Le.trans {σ₁ σ₂ σ₃ : Std.HashMap χ Nat}
  (h₁ : RenameM.Le σ₁ σ₂) (h₂ : RenameM.Le σ₂ σ₃) : RenameM.Le σ₁ σ₃ :=
  λ x i h => h₂ x i (h₁ x i h)

private theorem RenameM.toFun_le
  {renamer : Nat → χ → χ'} {σ σ' : Std.HashMap χ Nat} {x : χ} {i : Nat}
  (hle : RenameM.Le σ σ') (hx : σ[x]? = some i) :
    RenameM.toFun renamer σ' x = RenameM.toFun renamer σ x
  := by simp [RenameM.toFun, hx, hle x i hx]

private theorem RenameM.list_map_toFun_le
  {renamer : Nat → χ → χ'} {σ σ' : Std.HashMap χ Nat} {xs : List χ}
  (hle : RenameM.Le σ σ') (hxs : ∀ x ∈ xs, ∃ i, σ[x]? = some i) :
    xs.map (RenameM.toFun renamer σ') = xs.map (RenameM.toFun renamer σ)
  := by
  apply List.map_congr_left
  intros x hx
  have ⟨i, hi⟩ := hxs x hx
  exact RenameM.toFun_le hle hi

private theorem RenameM.vector_map_toFun_le
  {renamer : Nat → χ → χ'} {σ σ' : Std.HashMap χ Nat} {xs : Vector χ k}
  (hle : RenameM.Le σ σ') (hxs : ∀ x ∈ xs, ∃ i, σ[x]? = some i) :
    xs.map (RenameM.toFun renamer σ') = xs.map (RenameM.toFun renamer σ)
  := by
  apply Vector.toList_inj.mp
  simp only [Vector.toList_map]
  exact RenameM.list_map_toFun_le hle (λ x hx => hxs x (Vector.mem_toList_iff.mp hx))

/-- Specification of `List.mapM` in `RenameM` from one for each element. -/
private theorem RenameM.mapM_spec
  {α : Type v} {β : Type u}
  {g : α → RenameM χ β}
  {G : Std.HashMap χ Nat → α → β}
  {Names : α → χ → Prop}
  (hg : ∀ a σ, RenameM.Inv σ →
    RenameM.Inv ((g a).run σ).2 ∧
    RenameM.Le σ ((g a).run σ).2 ∧
    (∀ x, Names a x → ∃ i, ((g a).run σ).2[x]? = some i) ∧
    ((g a).run σ).1 = G ((g a).run σ).2 a)
  (hG : ∀ a σ σ', RenameM.Le σ σ' →
    (∀ x, Names a x → ∃ i, σ[x]? = some i) → G σ' a = G σ a) :
  ∀ (xs : List α) (σ : Std.HashMap χ Nat), RenameM.Inv σ →
    RenameM.Inv ((xs.mapM g).run σ).2 ∧
    RenameM.Le σ ((xs.mapM g).run σ).2 ∧
    (∀ a ∈ xs, ∀ x, Names a x → ∃ i, ((xs.mapM g).run σ).2[x]? = some i) ∧
    ((xs.mapM g).run σ).1 = xs.map (G ((xs.mapM g).run σ).2)
  | [], σ, hinv => ⟨hinv, λ _ _ h => h, by simp, rfl⟩
  | a :: xs, σ, hinv => by
    rw [RenameM.mapM_cons_run]
    have ⟨hinv₁, hle₁, hnames₁, heq₁⟩ := hg a σ hinv
    have ⟨hinv₂, hle₂, hnames₂, heq₂⟩ := RenameM.mapM_spec hg hG xs _ hinv₁
    refine ⟨hinv₂, hle₁.trans hle₂, ?_, ?_⟩
    · intros a' ha' x hx
      rcases List.mem_cons.mp ha' with rfl | ha'
      · have ⟨i, hi⟩ := hnames₁ x hx
        exact ⟨i, hle₂ x i hi⟩
      · exact hnames₂ a' ha' x hx
    · rw [List.map_cons, ← heq₂, heq₁, hG a _ _ hle₂ hnames₁]

private theorem RenameM.mapM_mapName_spec
  {renamer : Nat → χ → χ'} (xs : List χ) {σ : Std.HashMap χ Nat}
  (hinv : RenameM.Inv σ) :
    RenameM.Inv ((xs.mapM (RenameM.mapName renamer)).run σ).2 ∧
    RenameM.Le σ ((xs.mapM (RenameM.mapName renamer)).run σ).2 ∧
    (∀ x ∈ xs, ∃ i, ((xs.mapM (RenameM.mapName renamer)).run σ).2[x]? = some i) ∧
    ((xs.mapM (RenameM.mapName renamer)).run σ).1 =
      xs.map (RenameM.toFun renamer ((xs.mapM (RenameM.mapName renamer)).run σ).2)
  := by
  have ⟨h₁, h₂, h₃, h₄⟩ := RenameM.mapM_spec
    (g := RenameM.mapName renamer)
    (G := RenameM.toFun renamer)
    (Names := λ a x => x = a)
    (λ a σ hinv => by
      have ⟨h₁, h₂, i, h₃, h₄⟩ := RenameM.mapName_spec (renamer := renamer) (x := a) hinv
      exact ⟨h₁, h₂, λ x hx => by subst hx; exact ⟨i, h₃⟩, by simp [h₄, RenameM.toFun, h₃]⟩)
    (λ a σ σ' hle hnames => by
      have ⟨i, hi⟩ := hnames a rfl
      exact RenameM.toFun_le hle hi)
    xs σ hinv
  exact ⟨h₁, h₂, λ x hx => h₃ x hx x rfl, h₄⟩

private theorem RenameM.vector_mapM_mapName_spec
  {renamer : Nat → χ → χ'} (xs : Vector χ k) {σ : Std.HashMap χ Nat}
  (hinv : RenameM.Inv σ) :
    RenameM.Inv ((xs.mapM (RenameM.mapName renamer)).run σ).2 ∧
    RenameM.Le σ ((xs.mapM (RenameM.mapName renamer)).run σ).2 ∧
    (∀ x ∈ xs, ∃ i, ((xs.mapM (RenameM.mapName renamer)).run σ).2[x]? = some i) ∧
    ((xs.mapM (RenameM.mapName renamer)).run σ).1 =
      xs.map (RenameM.toFun renamer ((xs.mapM (RenameM.mapName renamer)).run σ).2)
  := by
  have ⟨hl₁, hl₂⟩ := RenameM.vector_mapM_run (RenameM.mapName renamer) xs σ
  have ⟨h₁, h₂, h₃, h₄⟩ := RenameM.mapM_mapName_spec (renamer := renamer) xs.toList hinv
  rw [hl₂]
  refine ⟨h₁, h₂, λ x hx => h₃ x (Vector.mem_toList_iff.mpr hx), ?_⟩
  apply Vector.toList_inj.mp
  rw [hl₁, h₄, Vector.toList_map]

end RenameM

section Rename

private theorem AtomicProc.mapChans_toFun_le
  [Arity Op] [DecidableEq χ] [Hashable χ]
  {renamer : Nat → χ → χ'} {σ σ' : Std.HashMap χ Nat} {ap : AtomicProc Op χ V}
  (hle : RenameM.Le σ σ')
  (hnames : ∀ x, x ∈ ap.inputs ∨ x ∈ ap.outputs → ∃ i, σ[x]? = some i) :
    ap.mapChans (RenameM.toFun renamer σ') = ap.mapChans (RenameM.toFun renamer σ)
  := by
  cases ap with
  | op o inputs outputs =>
    simp only [AtomicProc.inputs, AtomicProc.outputs, Vector.mem_toList_iff] at hnames
    simp only [AtomicProc.mapChans]
    rw [RenameM.vector_map_toFun_le hle (λ x hx => hnames x (.inl hx)),
      RenameM.vector_map_toFun_le hle (λ x hx => hnames x (.inr hx))]
  | async aop inputs outputs =>
    simp only [AtomicProc.inputs, AtomicProc.outputs] at hnames
    simp only [AtomicProc.mapChans]
    rw [RenameM.list_map_toFun_le hle (λ x hx => hnames x (.inl hx)),
      RenameM.list_map_toFun_le hle (λ x hx => hnames x (.inr hx))]

private theorem AtomicProc.renameChansM_spec
  [Arity Op] [DecidableEq χ] [Hashable χ]
  {renamer : Nat → χ → χ'} (ap : AtomicProc Op χ V) {σ : Std.HashMap χ Nat}
  (hinv : RenameM.Inv σ) :
    RenameM.Inv ((ap.renameChansM renamer).run σ).2 ∧
    RenameM.Le σ ((ap.renameChansM renamer).run σ).2 ∧
    (∀ x, x ∈ ap.inputs ∨ x ∈ ap.outputs →
      ∃ i, ((ap.renameChansM renamer).run σ).2[x]? = some i) ∧
    ((ap.renameChansM renamer).run σ).1 =
      ap.mapChans (RenameM.toFun renamer ((ap.renameChansM renamer).run σ).2)
  := by
  cases ap with
  | op o inputs outputs =>
    simp only [AtomicProc.renameChansM, RenameM.run_bind₂,
      AtomicProc.inputs, AtomicProc.outputs, Vector.mem_toList_iff]
    have ⟨h₁, h₂, h₃, h₄⟩ := RenameM.vector_mapM_mapName_spec (renamer := renamer) inputs hinv
    have ⟨h₁', h₂', h₃', h₄'⟩ := RenameM.vector_mapM_mapName_spec (renamer := renamer) outputs h₁
    refine ⟨h₁', h₂.trans h₂', ?_, ?_⟩
    · rintro x (hx | hx)
      · have ⟨i, hi⟩ := h₃ x hx
        exact ⟨i, h₂' x i hi⟩
      · exact h₃' x hx
    · simp only [AtomicProc.mapChans]
      rw [h₄, h₄', RenameM.vector_map_toFun_le h₂' h₃]
  | async aop inputs outputs =>
    simp only [AtomicProc.renameChansM, RenameM.run_bind₂,
      AtomicProc.inputs, AtomicProc.outputs]
    have ⟨h₁, h₂, h₃, h₄⟩ := RenameM.mapM_mapName_spec (renamer := renamer) inputs hinv
    have ⟨h₁', h₂', h₃', h₄'⟩ := RenameM.mapM_mapName_spec (renamer := renamer) outputs h₁
    refine ⟨h₁', h₂.trans h₂', ?_, ?_⟩
    · rintro x (hx | hx)
      · have ⟨i, hi⟩ := h₃ x hx
        exact ⟨i, h₂' x i hi⟩
      · exact h₃' x hx
    · simp only [AtomicProc.mapChans]
      rw [h₄, h₄', RenameM.list_map_toFun_le h₂' h₃]

/-- `Proc.renameChans` is a `Proc.mapChans` given by a valid renaming state. -/
private theorem Proc.renameChans_spec
  [Arity Op] [DecidableEq χ] [Hashable χ]
  {renamer : Nat → χ → χ'} (proc : Proc Op χ V m n) :
    ∃ σ : Std.HashMap χ Nat, RenameM.Inv σ ∧
      (∀ x ∈ proc.inputs, ∃ i, σ[x]? = some i) ∧
      (∀ x ∈ proc.outputs, ∃ i, σ[x]? = some i) ∧
      (∀ ap ∈ proc.atoms, ∀ x, x ∈ ap.inputs ∨ x ∈ ap.outputs → ∃ i, σ[x]? = some i) ∧
      proc.renameChans renamer = proc.mapChans (RenameM.toFun renamer σ)
  := by
  have hinv₀ : RenameM.Inv (∅ : Std.HashMap χ Nat) := ⟨by simp, by simp⟩
  have ⟨h₁, h₂, h₃, h₄⟩ :=
    RenameM.vector_mapM_mapName_spec (renamer := renamer) proc.inputs hinv₀
  have ⟨h₁', h₂', h₃', h₄'⟩ :=
    RenameM.vector_mapM_mapName_spec (renamer := renamer) proc.outputs h₁
  have ⟨h₁'', h₂'', h₃'', h₄''⟩ := RenameM.mapM_spec
    (g := AtomicProc.renameChansM renamer)
    (G := λ σ ap => ap.mapChans (RenameM.toFun renamer σ))
    (Names := λ ap x => x ∈ ap.inputs ∨ x ∈ ap.outputs)
    (λ ap _ hinv => AtomicProc.renameChansM_spec ap hinv)
    (λ _ _ _ hle hnames => AtomicProc.mapChans_toFun_le hle hnames)
    proc.atoms _ h₁'
  refine ⟨_, h₁'', ?_, ?_, h₃'', ?_⟩
  · intros x hx
    have ⟨i, hi⟩ := h₃ x hx
    exact ⟨i, h₂'' x i (h₂' x i hi)⟩
  · intros x hx
    have ⟨i, hi⟩ := h₃' x hx
    exact ⟨i, h₂'' x i hi⟩
  · simp only [Proc.renameChans, Proc.renameChansM, AtomicProcs.renameChansM,
      RenameM.run'_bind₃, Proc.mapChans, AtomicProcs.mapChans]
    rw [h₄, h₄', h₄'', RenameM.vector_map_toFun_le (h₂'.trans h₂'') h₃,
      RenameM.vector_map_toFun_le h₂'' h₃']

/-- Renaming channels is a simulation, as long as `renamer`
does not map different indices to the same name. -/
theorem sim_rename_chans_preserves_init
  [Arity Op]
  [DecidableEq χ] [Hashable χ]
  [DecidableEq χ']
  [InterpConsts V]
  {renamer : Nat → χ → χ'}
  {proc : Proc Op χ V m n}
  (hrenamer : ∀ i j x y, renamer i x = renamer j y → i = j) :
    proc.semantics ≲ₛ[PreservesInit] (proc.renameChans renamer).semantics
  := by
  have ⟨σ, ⟨_, hinj⟩, hins, houts, hatoms, heq⟩ := Proc.renameChans_spec (renamer := renamer) proc
  rw [heq]
  apply sim_map_chans_inj_on_preserves_init (P := λ x => ∃ i, σ[x]? = some i) hins houts hatoms
  rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
  simp only [RenameM.toFun, hx, hy, Option.getD_some] at hxy
  have := hrenamer _ _ _ _ hxy
  subst this
  exact hinj x y i hx hy

theorem sim_rename_chans
  [Arity Op]
  [DecidableEq χ] [Hashable χ]
  [DecidableEq χ']
  [InterpConsts V]
  {renamer : Nat → χ → χ'}
  {proc : Proc Op χ V m n}
  (hrenamer : ∀ i j x y, renamer i x = renamer j y → i = j) :
    proc.semantics ≲ₛ (proc.renameChans renamer).semantics
  := (sim_rename_chans_preserves_init hrenamer).weaken (by simp)

end Rename

section Affineness

variable {χ χ' : Type u} {Op : Type v} {V : Type w} {m n : Nat}
variable {f : χ → χ'}

theorem map_chans_preserves_aff_var
  [Arity Op]
  {proc : Proc Op χ V m n}
  (hf : Function.Injective f)
  (haff : proc.AffineChan) :
    (proc.mapChans f).AffineChan
  := by
  obtain ⟨h_in, h_out, ⟨h_atom_nodup, h_atom_pw⟩, h_ao_di, h_ai_do⟩ := haff
  simp only [Proc.AffineChan, Proc.mapChans, AtomicProcs.AffineChan]
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Vector.toList_map]; exact h_in.map hf
  · rw [Vector.toList_map]; exact h_out.map hf
  · intro ap hap
    simp [AtomicProcs.mapChans] at hap
    obtain ⟨ap', hap', rfl⟩ := hap
    constructor
    · simp; exact (h_atom_nodup ap' hap').1.map hf
    · simp; exact (h_atom_nodup ap' hap').2.map hf
  · apply List.Pairwise.map _ _ h_atom_pw
    intro a b ⟨hdi, hdo⟩
    constructor
    · simp; exact hdi.map hf
    · simp; exact hdo.map hf
  · intro ap hap
    simp [AtomicProcs.mapChans] at hap
    obtain ⟨ap', hap', rfl⟩ := hap
    rw [map_chans_comm_outputs, Vector.toList_map]
    exact (h_ao_di ap' hap').map hf
  · intro ap hap
    simp [AtomicProcs.mapChans] at hap
    obtain ⟨ap', hap', rfl⟩ := hap
    simp [Vector.toList_map]
    exact (h_ai_do ap' hap').map hf

end Affineness

end Wavelet.Dataflow
