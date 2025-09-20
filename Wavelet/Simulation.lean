import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

import Wavelet.Op
import Wavelet.Seq
import Wavelet.Dataflow
import Wavelet.Compile
import Wavelet.Lemmas

open Wavelet.Op

universe u
variable (Op : Type u) (χ : Type u) (V S)
variable [instArity : Arity Op] [DecidableEq χ] [instInterp : Interp Op V S]

namespace Wavelet.Simulation

open Op Seq Dataflow Compile

/-- Defines refinement of two transition systems in general. -/
def Refines
  {T : Type v} {S : Type w}
  (c₁ : T) (c₂ : S)
  (R : T → S → Prop)
  (Step₁ : T → T → Prop)
  (Step₂ : S → S → Prop) :=
  R c₁ c₂ ∧
  (∀ c₁ c₂ c₁',
    R c₁ c₂ →
    Step₁ c₁ c₁' →
    ∃ c₂', Step₂ c₂ c₂' ∧ R c₁' c₂')

/-- Specific case for a Seq config to refine a dataflow config. -/
def SeqRefinesDataflow
  [DecidableEq χ₁] [DecidableEq χ₂]
  (c₁ : Seq.Config Op χ₁ V S m n)
  (c₂ : Dataflow.Config Op χ₂ V S m n)
  (R : Seq.Config Op χ₁ V S m n → Dataflow.Config Op χ₂ V S m n → Prop) : Prop :=
  Refines c₁ c₂ R (Config.Step Op χ₁ V S) (Config.StepPlus Op χ₂ V S)

def SimR.varsToChans
  (ec : Seq.Config Op χ V S m n) : ChanMap (ChanName χ) V :=
  λ name =>
    match name with
    | .var v pathConds =>
      if pathConds = ec.pathConds then
        if let some val := ec.vars.getVar _ _ v then
          [val]
        else []
      else []
    | .merge_cond v =>
      if (true, v) ∈ ec.pathConds then
        [instInterp.trueVal]
      else if (false, v) ∈ ec.pathConds then
        [instInterp.falseVal]
      else []
    | .final_dest i =>
      -- Corresponding final return values
      if let .ret vals := ec.expr then
        if _ : i < n then [vals[i]]
        else []
      else []
    | _ => []

def SimR
  (hnz : m > 0 ∧ n > 0)
  (ec : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n) : Prop :=
  ec.state = pc.state ∧
  ∃ (rest : AtomicProcs Op (ChanName χ) V)
    (carryInLoop : Bool)
    (ctxLeft ctxCurrent ctxRight : AtomicProcs Op (ChanName χ) V),
    -- Some invariants about the "shape" of the processes
    pc.proc.atoms = compileFn.initCarry _ _ _ ec.fn carryInLoop :: rest ∧
    (compileFn Op χ V S hnz ec.fn).atoms = compileFn.initCarry _ _ _ ec.fn false :: rest ∧
    rest = ctxLeft ++ ctxCurrent ++ ctxRight ∧
    (∀ i, (h : i < ec.pathConds.length) →
      compileExpr.brMerge _ _ _ m n (ec.pathConds[i]'h).2 (ec.pathConds.drop i) ∈ pc.proc.atoms) ∧
    (∀ vals, ec.expr = .ret vals → ¬ carryInLoop ∧ ctxCurrent = [] ∧ ctxRight = []) ∧
    (∀ expr, ec.expr = .cont expr → carryInLoop ∧
      expr.WellFormed _ _ ec.definedVars ∧
      compileExpr Op χ V S hnz ec.definedVars ec.pathConds expr = ctxCurrent) ∧
    -- Some invariants about the correspondence between variables and channels
    pc.chans = SimR.varsToChans _ _ _ _ ec ∧
    (∀ var, var ∈ ec.definedVars ↔ ∃ val, ec.vars.getVar _ _ var = some val) ∧
    (∀ b var pathConds, (b, .var var pathConds) ∈ ec.pathConds →
      pathConds.length < ec.pathConds.length)

theorem push_vars_lookup_diff
  {map : ChanMap χ V}
  (hdiff : ∀ v ∈ names, v ≠ name) :
  map.pushVals _ _ names vals name = map name := sorry

theorem push_vars_lookup_singleton
  {map : ChanMap χ V}
  {names : Vector χ n}
  (i : Fin n)
  (hempty : map names[i] = [])
  (hdisj : names.toList.Nodup)
  (hval : val = vals[i])
  (hname : name = names[i]) :
  map.pushVals _ _ names vals name = [val] := sorry

theorem push_var_lookup_singleton
  {map : ChanMap χ V}
  (hempty : map name = []) :
  map.pushVal _ _ name val name = [val] := sorry

theorem pop_vars_lookup_diff
  {map : ChanMap χ V}
  (hpop : map.popVals _ _ names = some (vals, map'))
  (hdiff : ∀ v ∈ names, v ≠ name) :
  map' name = map name := sorry

theorem pop_var_lookup_diff
  {map : ChanMap χ V}
  (hpop : map.popVal _ _ name' = some (val, map'))
  (hdiff : name' ≠ name) :
  map' name = map name := sorry

theorem pop_var_lookup_singleton
  {map : ChanMap χ V}
  (hpop : map.popVal _ _ name = some (val, map'))
  (hsingleton : map name = [val]) :
  map' name = [] := sorry

theorem sim_step_br
  {cond}
  (hnz : m > 0 ∧ n > 0)
  (ec ec' : Seq.Config Op χ V S m n)
  (pc : Dataflow.Config Op (ChanName χ) V S m n)
  (hsim : SimR _ _ _ _ hnz ec pc)
  (hstep : Config.Step Op χ V S ec ec')
  (hbr : ec.expr = .cont (.br cond left right)) :
  ∃ pc',
    Config.StepPlus Op (ChanName χ) V S pc pc' ∧
    SimR _ _ _ _ hnz ec' pc' := by
  have ⟨
    heq_state,
    ⟨
      rest, carryInLoop, ctxLeft, ctxCurrent, ctxRight,
      hatoms,
      hcomp_fn,
      hrest,
      hmerges,
      hret,
      hcont,
      hlive_vars,
      hdefined_vars,
      hpath_conds_order,
    ⟩,
  ⟩ := hsim
  have ⟨hcarryInLoop, hwf_expr, hcurrent⟩ := hcont (.br cond left right) hbr
  simp [compileExpr] at hcurrent
  -- Deduce some facts from `hstep`
  cases hstep with
  | step_ret hexpr => simp [hbr] at hexpr
  | step_tail hexpr => simp [hbr] at hexpr
  | step_op hexpr => simp [hbr] at hexpr
  | step_br hexpr hcond =>
    rename_i condVal _ _ cond'
    simp [hbr] at hexpr
    have heq_cond' := hexpr.1; subst heq_cond'
    have heq_left' := hexpr.2.1; subst heq_left'
    have heq_right' := hexpr.2.2; subst heq_right'
    -- Some abbreviations
    generalize hcondName :
      compileExpr.varName χ ec.pathConds cond = condName
    simp only [hcondName] at hcurrent
    simp only [compileExpr.varName] at hcondName
    generalize hleftConds : (true, condName) :: ec.pathConds = leftConds
    generalize hrightConds : (false, condName) :: ec.pathConds = rightConds
    simp only [hleftConds, hrightConds] at hcurrent
    generalize hcondValInterp :
      Interp.asBool Op S condVal = condValBool
    generalize hleftComp :
      compileExpr Op χ V S hnz (ec.definedVars.erase cond) leftConds left = leftComp
    generalize hrightComp :
      compileExpr Op χ V S hnz (ec.definedVars.erase cond) rightConds right = rightComp
    simp only [hleftComp, hrightComp] at hcurrent
    -- Step 1: Pop `cond` and run the first `fork`.
    have hcondVal : pc.chans condName = [condVal]
    := by simp [hlive_vars, SimR.varsToChans, hcond, ← hcondName]
    have ⟨chans₁, hchans₁⟩ :
      ∃ chans₁, pc.chans.popVal _ _ condName = some (condVal, chans₁)
    := by simp [ChanMap.popVal, hlive_vars, SimR.varsToChans, hcond, ← hcondName]
    have hmem_fork :
      .fork condName #v[.switch_cond condName, .merge_cond condName] ∈ pc.proc.atoms
    := by grind
    generalize hpc₁ :
      { pc with
        chans := .pushVals _ _
          #v[.switch_cond condName, .merge_cond condName]
          (Vector.replicate 2 condVal)
          chans₁,
        : Dataflow.Config _ _ _ _ _ _ } = pc₁
    have hstep₁ :
      Dataflow.Config.Step _ _ _ _ pc pc₁
    := by
      apply step_eq
      apply Dataflow.Config.Step.step_fork hmem_fork hchans₁
      simp [← hpc₁]
    -- Step 2: Run the switch
    have hmem_switch :
      .switch (.switch_cond condName)
        (compileExpr.allVars χ ec.definedVars ec.pathConds)
        (compileExpr.allVars χ ec.definedVars leftConds)
        (compileExpr.allVars χ ec.definedVars rightConds)
      ∈ pc₁.proc.atoms
    := by grind
    have ⟨chans₂, hchans₂⟩ :
      ∃ chans₂, pc₁.chans.popVal _ _ (.switch_cond condName) = some (condVal, chans₂)
    := sorry
    have ⟨inputVals, chans₃, hchans₃⟩ :
      ∃ inputVals chans₃,
        chans₂.popVals _ _
          (compileExpr.allVars χ ec.definedVars ec.pathConds) =
          some (inputVals, chans₃)
    := sorry
    generalize hpc₂ :
      { pc with
        chans := ChanMap.pushVals (ChanName χ) V
          (compileExpr.allVars χ ec.definedVars
            (if condValBool then leftConds else rightConds))
          inputVals chans₃
      } = pc₂
    have hstep₂ :
      Dataflow.Config.Step _ _ _ _ pc₁ pc₂
    := by
      apply step_eq
      apply Dataflow.Config.Step.step_switch hmem_switch hchans₂ hchans₃
      simp [← hpc₁, ← hpc₂, ← hcondValInterp]
      split <;> simp
    -- Prove the preservation of invariants
    have hsteps : Dataflow.Config.StepPlus _ _ _ _ pc pc₂
    := by
      apply Relation.TransGen.trans
      apply Relation.TransGen.single hstep₁
      apply Relation.TransGen.single hstep₂
    exists pc₂
    simp only [hsteps, true_and]
    and_intros
    · simp [← hpc₂, heq_state]
    · exists rest, carryInLoop
      exists -- ctxLeft
        if condValBool then
          ctxLeft ++ [
            .fork condName #v[.switch_cond condName, .merge_cond condName],
            .switch (.switch_cond condName)
              (compileExpr.allVars χ ec.definedVars ec.pathConds)
              (compileExpr.allVars χ ec.definedVars leftConds)
              (compileExpr.allVars χ ec.definedVars rightConds)
          ]
        else
          ctxLeft ++ [
            .fork condName #v[.switch_cond condName, .merge_cond condName],
            .switch (.switch_cond condName)
              (compileExpr.allVars χ ec.definedVars ec.pathConds)
              (compileExpr.allVars χ ec.definedVars leftConds)
              (compileExpr.allVars χ ec.definedVars rightConds)
          ] ++ compileExpr Op χ V S hnz (ec.definedVars.erase cond) leftConds left
      exists -- ctxCurrent
        if condValBool then leftComp else rightComp
      exists -- ctxRight
        if condValBool then
          rightComp ++ [compileExpr.brMerge Op χ V m n condName ec.pathConds] ++ ctxRight
        else
          [compileExpr.brMerge Op χ V m n condName ec.pathConds] ++ ctxRight
      and_intros
      · grind only
      · grind only
      · grind only [List.length_cons, =_ List.cons_append, = List.append_assoc, List.length_nil,
          Array.size_empty, = Vector.toArray_empty, List.nil_append, Vector.replicate_zero,
          List.append_nil, List.eq_or_mem_of_mem_cons, = List.cons_append, Vector.replicate_succ,
          List.mem_cons_of_mem, =_ List.append_assoc, List.mem_cons_self,
          → List.eq_nil_of_append_eq_nil, List.size_toArray, List.mem_append, cases Or]
      · simp
        -- TODO: prove after checking that this invariant is enough for .ret
        sorry
      · split <;> simp
      · simp [hcarryInLoop]
        intros expr hcont'
        cases hwf_expr with | wf_br hwf_left hwf_right =>
        grind only [List.length_cons, =_ List.cons_append, = List.append_assoc, List.length_nil,
          Array.size_empty, = Vector.toArray_empty, List.nil_append, Vector.replicate_zero,
          List.eq_or_mem_of_mem_cons, = List.cons_append, Vector.replicate_succ,
          List.mem_cons_of_mem, =_ List.append_assoc, List.mem_cons_self,
          → List.eq_nil_of_append_eq_nil, List.size_toArray, List.mem_append, cases Or]
      · funext name
        simp only [← hpc₂, SimR.varsToChans]
        cases name with
        | var v pathConds =>
          simp

          sorry
        | merge_cond name =>
          cases hname : condName == name
          simp
          all_goals
            simp at hname
            split -- split on `condValBool`
            all_goals
              rename_i hcondValBool
              simp [hcondValBool]
          · rw [push_vars_lookup_diff]
            · rw [pop_vars_lookup_diff _ _ hchans₃]
              · rw [pop_var_lookup_diff _ _ hchans₂]
                · simp only [← hpc₁]
                  rw [push_vars_lookup_diff]
                  · rw [pop_var_lookup_diff _ _ hchans₁]
                    · simp only [← hcondName] at hname
                      have : name ≠ ChanName.var cond ec.pathConds := by
                        intros h; exact hname (h.symm)
                      simp [hlive_vars, SimR.varsToChans, this]
                    · simp [← hcondName]
                  · simp [hname]
                · simp
              · simp [compileExpr.allVars]
            · simp [compileExpr.allVars]
          -- NOTE: same as above, simplify...
          · rw [push_vars_lookup_diff]
            · rw [pop_vars_lookup_diff _ _ hchans₃]
              · rw [pop_var_lookup_diff _ _ hchans₂]
                · simp only [← hpc₁]
                  rw [push_vars_lookup_diff]
                  · rw [pop_var_lookup_diff _ _ hchans₁]
                    · simp only [← hcondName] at hname
                      have : name ≠ ChanName.var cond ec.pathConds := by
                        intros h; exact hname (h.symm)
                      simp [hlive_vars, SimR.varsToChans, this]
                    · simp [← hcondName]
                  · simp [hname]
                · simp
              · simp [compileExpr.allVars]
            · simp [compileExpr.allVars]
          · simp only [← hcondName] at hname
            simp [← hname]
            rw [push_vars_lookup_diff]
            · rw [pop_vars_lookup_diff _ _ hchans₃]
              · rw [pop_var_lookup_diff _ _ hchans₂]
                · simp only [← hpc₁]
                  rw [push_vars_lookup_singleton _ _ 1]
                  · simp
                    rw [pop_var_lookup_diff _ _ hchans₁]
                    · simp only [hlive_vars, SimR.varsToChans]
                      split
                      · rename_i h
                        simp only [← hcondName] at h
                        have := hpath_conds_order true cond ec.pathConds h
                        simp at this
                      · split
                        · rename_i h
                          simp only [← hcondName] at h
                          have := hpath_conds_order false cond ec.pathConds h
                          simp at this
                        · rfl
                    · grind only
                  · simp
                  · simp
                    simp only [← hcondValInterp] at hcondValBool
                    have := (instInterp.unique_true_val condVal).mp hcondValBool
                    simp [this]
                  · simp [hname, ← hcondName]
                · simp
              · simp [compileExpr.allVars]
            · simp [compileExpr.allVars]
          -- TODO: mostly the same as above, refactor...
          · simp only [← hcondName] at hname
            simp [← hname]
            rw [push_vars_lookup_diff]
            · rw [pop_vars_lookup_diff _ _ hchans₃]
              · split
                · rename_i h
                  have := hpath_conds_order true cond ec.pathConds h
                  simp at this
                rw [pop_var_lookup_diff _ _ hchans₂]
                · simp only [← hpc₁]
                  rw [push_vars_lookup_singleton _ _ 1]
                  · simp
                    rw [pop_var_lookup_diff _ _ hchans₁]
                    · simp only [hlive_vars, SimR.varsToChans]
                      split
                      · rename_i h
                        simp only [← hcondName] at h
                        have := hpath_conds_order true cond ec.pathConds h
                        simp at this
                      · split
                        · rename_i h
                          simp only [← hcondName] at h
                          have := hpath_conds_order false cond ec.pathConds h
                          simp at this
                        · rfl
                    · grind only
                  · simp
                  · simp
                    simp only [← hcondValInterp] at hcondValBool
                    have := (instInterp.unique_false_val condVal).mp hcondValBool
                    simp [this]
                  · simp [hname, ← hcondName]
                · simp
              · simp [compileExpr.allVars]
            · simp [compileExpr.allVars]
        | switch_cond v =>
          simp
          split
          all_goals
            rw [push_vars_lookup_diff]
            · rw [pop_vars_lookup_diff _ _ hchans₃]
              · if hv : condName = v then
                  -- rw [pop_var_lookup_singleton _ _ hchans₂]
                  simp only [← hv]
                  rw [pop_var_lookup_singleton _ _ hchans₂]
                  simp only [← hpc₁]
                  rw [push_vars_lookup_singleton _ _ 0]
                  · simp
                    rw [pop_var_lookup_diff _ _ hchans₁]
                    · simp only [hlive_vars, SimR.varsToChans]
                    · simp [← hcondName]
                  · simp
                  · simp
                  · simp
                else
                  rw [pop_var_lookup_diff _ _ hchans₂]
                  · simp only [← hpc₁]
                    rw [push_vars_lookup_diff]
                    · rw [pop_var_lookup_diff _ _ hchans₁]
                      · simp only [hlive_vars, SimR.varsToChans]
                      · simp [← hcondName]
                    · simp [hv]
                  · simp [hv]
              · simp [compileExpr.allVars]
            · simp [compileExpr.allVars]
        | _ =>
          simp
          split
          all_goals
            rw [push_vars_lookup_diff]
            · rw [pop_vars_lookup_diff _ _ hchans₃]
              · rw [pop_var_lookup_diff _ _ hchans₂]
                · simp only [← hpc₁]
                  rw [push_vars_lookup_diff]
                  · rw [pop_var_lookup_diff _ _ hchans₁]
                    · simp only [hlive_vars, SimR.varsToChans, hbr]
                    · simp [← hcondName]
                  · simp
                · simp
              · simp [compileExpr.allVars]
            · simp [compileExpr.allVars]
      · simp
        intros var
        constructor
        · sorry
        · sorry
      · grind

end Wavelet.Simulation
