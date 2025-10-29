import Wavelet.Dataflow.Proc

/-! Abbreviations of atomic processes and stepping rules. -/

namespace Wavelet.Dataflow

open Semantics

/-! Built-in asynchronous operators. -/
namespace AtomicProc

def switch [Arity Op]
  (decider : χ) (inputs : Vector χ n)
  (outputs₁ : Vector χ n)
  (outputs₂ : Vector χ n) : AtomicProc Op χ V
  := .async (.switch n) (#v[decider] ++ inputs).toList (outputs₁ ++ outputs₂).toList

def steer [Arity Op]
  (flavor : Bool)
  (decider : χ) (inputs : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.steer flavor n) (#v[decider] ++ inputs).toList outputs.toList

def merge [Arity Op]
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V :=
  -- TODO: make the order of inputs₁ and inputs₂ more consistent.
  .async (.merge .decider n) (#v[decider] ++ inputs₂ ++ inputs₁).toList outputs.toList

/-- Carry is a variant of merge that can have a different initial state. -/
def carry [Arity Op]
  (state : AsyncOp.MergeState)
  (decider : χ)
  (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
  (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.merge state n) (#v[decider] ++ inputs₁ ++ inputs₂).toList outputs.toList

def forward [Arity Op]
  (inputs : Vector χ n) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.forward n) inputs.toList outputs.toList

def fork [Arity Op]
  (input : χ) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.fork n) [input] outputs.toList

def const [Arity Op]
  (c : V) (act : χ) (outputs : Vector χ n) : AtomicProc Op χ V
  := .async (.const c n) [act] outputs.toList

def forwardc [Arity Op]
  (inputs : Vector χ n) (consts : Vector V m)
  (outputs : Vector χ (n + m)) : AtomicProc Op χ V
  := .async (.forwardc n m consts) inputs.toList outputs.toList

def sink [Arity Op]
  (inputs : Vector χ n) : AtomicProc Op χ V
  := .async (.sink n) inputs.toList #v[].toList

end AtomicProc

/-! Alternative rules for the stepping relation. -/
section AltStep

theorem Config.Step.step_async_alt
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {k₁' k₂'}
  {aop aop' : AsyncOp V}
  {ctxLeft ctxRight}
  {allInputs allOutputs}
  {inputs : Vector χ k₁'}
  {outputs : Vector χ k₂'}
  {inputVals outputVals chans'}
  (happ : c.proc.atoms = ctxLeft ++ .async aop allInputs allOutputs :: ctxRight)
  (hinterp : aop.Interp
    (.mk allInputs allOutputs inputs.toList inputVals.toList outputs.toList outputVals.toList)
    aop')
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ .async aop' allInputs allOutputs :: ctxRight,
    },
    chans := chans'.pushVals outputs outputVals,
  } := by
  have hget := List.getElem_of_append_cons happ
  apply Config.Step.step_async
    (by simp [happ])
    hget hinterp hpop_inputs
    |> Lts.Step.eq_rhs
  simp [happ]

theorem Config.Step.step_switch
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {outputs₁ outputs₂ : Vector χ k}
  (hmem : .switch decider inputs outputs₁ outputs₂ ∈ c.proc.atoms)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hpop_inputs : chans'.popVals inputs = some (inputVals, chans''))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool) :
  Step c .τ { c with
    chans :=
      let outputs := if deciderBool then outputs₁ else outputs₂
      chans''.pushVals outputs inputVals
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.switch] at happ
  apply Config.Step.step_async_alt
    (aop := .switch k)
    (aop' := .switch k)
    (outputs := if deciderBool then outputs₁ else outputs₂)
    happ
    (by
      apply AsyncOp.Interp.interp_switch (k := k)
        (inputs := inputs.toList)
        (outputs := (outputs₁ ++ outputs₂).toList)
        (by simp)
        (by simp)
        hdecider
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      split <;> simp)
    (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_steer
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs outputs : Vector χ k}
  (hmem : .steer flavor decider inputs outputs ∈ c.proc.atoms)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hpop_inputs : chans'.popVals inputs = some (inputVals, chans''))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool) :
  Step c .τ { c with
    chans :=
      if deciderBool = flavor then
        chans''.pushVals outputs inputVals
      else
        chans'',
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.steer] at happ
  by_cases h₁ : deciderBool = flavor
  · apply Config.Step.step_async_alt
      (aop := .steer flavor k)
      (aop' := .steer flavor k)
      happ
      (by
        apply AsyncOp.Interp.interp_steer_true (k := k)
          (inputs := inputs.toList)
          (outputs := outputs.toList)
          (by simp)
          (by simp)
          hdecider h₁
          |> AsyncOp.Interp.eq_label
        simp [Vector.toList]
        and_intros
        any_goals try rfl)
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp [h₁]
    congr 1
    exact happ.symm
  · apply Config.Step.step_async_alt
      (aop := .steer flavor k)
      (aop' := .steer flavor k)
      happ
      (by
        apply AsyncOp.Interp.interp_steer_false (k := k)
          (inputs := inputs.toList)
          (outputs := outputs.toList)
          (by simp)
          (by simp)
          hdecider h₁
          |> AsyncOp.Interp.eq_label
        simp [Vector.toList]
        and_intros
        any_goals try rfl
        exact #v[]
        exact #v[])
      (pop_vals_append (pop_val_to_pop_vals hpop_decider) hpop_inputs)
      |> Lts.Step.eq_rhs
    simp [h₁, ChanMap.pushVals]
    congr 1
    exact happ.symm

theorem Config.Step.step_carry_left
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  {ctxLeft ctxRight : List (AtomicProc Op χ V)}
  (happ : c.proc.atoms =
    ctxLeft ++ [.carry .popLeft decider inputs₁ inputs₂ outputs] ++ ctxRight)
  (hpop_inputs₁ : c.chans.popVals inputs₁ = some (inputVals, chans')) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight,
    },
    chans := chans'.pushVals outputs inputVals,
  } := by
  simp at happ
  apply Config.Step.step_async_alt
    (aop := .merge .popLeft k)
    (aop' := .merge .decider k)
    happ
    (by
      apply AsyncOp.Interp.interp_merge_left (k := k)
        (inputs := (inputs₁ ++ inputs₂).toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
    hpop_inputs₁
    |> Lts.Step.eq_rhs
  simp
  congr 1
  simp

theorem Config.Step.step_carry_right
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  {ctxLeft ctxRight : List (AtomicProc Op χ V)}
  (happ : c.proc.atoms =
    ctxLeft ++ [.carry .popRight decider inputs₁ inputs₂ outputs] ++ ctxRight)
  (hpop_inputs₂ : c.chans.popVals inputs₂ = some (inputVals, chans')) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight,
    },
    chans := chans'.pushVals outputs inputVals,
  } := by
  simp at happ
  apply Config.Step.step_async_alt
    (aop := .merge .popRight k)
    (aop' := .merge .decider k)
    happ
    (by
      apply AsyncOp.Interp.interp_merge_right (k := k)
        (inputs := (inputs₁ ++ inputs₂).toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
    hpop_inputs₂
    |> Lts.Step.eq_rhs
  simp
  congr 1
  simp

theorem Config.Step.step_carry_decider
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  {ctxLeft ctxRight : List (AtomicProc Op χ V)}
  (happ : c.proc.atoms =
    ctxLeft ++ [.carry .decider decider inputs₁ inputs₂ outputs] ++ ctxRight)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool) :
  Step c .τ { c with
    proc := { c.proc with
      atoms := ctxLeft ++ [
          .carry (if deciderBool then .popRight else .popLeft)
            decider inputs₁ inputs₂ outputs
        ] ++ ctxRight,
    },
    chans := chans',
  } := by
  simp at happ
  apply Config.Step.step_async_alt
    (aop := .merge .decider k)
    (aop' := .merge (if deciderBool then .popRight else .popLeft) k)
    happ
    (by
      apply AsyncOp.Interp.interp_merge_decider (k := k)
        (inputs := (inputs₁ ++ inputs₂).toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        hdecider
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      exact #v[]; exact #v[])
    (pop_val_to_pop_vals hpop_decider)
    |> Lts.Step.eq_rhs
  simp [AtomicProc.carry]

theorem Config.Step.step_merge
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs₁ inputs₂ outputs : Vector χ k}
  (hmem : .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms)
  (hpop_decider : c.chans.popVal decider = some (deciderVal, chans'))
  (hdecider : InterpConsts.toBool deciderVal = some deciderBool)
  (hpop_inputs : chans'.popVals
    (if deciderBool then inputs₁ else inputs₂) = some (inputVals, chans'')) :
    Step.TauStar .τ c { c with
      chans := chans''.pushVals outputs inputVals
    }
  := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.merge] at happ
  have hstep₁ : Step c .τ _
    := .step_carry_decider (by
      simp [AtomicProc.carry]
      rw [happ]
      congr; simp; rfl) hpop_decider hdecider
  if hdecider_bool : deciderBool then
    subst hdecider_bool
    have hsteps : Step.TauStar .τ c _
      := .tail (.single hstep₁)
      (.step_carry_right
        (by rfl)
        hpop_inputs)
    exact .eq_rhs hsteps (by
      simp [AtomicProc.carry]
      congr
      rw [happ]
      simp [le_of_lt hi, List.drop_append])
  else
    simp at hdecider_bool
    subst hdecider_bool
    have hsteps : Step.TauStar .τ c _
      := .tail (.single hstep₁)
      (.step_carry_left
        (by rfl)
        hpop_inputs)
    exact .eq_rhs hsteps (by
      simp [AtomicProc.carry]
      congr
      rw [happ]
      simp [le_of_lt hi, List.drop_append])

theorem Config.Step.step_forward
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs outputs : Vector χ k}
  (hmem : .forward inputs outputs ∈ c.proc.atoms)
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs inputVals,
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.forward] at happ
  apply Config.Step.step_async_alt
    (aop := .forward k)
    (aop' := .forward k)
    happ
    (.interp_forward (k := k)
      (by simp)
      (by simp))
    hpop_inputs
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_fork
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {input : χ}
  {outputs : Vector χ k}
  (hmem : .fork input outputs ∈ c.proc.atoms)
  (hpop_input : c.chans.popVal input = some (inputVal, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs (Vector.replicate _ inputVal),
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.fork] at happ
  apply Config.Step.step_async_alt
    (aop := .fork k)
    (aop' := .fork k)
    (outputVals := Vector.replicate _ inputVal)
    happ
    (by
      apply AsyncOp.Interp.interp_fork (k := k)
        (outputs := outputs.toList)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      simp)
    (pop_val_to_pop_vals hpop_input)
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_const
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {val : V}
  {act : χ}
  {outputs : Vector χ k}
  (hmem : .const val act outputs ∈ c.proc.atoms)
  (hpop_act : c.chans.popVal act = some (actVal, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs (Vector.replicate _ val),
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.const] at happ
  apply Config.Step.step_async_alt
    (aop := .const val k)
    (aop' := .const val k)
    (outputVals := Vector.replicate _ val)
    happ
    (by
      apply AsyncOp.Interp.interp_const (k := k)
        (outputs := outputs.toList)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
    (pop_val_to_pop_vals hpop_act)
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_forwardc
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs : Vector χ k}
  {consts : Vector V l}
  {outputs : Vector χ (k + l)}
  (hmem : .forwardc inputs consts outputs ∈ c.proc.atoms)
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
  Step c .τ { c with
    chans := chans'.pushVals outputs (inputVals ++ consts),
  } := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.forwardc] at happ
  apply Config.Step.step_async_alt
    (aop := .forwardc k l consts)
    (aop' := .forwardc k l consts)
    (outputVals := inputVals ++ consts)
    happ
    (by
      apply AsyncOp.Interp.interp_forwardc (k := k) (l := l)
        (inputs := inputs.toList)
        (outputs := outputs.toList)
        (by simp)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl)
    hpop_inputs
    |> Lts.Step.eq_rhs
  simp
  congr 1
  exact happ.symm

theorem Config.Step.step_sink
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  {c : Config Op χ V m n}
  {inputs : Vector χ k}
  (hmem : .sink inputs ∈ c.proc.atoms)
  (hpop_inputs : c.chans.popVals inputs = some (inputVals, chans')) :
    Step c .τ { c with chans := chans' }
  := by
  have ⟨i, hi, hget_i⟩ := List.getElem_of_mem hmem
  have happ := List.to_append_cons (l := c.proc.atoms) hi
  simp only [hget_i, AtomicProc.sink] at happ
  apply Config.Step.step_async_alt
    (aop := .sink k)
    (aop' := .sink k)
    happ
    (by
      apply AsyncOp.Interp.interp_sink (k := k)
        (inputs := inputs.toList)
        (by simp)
        |> AsyncOp.Interp.eq_label
      simp [Vector.toList]
      and_intros
      any_goals try rfl
      exact #v[]; exact #v[])
    hpop_inputs
    |> Lts.Step.eq_rhs
  simp [ChanMap.pushVals]
  congr 1
  exact happ.symm

end AltStep

end Wavelet.Dataflow
