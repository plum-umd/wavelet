import Mathlib.Logic.Relation
import Wavelet.Op

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Op

universe u
variable (Op : Type u) (χ : Type u)
variable [instArity : Arity Op]
variable [DecidableEq χ]

/-- Dataflow operators. -/
inductive AtomicProc (V : Type u) where
  | op (op : Op) (inputs : Vector χ (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  | switch (decider : χ) (inputs : Vector χ n) (outputs₁ : Vector χ n) (outputs₂ : Vector χ n)
  | steer (flavor : Bool) (decider : χ) (inputs : Vector χ n) (outputs : Vector χ n)
  | carry (inLoop : Bool)
    (decider : χ)
    (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
    (outputs : Vector χ n)
  | merge (decider : χ)
    (inputs₁ : Vector χ n) (inputs₂ : Vector χ n)
    (outputs : Vector χ n)
  | forward (inputs : Vector χ n) (outputs : Vector χ n)
  | fork (input : χ) (outputs : Vector χ n)
  | const (c : V) (act : χ) (outputs : Vector χ n)

abbrev AtomicProcs V := List (AtomicProc Op χ V)

/-- `Proc _ m n` is a process with `m` inputs and `n` outputs. -/
structure Proc V (m : Nat) (n : Nat) where
  inputs : Vector χ m
  outputs : Vector χ n
  atoms : AtomicProcs Op χ V

/- From this point onwards, assume a fixed operator semantics. -/
variable (V S) [instInterp : Interp Op V S]

abbrev ChanMap := χ → List V

def ChanMap.empty : ChanMap χ V := λ _ => []

def ChanMap.pushVal (name : χ) (val : V) (map : ChanMap χ V) : ChanMap χ V :=
  λ n => if n = name then map n ++ [val] else map n

def ChanMap.pushVals
  (names : Vector χ n) (vals : Vector V n)
  (map : ChanMap χ V) : ChanMap χ V :=
  (names.zip vals).foldl (λ map (n, v) => map.pushVal _ _ n v) map

def ChanMap.popVal
  (name : χ)
  (map : ChanMap χ V) : Option (V × ChanMap χ V) :=
  match map name with
  | [] => none
  | v :: vs => some (v, λ n => if n = name then vs else map n)

def ChanMap.popVals
  (names : Vector χ n)
  (map : ChanMap χ V) : Option (Vector V n × ChanMap χ V) :=
  match h : n with
  | 0 => some (#v[], map)
  | n + 1 => do
    let (v, map') ← map.popVal _ _ names[0]
    let (vs, map'') ← map'.popVals names.tail
    pure (cast (by simp; congr 1; omega) (#v[v] ++ vs), map'')

def ChanMap.IsSingleton (name : χ) (val : V) (map : ChanMap χ V) : Prop := map name = [val]

def ChanMap.IsEmpty (name : χ) (map : ChanMap χ V) : Prop := map name = []

def ChanMap.getBuf (name : χ) (map : ChanMap χ V) : List V := map name

structure Config m n where
  proc : Proc Op χ V m n
  chans : ChanMap χ V
  state : S

/-- Initial process configuration. -/
def Config.init
  (proc : Proc Op χ V m n)
  (state : S)
  (args : Vector V m) : Config Op χ V S m n
  := {
    proc,
    chans := (ChanMap.empty _ _).pushVals _ _ proc.inputs args,
    state,
  }

inductive Config.Step : Config Op χ V S m n → Config Op χ V S m n → Prop where
  | step_op {inputs : Vector χ (Arity.ι o)} :
    .op o inputs outputs ∈ c.proc.atoms →
    c.chans.popVals _ _ inputs = some (inputVals, chans') →
    (instInterp.interp o inputVals).run c.state = some (outputVals, state') →
    Step c { c with
      chans := chans'.pushVals _ _ outputs outputVals,
      state := state',
    }
  | step_switch :
    .switch decider inputs outputs₁ outputs₂ ∈ c.proc.atoms →
    c.chans.popVal _ _ decider = some (deciderVal, chans') →
    chans'.popVals _ _ inputs = some (inputVals, chans'') →
    Step c { c with
      chans :=
        if instInterp.asBool deciderVal then
          chans''.pushVals _ _ outputs₁ inputVals
        else
          chans''.pushVals _ _ outputs₂ inputVals,
    }
  | step_steer :
    .steer flavor decider inputs outputs ∈ c.proc.atoms →
    c.chans.popVal _ _ decider = some (deciderVal, chans') →
    chans'.popVals _ _ inputs = some (inputVals, chans'') →
    Step c { c with
      chans :=
        if instInterp.asBool deciderVal = flavor then
          chans''.pushVals _ _ outputs inputVals
        else
          chans'',
    }
  | step_merge_true :
    .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms →
    c.chans.popVal _ _ decider = some (deciderVal, chans') →
    instInterp.asBool deciderVal →
    chans'.popVals _ _ inputs₁ = some (inputVals, chans'') →
    Step c { c with chans := chans''.pushVals _ _ outputs inputVals }
  | step_merge_false :
    .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms →
    c.chans.popVal _ _ decider = some (deciderVal, chans') →
    ¬ instInterp.asBool deciderVal →
    chans'.popVals _ _ inputs₂ = some (inputVals, chans'') →
    Step c { c with chans := chans''.pushVals _ _ outputs inputVals }
  | step_carry_init :
    c.proc.atoms = ctxLeft ++ [.carry false decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVals _ _ inputs₁ = some (inputVals, chans') →
    Step c { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight,
      },
      chans := chans'.pushVals _ _ outputs inputVals,
    }
  | step_carry_true :
    c.proc.atoms = ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVal _ _ decider = some (deciderVal, chans') →
    instInterp.asBool deciderVal →
    chans'.popVals _ _ inputs₂ = some (inputVals, chans'') →
    Step c { c with
      chans := chans''.pushVals _ _ outputs inputVals,
    }
  | step_carry_false :
    c.proc.atoms = ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVal _ _ decider = some (deciderVal, chans') →
    ¬ instInterp.asBool deciderVal →
    Step c { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry false decider' inputs₁ inputs₂ outputs] ++ ctxRight,
      },
    }
  | step_forward :
    .forward inputs outputs ∈ c.proc.atoms →
    c.chans.popVals _ _ inputs = some (inputVals, chans') →
    Step c { c with
      chans := chans'.pushVals _ _ outputs inputVals,
    }
  | step_fork :
    .fork input outputs ∈ c.proc.atoms →
    c.chans.popVal _ _ input = some (inputVal, chans') →
    Step c { c with
      chans := chans'.pushVals _ _ outputs (Vector.replicate _ inputVal),
    }
  | step_const :
    .const val act outputs ∈ c.proc.atoms →
    c.chans.popVal _ _ act = some (actVal, chans') →
    Step c { c with
      chans := chans'.pushVals _ _ outputs (Vector.replicate _ val),
    }

def Config.StepPlus {m n} := @Relation.TransGen (Config Op χ V S m n) (Step Op χ V S)
def Config.StepStar {m n} := @Relation.ReflTransGen (Config Op χ V S m n) (Step Op χ V S)

/- Some alternative forms of stepping. -/

theorem step_eq
  (hstep : Config.Step Op χ V S c₁ c₂)
  (heq : c₂ = c₂') :
  Config.Step _ _ _ _ c₁ c₂' := by
  simp [heq] at hstep
  exact hstep

end Wavelet.Dataflow
