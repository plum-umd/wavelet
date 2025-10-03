import Mathlib.Logic.Relation
import Wavelet.Op
import Wavelet.Lts

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Op Lts

/-- Dataflow operators. -/
inductive AtomicProc (Op χ V : Type*) [Arity Op] where
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
  -- A combination of `forward` and `const` to wait for inputs to arrive,
  -- forward the inputs to the first `n` outputs, and then send constants
  -- to the last `m` outputs.
  | forwardc
    (inputs : Vector χ n) (consts : Vector V m) (outputs : Vector χ (n + m))
  | sink (inputs : Vector χ n)

abbrev AtomicProcs Op χ V [Arity Op] := List (AtomicProc Op χ V)

/-- `Proc ... m n` is a process with `m` inputs and `n` outputs. -/
structure Proc Op χ V [Arity Op] (m : Nat) (n : Nat) where
  inputs : Vector χ m
  outputs : Vector χ n
  atoms : AtomicProcs Op χ V

abbrev ChanMap χ V := χ → List V

def ChanMap.empty : ChanMap χ V := λ _ => []

def ChanMap.pushVal [DecidableEq χ] (name : χ) (val : V) (map : ChanMap χ V) : ChanMap χ V :=
  λ n => if n = name then map n ++ [val] else map n

def ChanMap.pushVals [DecidableEq χ]
  (names : Vector χ n) (vals : Vector V n)
  (map : ChanMap χ V) : ChanMap χ V :=
  (names.zip vals).foldl (λ map (n, v) => map.pushVal n v) map

def ChanMap.popVal
  {χ : Type*}
  [DecidableEq χ]
  (name : χ)
  (map : ChanMap χ V) : Option (V × ChanMap χ V) :=
  match map name with
  | [] => none
  | v :: vs => some (v, λ n => if n = name then vs else map n)

def ChanMap.popVals

  [DecidableEq χ]
  (names : Vector χ n)
  (map : ChanMap χ V) : Option (Vector V n × ChanMap χ V)
  := (names.mapM popValM).run map
  where
    @[simp]
    popValM : χ → StateT (ChanMap χ V) Option V := popVal

def ChanMap.IsSingleton (name : χ) (val : V) (map : ChanMap χ V) : Prop := map name = [val]

def ChanMap.IsEmpty (name : χ) (map : ChanMap χ V) : Prop := map name = []

def ChanMap.getBuf (name : χ) (map : ChanMap χ V) : List V := map name

structure Config Op χ V [Arity Op] m n where
  proc : Proc Op χ V m n
  chans : ChanMap χ V

/-- Initial process configuration. -/
def Config.init
  [Arity Op] [DecidableEq χ]
  (proc : Proc Op χ V m n) : Config Op χ V m n
  := { proc, chans := .empty }

inductive Config.Step
  [Arity Op] [DecidableEq χ]
  [InterpConsts V]
  : Lts (Config Op χ V m n) (Label Op V m n) where
  | step_init :
    Step c (.input args) { c with
      chans := c.chans.pushVals c.proc.inputs args,
    }
  | step_output :
    c.chans.popVals c.proc.outputs = some (outputVals, chans') →
    Step c (.output outputVals) { c with
      chans := chans',
    }
  | step_op {inputs : Vector χ (Arity.ι op)} :
    .op op inputs outputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c (.yield op inputVals outputVals) { c with
      chans := chans'.pushVals outputs outputVals,
    }
  | step_switch
    {outputs₁ outputs₂ : Vector χ n} :
    .switch decider inputs outputs₁ outputs₂ ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    chans'.popVals inputs = some (inputVals, chans'') →
    InterpConsts.toBool deciderVal = some deciderBool →
    Step c .τ { c with
      chans :=
        let outputs := if deciderBool then outputs₁ else outputs₂
        chans''.pushVals outputs inputVals
    }
  | step_steer :
    .steer flavor decider inputs outputs ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    chans'.popVals inputs = some (inputVals, chans'') →
    InterpConsts.toBool deciderVal = some deciderBool →
    Step c .τ { c with
      chans :=
        if deciderBool = flavor then
          chans''.pushVals outputs inputVals
        else
          chans'',
    }
  | step_merge :
    .merge decider inputs₁ inputs₂ outputs ∈ c.proc.atoms →
    c.chans.popVal decider = some (deciderVal, chans') →
    InterpConsts.toBool deciderVal = some deciderBool →
    chans'.popVals
      (if deciderBool then inputs₁ else inputs₂)
      = some (inputVals, chans'') →
    Step c .τ { c with chans := chans''.pushVals outputs inputVals }
  | step_carry_init :
    c.proc.atoms = ctxLeft ++ [.carry false decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVals inputs₁ = some (inputVals, chans') →
    Step c .τ { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight,
      },
      chans := chans'.pushVals outputs inputVals,
    }
  | step_carry_true :
    c.proc.atoms = ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVal decider = some (deciderVal, chans') →
    InterpConsts.toBool deciderVal = some true →
    chans'.popVals inputs₂ = some (inputVals, chans'') →
    Step c .τ { c with
      chans := chans''.pushVals outputs inputVals,
    }
  | step_carry_false :
    c.proc.atoms = ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight →
    c.chans.popVal decider = some (deciderVal, chans') →
    InterpConsts.toBool deciderVal = some false →
    Step c .τ { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry false decider inputs₁ inputs₂ outputs] ++ ctxRight,
      },
      chans := chans',
    }
  | step_forward :
    .forward inputs outputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs inputVals,
    }
  | step_fork :
    .fork input outputs ∈ c.proc.atoms →
    c.chans.popVal input = some (inputVal, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs (Vector.replicate _ inputVal),
    }
  | step_const :
    .const val act outputs ∈ c.proc.atoms →
    c.chans.popVal act = some (actVal, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs (Vector.replicate _ val),
    }
  | step_forwardc :
    .forwardc inputs consts outputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with
      chans := chans'.pushVals outputs (inputVals ++ consts),
    }
  | step_sink :
    .sink inputs ∈ c.proc.atoms →
    c.chans.popVals inputs = some (inputVals, chans') →
    Step c .τ { c with chans := chans' }

def Proc.semantics
  [Arity Op] [DecidableEq χ] [InterpConsts V]
  (proc : Proc Op χ V m n) : Semantics Op V m n := {
    S := Config Op χ V m n,
    init := Config.init proc,
    lts := Config.Step,
  }

def AtomicProc.mapChans [Arity Op] (f : χ → χ') : AtomicProc Op χ V → AtomicProc Op χ' V
  | .op o inputs outputs => .op o (inputs.map f) (outputs.map f)
  | .switch decider inputs outputs₁ outputs₂ =>
    .switch (f decider) (inputs.map f) (outputs₁.map f) (outputs₂.map f)
  | .steer flavor decider inputs outputs =>
    .steer flavor (f decider) (inputs.map f) (outputs.map f)
  | .carry inLoop decider inputs₁ inputs₂ outputs =>
    .carry inLoop (f decider) (inputs₁.map f) (inputs₂.map f) (outputs.map f)
  | .merge decider inputs₁ inputs₂ outputs =>
    .merge (f decider) (inputs₁.map f) (inputs₂.map f) (outputs.map f)
  | .forward inputs outputs => .forward (inputs.map f) (outputs.map f)
  | .fork input outputs => .fork (f input) (outputs.map f)
  | .const c act outputs => .const c (f act) (outputs.map f)
  | .forwardc inputs consts outputs => .forwardc (inputs.map f) consts (outputs.map f)
  | .sink inputs => .sink (inputs.map f)

def AtomicProcs.mapChans [Arity Op] (f : χ → χ')
  : AtomicProcs Op χ V → AtomicProcs Op χ' V
  := List.map (AtomicProc.mapChans f)

def Proc.mapChans [Arity Op] (f : χ → χ') (p : Proc Op χ V m n) : Proc Op χ' V m n :=
  {
    inputs := p.inputs.map f,
    outputs := p.outputs.map f,
    atoms := p.atoms.mapChans f,
  }

end Wavelet.Dataflow
