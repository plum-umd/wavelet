import Mathlib.Logic.Relation
import Wavelet.Op

/-! Syntax and semantics for a simple dataflow calculus. -/

namespace Wavelet.Dataflow

open Op

universe u
variable (Op : Type u) (χ : Type u)
variable [Arity Op]
variable [DecidableEq χ]

/- A channel name attached with a value buffer. -/
abbrev ChanBuf V := χ × List V

abbrev ChanBufs V (n : Nat) := Vector (ChanBuf χ V) n

def ChanBuf.empty (v : χ) : ChanBuf χ V := (v, [])

def ChanBuf.singleton (v : χ) (val : V) : ChanBuf χ V := (v, [val])

def ChanBuf.push (vars : Vector χ n) (vals : Vector V n) (buf : ChanBuf χ V) : ChanBuf χ V :=
  (vars.zip vals).foldl (λ buf (var, val) =>
    if buf.1 = var then (buf.1, buf.2.concat val)
    else (buf.1, buf.2)) buf

def ChanBuf.pop (buf : ChanBuf χ V) : Option (V × ChanBuf χ V) :=
  match buf.2 with
  | [] => none
  | v :: vs => some (v, (buf.1, vs))

def ChanBufs.empty (vars : Vector χ n) : ChanBufs χ V n :=
  vars.map (ChanBuf.empty _)

def ChanBufs.singleton (vars : Vector χ n) (vals : Vector V n) : ChanBufs χ V n :=
  vars.zipWith (λ var val => .singleton _ var val) vals

def ChanBufs.push (vars : Vector χ m) (vals : Vector V m)
  (bufs : ChanBufs χ V n) : ChanBufs χ V n :=
  bufs.map (ChanBuf.push _ vars vals)

def ChanBufs.pop (bufs : ChanBufs χ V n) : Option (Vector V n × ChanBufs χ V n) := do
  let res ← bufs.mapM (ChanBuf.pop _)
  return (res.map Prod.fst, res.map Prod.snd)

/-- Dataflow operators. -/
inductive AtomicProc V where
  | op (op : Op) (inputs : ChanBufs χ V (Arity.ι op)) (outputs : Vector χ (Arity.ω op))
  | steer (flavor : Bool) (decider : ChanBuf χ V) (inputs : ChanBufs χ V n) (outputs : Vector χ n)
  | carry (inLoop : Bool)
    (decider : ChanBuf χ V)
    (inputs₁ : ChanBufs χ V n) (inputs₂ : ChanBufs χ V n)
    (outputs : Vector χ n)
  | merge (decider : ChanBuf χ V)
    (inputs₁ : ChanBufs χ V n) (inputs₂ : ChanBufs χ V n)
    (outputs : Vector χ n)
  | forward (inputs : ChanBufs χ V n) (outputs : Vector χ n)
  | const (c : V) (act : ChanBuf χ V) (outputs : Vector χ n)
  deriving Repr

def AtomicProc.inputs (ap : AtomicProc Op χ V) : List (ChanBuf χ V) :=
  match ap with
  | .op _ inputs _ => inputs.toList
  | .steer _ decider inputs _ => [decider] ++ inputs.toList
  | .carry _ decider input₁ input₂ _ => [decider] ++ input₁.toList ++ input₂.toList
  | .merge decider input₁ input₂ _ => [decider] ++ input₁.toList ++ input₂.toList
  | .forward inputs _ => inputs.toList
  | .const _ act _ => [act]

def AtomicProc.outputs (ap : AtomicProc Op χ V) : List χ :=
  match ap with
  | .op _ _ outputs => outputs.toList
  | .steer _ _ _ outputs => outputs.toList
  | .carry _ _ _ _ outputs => outputs.toList
  | .merge _ _ _ outputs => outputs.toList
  | .forward _ outputs => outputs.toList
  | .const _ _ outputs => outputs.toList

abbrev AtomicProcs V := List (AtomicProc Op χ V)

/-- `Proc _ m n` is a process with `m` inputs and `n` outputs. -/
structure Proc V (m : Nat) (n : Nat) where
  inputs : Vector χ m
  outputs : ChanBufs χ V n
  atoms : AtomicProcs Op χ V

/- From this point onwards, assume a fixed operator semantics. -/
variable (V S) [instInterp : Interp Op V S]

@[simp]
def AtomicProc.push (vars : Vector χ n) (vals : Vector V n) : AtomicProc Op χ V → AtomicProc Op χ V
  | .op o inputs outputs => .op o (pushAll inputs) outputs
  | .steer flavor decider inputs outputs => .steer flavor (pushOne decider) (pushAll inputs) outputs
  | .carry inLoop decider inputs₁ inputs₂ outputs =>
    .carry inLoop (pushOne decider) (pushAll inputs₁) (pushAll inputs₂) outputs
  | .merge decider inputs₁ inputs₂ outputs =>
    .merge (pushOne decider) (pushAll inputs₁) (pushAll inputs₂) outputs
  | .forward inputs outputs => .forward (pushAll inputs) outputs
  | .const c act outputs => .const c (pushOne act) outputs
  where
    @[simp] pushOne (buf : ChanBuf χ V) := ChanBuf.push _ vars vals buf
    @[simp] pushAll {m} (bufs : ChanBufs χ V m) := ChanBufs.push _ vars vals bufs

@[simp]
def AtomicProcs.push
  (vars : Vector χ n)
  (vals : Vector V n)
  (aps : AtomicProcs Op χ V) :
  AtomicProcs Op χ V :=
  aps.map (AtomicProc.push _ _ _ vars vals)

@[simp]
def Proc.push
  (vars : Vector χ k)
  (vals : Vector V k)
  (p : Proc Op χ V m n) : Proc Op χ V m n :=
  { p with
    outputs := .push _ vars vals p.outputs,
    atoms := AtomicProcs.push _ _ _ vars vals p.atoms }

structure Config m n where
  proc : Proc Op χ V m n
  state : S

/-- Initial process configuration. -/
@[simp]
def Config.init
  (proc : Proc Op χ V m n)
  (state : S)
  (args : Vector V m) : Config Op χ V S m n
  := {
    proc := proc.push _ _ _ proc.inputs args,
    state,
  }

inductive Config.Step : Config Op χ V S m n → Config Op χ V S m n → Prop where
  | step_op {inputs : ChanBufs χ V (Arity.ι o)} :
    c.proc.atoms = ctxLeft ++ [.op o inputs outputs] ++ ctxRight →
    inputs.pop _ = some (inputVals, inputs') →
    (instInterp.interp o inputVals).run c.state = some (outputVals, state') →
    Step c
      {
        proc := { c.proc with
          outputs := c.proc.outputs.push _ outputs outputVals,
          atoms := .push _ _ _ outputs outputVals
            (ctxLeft ++ [.op o inputs' outputs] ++ ctxRight),
        },
        state := state',
      }
  | step_steer :
    c.proc.atoms = ctxLeft ++ [.steer flavor decider inputs outputs] ++ ctxRight →
    decider.pop _ = some (deciderVal, decider') →
    inputs.pop _ = some (inputVals, inputs') →
    Step c { c with
      proc :=
        if instInterp.asBool deciderVal = flavor then
          { c.proc with
            outputs := c.proc.outputs.push _ outputs inputVals,
            atoms := .push _ _ _ outputs inputVals
              (ctxLeft ++ [.steer flavor decider' inputs' outputs] ++ ctxRight),
          }
        else
          { c.proc with
            atoms := ctxLeft ++ [.steer flavor decider' inputs' outputs] ++ ctxRight,
          }
    }
  | step_merge_true :
    c.proc.atoms = ctxLeft ++ [.merge decider inputs₁ inputs₂ outputs] ++ ctxRight →
    decider.pop _ = some (deciderVal, decider') →
    instInterp.asBool deciderVal →
    inputs₁.pop _ = some (inputVals, inputs₁') →
    Step c { c with
      proc := { c.proc with
        outputs := c.proc.outputs.push _ outputs inputVals,
        atoms := .push _ _ _ outputs inputVals
          (ctxLeft ++ [.merge decider' inputs₁' inputs₂ outputs] ++ ctxRight),
      },
    }
  | step_merge_false :
    c.proc.atoms = ctxLeft ++ [.merge decider inputs₁ inputs₂ outputs] ++ ctxRight →
    decider.pop _ = some (deciderVal, decider') →
    ¬ instInterp.asBool deciderVal →
    inputs₂.pop _ = some (inputVals, inputs₂') →
    Step c { c with
      proc := { c.proc with
        outputs := c.proc.outputs.push _ outputs inputVals,
        atoms := .push _ _ _ outputs inputVals
          (ctxLeft ++ [.merge decider' inputs₁ inputs₂' outputs] ++ ctxRight),
      },
    }
  | step_carry_init :
    c.proc.atoms = ctxLeft ++ [.carry false decider inputs₁ inputs₂ outputs] ++ ctxRight →
    inputs₁.pop _ = some (inputVals, inputs₁') →
    Step c { c with
      proc := { c.proc with
        outputs := c.proc.outputs.push _ outputs inputVals,
        atoms := .push _ _ _ outputs inputVals
          (ctxLeft ++ [.carry true decider inputs₁' inputs₂ outputs] ++ ctxRight),
      },
    }
  | step_carry_true :
    c.proc.atoms = ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight →
    decider.pop _ = some (deciderVal, decider') →
    instInterp.asBool deciderVal →
    inputs₂.pop _ = some (inputVals, inputs₂') →
    Step c { c with
      proc := { c.proc with
        outputs := c.proc.outputs.push _ outputs inputVals,
        atoms := .push _ _ _ outputs inputVals
          (ctxLeft ++ [.carry true decider' inputs₁ inputs₂' outputs] ++ ctxRight),
      },
    }
  | step_carry_false :
    c.proc.atoms = ctxLeft ++ [.carry true decider inputs₁ inputs₂ outputs] ++ ctxRight →
    decider.pop _ = some (deciderVal, decider') →
    ¬ instInterp.asBool deciderVal →
    Step c { c with
      proc := { c.proc with
        atoms := ctxLeft ++ [.carry false decider' inputs₁ inputs₂ outputs] ++ ctxRight,
      },
    }
  | step_forward :
    c.proc.atoms = ctxLeft ++ [.forward inputs outputs] ++ ctxRight →
    inputs.pop _ = some (inputVals, inputs') →
    Step c { c with
      proc := { c.proc with
        outputs := c.proc.outputs.push _ outputs inputVals,
        atoms := .push _ _ _ outputs inputVals
          (ctxLeft ++ [.forward inputs' outputs] ++ ctxRight),
      },
    }
  | step_const :
    c.proc.atoms = ctxLeft ++ [.const val act outputs] ++ ctxRight →
    act.pop _ = some (inputVal, act') →
    Step c { c with
      proc := { c.proc with
        outputs := c.proc.outputs.push _ outputs (Vector.replicate _ val),
        atoms := .push _ _ _ outputs (Vector.replicate _ val)
          (ctxLeft ++ [.const val act' outputs] ++ ctxRight),
      },
    }

def Config.StepPlus {m n} := @Relation.TransGen (Config Op χ V S m n) (Step Op χ V S)
def Config.StepStar {m n} := @Relation.ReflTransGen (Config Op χ V S m n) (Step Op χ V S)

/- Some alternative forms of stepping. -/

theorem step_eq :
  Config.Step Op χ V S c₁ c₂ →
  c₂ = c₂' →
  Config.Step _ _ _ _ c₁ c₂' := sorry

theorem step_forward_alt₁
  ctxLeft inputVals inputs' :
  c.proc.atoms = ctxLeft ++ [.forward inputs outputs] ++ ctxRight →
  inputs.pop _ = some (inputVals, inputs') →
  Config.Step Op χ V S c { c with
    proc := { c.proc with
      outputs := c.proc.outputs.push _ outputs inputVals,
      atoms := .push _ _ _ outputs inputVals
        (ctxLeft ++ [.forward inputs' outputs] ++ ctxRight),
    },
  } := by apply Config.Step.step_forward

theorem step_const_alt₁
  ctxLeft :
  c.proc.atoms = ctxLeft ++ [.const val act outputs] ++ ctxRight →
  act.pop _ = some (inputVal, act') →
  Config.Step Op χ V S c { c with
    proc := { c.proc with
      outputs := c.proc.outputs.push _ outputs (Vector.replicate _ val),
      atoms := .push _ _ _ outputs (Vector.replicate _ val)
        (ctxLeft ++ [.const val act' outputs] ++ ctxRight),
    },
  } := sorry

/-- The step relation does not depend on the input annotations. -/
theorem step_inputs_indep
  (inputs : Vector χ m)
  (h : Config.Step Op χ V S c₁ c₂) :
  Config.Step Op χ V S
    { c₁ with proc := { c₁.proc with inputs } }
    { c₂ with proc := { c₂.proc with inputs } } := sorry

-- def Proc.Computes (p : Proc Op χ V m n) (f : Vector V m → StateM S (Vector V n)) : Prop :=
--   ∀ state inputs,
--     Dataflow.Config.StepStar Op χ V S
--     (Dataflow.Config.init _ _ _ _ p state inputs)
--     {
--       proc := {
--         p with
--         outputs := (p.outputs.zip ((f inputs).run state).1).map
--           λ (buf, val) => (buf.1, [val]),
--       },
--       state := ((f inputs).run state).2,
--     }

end Wavelet.Dataflow
