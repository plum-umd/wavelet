import Mathlib.Data.List.Basic

/-!
Trying a simple version without function calls or recursion.
-/

variable
  (Op : Type u) -- Type of operators
  (χ : Type u) -- Type of variables

class OpArity where
  ι : Op → ℕ
  ω : Op → ℕ

variable [arity : OpArity Op]

inductive Expr : ℕ → Type u where
  | ret (vars : Vector χ n) : Expr n
  | op (op : Op)
    (args : Vector χ (arity.ι op))
    (rets : Vector χ (arity.ω op))
    (cont : Expr n) : Expr n
  | br (cond : χ) (left : Expr n) (right : Expr n) : Expr n

abbrev InputBuf (V) := χ × List V

def InputBuf.empty (v : χ) : InputBuf χ V := (v, [])

inductive AtomicProc (V) where
  | op (op : Op) (inputs : Vector (InputBuf χ V) (arity.ι op)) (outputs : Vector χ (arity.ω op))
  | steer (decider : InputBuf χ V) (input : InputBuf χ V) (output : χ)
  | merge (decider : InputBuf χ V) (input₁ : InputBuf χ V) (input₂ : InputBuf χ V) (output : χ)
  | forward (inputs : Vector (InputBuf χ V) n) (outputs : Vector χ n)
  deriving Repr

abbrev Proc (V) := List (AtomicProc Op χ V)

inductive ChanName where
  | var (base : χ) (count : ℕ) (pathConds : List (Bool × ChanName))
  | merge_cond (chan : ChanName)
  | dest (i : ℕ) (pathConds : List (Bool × ChanName))
  deriving Repr

/--

// pathConds = []
let y = op(x)
if c then
  // pathConds = [(true, c)]
  let _ = f(y)
  let _ = g(y)
else
  // pathConds = [(false, c)]
  if c2 then
    // pathConds = [(false, c), (true, c2)]
    // (y, pathConds)
    E2(y)
  else
    // pathConds = [(false, c), (false, c2)]
    E3(y)

-/

def compile
  [DecidableEq χ]
  (definedVars : List χ)
  (pathConds : List (Bool × ChanName χ))
  : Expr Op χ n → Option (Proc Op (ChanName χ) V)
  | .ret vars => do
    let chans := vars.map curVar
    let dests := (Vector.range n).mapIdx λ i _ => .dest i pathConds
    return [.forward chans dests]
  | .op op args rets cont => do
    let inputChans := args.map curVar
    let (definedVars', outputChans) := newVars definedVars rets
    return (.op op inputChans outputChans) ::
           (← compile definedVars' pathConds cont)
  | .br cond left right => do
    let condChan := curVar cond
    let leftConds := (true, condChan.1) :: pathConds
    let rightConds := (false, condChan.1) :: pathConds
    let leftComp ← compile definedVars leftConds left
    let rightComp ← compile definedVars rightConds right
    -- Filter variables to the branch body based on the branch condition
    let steers :=
      definedVars.eraseDups.map λ v =>
        .steer condChan
          (.empty _ (.var v (definedVars.count v) pathConds))
          (.var v (definedVars.count v) leftConds)
    -- Forward the condition to the merge nodes
    let forward := .forward #v[condChan] #v[.merge_cond condChan.1]
    -- Merge results from the two branches
    let merges := genMerges n condChan.1
    return steers ++ [forward] ++ leftComp ++ rightComp ++ merges
  where
    /-- Generates the current channel name of the given variable name. -/
    curVar v := .empty _ (.var v (definedVars.count v) pathConds)
    /-- Generates merge gates to combine return values of multiple branches. -/
    genMerges n condChan : List (AtomicProc Op _ V) :=
      let leftConds := (true, condChan) :: pathConds
      let rightConds := (false, condChan) :: pathConds
      let mergeCond := .empty _ (.merge_cond condChan)
      (List.range n).mapIdx λ i _ =>
        .merge mergeCond
          (.empty _ (.dest i leftConds))
          (.empty _ (.dest i rightConds))
          (.dest i pathConds)
    /--
    Defines new variables while maintaining a list of defined variables.
    `vs` may contain duplicates.
    -/
    newVars {m : ℕ} (definedVars : List χ) (vs : Vector χ m) : List χ × Vector (ChanName χ) m :=
      match m with
      | 0 => (definedVars, #v[])
      | m' + 1 =>
        let v := vs[0]
        let definedVars' := definedVars ++ [v]
        let name := ChanName.var v (definedVars'.count v) pathConds
        let (definedVars'', rest) := newVars definedVars' vs.tail
        (definedVars'', ⟨(name :: rest.toList).toArray, by simp⟩)

def compileTop [DecidableEq χ] : Expr Op χ n → Option (Proc Op (ChanName χ) V) :=
  compile Op χ [] []

/-- Some static, non-typing constraints on expressions. -/
inductive Expr.WellFormed : Expr Op χ n → Prop where
  | wf_ret : WellFormed (.ret vars)
  | wf_op :
    rets.toList.Nodup →
    WellFormed cont →
    WellFormed (.op o args rets cont)
  | wf_br :
    WellFormed left →
    WellFormed right →
    WellFormed (.br c left right)

inductive AtomicProc.WellFormed : AtomicProc Op χ V → Prop where
  | wf_op :
    outputs.toList.Nodup →
    WellFormed (.op o inputs outputs)
  | wf_steer : WellFormed (.steer decider input output)
  | wf_merge : WellFormed (.merge decider input₁ input₂ output)
  | wf_forward :
    outputs.toList.Nodup →
    WellFormed (.forward inputs outputs)

def Proc.WellFormed (p : Proc Op χ V) : Prop :=
  ∀ ap ∈ p, ap.WellFormed Op χ

section Semantics

/-- Interpretation of an operator set as concrete values. -/
class OpInterp (V S : Type u) where
  interp : (op : Op) → Vector V (arity.ι op) → StateT S Option (Vector V (arity.ω op))
  asBool : V → Bool

variable (V S) [OpInterp Op V S]
variable [DecidableEq χ]

inductive Label where
  | op (op : Op) (args : Vector V (arity.ι op))
  | tau
  deriving Repr

abbrev Labels := List (Label Op V)

def Labels.AllSilent (ls : Labels Op V) : Prop := ∀ l ∈ ls, l = .tau

def Labels.OneOp (ls : Labels Op V) : Prop :=
  ∃ (ls' ls'' : Labels Op V) (op : Op) (args : _),
    ls = ls' ++ (Label.op op args :: ls'') ∧
    ls'.AllSilent Op V ∧
    ls''.AllSilent Op V

structure ExprState where
  vars : χ → Option V
  state : S

  -- Ghost states for the simulation relation
  -- TODO: maintain these ghost states in the
  --       step function.
  definedVars : List χ
  pathConds : List (Bool × ChanName χ)

abbrev ExprStateM := StateT (ExprState χ V S) Option

def ExprStateM.getVar (v : χ) : ExprStateM χ V S V := do
  match (← get).vars v with
  | some val => return val
  | none => .failure

def ExprStateM.setVar (v : χ) (val : V) : ExprStateM χ V S PUnit := do
  modify λ s => {
    s with vars := λ x => if x = v then some val else s.vars x
  }

def ExprStateM.liftS (s : StateT S Option T) : ExprStateM χ V S T := do
  let (val, state) ← s.run (← get).state
  modify λ s => { s with state }
  return val

inductive ExprResult (n : ℕ) where
  | ret (vals : Vector V n)
  | cont (expr : Expr Op χ n)

def Expr.step : Expr Op χ n → ExprStateM χ V S (Label Op V × ExprResult Op χ V n)
  | .ret vars => do
    let vals ← vars.mapM (.getVar _ _ _)
    return (.tau, .ret vals)
  | .op o args rets cont => do
    let argVals ← args.mapM (.getVar _ _ _)
    let retVals ← .liftS _ _ _ (OpInterp.interp o argVals)
    (rets.zip retVals).forM λ (v, val) => .setVar _ _ _ v val
    return (.op o argVals, .cont cont)
  | .br cond left right => do
    let condVal ← .getVar _ _ _ cond
    if OpInterp.asBool Op S condVal then
      return (.tau, .cont left)
    else
      return (.tau, .cont right)

abbrev ProcStateM := StateT S List
abbrev ChanUpdate := List (χ × V)

/-- Channel update should not have duplicate variables. -/
def ChanUpdate.WellFormed (upd : ChanUpdate χ V) : Prop :=
  (upd.map Prod.fst).Nodup

def ProcStateM.liftS (s : StateT S Option T) : ProcStateM S T := do
  match s.run (← get) with
  | none => .failure
  | some (val, state) =>
    set state
    return val

def ProcStateM.popInputs
  (inputs : Vector (InputBuf χ V) n) :
  ProcStateM S (Vector V n × Vector (InputBuf χ V) n) := do
  let vs ← inputs.mapM λ (var, buf) =>
    match buf with
    | [] => .failure
    | val :: rest => return (val, (var, rest))
  return (vs.map Prod.fst, vs.map Prod.snd)

/-- Fire the `i`-th atomic process and return the modified process with channel pushes. -/
def AtomicProc.step :
  AtomicProc Op χ V → ProcStateM S (Label Op V × AtomicProc Op χ V × ChanUpdate χ V)
  | .op o inputs outputs => do
    let (inputVals, inputs') ← .popInputs _ _ _ inputs
    let outputVals ← ProcStateM.liftS _ (OpInterp.interp o inputVals)
    return (
      .op o inputVals, .op o inputs' outputs,
      (outputs.zip outputVals).toList,
    )
  | .steer
      (decider, deciderVal :: restDecider)
      (input, inputVal :: restInput)
      output =>
    return (
      .tau, .steer (decider, restDecider) (input, restInput) output,
      if OpInterp.asBool Op S deciderVal then [(output, inputVal)]
      else [],
    )
  | .merge
      (decider, deciderVal :: restDecider)
      (input₁, inputVal₁ :: restInput₁)
      (input₂, inputVal₂ :: restInput₂)
      output =>
    return (
      .tau, .merge (decider, restDecider) (input₁, restInput₁) (input₂, restInput₂) output,
      if OpInterp.asBool Op S deciderVal then [(output, inputVal₁)]
      else [(output, inputVal₂)],
    )
  | .forward inputs outputs => do
    let (inputVals, inputs') ← .popInputs _ _ _ inputs
    return (.tau, .forward inputs' outputs, (outputs.zip inputVals).toList)
  | _ => .failure

/-- Pushes the value to the buffer if the variables match. -/
def InputBuf.push (var : χ) (val : V) : InputBuf χ V → InputBuf χ V
  | (v, buf) => if v = var then (v, buf ++ [val]) else (v, buf)

def AtomicProc.push (var : χ) (val : V) : AtomicProc Op χ V → AtomicProc Op χ V
  | .op o inputs outputs =>
    .op o (inputs.map (InputBuf.push _ _ var val)) outputs
  | .steer decider input output =>
    .steer (InputBuf.push _ _ var val decider) (InputBuf.push _ _ var val input) output
  | .merge decider input₁ input₂ output =>
    .merge
      (InputBuf.push _ _ var val decider)
      (InputBuf.push _ _ var val input₁)
      (InputBuf.push _ _ var val input₂)
      output
  | .forward inputs outputs =>
    .forward (inputs.map (InputBuf.push _ _ var val)) outputs

def Proc.push (var : χ) (val : V) (p : Proc Op χ V) : Proc Op χ V :=
  p.map (AtomicProc.push _ _ _ var val)

def Proc.pushAll (updates : ChanUpdate χ V) (p : Proc Op χ V) : Proc Op χ V :=
  updates.foldl (λ p (var, val) => p.push _ _ _ var val) p

def Proc.step (p : Proc Op χ V) : ProcStateM S (Label Op V × Proc Op χ V) := do
  -- Chose one atomic process to fire
  let m ← (List.finRange p.length).map (λ i => do
    let (lbl, ap, upd) ← p[i].step Op χ V S
    return (lbl, p.set i ap, upd))
  -- Apply the effects of the atomic process
  let (lbl, p', upd) ← m
  -- Apply channel updates
  let p'' := Proc.pushAll _ _ _ upd p'
  return (lbl, p'')

structure Expr.Config n where
  expr : ExprResult Op χ V n
  estate : ExprState χ V S

/-- Initial `Expr` state, with `vars` assigning free variables. -/
def Expr.Config.init
  (expr : Expr Op χ n)
  (state : S)
  (vars : List (χ × V)) : Expr.Config Op χ V S n
  := {
    expr := .cont expr,
    estate := {
      vars := λ v => (vars.find? (·.1 = v)).map (·.2),
      state,
      definedVars := [],
      pathConds := [],
    }
  }

structure Proc.Config where
  proc : Proc Op χ V
  state : S

/-- Convert vars to names of free channels. -/
def ChanUpdate.init
  (vars : List (χ × V)) : ChanUpdate (ChanName χ) V :=
  vars.map λ (v, val) =>
    (.var v 0 [], val)

/-- Initial process state, with `vars` given as initial
values pushed to some channels. -/
def Proc.Config.init
  (proc : Proc Op χ V)
  (state : S)
  (vars : List (χ × V)) : Proc.Config Op χ V S
  := { proc := proc.pushAll _ _ _ vars, state }

/-
Various small-step operational semantics.
-/

def Expr.Step (n : ℕ)
  (c : Expr.Config Op χ V S n) (l : Label Op V) (c' : Expr.Config Op χ V S n) : Prop :=
  match c.expr with
  | .ret _ => False
  | .cont expr =>
    some ((l, c'.expr), c'.estate) = (expr.step Op χ V S).run c.estate

def Proc.Step
  (c : Proc.Config Op χ V S) (l : Label Op V) (c' : Proc.Config Op χ V S) : Prop :=
  ((l, c'.proc), c'.state) ∈ (c.proc.step Op χ V S).run c.state

inductive TransClosure (R : C → L → C → Prop) : C → List L → C → Prop where
  | base : R c l c' → TransClosure R c [l] c'
  | trans : R c l c' → TransClosure R c' ls c'' → TransClosure R c (l :: ls) c''

inductive TransReflClosure (R : C → L → C → Prop) : C → List L → C → Prop where
  | refl : TransReflClosure R c [] c
  | trans : R c l c' → TransReflClosure R c' ls c'' → TransReflClosure R c (l :: ls) c''

abbrev Expr.StepPlus n := TransClosure (Expr.Step Op χ V S n)
abbrev Expr.StepStar n := TransReflClosure (Expr.Step Op χ V S n)

abbrev Proc.StepPlus := TransClosure (Proc.Step Op χ V S)
abbrev Proc.StepStar := TransReflClosure (Proc.Step Op χ V S)

/-- `pc` simulates `ec` as witnessed by the simulation relation `R`. -/
inductive Refines
  [DecidableEq χ₁]
  [DecidableEq χ₂]
  (ec : Expr.Config Op χ₁ V S n)
  (pc : Proc.Config Op χ₂ V S)
  (R : Expr.Config Op χ₁ V S n → Proc.Config Op χ₂ V S → Prop) where
  | mk
    (hr : R ec pc)
    (hcoind : ∀ ec' ec'' l₁ pc',
      R ec' pc' →
      Expr.Step _ _ V S n ec' l₁ ec'' →
      ∃ pc'' ls₂,
        Proc.StepPlus _ _ V S pc' ls₂ pc'' ∧
        /- TODO: match labels? -/
        R ec'' pc'')

end Semantics

section Simulation

variable (V S) [OpInterp Op V S]
variable [DecidableEq χ]
variable [DecidableEq Op]

def AtomicProc.inputs (ap : AtomicProc Op χ V) : List (InputBuf χ V) :=
  match ap with
  | .op _ inputs _ => inputs.toList
  | .steer decider input _ => [decider, input]
  | .merge decider input₁ input₂ _ => [decider, input₁, input₂]
  | .forward inputs _ => inputs.toList

def AtomicProc.outputs (ap : AtomicProc Op χ V) : List χ :=
  match ap with
  | .op _ _ outputs => outputs.toList
  | .steer _ _ output => [output]
  | .merge _ _ _ output => [output]
  | .forward _ outputs => outputs.toList

def AtomicProc.HasInput (ap : AtomicProc Op χ V) (v : χ) : Prop :=
  ∃ inp ∈ ap.inputs, inp.1 = v

def AtomicProc.HasInputWithBuf (ap : AtomicProc Op χ V) (v : χ) (buf : List V) : Prop :=
  ∃ inp ∈ ap.inputs, inp = (v, buf)

def AtomicProc.HasEmptyInputs (ap : AtomicProc Op χ V) : Prop :=
  ∀ inp ∈ ap.inputs, inp.2 = []

def AtomicProc.MatchModuloBuffers : AtomicProc Op χ V → AtomicProc Op χ V → Prop
  | .op o₁ inputs₁ outputs₁, .op o₂ inputs₂ outputs₂ =>
    if o₁ = o₂ then
      List.Forall₂ (λ i₁ i₂ => i₁.1 = i₂.1) inputs₁.toList inputs₂.toList ∧
      outputs₁.toList = outputs₂.toList
    else
      False
  | .steer decider₁ input₁ output₁, .steer decider₂ input₂ output₂ =>
    decider₁.1 = decider₂.1 ∧
    input₁.1 = input₂.1 ∧
    output₁ = output₂
  | .merge decider₁ input₁₁ input₁₂ output₁, .merge decider₂ input₂₁ input₂₂ output₂ =>
    decider₁.1 = decider₂.1 ∧
    input₁₁.1 = input₂₁.1 ∧
    input₁₂.1 = input₂₂.1 ∧
    output₁ = output₂
  | .forward inputs₁ outputs₁, .forward inputs₂ outputs₂ =>
    List.Forall₂ (λ i₁ i₂ => i₁.1 = i₂.1) inputs₁.toList inputs₂.toList ∧
    outputs₁.toList = outputs₂.toList
  | _, _ => False

def Proc.MatchModuloBuffers (p₁ p₂ : Proc Op χ V) : Prop :=
  List.Forall₂ (AtomicProc.MatchModuloBuffers Op χ V) p₁ p₂

def Proc.IsDAG (p : Proc Op χ V) : Prop :=
  ∀ i j, (hi : i < p.length) → (hj : j ≤ i) →
    ∀ output ∈ p[i].outputs, ¬ p[j].HasInput Op χ V output

def Proc.HasEmptyInputs (p : Proc Op χ V) : Prop :=
  ∀ ap ∈ p, ap.HasEmptyInputs Op χ V

def SimR (ec : Expr.Config Op χ V S n) (pc : Proc.Config Op (ChanName χ) V S) : Prop :=
  -- Equal global states
  ec.estate.state = pc.state ∧
  -- Process is a DAG
  pc.proc.IsDAG _ _ _ ∧
  -- We can find a fragment of the compiled process list
  -- that is compiled from the current expression.
  ∃ contextLeft currentProc contextRight,
    pc.proc = contextLeft ++ currentProc ++ contextRight ∧
    contextLeft.HasEmptyInputs _ _ _ ∧
    -- TODO: more constraints for the final state
    (∀ vs, ec.expr = .ret vs → currentProc = [] ∧ contextRight = []) ∧
    -- For continuations, we require that `currentProc` is exactly
    -- their compiled process (modulo buffer differences).
    (∀ expr, ec.expr = .cont expr →
      -- Expr is well-formed
      expr.WellFormed _ _ ∧
      -- Match except for exact buffers
      (∃ currentProc',
        compile _ _ ec.estate.definedVars ec.estate.pathConds expr = some currentProc' ∧
        currentProc.MatchModuloBuffers _ _ _ currentProc') ∧
      -- For all inputs of processes in `currentProc`
      (∀ ap ∈ currentProc, ∀ inp ∈ ap.inputs,
        -- Check if the channel name corresponds to a live variable
        -- in the current branch
        let IsLiveVar (name : ChanName χ) val := ∃ var,
          ec.estate.vars var = some val ∧
          name = .var var (ec.estate.definedVars.count var) ec.estate.pathConds
        -- If it's a live var, the channel buffer should have the corresponding value
        (∀ val, IsLiveVar inp.1 val → inp.2 = [val]) ∧
        -- Otherwise it's empty.
        ((∀ val, ¬ IsLiveVar inp.1 val) → inp.2 = []))) ∧
    -- The remaining processes in `contextRight` should be of the form
    --
    --   `p₁ ... pₘ || merge x n || p'₁ ... p'ₖ || merge x n || ...`
    --
    -- i.e., a sequence of processes interspersed with consecutive
    -- chunks of n merge nodes.
    -- Furthermore, all processes other than these merges should
    -- have empty input buffers, and the merges will have exactly
    -- one Boolean in the decider buffers corresponding to the
    -- branching decision.
    (∃ (chunks : List (Proc Op _ V × Proc Op _ V)) (tail : Proc Op _ V),
      contextRight = (joinM (chunks.map (λ (l, r) => l ++ r))) ++ tail ∧
      -- The first half chunks and the tail have empty inputs
      (∀ chunk₁ chunk₂, (chunk₁, chunk₂) ∈ chunks → chunk₁.HasEmptyInputs _ _ _) ∧
      tail.HasEmptyInputs _ _ _ ∧
      -- The second half chunk corresponds exactly to the merge nodes
      -- generated along the branches marked in the current `pathConds`.
      List.Forall₂
        (λ (_, chunk) (b, cond) =>
          chunk.length = n ∧
          ∀ i : ℕ, (h : i < chunk.length) →
            ∃ v,
              OpInterp.asBool Op S v = b ∧
              let prevPathCond := ec.estate.pathConds.drop (i + 1)
              -- This should match `compile.genMerges` except for the decider buffers
              chunk[i]'h = .merge
                (.merge_cond cond, [v]) -- Decider buffer
                (.empty _ (.dest i ((true, cond) :: prevPathCond)))
                (.empty _ (.dest i ((false, cond) :: prevPathCond)))
                (.dest i prevPathCond))
        chunks ec.estate.pathConds)

  /- Invariants?
  1. pc.proc = left ++ right such that right == compile ? ? current_expr, and none of left is fireable (empty input channels).
  2. pc.proc is a DAG: output channels only occur in atoms with higher indices.
  3. Equal states.
  4. Final destinations are empty unless expr is a return.
  5. ** For all live variables in ec.vars, all processes in <right>, if having
     input channel with the same pathConds, the channel buffer is a singleton
     with the corresponding value.
     - shadowing?
  -/

/-- Well-formed `Expr` compiles to well-formed processes. -/
theorem wf_expr_compile_to_wf_proc
  (e : Expr Op χ n)
  (p : Proc Op (ChanName χ) V)
  (hwf : e.WellFormed _ _)
  (hcomp : compile _ _ definedVars pathConds e = some p) :
  p.WellFormed _ _ := sorry

/-- Output of compile should be a DAG. -/
theorem compile_is_dag
  {e : Expr Op χ n}
  {p : Proc Op (ChanName χ) V}
  (hcomp : compile _ _ definedVars pathConds e = some p) :
  p.IsDAG _ _ _ := sorry

/-- Output process of compile has empty buffers. -/
theorem compile_empty_buf
  (e : Expr Op χ n)
  (p : Proc Op (ChanName χ) V)
  (hcomp : compile _ _ definedVars pathConds e = some p) :
  p.HasEmptyInputs _ _ _ := sorry

/-- Pushing preserves the "shape" of the process. -/
theorem push_preserves_shape
  {p : Proc Op χ V}
  {upd : ChanUpdate χ V} :
  (p.pushAll _ _ _ upd).MatchModuloBuffers _ _ _ p := sorry

theorem push_preserves_dag
  {p : Proc Op χ V}
  (upd : ChanUpdate χ V)
  (hd : p.IsDAG _ _ _) :
  (p.pushAll _ _ _ upd).IsDAG _ _ _ := sorry

/-- TODO: should be auto derived. -/
instance [DecidableEq χ] : DecidableEq (ChanName χ) := sorry

/-- Initial configs satisfy the simulation relation. -/
theorem sim_init_config
  (e : Expr Op χ n)
  (p : Proc Op (ChanName χ) V)
  (hwf : e.WellFormed _ _)
  (hcomp : compile _ _ [] [] e = some p)
  (s : S)
  (initVars : List (χ × V)) :
  SimR _ _ _ _
    (Expr.Config.init _ _ _ _ e s initVars)
    (Proc.Config.init _ _ _ _ p s (ChanUpdate.init _ _ initVars)) := by
  and_intros
  · rfl
  · have := compile_is_dag _ _ _ hcomp
    exact push_preserves_dag _ _ _ _ this
  · -- simp only [compile] at hcomp
    generalize (ChanUpdate.init χ V initVars) = initChans
    exists [], p.pushAll _ _ _ initChans, []
    and_intros
    · simp; rfl
    · simp [Proc.HasEmptyInputs]
    · simp [Expr.Config.init]
    · intros e' he'
      simp [Expr.Config.init] at he'
      simp only [←he']
      and_intros
      · exact hwf
      · exists p
        simp only [Expr.Config.init, hcomp, true_and]
        apply push_preserves_shape
      · intros ap hap inp hinp
        and_intros
        -- TODO: reason about facts about `pushAll`
        · simp [Expr.Config.init]
          sorry
        · simp [Expr.Config.init]
          sorry
    · exists [], []
      and_intros
      · simp [joinM]
      · simp
      · simp [Proc.HasEmptyInputs]
      · simp [Expr.Config.init]

/-- Main simulation requirement. -/
theorem sim_step
  (ec ec' : Expr.Config Op χ V S n)
  (pc : Proc.Config Op (ChanName χ) V S)
  (hsim : SimR _ _ _ _ ec pc)
  (hstep : Expr.Step _ _ _ _ n ec l ec') :
  ∃ pc' ls,
    Proc.StepPlus _ _ _ _ pc ls pc' ∧
    SimR _ _ _ _ ec' pc' := by
  simp [Expr.Step] at hstep
  cases hec : ec.expr with
  | ret vars => simp [hec] at hstep
  | cont expr =>
    simp [hec] at hstep
    -- TODO: maybe use separate theorems to extract these facts from `SimR`
    have ⟨
      hsim_eqs,
      hsim_dag,
      ⟨
        ctxLeft, curProc, ctxRight,
        hproc,
        hctx_left_empty,
        _,
        hsim_cont,
        hsim_tail,
      ⟩,
    ⟩ := hsim
    have ⟨
      hwf_expr,
      ⟨comp_expr, hcomp_expr, hsame_shape_proc⟩,
      hlive_vars,
    ⟩ := hsim_cont expr hec
    cases hexpr : expr with
    | ret vars =>
      simp [hexpr, Expr.step] at hstep
      simp [compile, hexpr] at hcomp_expr
      simp [← hcomp_expr, Proc.MatchModuloBuffers] at hsame_shape_proc
      sorry
    | op => sorry
    | br => sorry

theorem comp_refines
  (e : Expr Op χ n)
  (p : Proc Op (ChanName χ) V)
  (hwf : e.WellFormed _ _)
  (hcomp : compile _ _ [] [] e = some p)
  (s : S)
  (initVars : List (χ × V)) :
  Refines _ _ _
    (Expr.Config.init _ _ _ _ e s initVars)
    (Proc.Config.init _ _ _ _ p s (ChanUpdate.init _ _ initVars))
    (SimR _ _ _ _) := by
  constructor
  · apply sim_init_config <;> assumption
  · intros ec ec' l₁ pc hsim hstep
    apply sim_step <;> assumption

end Simulation

section Examples

inductive MiniOp where
  | add
  | less
  | const (n : Nat)
  deriving Repr

instance : ToString MiniOp where
  toString | .add => "add"
           | .less => "less"
           | .const n => s!"const[{n}]"

instance : OpArity MiniOp where
  ι | .add => 2
    | .less => 2
    | .const _ => 0
  ω | .add => 1
    | .less => 1
    | .const _ => 1

def exampleExpr : Expr MiniOp String 1 :=
  .op .less #v["x", "y"] #v["b"] <|
  .br "b"
    (.op .add #v["x", "y"] #v["z"]
      (.ret #v["z"]))
    (.op (.const 42) #v[] #v["z"]
      (.ret #v["z"]))

#eval @compileTop MiniOp String _ 1 ℕ _ exampleExpr

end Examples
