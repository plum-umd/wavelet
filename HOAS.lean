import Mathlib.Data.List.Basic

section

variable
  (Op : Type u) -- Type of operators
  (χ : Type v) -- Type of variables

class OpArity where
  ι : Op → ℕ
  ω : Op → ℕ

variable [arity : OpArity Op]

/-- `MuTree m n` is an expression that either returns n variables or does a tail call with m arguments. -/
inductive MuTree : ℕ → ℕ → Type (max u v) where
  | ret : Vector χ n → MuTree m n
  | tail : Vector χ m → MuTree m n
  | op : (op : Op) → Vector χ (arity.ι op) → (Vector χ (arity.ω op) → MuTree m n) → MuTree m n
  | br : χ → MuTree m n → MuTree m n → MuTree m n
  | fix : (Vector χ m → MuTree m n) → Vector χ m → (Vector χ n → MuTree m' n') → MuTree m' n'

/-- Substitutes return and tail calls with different expressions. -/
def MuTree.bindCont
  (contRet : Vector χ n → MuTree Op χ m' n')
  (contTail : Vector χ m → MuTree Op χ m' n') :
  MuTree Op χ m n →
  MuTree Op χ m' n'
  | .ret v => contRet v
  | .tail args => contTail args
  | .op o args cont => .op o args (λ v => bindCont contRet contTail (cont v))
  | .br c left right => .br c (bindCont contRet contTail left) (bindCont contRet contTail right)
  | .fix body args cont => .fix body args (λ v => bindCont contRet contTail (cont v))

/-- Interpretation of an operator set as concrete values. -/
class OpInterp (V S : Type u) where
  interp : (op : Op) → Vector V (arity.ι op) → StateT S Option (Vector V (arity.ω op))
  asBool : V → Bool

inductive Label (V : Type w) where
  | op (op : Op) (args : Vector V (arity.ι op))
  | tau
  deriving Repr

/-- Reduces the expression by one step in the given interpretation. -/
def MuTree.step [OpInterp Op V S]
  : MuTree Op V m n → StateT S Option (Label Op V × (Vector V n ⊕ MuTree Op V m n))
  | .ret v => return (.tau, .inl v)
  | .tail _ => StateT.lift none -- Cannot reduce from tail calls
  | .op o args cont => return (.op o args, .inr (cont (← OpInterp.interp o args)))
  | .br c left right =>
    if OpInterp.asBool Op S c then return (.tau, .inr left)
    else return (.tau, .inr right)
  | .fix body args cont =>
    return (.tau, .inr (bindCont Op V
      cont
      (λ args => .fix body args cont)
      (body args)))
partial def MuTree.steps [OpInterp Op V S]
  (e : MuTree Op V m n) : StateT S Option (List (Label Op V) × Vector V n)
  := do
    match ← MuTree.step Op e with
    | (l, .inl v) => return ([l], v)
    | (l, .inr e') => do
      let (ls, res) ← steps e'
      return (l :: ls, res)

example (x : χ) : MuTree Op χ m 1 := .ret #v[x]

example (x : χ) (y : χ) : MuTree Op χ m 2 :=
  .br x
    (.ret #v[x, y])
    (.ret #v[y, x])

end

section

variable (Op : Type u) (χ : Type u) (V : Type u)
variable [arity : OpArity Op]
variable (S) [OpInterp Op V S]

abbrev Input : Type u := χ × List V

/-- `AtomicProc n` -/
inductive AtomicProc : ℕ → Type u where
  | op (op : Op) (inputs : Vector (Input χ V) (arity.ι op)) : AtomicProc (arity.ω op)
  | steer (decider : Input χ V) (input : Input χ V) : AtomicProc 1
  | merge (decider : Input χ V) (input₁ input₂ : Input χ V) : AtomicProc 1
  -- Forward needs to be n-ary to allow combining multiple outputs
  | forward (input : Vector (Input χ V) n) : AtomicProc n

/--
Essentially the parallel composition of a list of atomic processes,
with data dependencies going forward through the closure.
-/
inductive DagProc : ℕ → Type u where
  | atom : AtomicProc Op χ V n → DagProc n
  | par : DagProc n → (Vector χ n → DagProc m) → DagProc m

def AtomicProc.resolvePush :
  AtomicProc Op (χ × Option V) V n → AtomicProc Op χ V n
  | .op o inputs => .op o (inputs.map resolve)
  | .steer decider input => .steer (resolve decider) (resolve input)
  | .merge decider input₁ input₂ =>
    .merge (resolve decider) (resolve input₁) (resolve input₂)
  | .forward inputs => .forward (inputs.map resolve)
  where resolve (i : Input (χ × Option V) V) : Input χ V :=
    match i.fst.snd with
    | none => (i.fst.fst, i.snd)
    | some v => (i.fst.fst, i.snd ++ [v])

def DagProc.resolvePush : DagProc Op (χ × Option V) V n → DagProc Op χ V n
  | .atom ap => .atom (ap.resolvePush Op χ V)
  | .par p k =>
    .par p.resolvePush
      -- Don't change buffers of other binders
      (λ xs => (k (xs.map (Prod.mk · none))).resolvePush)

/-- Pushes one value to the i-th bound channel. -/
def push (i : Fin n) (v : V) (p : ∀ χ, Vector χ n → DagProc Op χ V m) :
  ∀ χ, Vector χ n → DagProc Op χ V m :=
  λ χ xs =>
    -- Replace variables with temporarily pushed values
    let p' := p (χ × Option V)
      (xs.mapFinIdx λ j _ _ => (xs[j], if i = j then some v else none))
    -- Push to the buffer at the i-th channel
    p'.resolvePush Op χ V

/-- Pushes all channels bound by the top-level binder. -/
def pushAll (vs : Vector V n) (p : ∀ χ, Vector χ n → DagProc Op χ V m) :
  ∀ χ, Vector χ n → DagProc Op χ V m :=
  λ χ xs =>
    let p' := p (χ × Option V)
      (xs.mapFinIdx λ j _ _ => (xs[j], some vs[j]))
    p'.resolvePush Op χ V

/-- Selectively pushes channels bound by the top-level binder. -/
def pushAllOpt (vs : Vector (Option V) n) (p : ∀ (χ : Type u), Vector χ n → DagProc Op χ V m) :
  ∀ (χ : Type u), Vector χ n → DagProc Op χ V m :=
  λ χ xs =>
    let p' := p (χ × Option V)
      (xs.mapFinIdx λ j _ _ => (xs[j], vs[j]))
    p'.resolvePush Op χ V

/-! Some utilities to print processes. -/
section Print

inductive ChanName.{v} : Type v where
  | chan (n : ℕ)
  deriving Nonempty

instance : ToString ChanName where
  toString | .chan n => s!"c{n}"

def AtomicProc.toString [ToString Op] [ToString V] : AtomicProc Op ChanName V n → String
  | .op o inputs =>
    let inputStr := String.intercalate ", " (inputs.toList.map (λ (c, buf) => s!"{c} : {buf}"))
    s!"{o}({inputStr})"
  | .steer (decider, buf₁) (input, buf₂) =>
    s!"steer({decider} : {buf₁}, {input} : {buf₂})"
  | .merge (decider, buf₁) (input₁, buf₂) (input₂, buf₃) =>
    s!"merge({decider} : {buf₁}, {input₁} : {buf₂}, {input₂} : {buf₃})"
  | .forward inputs =>
    let inputStr := String.intercalate ", " (inputs.toList.map (λ (c, buf) => s!"{c} : {buf}"))
    s!"forward({inputStr})"

/-! Some utilities -/
mutual

partial def DagProc.contToString [ToString Op] [ToString V]
  (offset : ℕ) (k : Vector ChanName n → DagProc Op ChanName V m) : Vector ChanName n × String × ℕ :=
  let names := (Vector.range n).map (λ i => ChanName.chan (offset + i))
  (names, (k names).toString (offset + n))

partial def DagProc.toString [ToString Op] [ToString V]
  (offset : ℕ) (p : DagProc Op ChanName V m) : String × ℕ :=
  match p with
  | .atom ap => (ap.toString Op V, offset)
  | .par p k =>
    let (lhs, offset') := p.toString offset
    let (names, rhs, offset'') := DagProc.contToString offset' k
    (s!"{lhs} => {names.toList} || {rhs}", offset'')

end -- mutual

end Print

/-- `Proc` structural equivalence -/
inductive Equiv : DagProc Op χ V n → DagProc Op χ V n → Prop where
  /-- Commutes two atomic processes if there is no data dependency. -/
  | equiv_par_comm (k : Vector χ n → Vector χ m → DagProc Op χ V k) :
    Equiv (.par p λ vs => .par q λ vs' => k vs vs') (.par q λ vs' => .par p λ vs => k vs vs')
  | equiv_par_assoc :
    Equiv (.par (.par p k) k') (.par p λ vs => .par (k vs) k')
  /- TODO: structural rule for inaction/unit? -/
  | equiv_refl : Equiv p p
  | equiv_symm : Equiv p q → Equiv q p
  | equiv_trans : Equiv p q → Equiv q r → Equiv p r
  | equiv_congr :
    Equiv p p' →
    (∀ xs, Equiv (k xs) (k' xs)) →
    Equiv (.par p k) (.par p' k')

infix:50 " ≡ " => Equiv

inductive AtomicProc.Step : (∀ χ, AtomicProc Op χ V n) → Label Op V → AtomicProc Op χ V n → Vector (Option V) n → Prop where
  | step_steer :
    p χ = .steer (decider, deciderVal :: deciderBuf) (input, inputVal :: inputBuf) →
    Step
      p .tau
      (.steer (decider, deciderBuf) (input, inputBuf))
      (#v[if OpInterp.asBool Op S deciderVal then some inputVal else none])
  | step_forward :
    p χ = .forward inputs →
    Step
      p .tau
      (.forward (inputs.map (λ (x, buf) => (x, buf.tail))))
      (inputs.map (λ (_, buf) => match buf with
        | [] => none
        | v :: _ => some v))

inductive DagProc.Step' : (∀ χ, DagProc Op χ V n) → Label Op V → DagProc Op χ V n → Vector (Option V) n → Prop where
  | step_atom :
    AtomicProc.Step Op χ V S ap l ap' outputVals →
    Step' (λ χ => .atom (ap χ)) l (.atom ap') outputVals
  | step_par_left {k : ∀ χ, Vector χ n → DagProc Op χ V m} :
    Step' p l p' outputVals →
    Step' (λ χ => .par (p χ) (k χ)) l (.par p' (pushAllOpt Op V outputVals k χ)) (Vector.replicate m none)
  | step_par_right
    {p : ∀ χ, DagProc Op χ V n}
    {k : ∀ χ, Vector χ n → DagProc Op χ V m}
    {k' : Vector χ n → DagProc Op χ V m} :
    (∀ xs : ∀ χ, Vector χ n, Step' (λ χ => k χ (xs χ)) l (k' (xs χ)) outputVals) →
    Step' (λ χ => .par (p χ) (k χ)) l (.par (p χ) (k χ)) outputVals

def DagProc.Step (p : ∀ χ, DagProc Op χ V n) (l : Label Op V) (q : ∀ χ, DagProc Op χ V n) (outputVals : Vector (Option V) n) : Prop
  := ∃ p' q' : ∀ χ, DagProc Op χ V n,
    (∀ χ, Equiv Op χ V (p χ) (p' χ)) ∧
    (∀ χ, Equiv Op χ V (q χ) (q' χ)) ∧
    ∀ χ, DagProc.Step' Op χ V S p' l (q' χ) outputVals

end

section Compile

variable (Op : Type u) (χ : Type u) (V : Type u)
variable [arity : OpArity Op]
variable (S) [OpInterp Op V S]

def compile (e : MuTree Op χ m n) : DagProc Op χ V n :=
  match e with
  | .ret vs => .atom (.forward (vs.map (λ v => (v, []))))
  | .op o args cont =>
    let ap : AtomicProc Op χ V (OpArity.ω o) := .op o (args.map (λ v => (v, [])))
    .par (.atom ap) (λ vs => compile (cont vs))
  | .br c left right =>
    sorry
  -- Recursion not supported yet
  | .tail ..
  | .fix .. => sorry

end Compile

inductive MiniOp where
  | add
  | less
  | const (n : Nat)
  deriving Repr

instance : ToString MiniOp where
  toString | .add => "add"
           | .less => "less"
           | .const n => s!"const[{n}]"

namespace MiniOp

instance : OpArity MiniOp where
  ι | .add => 2
    | .less => 2
    | .const _ => 0
  ω | .add => 1
    | .less => 1
    | .const _ => 1

instance : OpInterp MiniOp ℕ Unit where
  interp | .add => λ args => return #v[args[0] + args[1]]
         | .less => λ args => return #v[if args[0] < args[1] then 1 else 0]
         | .const n => λ _ => return #v[n]
  asBool | 0 => false
         | _ => true

abbrev Expr := MuTree MiniOp

def exampleAdd (x : χ) (y : χ) : Expr χ 0 1 :=
  .op .add #v[x, y] (λ v => .ret #v[v[0]])

/--
def f(x, y) = if x < y then x else f(x + 10, y)
-/
def exampleFix (x : χ) (y : χ) : Expr χ 0 1 :=
  .fix (λ v => let x := v[0]; let y := v[1]
    .op .less #v[x, y] (λ v => let less? := v[0]
    .br less?
      (.op (.const 10) #v[] (λ v => let c := v[0]
      (.op .add #v[x, c] (λ v => let x' := v[0]
      .tail #v[x', y]))))

      (.ret #v[x])))
    #v[x, y]
    (λ v => .ret #v[v[0]])

def MiniExpr.steps (e : Expr ℕ m n) : StateT Unit Option (List (Label MiniOp ℕ) × Vector ℕ n) := MuTree.steps MiniOp e

#eval (MiniExpr.steps (exampleAdd 1 202)).run ()

#eval (MiniExpr.steps (exampleFix 5 20)).run ()

def exampleProc1 (χ) (x : χ) (y : χ) : AtomicProc MiniOp χ V 1 :=
  .steer (x, []) (y, [])

def exampleProc2 (χ) (v : Vector χ 3) : DagProc MiniOp χ ℕ 1 :=
  let x := v[0]; let y := v[1]; let z := v[2]
  .par (.atom (.steer (x, []) (y, []))) λ vs => let y' := vs[0]
  .par (.atom (.steer (x, []) (z, []))) λ vs => let z' := vs[0]
        .atom (.op MiniOp.add #v[(y', []), (z', [])])

#eval (DagProc.contToString MiniOp ℕ 0 (exampleProc2 ChanName)).2.1

#eval (DagProc.contToString MiniOp ℕ 0
  ((pushAllOpt MiniOp ℕ #v[some 101, none, some 300] exampleProc2) ChanName)).2.1

#eval (DagProc.contToString MiniOp ℕ 0
  (pushAllOpt MiniOp ℕ #v[some 100, some 200, none]
  (pushAllOpt MiniOp ℕ #v[some 101, none, some 300] exampleProc2) ChanName)).2.1

end MiniOp
