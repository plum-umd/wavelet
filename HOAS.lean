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
class OpInterp (V : Type u) (M : Type u → Type w) where
  interp : (op : Op) → Vector V (arity.ι op) → OptionT M (Vector V (arity.ω op))
  asBool : V → Bool

inductive Label (V : Type w) where
  | op (op : Op) (args : Vector V (arity.ι op))
  | tau
  deriving Repr

/-- Reduces the expression by one step in the given interpretation. -/
def MuTree.step [OpInterp Op V M] [Monad M]
  : MuTree Op V m n → OptionT M (Label Op V × (Vector V n ⊕ MuTree Op V m n))
  | .ret v => return (.tau, .inl v)
  | .tail _ => .fail -- Cannot reduce from tail calls
  | .op o args cont => return (.op o args, .inr (cont (← OpInterp.interp o args)))
  | .br c left right =>
    if OpInterp.asBool Op M c then return (.tau, .inr left)
    else return (.tau, .inr right)
  | .fix body args cont =>
    return (.tau, .inr (bindCont Op V
      cont
      (λ args => .fix body args cont)
      (body args)))

partial def MuTree.steps [OpInterp Op V M] [Monad M]
  (e : MuTree Op V m n) : OptionT M (List (Label Op V) × Vector V n)
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

inductive MiniOp where
  | add
  | less
  | const (n : Nat)
  deriving Repr

namespace MiniOp

instance : OpArity MiniOp where
  ι | .add => 2
    | .less => 2
    | .const _ => 0
  ω | .add => 1
    | .less => 1
    | .const _ => 1

instance : OpInterp MiniOp ℕ Id where
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

def MiniExpr.steps (e : Expr ℕ m n) : OptionT Id (List (Label MiniOp ℕ) × Vector ℕ n) := MuTree.steps MiniOp e

#eval MiniExpr.steps (exampleAdd 1 202)

#eval MiniExpr.steps (exampleFix 5 20)

end MiniOp

section

variable (Op : Type u) (χ : Type v) (V : Type u)
variable [arity : OpArity Op]
variable [OpInterp Op V M]

abbrev Input : Type (max v u) := χ × List V

inductive AtomicProc : ℕ → Type (max u v) where
  | op (op : Op) (inputs : Vector (Input χ V) (arity.ι op)) : AtomicProc (arity.ω op)
  | steer (decider : Input χ V) (input : Input χ V) : AtomicProc 1
  | forward (input : Input χ V) : AtomicProc 1

/--
Essentially the parallel composition of a list of atomic processes,
with data dependencies going forward through the closure.
-/
inductive DagProc : ℕ → Type (max u v) where
  | atom : AtomicProc Op χ V n → DagProc n
  | par : DagProc n → (Vector χ n → DagProc m) → DagProc m

def exampleProc1 (x : χ) (y : χ) : AtomicProc Op χ V 1 :=
  .steer (x, []) (y, [])

def exampleProc2 (x : χ) (y : χ) (z : χ) : DagProc MiniOp χ ℕ 1 :=
  .par (.atom (.steer (x, []) (y, []))) λ vs => let y' := vs[0]
  .par (.atom (.steer (x, []) (z, []))) λ vs => let z' := vs[0]
        .atom (.op MiniOp.add #v[(y', []), (z', [])])

-- def pushAll (p : ∀ χ, Vector χ n → AtomicProc Op χ V m) (vs : Vector V n) :
--   Vector χ n → AtomicProc Op χ V m :=
--   λ xs => match p (Fin n × V) (vs.mapFinIdx λ i v hv => (Fin.mk i hv, v)) with
--     | .op o inputs => .op o (inputs.map (λ ((i, v), buf) => (xs[i], buf ++ [v])))
--     | .steer ((i₁, v₁), buf₁) ((i₂, v₂), buf₂) =>
--       .steer (xs[i₁], buf₁ ++ [v₁]) (xs[i₂], buf₂ ++ [v₂])
--     | .forward ((i, v), buf) => .forward (xs[i], buf ++ [v])

def AtomicProc.resolvePush :
  AtomicProc Op (χ × Option V) V n → AtomicProc Op χ V n
  | .op o inputs => .op o (inputs.map resolve)
  | .steer decider input => .steer (resolve decider) (resolve input)
  | .forward input => .forward (resolve input)
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
def push (p : ∀ χ, Vector χ n → DagProc Op χ V m) (i : Fin n) (v : V) :
  (∀ χ, Vector χ n → DagProc Op χ V m) :=
  λ χ' xs =>
    -- Replace variables with indices
    let p' := p (χ' × Option V) (xs.mapFinIdx λ j _ hv => (xs[j]'hv, if i = j then some v else none))
    -- Push to the buffer at the i-th channel
    p'.resolvePush Op χ' V

/-- `Proc` structural equivalence -/
inductive Equiv : DagProc Op χ V n → DagProc Op χ V n → Prop where
  /-- Commutes two atomic processes if there is no data dependency. -/
  | equiv_par_comm (k : Vector χ n → Vector χ m → DagProc Op χ V k) :
    Equiv (.par p λ vs => .par q λ vs' => k vs vs') (.par q λ vs' => .par p λ vs => k vs vs')
  | equiv_par_assoc :
    Equiv (.par (.par p k) k') (.par p λ vs => .par (k vs) k')
  | equiv_refl : Equiv p p
  | equiv_symm : Equiv p q → Equiv q p
  | equiv_trans : Equiv p q → Equiv q r → Equiv p r
  | equiv_congr :
    (∀ xs, Equiv (k xs) (k' xs)) →
    Equiv (.par p k) (.par p k')

end
