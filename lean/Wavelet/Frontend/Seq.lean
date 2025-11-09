import Wavelet.Seq.Prog

/-! A simple JSON format of Seq `Prog`/`Fn`/`Expr`. -/

namespace Wavelet.Seq

open Semantics

def Sigs.push (sigs : Sigs k) (sig : Sig) : Sigs (k + 1) :=
  λ i => if h : i.val < k then sigs ⟨i.val, by omega⟩ else sig

/-- Rename operators in an expression, provided that
the renaming preserves arity. -/
def Expr.renameOp
  [Arity Op₁] [Arity Op₂]
  (f : Op₁ → Op₂)
  (h : ∀ {op}, Arity.ι op = Arity.ι (f op) ∧ Arity.ω op = Arity.ω (f op))
  : Expr Op₁ χ m n → Expr Op₂ χ m n
  | .ret vars => .ret vars
  | .tail vars => .tail vars
  | .op o args rets cont =>
    .op (f o)
      (args.cast (by simp [h]))
      (rets.cast (by simp [h]))
      (cont.renameOp f h)
  | .br cond left right =>
    .br cond (left.renameOp f h) (right.renameOp f h)

def Fn.renameOp
  [Arity Op₁] [Arity Op₂]
  (f : Op₁ → Op₂)
  (h : ∀ {op}, Arity.ι op = Arity.ι (f op) ∧ Arity.ω op = Arity.ω (f op))
  (fn : Fn Op₁ χ V m n) : Fn Op₂ χ V m n
  := {
    params := fn.params,
    body := fn.body.renameOp f h,
  }

end Wavelet.Seq

namespace Wavelet.Frontend

open Semantics Seq

/-- Extending the base operator set with calls to another function. -/
inductive WithCall (Op : Type u) (FnName : Type v) where
  | op : Op → WithCall Op FnName
  | call : FnName → WithCall Op FnName
  deriving Repr, Lean.ToJson

inductive RawExpr (Op : Type u) (χ : Type v) : Type (max u v) where
  | ret : List χ → RawExpr Op χ
  | tail : List χ → RawExpr Op χ
  | op : Op → List χ → List χ → RawExpr Op χ → RawExpr Op χ
  | br : χ → RawExpr Op χ → RawExpr Op χ → RawExpr Op χ
  deriving Repr, Lean.ToJson

structure RawFn (Op : Type u) (χ : Type v) where
  name : String
  params : List χ
  outputs : Nat
  body : RawExpr Op χ
  deriving Repr, Lean.ToJson

structure RawProg (Op : Type u) (χ : Type v) where
  fns : List (RawFn Op χ)
  deriving Repr, Lean.ToJson

/-! Custom instances for `FromJson` for better error messages. -/
section FromJson

instance [Lean.FromJson Op] [Lean.FromJson FnName] : Lean.FromJson (WithCall Op FnName) where
  fromJson? json := do
    if let .ok obj := json.getObjVal? "op" then
      .op <$> Lean.fromJson? obj
    else if let .ok obj := json.getObjVal? "call" then
      .call <$> Lean.fromJson? obj
    else
      .error s!"unable to parse operator or function call: {json}"

partial def RawExpr.fromJson? [Lean.FromJson Op] [Lean.FromJson χ]
  (json : Lean.Json) : Except String (RawExpr Op χ) := do
  if let .ok obj := json.getObjVal? "ret" then
    .ret <$> Lean.fromJson? obj
    |>.mapError (λ e => s!"when parsing return: {e}")
  else if let .ok obj := json.getObjVal? "tail" then
    .tail <$> Lean.fromJson? obj
    |>.mapError (λ e => s!"when parsing tail call: {e}")
  else if let .ok obj := json.getObjVal? "op" then
    let arr ← obj.getArr?
    if h : arr.size = 4 then
      (.op
        <$> Lean.fromJson? (arr[0])
        <*> Lean.fromJson? (arr[1])
        <*> Lean.fromJson? (arr[2])
        |>.mapError (λ e => s!"when parsing operator call: {e}"))
        <*> RawExpr.fromJson? (arr[3])
    else
      .error s!"unable to parse operator call: {json}"
  else if let .ok obj := json.getObjVal? "br" then
    let arr ← obj.getArr?
    if h : arr.size = 3 then
      (.br
        <$> Lean.fromJson? (arr[0])
        |>.mapError (λ e => s!"when parsing branching: {e}"))
        <*> RawExpr.fromJson? (arr[1])
        <*> RawExpr.fromJson? (arr[2])
    else
      .error s!"unable to parse branching: {json}"
  else
    .error s!"when parsing expr: {json}"

instance RawExpr.instFromJson [Lean.FromJson Op] [Lean.FromJson χ] : Lean.FromJson (RawExpr Op χ) where
  fromJson? := RawExpr.fromJson?

instance [Lean.FromJson Op] [Lean.FromJson χ] : Lean.FromJson (RawFn Op χ) where
  fromJson? json := do
    let name ← json.getObjValAs? String "name"
      |>.mapError (λ e => s!"when parsing function name: {e}")
    return {
      name := name,
      params := ← json.getObjValAs? (List χ) "params"
        |>.mapError (λ e => s!"when parsing params of function `{name}`: {e}"),
      outputs := ← json.getObjValAs? Nat "outputs"
        |>.mapError (λ e => s!"when parsing output number of function `{name}`: {e}"),
      body := ← json.getObjValAs? (RawExpr Op χ) "body"
        |>.mapError (λ e => s!"when parsing body of function `{name}`: {e}"),
    }

instance [Lean.FromJson Op] [Lean.FromJson χ] : Lean.FromJson (RawProg Op χ) where
  fromJson? json :=
    return {
      fns := ← json.getObjValAs? (List (RawFn Op χ)) "fns"
        |>.mapError (λ e => s!"when parsing program: {e}"),
    }

end FromJson

structure EncapProg Op χ V [Arity Op] where
  numFns : Nat
  sigs : Sigs numFns
  prog : Prog Op χ V sigs
  neZero : NeZeroSigs sigs

/-- State for converting from `RawProg` to `Prog`. -/
structure CheckState Op χ V [Arity Op] where
  numFns : Nat
  nameToIdx : String → Option (Fin numFns)
  sigs : Sigs numFns
  prog : Prog Op χ V sigs
  -- Some validated invariants
  neZero : NeZeroSigs sigs

abbrev CheckM Op χ V [Arity Op] T := StateT (CheckState Op χ V) (Except String) T

def CheckState.init [Arity Op] : CheckState Op χ V :=
  {
    numFns := 0,
    nameToIdx := λ _ => none,
    sigs := λ i => i.elim0,
    prog := λ i => i.elim0,
    neZero := {
      neZeroᵢ := λ i => i.elim0,
      neZeroₒ := λ i => i.elim0,
    }
  }

/-- Converts operators after a new function has been added to the signature. -/
def CheckState.pushFn.renameOp {k m n}
  {sigs : Sigs k}
  {i : Fin (k + 1)} :
    Op ⊕ SigOps sigs i →
    Op ⊕ SigOps (sigs.push { ι := m, ω := n }) i.castSucc
  | .inl op => .inl op
  | .inr (.call j) => .inr (.call j)

/-- Pushes a new function into the program, while maintaining the dependent invariants
within the `Prog` and `Fn` types. -/
def CheckState.pushFn [Arity Op]
  (state : CheckState Op χ V)
  {m n}
  (name : String)
  (fn : Fn (Op ⊕ SigOps state.sigs ⟨state.numFns, by simp⟩) χ V m n)
  (hnz : m ≠ 0 ∧ n ≠ 0) :
    CheckState Op χ V
  := {
    numFns := state.numFns + 1,
    nameToIdx := λ name' =>
      if name' = name then
        some ⟨state.numFns, by omega⟩
      else
        (state.nameToIdx name').map (λ i => ⟨i.val, by omega⟩),
    sigs := state.sigs.push ⟨m, n⟩,
    prog := λ i =>
      if h : state.numFns = i.val then
        cast (by
          rcases i
          simp at h
          subst h
          simp [Sigs.push]) (renameFn fn)
      else
        cast (by
          rcases i with ⟨i, _⟩
          simp at h
          have : i < state.numFns := by omega
          simp [Sigs.push, this]) (renameFn (state.prog ⟨i, by omega⟩)),
    neZero := {
      neZeroᵢ i := by
        if h : i < state.numFns then
          simp [Sigs.push, h]
          apply state.neZero.neZeroᵢ
        else
          simp [Sigs.push, h]
          exact .mk hnz.1,
      neZeroₒ i := by
        if h : i < state.numFns then
          simp [Sigs.push, h]
          apply state.neZero.neZeroₒ
        else
          simp [Sigs.push, h]
          exact .mk hnz.2,
    }
  }
  where
    renameFn
      {i : Fin (state.numFns + 1)} {m' n'}
      (fn : Fn (Op ⊕ SigOps state.sigs i) χ V m' n') :
        Fn (Op ⊕ SigOps (state.sigs.push { ι := m, ω := n }) i.castSucc) χ V m' n'
      := fn.renameOp CheckState.pushFn.renameOp (by
        intros op
        cases op <;> simp [CheckState.pushFn.renameOp]
        · constructor <;> rfl
        · rename_i call
          rcases call with ⟨j, hlt⟩
          have : j < state.numFns := by omega
          simp [Arity.ι, Arity.ω, Sigs.push, this])

def CheckState.toProg [Arity Op]
  (state : CheckState Op χ V) : EncapProg Op χ V :=
  {
    numFns := state.numFns,
    sigs := state.sigs,
    prog := state.prog,
    neZero := state.neZero,
  }

/-- Converts a `RawExpr` to `Expr` while checking some static constraints. -/
def RawExpr.checkExpr [Arity Op] [Repr Op]
  (state : CheckState Op χ V)
  (m n : Nat) :
    RawExpr (WithCall Op String) χ →
    Except String (Expr (Op ⊕ SigOps state.sigs ⟨state.numFns, by omega⟩) χ m n)
  | .ret vars =>
    if h : vars.length = n then
      return .ret (vars.toVector.cast h)
    else
      .error s!"unexpected number of return variables: expected {n}, got {vars.length}"
  | .tail vars =>
    if h : vars.length = m then
      return .tail (vars.toVector.cast h)
    else
      .error s!"unexpected number of tail call arguments: expected {m}, got {vars.length}"
  | .op (.op o) args rets cont => do
    if h₁ : args.length = Arity.ι o then
      if h₂ : rets.length = Arity.ω o then
        return .op (.inl o)
          (args.toVector.cast h₁)
          (rets.toVector.cast h₂)
          (← cont.checkExpr state m n)
      else
        .error s!"unexpected output arity for operator `{repr o}`: expected {Arity.ω o}, got {rets.length}"
    else
      .error s!"unexpected input arity for operator `{repr o}`: expected {Arity.ι o}, got {args.length}"
  | .op (.call name) args rets cont => do
    match state.nameToIdx name with
    | some i =>
      if h₁ : args.length = (state.sigs i).ι then
        if h₂ : rets.length = (state.sigs i).ω then
          return .op (.inr (.call i))
            (args.toVector.cast h₁)
            (rets.toVector.cast h₂)
            (← cont.checkExpr state m n)
        else
          .error s!"unexpected output arity for function call `{name}`: expected {(state.sigs i).ω}, got {rets.length}"
      else
        .error s!"unexpected input arity for function call `{name}`: expected {(state.sigs i).ι}, got {args.length}"
    | none =>
      .error s!"unknown function {name}"
  | .br cond left right => do
    return .br cond (← left.checkExpr state m n) (← right.checkExpr state m n)

/-- Converts the `RawFn` to a `Fn` and adds it to the context. -/
def RawFn.checkFn [Arity Op] [Repr Op]
  (rawFn : RawFn (WithCall Op String) χ) : CheckM Op χ V Unit
  := do
  let state ← get
  let expr ← rawFn.body.checkExpr state rawFn.params.length rawFn.outputs
    |>.mapError (λ e => s!"when checking function `{rawFn.name}`: {e}")
  if h₁ : rawFn.params.length = 0 then
    throw s!"function {rawFn.name} with zero inputs is not allowed"
  else if h₂ : rawFn.outputs = 0 then
    throw s!"function {rawFn.name} with zero outputs is not allowed"
  else
    set (state.pushFn rawFn.name {
      params := rawFn.params.toVector,
      body := expr,
    } ⟨h₁, h₂⟩)

def RawProg.checkProg [Arity Op] [Repr Op]
  (rawProg : RawProg (WithCall Op String) χ) : CheckM Op χ V Unit
  := for fn in rawProg.fns do
    fn.checkFn

/-- Converts a `RawProg` to the internal dependently typed `Prog`. -/
def RawProg.toProg [Arity Op] [Repr Op]
  (rawProg : RawProg (WithCall Op String) χ) :
    Except String (EncapProg Op χ V)
  := do
  let (_, state) ← rawProg.checkProg.run CheckState.init
  return state.toProg

section Examples

inductive MiniOp where
  | add
  | sub
  deriving Repr, Lean.ToJson, Lean.FromJson

instance : Arity MiniOp where
  ι | .add => 2
    | .sub => 2
  ω | .add => 1
    | .sub => 1

def expr₁ : RawExpr MiniOp String :=
  .op .add ["a", "b"] ["c"] <|
  .ret ["c"]

def expr₂ : RawExpr (WithCall String String) String :=
  .op (.call "foo") ["x", "y"] ["z"] <|
  .op (.call "bar") ["n"] ["m"] <|
  .op (.op "add") ["z", "w"] ["k"] <|
  .br "cond"
    (.ret ["k"])
    (.tail ["n", "m"])

-- #eval Lean.ToJson.toJson expr₁
-- #eval Lean.ToJson.toJson expr₂

def fn₁ : RawFn MiniOp String :=
  {
    name := "main",
    params := ["a", "b"],
    outputs := 1,
    body := expr₁,
  }

-- #eval Lean.ToJson.toJson fn₁

def prog₁ : RawProg MiniOp String := ⟨[fn₁]⟩

def prog₂ : RawProg (WithCall MiniOp String) String :=
  {
    fns := [
      {
        name := "foo",
        params := ["x", "y"],
        outputs := 1,
        body :=
          .op (.op .add) ["x", "y"] ["z"] <|
          .ret ["z"],
      },
      {
        name := "bar",
        params := ["n", "m"],
        outputs := 1,
        body :=
          .op (.call "foo") ["n", "m"] ["k"] <|
          .ret ["k"],
      },
    ],
  }

def prog₃ : RawProg (WithCall MiniOp String) String :=
  {
    fns := [
      {
        name := "foo",
        params := ["x", "y"],
        outputs := 1,
        body :=
          -- Incorrect arity
          .op (.op .add) ["x"] ["z"] <|
          .ret ["z"],
      },
      {
        name := "bar",
        params := ["n", "m"],
        outputs := 1,
        body :=
          .op (.call "foo") ["n", "m"] ["k"] <|
          .ret ["k"],
      },
    ],
  }

def prog₄ : RawProg (WithCall MiniOp String) String :=
  {
    fns := [
      {
        name := "foo",
        params := ["x", "y"],
        outputs := 1,
        body :=
          .op (.op .add) ["x", "y"] ["z"] <|
          .ret ["z"],
      },
      {
        name := "bar",
        params := ["n", "m"],
        outputs := 1,
        body :=
          -- Undefined function
          .op (.call "foo?") ["n", "m"] ["k"] <|
          .ret ["k"],
      },
    ],
  }

-- #eval Lean.ToJson.toJson prog₁
-- #eval Lean.ToJson.toJson prog₂
-- #eval Lean.ToJson.toJson prog₃

-- #eval (prog₂.toProg (V := Nat)).map (λ _ => ())
-- #eval (prog₃.toProg (V := Nat)).map (λ _ => ())
-- #eval (prog₄.toProg (V := Nat)).map (λ _ => ())

def prog₅ : Except String (RawProg (WithCall MiniOp String) String) := do
  let json ← Lean.Json.parse r#"
    {"fns":
    [{"params": ["x", "y"],
      "outputs": 1,
      "name": "foo",
      "body":
      {"op":
        {"rets": ["z"],
        "op": {"op": "add"},
        "cont": {"ret": ["z"]},
        "args": ["x", "y"]}}},
      {"params": ["n", "m"],
      "outputs": 1,
      "name": "bar",
      "body":
      {"op":
        {"rets": ["k"],
        "op": {"call": "foo"},
        "cont": {"ret": ["k"]},
        "args": ["n", "m"]}}}]}
    "#
  Lean.FromJson.fromJson? json

-- #eval prog₅
-- #eval do
--   let prog₅ ← prog₅
--   let _ ← prog₅.toProg (V := Nat)

end Examples

end Wavelet.Frontend
