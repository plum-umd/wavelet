import Wavelet.Thm.Compile.Rewrite.Defs
import Wavelet.Thm.Dataflow.ChanMap
import Wavelet.Thm.Dataflow.AltStep

/-!
Helper lemmas for proving `LocalSimRel` for rewrite rules.

The main tools are point-wise characterizations of channel operations
(`ChanMap.pushVals_apply`, `ChanMap.popVals_eq_some_iff`, ...) in terms of
`ChanMap.pushed`, and constructors for `LocalTauStar`.
-/

namespace Wavelet.Dataflow

open Semantics

/-! Point-wise characterizations of channel operations. -/
section ChanMap

@[simp]
theorem ChanMap.pushed_nil_left [DecidableEq χ] {vals : List V} {y : χ} :
    ChanMap.pushed [] vals y = [] := by
  simp [ChanMap.pushed]

@[simp]
theorem ChanMap.pushed_nil_right [DecidableEq χ] {names : List χ} {y : χ} :
    ChanMap.pushed names ([] : List V) y = [] := by
  simp [ChanMap.pushed]

@[simp]
theorem ChanMap.pushed_cons [DecidableEq χ] {x : χ} {names : List χ} {v : V} {vals : List V} {y : χ} :
    ChanMap.pushed (x :: names) (v :: vals) y =
      (if x = y then [v] else []) ++ ChanMap.pushed names vals y := by
  unfold ChanMap.pushed
  by_cases h : x = y <;> simp [h]

theorem ChanMap.pushed_append [DecidableEq χ]
  {names₁ names₂ : List χ} {vals₁ vals₂ : List V} {y : χ}
  (hlen : names₁.length = vals₁.length) :
    ChanMap.pushed (names₁ ++ names₂) (vals₁ ++ vals₂) y =
      ChanMap.pushed names₁ vals₁ y ++ ChanMap.pushed names₂ vals₂ y := by
  simp [ChanMap.pushed, List.zip_append hlen]

theorem ChanMap.pushed_not_mem [DecidableEq χ]
  {names : List χ} {vals : List V} {y : χ}
  (h : y ∉ names) : ChanMap.pushed names vals y = [] := by
  induction names generalizing vals with
  | nil => simp
  | cons x names ih =>
    cases vals with
    | nil => simp
    | cons v vals =>
      simp at h
      simp [Ne.symm h.1, ih h.2]

theorem ChanMap.pushVal_apply [DecidableEq χ]
  {map : ChanMap χ V} {x y : χ} {v : V} :
    map.pushVal x v y = map y ++ (if y = x then [v] else []) := by
  simp only [ChanMap.pushVal]
  split <;> simp

theorem ChanMap.pushVals_apply [DecidableEq χ]
  {map : ChanMap χ V} {names : Vector χ n} {vals : Vector V n} {y : χ} :
    map.pushVals names vals y = map y ++ ChanMap.pushed names.toList vals.toList y := by
  induction names using Vector.back_induction generalizing map with
  | empty =>
    have : vals = #v[] := by simp [Vector.eq_empty]
    subst this
    simp
  | push names x ih =>
    cases vals using Vector.back_induction with
    | push vals v =>
    rw [push_vals_unfold]
    simp only [Vector.pop_push, Vector.back_push, ChanMap.pushVal_apply, ih]
    simp only [Vector.toList_push]
    rw [ChanMap.pushed_append (by simp)]
    simp only [List.append_assoc]
    congr 2
    simp [eq_comm]

theorem ChanMap.pushVals_eq [DecidableEq χ]
  {map : ChanMap χ V} {names : Vector χ n} {vals : Vector V n} :
    map.pushVals names vals = λ y => map y ++ ChanMap.pushed names.toList vals.toList y := by
  funext y
  exact ChanMap.pushVals_apply

theorem ChanMap.popVal_eq_some_iff [DecidableEq χ]
  {map map' : ChanMap χ V} {x : χ} {v : V} :
    map.popVal x = some (v, map') ↔
      ∀ y, map y = (if y = x then [v] else []) ++ map' y := by
  constructor
  · intro h y
    simp only [ChanMap.popVal] at h
    split at h
    · contradiction
    · rename_i v' vs hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hy : y = x
      · subst hy; simp [hx]
      · simp [hy]
  · intro h
    have hx := h x
    simp only [ite_true, List.singleton_append] at hx
    simp only [ChanMap.popVal, hx]
    congr 2
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · have := h y
      simp [hy] at this
      simp [hy, this]

theorem ChanMap.popVals_eq_some_iff [DecidableEq χ]
  {map map' : ChanMap χ V} {names : Vector χ n} {vals : Vector V n} :
    map.popVals names = some (vals, map') ↔
      ∀ y, map y = ChanMap.pushed names.toList vals.toList y ++ map' y := by
  induction names using Vector.back_induction generalizing map' with
  | empty =>
    have : vals = #v[] := by simp [Vector.eq_empty]
    subst this
    simp only [pop_vals_zero, Option.some.injEq, Prod.mk.injEq, true_and, Vector.toList_empty,
      ChanMap.pushed_nil_left, List.nil_append]
    constructor
    · intro h; subst h; simp
    · intro h; funext y; exact h y
  | push names x ih =>
    cases vals using Vector.back_induction with
    | push vals v =>
    rw [pop_vals_unfold]
    simp only [Vector.pop_push, Vector.back_push, Vector.toList_push]
    constructor
    · intro h y
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨vals', map₁⟩, h₁, ⟨v', map₂⟩, h₂, h₃⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h₃
      obtain ⟨h₃, rfl⟩ := h₃
      obtain ⟨rfl, rfl⟩ := Vector.push_eq_push.mp h₃
      have h₂' : map₁.popVal x = some (v', map₂) := h₂
      rw [ih.mp h₁ y, ChanMap.popVal_eq_some_iff.mp h₂' y]
      rw [ChanMap.pushed_append (by simp)]
      simp [List.append_assoc, eq_comm]
    · intro h
      have h₁ : map.popVals names = some (vals, λ y => (if y = x then [v] else []) ++ map' y) := by
        apply ih.mpr
        intro y
        rw [h y, ChanMap.pushed_append (by simp)]
        simp [List.append_assoc, eq_comm]
      simp only [h₁, Option.bind_eq_bind, Option.bind_some]
      have h₂ : ChanMap.popVal x (λ y => (if y = x then [v] else []) ++ map' y) = some (v, map') := by
        apply ChanMap.popVal_eq_some_iff.mpr
        intro y
        rfl
      simp [h₂]

theorem ChanMap.popVals_apply [DecidableEq χ]
  {map map' : ChanMap χ V} {names : Vector χ n} {vals : Vector V n}
  (h : map.popVals names = some (vals, map')) (y : χ) :
    map y = ChanMap.pushed names.toList vals.toList y ++ map' y :=
  ChanMap.popVals_eq_some_iff.mp h y

@[simp]
theorem ChanMap.empty_apply {y : χ} : (ChanMap.empty : ChanMap χ V) y = [] := rfl

end ChanMap

/-! Constructing local steps. -/
section LocalTauStar

variable [Arity Op] [DecidableEq χ] [InterpConsts V]

theorem LocalTauStar.refl {L : AtomicProcs Op χ V} {chans : ChanMap χ V} :
    LocalTauStar L chans L chans := Lts.TauStar.refl

theorem LocalTauStar.trans
  {L₁ L₂ L₃ : AtomicProcs Op χ V} {chans₁ chans₂ chans₃ : ChanMap χ V}
  (h₁ : LocalTauStar L₁ chans₁ L₂ chans₂)
  (h₂ : LocalTauStar L₂ chans₂ L₃ chans₃) :
    LocalTauStar L₁ chans₁ L₃ chans₃ := Lts.TauStar.trans h₁ h₂

theorem LocalTauStar.eq_rhs
  {L₁ L₂ L₂' : AtomicProcs Op χ V} {chans₁ chans₂ chans₂' : ChanMap χ V}
  (h : LocalTauStar L₁ chans₁ L₂ chans₂) (hL : L₂ = L₂') (hchans : chans₂ = chans₂') :
    LocalTauStar L₁ chans₁ L₂' chans₂' := by
  subst hL hchans; exact h

/-- Fires an async operator in a local configuration. -/
theorem LocalTauStar.async
  {L : AtomicProcs Op χ V} {chans chans' : ChanMap χ V} {i : Nat}
  {aop aop' : AsyncOp V} {allInputs allOutputs : List χ}
  {inputs : Vector χ k₁} {inputVals : Vector V k₁}
  {outputs : Vector χ k₂} {outputVals : Vector V k₂}
  (hget : L[i]? = some (.async aop allInputs allOutputs))
  (hinterp : aop.Interp (.mk allInputs allOutputs
    inputs.toList inputVals.toList outputs.toList outputVals.toList) aop')
  (hpop : chans.popVals inputs = some (inputVals, chans')) :
    LocalTauStar L chans
      (L.set i (.async aop' allInputs allOutputs)) (chans'.pushVals outputs outputVals) := by
  have ⟨hi, hget'⟩ := List.getElem?_eq_some_iff.mp hget
  exact .single (Config.Step.step_async (c := LocalConfig L chans) hi hget' hinterp hpop)

/-- Same as `LocalTauStar.async` but with lists and point-wise channel updates. -/
theorem LocalTauStar.async_list
  {L : AtomicProcs Op χ V} {chans chans' : ChanMap χ V} {i : Nat}
  {aop aop' : AsyncOp V} {allInputs allOutputs : List χ}
  {inputs outputs : List χ} {inputVals outputVals : List V}
  (hget : L[i]? = some (.async aop allInputs allOutputs))
  (hinterp : aop.Interp (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop')
  (hlen₁ : inputs.length = inputVals.length)
  (hlen₂ : outputs.length = outputVals.length)
  (hpop : ∀ y, chans y = ChanMap.pushed inputs inputVals y ++ chans' y) :
    LocalTauStar L chans
      (L.set i (.async aop' allInputs allOutputs))
      (λ y => chans' y ++ ChanMap.pushed outputs outputVals y) := by
  have := LocalTauStar.async (chans' := chans')
    (inputs := inputs.toVector.cast hlen₁) (inputVals := inputVals.toVector)
    (outputs := outputs.toVector.cast hlen₂) (outputVals := outputVals.toVector)
    hget (by simpa [List.toVector] using hinterp)
    (ChanMap.popVals_eq_some_iff.mpr (by simpa [List.toVector] using hpop))
  apply this.eq_rhs rfl
  funext y
  simp [ChanMap.pushVals_apply, List.toVector]

/-- An async operator that does not change its state. -/
theorem LocalTauStar.async_list_mem
  {L : AtomicProcs Op χ V} {chans chans' : ChanMap χ V}
  {aop : AsyncOp V} {allInputs allOutputs : List χ}
  {inputs outputs : List χ} {inputVals outputVals : List V}
  (hmem : .async aop allInputs allOutputs ∈ L)
  (hinterp : aop.Interp (.mk allInputs allOutputs inputs inputVals outputs outputVals) aop)
  (hlen₁ : inputs.length = inputVals.length)
  (hlen₂ : outputs.length = outputVals.length)
  (hpop : ∀ y, chans y = ChanMap.pushed inputs inputVals y ++ chans' y) :
    LocalTauStar L chans L (λ y => chans' y ++ ChanMap.pushed outputs outputVals y) := by
  have ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have := LocalTauStar.async_list (i := i)
    (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩) hinterp hlen₁ hlen₂ hpop
  apply this.eq_rhs _ rfl
  rw [← hget]
  exact List.set_getElem_self _

end LocalTauStar

/-! Facts about `SameShape`. -/
section SameShape

variable [Arity Op]

theorem AtomicProc.SameShape.inputs_eq {ap ap' : AtomicProc Op χ V}
  (h : ap.SameShape ap') : ap.inputs = ap'.inputs := by
  cases h <;> rfl

theorem AtomicProc.SameShape.outputs_eq {ap ap' : AtomicProc Op χ V}
  (h : ap.SameShape ap') : ap.outputs = ap'.outputs := by
  cases h <;> rfl

theorem AtomicProc.SameShape.of_interp [InterpConsts V]
  {aop aop' : AsyncOp V} {ins outs : List χ} {label : AsyncOp.Label χ V}
  (h : aop.Interp label aop') :
    (AtomicProc.async (Op := Op) aop ins outs).SameShape (.async aop' ins outs) := by
  cases h <;> first | exact .refl | exact .merge | exact .inv

/-- Atoms other than merges and invariants never change. -/
theorem AtomicProc.SameShape.eq_of_not_stateful {ap ap' : AtomicProc Op χ V}
  (h : ap.SameShape ap')
  (hmerge : ∀ st n (_ : NeZero n) ins outs, ap ≠ .async (.merge st n) ins outs)
  (hinv : ∀ flavor c ins outs, ap ≠ .async (.inv flavor c) ins outs) :
    ap' = ap := by
  cases h with
  | refl => rfl
  | merge => exact absurd rfl (hmerge _ _ inferInstance _ _)
  | inv => exact absurd rfl (hinv _ _ _ _)

theorem AtomicProc.SameShape.op_eq {ap : AtomicProc Op χ V}
  {o : Op} {ins : Vector χ (Arity.ι o)} {outs : Vector χ (Arity.ω o)}
  (h : ap.SameShape (.op o ins outs)) : ap = .op o ins outs := by
  cases h; rfl

theorem forall₂_sameShape_getElem?
  {P L : AtomicProcs Op χ V} {i : Nat} {ap : AtomicProc Op χ V}
  (h : List.Forall₂ AtomicProc.SameShape P L)
  (hget : L[i]? = some ap) :
    ∃ ap₀, P[i]? = some ap₀ ∧ ap₀.SameShape ap := by
  induction h generalizing i with
  | nil => simp at hget
  | cons hhd _ ih =>
    cases i with
    | zero => simp at hget; subst hget; exact ⟨_, rfl, hhd⟩
    | succ i => simpa using ih hget

theorem forall₂_sameShape_op_mem
  {P L : AtomicProcs Op χ V}
  (h : List.Forall₂ AtomicProc.SameShape P L)
  (hmem : .op o inputs outputs ∈ L) :
    .op o inputs outputs ∈ P := by
  have ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have ⟨ap₀, h₀, hshape⟩ := forall₂_sameShape_getElem? h (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)
  rw [hshape.op_eq] at h₀
  exact List.mem_of_getElem? h₀

end SameShape

/-! Facts from `AffineChan`. -/
section AffineChan

variable [Arity Op] {i j : Nat}

theorem Proc.AffineChan.atom_nodup {proc : Proc Op χ V m n} {ap : AtomicProc Op χ V}
  (haff : proc.AffineChan) (hget : proc.atoms[i]? = some ap) :
    ap.inputs.Nodup ∧ ap.outputs.Nodup :=
  haff.2.2.1.1 ap (List.mem_of_getElem? hget)

theorem Proc.AffineChan.atom_disjoint {proc : Proc Op χ V m n} {ap₁ ap₂ : AtomicProc Op χ V}
  (haff : proc.AffineChan)
  (hget₁ : proc.atoms[i]? = some ap₁) (hget₂ : proc.atoms[j]? = some ap₂) (hne : i ≠ j) :
    ap₁.inputs.Disjoint ap₂.inputs ∧ ap₁.outputs.Disjoint ap₂.outputs := by
  have hpw := List.pairwise_iff_getElem.mp haff.2.2.1.2
  have ⟨hi, hget₁⟩ := List.getElem?_eq_some_iff.mp hget₁
  have ⟨hj, hget₂⟩ := List.getElem?_eq_some_iff.mp hget₂
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hpw i j hi hj hlt
    rw [hget₁, hget₂] at this
    exact this
  · have := hpw j i hj hi hlt
    rw [hget₁, hget₂] at this
    exact ⟨this.1.symm, this.2.symm⟩

theorem Proc.AffineChan.atom_outputs_disjoint_inputs {proc : Proc Op χ V m n}
  {ap : AtomicProc Op χ V}
  (haff : proc.AffineChan) (hget : proc.atoms[i]? = some ap) :
    ap.outputs.Disjoint proc.inputs.toList :=
  haff.2.2.2.1 ap (List.mem_of_getElem? hget)

theorem Proc.AffineChan.atom_inputs_disjoint_outputs {proc : Proc Op χ V m n}
  {ap : AtomicProc Op χ V}
  (haff : proc.AffineChan) (hget : proc.atoms[i]? = some ap) :
    ap.inputs.Disjoint proc.outputs.toList :=
  haff.2.2.2.2 ap (List.mem_of_getElem? hget)

theorem Proc.mem_allNames_of_input {proc : Proc Op χ V m n} {ap : AtomicProc Op χ V}
  (hget : proc.atoms[i]? = some ap) (hx : x ∈ ap.inputs) : x ∈ proc.allNames := by
  simp only [Proc.allNames, AtomicProcs.inputNames, List.mem_append, List.mem_flatMap]
  exact .inl (.inr ⟨ap, List.mem_of_getElem? hget, hx⟩)

theorem Proc.mem_allNames_of_output {proc : Proc Op χ V m n} {ap : AtomicProc Op χ V}
  (hget : proc.atoms[i]? = some ap) (hx : x ∈ ap.outputs) : x ∈ proc.allNames := by
  simp only [Proc.allNames, AtomicProcs.outputNames, List.mem_append, List.mem_flatMap]
  exact .inr ⟨ap, List.mem_of_getElem? hget, hx⟩

end AffineChan

/-! Simp lemmas for names. -/

@[simp]
theorem AtomicProcs.inputNames_nil [Arity Op] :
    AtomicProcs.inputNames ([] : AtomicProcs Op χ V) = [] := rfl

@[simp]
theorem AtomicProcs.inputNames_cons [Arity Op] {ap : AtomicProc Op χ V} {aps : AtomicProcs Op χ V} :
    AtomicProcs.inputNames (ap :: aps) = ap.inputs ++ AtomicProcs.inputNames aps := rfl

@[simp]
theorem AtomicProcs.outputNames_nil [Arity Op] :
    AtomicProcs.outputNames ([] : AtomicProcs Op χ V) = [] := rfl

@[simp]
theorem AtomicProcs.outputNames_cons [Arity Op] {ap : AtomicProc Op χ V} {aps : AtomicProcs Op χ V} :
    AtomicProcs.outputNames (ap :: aps) = ap.outputs ++ AtomicProcs.outputNames aps := rfl

@[simp]
theorem AtomicProc.inputs_async [Arity Op] {aop : AsyncOp V} {ins outs : List χ} :
    (AtomicProc.async (Op := Op) aop ins outs).inputs = ins := rfl

@[simp]
theorem AtomicProc.outputs_async [Arity Op] {aop : AsyncOp V} {ins outs : List χ} :
    (AtomicProc.async (Op := Op) aop ins outs).outputs = outs := rfl

@[simp]
theorem AtomicProc.inputs_op [Arity Op] {o : Op} {ins : Vector χ (Arity.ι o)} {outs : Vector χ (Arity.ω o)} :
    (AtomicProc.op (V := V) o ins outs).inputs = ins.toList := rfl

@[simp]
theorem AtomicProc.outputs_op [Arity Op] {o : Op} {ins : Vector χ (Arity.ι o)} {outs : Vector χ (Arity.ω o)} :
    (AtomicProc.op (V := V) o ins outs).outputs = outs.toList := rfl

end Wavelet.Dataflow

namespace Wavelet.Compile

open Semantics Dataflow

@[simp]
theorem matchedOf_nil {aps : List α} : matchedOf aps [] = [] := rfl

@[simp]
theorem matchedOf_cons {aps : List α} {i : Nat} {I : List Nat} :
    matchedOf aps (i :: I) = aps[i]?.toList ++ matchedOf aps I := by
  simp only [matchedOf, List.filterMap_cons]
  cases aps[i]? <;> simp

end Wavelet.Compile
