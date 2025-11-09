/-! Some additional lemmas for `Except`. -/

namespace Except

@[simp]
theorem mapError_ok_iff_ok
  {α} {f : ε → ε'} {e : Except ε α} :
    (e.mapError f).isOk = e.isOk
  := by cases e <;> simp [Except.mapError, isOk, Except.toBool]

end Except

abbrev ExceptDec ε (p : Prop) := Except (ε × PLift ¬p) (PLift p)

namespace ExceptDec

/-- Dynamically decides a proposition, and returns its proof. -/
def check (p : Prop) [Decidable p] (e : ε) : ExceptDec ε p :=
  if h : p then
    .ok (.up h)
  else
    .error (e, .up h)

/-- Converts one `ExceptDec` to another. -/
def necessary (ed : ExceptDec ε q) (hpq : p → q) : Except (ε × PLift ¬p) (PLift q) :=
  match ed with
  | .ok hq => .ok hq
  | .error (e, h) => .error (e, .up (λ hp => h.down (hpq hp)))

def toDecidable (ed : ExceptDec ε p) : Decidable p :=
  match ed with
  | .ok h => isTrue h.down
  | .error (_, h) => isFalse h.down

def resolve (ed : ExceptDec ε p) : Except ε Unit :=
  match ed with
  | .ok _ => .ok ()
  | .error (e, _) => .error e

end ExceptDec

namespace Option

def toExcept {ε α} (o : Option α) (e : ε) : Except ε α :=
  match o with
  | some x => .ok x
  | none => .error e

end Option
