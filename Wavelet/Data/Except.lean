/-! Some additional lemmas for `Except`. -/

namespace Except

@[simp]
theorem mapError_ok_iff_ok
  {α} {f : ε → ε'} {e : Except ε α} :
    (e.mapError f).isOk = e.isOk
  := by cases e <;> simp [Except.mapError, isOk, Except.toBool]

end Except
