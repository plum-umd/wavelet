import Mathlib.Logic.Function.Basic
import Wavelet.Data.Basic

namespace Function

@[simp, grind]
theorem update'_eq_update
  {α : Sort u} {β : α → Sort v} [DecidableEq α]
  (f : ∀ a, β a) (a' : α) (v : β a') :
    Function.update' f a' v = Function.update f a' v
  := by
  funext a
  simp [Function.update', Function.update]

end Function
