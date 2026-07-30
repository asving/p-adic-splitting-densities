import Mathlib
import LeanUrat.Moves.Defs

namespace LeanUrat.Moves

open Polynomial

theorem L2_iaugRoot (e' h' : ℕ) (hh' : 1 ≤ h') : (h' : ℤ) > (e' : ℤ) * (0 : ℤ) := by
  rw [mul_zero]
  exact_mod_cast hh'

end LeanUrat.Moves
