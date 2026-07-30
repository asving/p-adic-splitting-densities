/-
Unit U-27 `ratfunc_eval_infinite` (medium) — the shared infinitude engine.
moves_ref: "a rational function equal to 1 at infinitely many prime powers is
identically 1" (consumers apply to f − 1).  sketch: num vanishes on S;
`Polynomial.eq_zero_of_infinite_isRoot`; `RatFunc.num_eq_zero_iff`-style closure.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem ratfunc_eval_infinite (f : Qq) (S : Set ℚ) (hS : S.Infinite)
    (hden : ∀ x ∈ S, f.denom.eval x ≠ 0)
    (hval : ∀ x ∈ S, RatFunc.eval (RingHom.id ℚ) x f = 0) :
    f = 0 := by
  rw [← RatFunc.num_eq_zero_iff]
  refine Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono ?_)
  intro x hx
  have hv := hval x hx
  have hd := hden x hx
  rw [RatFunc.eval, Polynomial.eval₂_id, Polynomial.eval₂_id, div_eq_zero_iff] at hv
  exact hv.resolve_right hd

end LeanUrat.MovesS
