/-
Unit U-22b `allActive_cofinite` (medium) — PER-CELL keyed (R45); split (R48).
moves_ref: "at all-active primes (cofinitely many — only finitely many primes are
roots of some not-identically-zero cell-size polynomial)".  Route IN SCOPE
(Fable#7-GAP-2): the exceptional pools are roots of the finitely many PER-CELL
polynomials `cellP ≠ 0` (root-set finiteness over the finitely many (e, τ, c);
act_iff per cell); infinitude = `M.pools_infinite` minus the finite root union.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem allActive_cofinite {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) :
    {q₀ ∈ M.Pools | q₀ ∉ allActivePools M}.Finite ∧ (allActivePools M).Infinite :=
  sorry

end LeanUrat.MovesS
