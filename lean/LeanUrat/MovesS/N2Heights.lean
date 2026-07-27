/-
Unit `n2_heights` (easy; S5 construction batch) — Hgt/HDom/gwt data (split):
each cell carries a SINGLETON exact height class (the one-step masses are single
monomials at this instance).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_heights :
    ∀ e (τ : n2T.State e) (c : n2M.Cell e τ), ∃ h₀, n2M.HDom e τ c = {h₀} :=
  sorry

end LeanUrat.MovesS
