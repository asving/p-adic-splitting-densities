/-
Unit U-29d2 `n2_pools_all` (medium) — legs_reg/pools_e0 at EVERY base prime:
1×1 packages, entry q₀⁻³ < 1 uniformly at q₀ ≥ 2.  consumedDeltas = {1} at this
instance (n2_shapefam), so RegP reduces to the base pools themselves.
-/
import LeanUrat.MovesS.N2Pool
import LeanUrat.MovesS.N2ShapeFam

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_pools_all :
    (∀ p : ℕ, p.Prime → RegP n2T n2M n2RB p n2hK n2F) ∧
    (∀ e (he : e ∈ Finset.Icc 1 2), ∀ q₀ : ℚ, (∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)) →
      Nonempty (PoolHyp n2T n2M n2RB e (n2hK e he) q₀)) :=
  sorry

end LeanUrat.MovesS
