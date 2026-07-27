/-
Unit U-29c `n2_pool` (easy) — PoolHyp at q₀ = 2; EscapeE0 for A = [1/8]:
geometric decay (`tendsto_pow_atTop_nhds_zero_of_lt_one`).  The 1/8 entry is
`msW_eighth_le`'s p = 2 ratio shadow.
-/
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2ScsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable def n2P2 : PoolHyp n2T n2M n2RB 2 (n2hK 2 (by decide)) 2 := sorry

theorem n2_pool :
    (∀ τA βA : n2P2.Act, n2P2.A τA βA = 1 / 8) ∧ n2P2.Act = Finset.univ :=
  sorry

end LeanUrat.MovesS
