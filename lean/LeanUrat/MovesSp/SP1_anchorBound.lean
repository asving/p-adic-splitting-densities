/-
Unit Sp.anchorBoundCensus — moves_ref: "from (B3)'s 0 ≤ s₀′ ≤ W − w′ and
floor-monotonicity, 0 ≤ a ≤ ⌊(W − w′)/e⌋, a + ℓ = ⌊(s₀′ + w′)/e⌋ ≤ ⌊W/e⌋ ≤ W ≤ n"
(+ "At e = 1 the two statements are ONE: 0 ≤ a = a^geo ≤ W − w′").
sketch: (G2) a = s0/e; Nat.div_le_div_right on s0 ≤ W − w′; for a + ℓ:
a + ℓ ≤ (s0 + e·ℓ)/e ≤ W/e; Nat.div_le_self. NOTE: a ≥ 0 is free in ℕ (the
note's 0 ≤ a). difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem anchor_bound {n : ℕ} {s : Species} (hc : Coherent s)
    (hb : Budget n s) : s.a ≤ (s.W - s.wraw) / s.e ∧ s.a + s.ell ≤ s.W / s.e ∧
    s.W / s.e ≤ s.W ∧ s.W ≤ n ∧ (s.e = 1 → s.a = s.s0 ∧ s.a ≤ s.W - s.wraw) := sorry

end LeanUrat.MovesSp
