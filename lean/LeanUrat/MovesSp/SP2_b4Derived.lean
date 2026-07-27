/-
Unit Sp.b4Derived — moves_ref: "(B4) … hence the Σ eᵢgᵢμᵢ-type constraint
e_r·g_r·μ_r·D_r ≤ e_r·ℓ_r·D_r = w′_r·D_r ≤ n."
sketch: g·μ ≤ ℓ (B4) scaled by e·D; w′ ≤ W ≤ n/D (B3) ⇒ w′·D ≤ n (Nat.div:
W ≤ n/D → W·D ≤ n via Nat.le_div_iff_mul_le, D ≥ 1). difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem egμD_le {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
    {g μ : ℕ} (hsel : s.sel = some (g, μ)) : s.e * g * μ * s.D ≤ s.wraw * s.D ∧
    s.wraw * s.D ≤ n := sorry

end LeanUrat.MovesSp
