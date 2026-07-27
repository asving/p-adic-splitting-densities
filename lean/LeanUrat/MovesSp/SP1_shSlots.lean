/-
Unit Sp.shSlots [REV 2, F10 — binders in full, both theorems] — moves_ref:
"p_{j_k} + σ = (j_k − t·γ)/e + (t·γ − (s₀′ mod e))/e = … = ⌊s₀′/e⌋ + k;
k = 0 is the anchor identity."
deps: Sp.shDvd. sketch: fdiv-additivity on the exact divisions (shDvd + the σ
congruence give both remainders); `Int.add_mul_fdiv_right`, `omega` after
extracting the two dvd witnesses. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem sh_slots (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e)
    (hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) (k : ℤ) :
    Sh t γ e (geoPos e t γ (s0 + k * e)) = s0.fdiv e + k := sorry

/-- = sh_slots at k = 0. -/
theorem sh_anchor (e h s t γ u0 s0 : ℤ) (he : 1 ≤ e)
    (hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) :
    Sh t γ e (geoPos e t γ s0) = s0.fdiv e := sorry

end LeanUrat.MovesSp
