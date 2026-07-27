/-
Unit Sp.shExample — moves_ref: "THE VERIFIER'S EXAMPLE (pass-2 C1) … GEOMETRIC:
p₁ = (1 − 3)/2 = −1, p₃ = (3 − 3)/2 = 0 … CENSUS: a = ⌊1/2⌋ = 0 … BÉZOUT CHECK:
(s, t) = (1, −1) … σ = ⌊−3/2⌋ = −2 — the same census image ✓".
sketch: `decide` (Int literals). difficulty: easy. (Named theorem per blueprint.)
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem sh_example : geoPos 2 1 3 1 = -1 ∧ geoPos 2 1 3 3 = 0 ∧ shSigma 1 3 2 = 1
    ∧ Sh 1 3 2 (-1) = 0 ∧ Sh 1 3 2 0 = 1 ∧ shSigma (-1) 3 2 = -2 ∧
    Sh (-1) 3 2 (geoPos 2 (-1) 3 1) = 0 := sorry

end LeanUrat.MovesSp
