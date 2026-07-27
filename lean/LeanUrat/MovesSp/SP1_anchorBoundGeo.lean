/-
Unit Sp.anchorBoundGeo — moves_ref: "GEOMETRIC IMAGE (through Sh⁻¹, per realized
read): −σ ≤ a^geo ≤ ⌊(W − w′)/e⌋ − σ with σ = ⌊tγ/e⌋ — height- and
Bézout-dependent, hence NOT a species-level bound".
deps: Sp.anchorBoundCensus. sketch: rearrange hshift with 0 ≤ a ≤ bound; omega.
difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem anchor_bound_geo {n} {s : Species} (hc : Coherent s)
    (hb : Budget n s) (σ ageo : ℤ) (hshift : (s.a : ℤ) = ageo + σ) :
    -σ ≤ ageo ∧ ageo ≤ ((s.W - s.wraw) / s.e : ℕ) - σ := sorry

end LeanUrat.MovesSp
