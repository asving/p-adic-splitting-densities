/-
Unit Sp.shDvd [REV 2, F9 — binders in full] — moves_ref: "(SH-G) p_j(γ) =
(j − t·γ)/e ∈ ℤ (D.3(c))" [j = j_k = s₀′ + k·e].
(no `1 ≤ e` hypothesis: pure divisibility, degenerate e included)
deps: Sp.shCongr. sketch: s0 − t·γ ≡ 0 [ZMOD e] from shCongr; add k·e.
difficulty: easy.
AS-BUILT (2026-07-30 verify-2 fold-in): the deps/sketch above are the blueprint
plan — the file imports only Defs and closes the divisibility by an inline
`linear_combination`; Sp.shCongr is neither imported nor cited. Inline
duplication tracked under the Class-D watch (notes/GOLF_CAMPAIGN_2026-07-30.md).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem sh_dvd (e h s t γ u0 s0 : ℤ) (hbez : e * s + h * t = 1)
    (hγ : γ = e * u0 + s0 * h) (k : ℤ) : e ∣ (s0 + k * e - t * γ) := by
  refine ⟨k - t * u0 + s0 * s, ?_⟩
  subst hγ
  linear_combination (-s0) * hbez

end LeanUrat.MovesSp
