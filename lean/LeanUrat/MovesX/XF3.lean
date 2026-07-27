/-
Unit XF.3 valExtOf  [E-phase: stated, body sorry]
moves_ref: none (proof apparatus; §4 flag: never strengthens (3b) — and per Ruling 2 it
appears in NO public statement).
sketch: `g.SplittingField` finite over complete ℚ_[p]; `spectralNorm` multiplicative
there (Mathlib `SpectralNorm.lean` + Krasner layer); package as `AbsoluteValue`.
deps: Defs. difficulty: HARD; STUCK ⟹ report (Ruling 2), no rider.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable def valExtOf (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) (hg : g ≠ 0) :
    ValExt p g :=
  sorry

end LeanUrat.MovesX
