/-
Unit XF.3 valExtOf  [PROVED, fleet 2026-07-28]
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
    ValExt p g where
  L := g.SplittingField
  w := MulRingNorm.mulRingNormEquivAbsoluteValue
    (spectralMulAlgNorm ℚ_[p] g.SplittingField).toMulRingNorm
  ext := fun x => by
    rw [MulRingNorm.mulRingNormEquivAbsoluteValue_apply]
    change spectralNorm ℚ_[p] g.SplittingField (algebraMap ℚ_[p] g.SplittingField x) = ‖x‖
    exact spectralNorm_extends x
  splits := Polynomial.SplittingField.splits g

end LeanUrat.MovesX
