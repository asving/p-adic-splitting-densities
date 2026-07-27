/-
Unit E7.selRank_lt  (MovesD campaign, E-phase)  [AUX]
[REV 4: re-verified against the TRANSPORTED `EligibleImage` (§3.4) — Fable#2 G1's
counterexample (six reducible ord-1 quadratics vs m̄ = 2) hits only the withdrawn gloss.]
informal: the defined rank is a legal selection index: selRank < m̄_r.
deps: E3, E6.
sketch: (i) MEMBERSHIP: ψImage ν satisfies the transported predicate — monic/deg/ord push
through the coefficient embedding, and ν.ψ itself is the irreducible lift over
↥σ.K ≃ poolSubfield (E3's identification); (ii) CARD: the transported eligible set pulls
back injectively to E6's K-side set, so its card ≤ m̄; rank = a proper-initial-segment
count in a set of card ≤ m̄ containing ψImage.  difficulty: medium-hard.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The defined rank is a legal selection index: selRank < m̄_r. -/
theorem selRank_lt {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    selRank R.w ν < R.mbar := by
  sorry

end LeanUrat.MovesD
