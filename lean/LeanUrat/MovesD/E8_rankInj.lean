/-
Unit E8.rank_inj  (MovesD campaign, E-phase)  [AUX]
informal: on ONE eligible set, rank determines the factor (lex through the shared
`fieldEnum` is a strict total order — the note's "ordered lexicographically by
coefficient vectors in D.3(e)'s fixed residue bases").
deps: E3, E6.
sketch: equal Ranch-images + E3's common subfield give literally equal F-side eligible
sets; two members of a finite set with equal strict-initial-segment counts under a strict
total order are equal.  difficulty: medium-hard.  hypothesis_fields: none.
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

/-- On one eligible set, equal rank forces equal ψ-image. -/
theorem rank_inj {R : ShapeRead} {ν ν' : Node p F} (hM : R.Matches ν) (hM' : R.Matches ν')
    (hg : ν.g = ν'.g) (hμ : ν.μ = ν'.μ) (hR : RanchImage ν = RanchImage ν')
    (hs : selRank R.w ν = selRank R.w ν') :
    ψImage ν = ψImage ν' := by
  sorry

end LeanUrat.MovesD
