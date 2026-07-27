/-
Unit W2.Mfac_le  (MovesD campaign, E-phase)  [REV 6, Codex#4 f.3: UNCONDITIONAL over the
subtype — the "smuggled" rider is GONE with the domain ruling]
moves_ref: "M(P̂) := ∏_r m̄_r ≤ ∏_r ⌊n/(g_rμ_r)⌋ ≤ n^{|P̂|} (m̄_r as above … coarse chain
displayed)" — for every shape-prefix of the degree-n classifier, verbatim.
deps: W1′.
sketch: m̄_r ≤ ℓ_r ≤ n (W1′); List.prod ≤ pow.  difficulty: easy.
hypothesis_fields: NONE.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n : ℕ}

/-- M(P̂) ≤ n^{|P̂|}, unconditional over the note's shapes. -/
theorem Mfac_le (P : Shape n) :
    (P : ShapePrefix).Mfac ≤ n ^ (P : ShapePrefix).reads.length := by
  sorry

end LeanUrat.MovesD
