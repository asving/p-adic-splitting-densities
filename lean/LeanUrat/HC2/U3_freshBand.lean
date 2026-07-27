/-
Unit U3.mkFresh_band  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.fresh_band` docstring (supports ⊆ the D.11 band, ROUND-6 fine
boundary).
deps: D6.  difficulty: medium.  hypothesis_fields: none.
sketch: strip supports are chosen from the band; value level-set members have height =
slotVal (the band's upper edge) — the in-band condition is D6's own roster selection
(value clauses only at pre-crossing slots), the `< prevRim` from D6's slot range.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Every constructed fresh clause support lies INSIDE the band (verbatim
`JetSetup.fresh_band`'s field type at `mkFresh`). -/
theorem mkFresh_band {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses, ∀ c ∈ cl.support,
      inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c := by
  sorry

end LeanUrat.MovesJ
