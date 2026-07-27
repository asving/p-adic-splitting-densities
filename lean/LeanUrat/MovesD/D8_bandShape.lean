/-
Unit D8.band_shape  (MovesD campaign, E-phase)
moves_ref: (L9's per-read exponent — `inFreshBand` is §C C.1(ii)'s inventory; all three
conjuncts shape formulas).
deps: D6d, D6e, D7b, D7c (coherence via `J.coherent`).
sketch: conjunct-wise transfer.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D6d_htShape
import LeanUrat.MovesD.D6e_prevRimShape
import LeanUrat.MovesD.D7b_floorShape
import LeanUrat.MovesD.D7c_slotValShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {P : Shape n}

/-- The fresh band is the shape band, coordinate for coordinate. -/
theorem band_shape {H : History p F} {J : JetSetup H n N m}
    (hP : (P : ShapePrefix).MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (c : Fin m) :
    inFreshBand H n J.coordOf r (H.nodes[r]'hr) c
      ↔ (P : ShapePrefix).bandS n r (J.coordOf c) := by
  -- lengths agree (Matches carries `H.nodes.length = P.reads.length`)
  have hr' : r < (P : ShapePrefix).reads.length := by
    obtain ⟨hlen, _⟩ := hP
    omega
  -- Conjunct-wise transfer of the three `inFreshBand` clauses to their `bandS` mirrors:
  --   conjunct 1 (rim region) via D6e `prevRim_shape`;
  --   conjunct 2 (above the floor) via D7b `floorH_shape` + D6d `htH_shape`;
  --   conjunct 3 (below the fine-slot valuation) via D7c `slotVal_shape` + D6d `htH_shape`.
  unfold inFreshBand ShapePrefix.bandS
  rw [htH_shape hP r (J.coordOf c), floorH_shape J.coherent hP r (J.coordOf c).2,
    prevRim_shape hP r, slotVal_shape J.coherent hP r hr hr' (J.coordOf c).2,
    List.getElem?_eq_getElem hr']
  -- collapse `(some R).elim False (fun R => …)` on the shape side to close the trivial `↔`
  simp only [Option.elim_some]

end LeanUrat.MovesD
