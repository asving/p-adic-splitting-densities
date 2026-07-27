/-
Unit U31.gate_readsOf_inert2  (HC-2 campaign, E-phase — rev 2, audit GAP-4: the
`ReadsOf` NON-VACUITY ANCHOR; FIRST E/P block with U27/U30)
moves_ref: at U27's root-only inert history H₀ (p = 2, n = 2), a CONCRETE monic
quadratic f (the inert gate's polynomial — the P-phase pins the exact instance from the
W1/realF2 gate data) with `ReadsOf 2 F4 2 f H₀` PROVED by an explicit development
witness — axiom- and seed-free.
PURPOSE: D4's `SideReads` body is an E-phase transcription; if the transcription
over-strengthens (flagged risk: clause (iii)'s `σ.R f` anchor), `ReadsOf` is EMPTY,
U19–U24 become vacuously true, and the W4-1 `eligible` seam dies silently — this gate
converts that silent death into a day-one failure.
deps: D4.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- GATE: `ReadsOf` is INHABITED on concrete order-0 data — the root-only inert history
at p = 2, n = 2, with a concrete monic quadratic run on it. -/
theorem gate_readsOf_inert2 :
    ∃ (H₀ : History 2 F4) (f : Polynomial ℤ_[2]),
      H₀.nodes.length = 1 ∧
      (∀ h0 : 0 < H₀.nodes.length,
        (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
        (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
      ReadsOf 2 F4 2 f H₀ := by
  sorry

end LeanUrat.MovesJ
