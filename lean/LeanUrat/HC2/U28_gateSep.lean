/-
Unit U28.gate_order0_sep  (HC-2 campaign, E-phase — blueprint §5 Layer E)
moves_ref: the V2 gate's mirror at the tame prime q′ = 3 (realF2: split ≠ inert at
q′ = 3): the split and inert root histories yield DIFFERENT masses — σ-separation
through the bridge, as a stratum-count inequality at a fixed small N.
deps: U13 (concrete seeds), MovesC.thmC_b.  difficulty: medium.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- ORDER-0 SEPARATION GATE (p = 3, n = 2): the inert root history (g = 2) and a split
root history (g = 1) produce DIFFERENT stratum masses at the same level N. -/
theorem gate_order0_sep (N : ℕ) (hN : 1 ≤ N) :
    ∃ (Hin Hsp : History 3 F9)
      (Jin : JetSetup Hin 2 N (2 * N)) (Jsp : JetSetup Hsp 2 N (2 * N)),
      Hin.nodes.length = 1 ∧ Hsp.nodes.length = 1 ∧
      (∀ h0 : 0 < Hin.nodes.length,
        (Hin.nodes[0]'h0).species = ReadSpecies.root ∧
        (Hin.nodes[0]'h0).g = 2 ∧ (Hin.nodes[0]'h0).μ = 1) ∧
      (∀ h0 : 0 < Hsp.nodes.length,
        (Hsp.nodes[0]'h0).species = ReadSpecies.root ∧
        (Hsp.nodes[0]'h0).g = 1 ∧ (Hsp.nodes[0]'h0).μ = 1) ∧
      Nat.card (Jin.SHZ (topLocus 3 (2 * N)))
        ≠ Nat.card (Jsp.SHZ (topLocus 3 (2 * N))) := by
  sorry

end LeanUrat.MovesJ
