/-
Unit U27.gate_order0_inert  (HC-2 campaign, E-phase — blueprint §5 Layer E; runs in the
FIRST E/P block per §7.1: the realF2 lesson)
moves_ref: the root-only n = 2 inert history at p = 2; MovesC `C6.thmC_b`; the
INDEPENDENTLY RECORDED value: realM2's decided count for the inert shape at n = 2 — the
1/4 density anchor of `gate_v2_countingDensity_inert2` (OM/RealInstanceV2Gates). The 1/4
tie is the second equation below (mass · 2² = 2^{2N}); with the thmC_b instance it forces
totalPins = 2 (recorded as the first equation — the census stop-the-line number).
deps: U13 (concrete seed), MovesC.thmC_b.  difficulty: medium.
hypothesis_fields: none — THIS UNIT MUST BE AXIOM- AND SEED-HYPOTHESIS-FREE (the seed is
constructed concretely; that is the point).
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Sorries retained for the next fleet round.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- ORDER-0 GATE (inert, p = 2, n = 2): a concrete root-only inert history with a
CONCRETE seed fires `jetSetup_of_seed`, and the resulting stratum mass is the recorded
1/4 (totalPins = 2). -/
theorem gate_order0_inert (N : ℕ) (hN : 1 ≤ N) :
    ∃ (H₀ : History 2 F4) (keys : ℕ → Polynomial ℤ_[2]),
      KeysLawful H₀ keys ∧
      H₀.nodes.length = 1 ∧
      (∀ h0 : 0 < H₀.nodes.length,
        (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
        (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
      ∃ (S : PresentSeed 2 F4 H₀ 2 N keys) (J : JetSetup H₀ 2 N (2 * N)),
        totalPins J (topLocus 2 (2 * N)) = 2 ∧
        Nat.card (J.SHZ (topLocus 2 (2 * N))) * 2 ^ 2 = 2 ^ (2 * N) := by
  sorry

end LeanUrat.MovesJ
