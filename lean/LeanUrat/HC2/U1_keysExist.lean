/-
Unit U1.keys_exist  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.keys_mid`/`landing` docstrings ("ALL reads incl. the FINAL one
obey the recorded-data landing law").
deps: Moves L3_liftExists (proof SHAPE only), IsRecenteringCore, U1b (final-read landing),
D8 `isNodeLift_iff`.  difficulty: medium.  hypothesis_fields: none.
F10 GUARD: L3's lift is at the STAGE pair and must NEVER be conflated with the node pair.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A lawful key tower exists for every coherent history: interior keys are the recorded
child keys (coherence's `IsNodeLift`/`IsRecenteringCore` clauses ARE the landing law
there); the FINAL key is `Φ − lift` at a recentering, else U1b's read-pair lift. -/
theorem keys_exist {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) :
    ∃ keys : ℕ → Polynomial ℤ_[p],
      (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
      (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i)) := by
  sorry

end LeanUrat.MovesJ
