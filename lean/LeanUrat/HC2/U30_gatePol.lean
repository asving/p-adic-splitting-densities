/-
Unit U30.gate_polOM  (HC-2 campaign, E-phase — blueprint §5 Layer E; FIRST-block
tripwire for U25's D.10 scale-arithmetic risk)
moves_ref: a concrete recentering node — the Case-L gate's recentering read data at
p = 2, transcribed (the P-phase pins the exact Case-L instance; the E-phase statement
pins p = 2 + species + the explicit-witness form). If even the witness instance fails
against `RecenterLiftSpec`, the scale-bookkeeping risk fires at day one, not at
escalation.  deps: D2, D3; Moves L1_base* (the base-stage construction).
difficulty: medium.  hypothesis_fields: none (axiom-free by construction).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- GATE: a concrete recentering node at p = 2 on which the recentering-lift spec is
realized by EXPLICIT WITNESS — polOM's totality instantiated once, axiom-free. -/
theorem gate_polOM :
    ∃ ν : Node 2 (ZMod 2), ν.species = ReadSpecies.recentering ∧
      (∃ tL : Polynomial ℤ_[2], RecenterLiftSpec ν tL) ∧
      RecenterLiftSpec ν ((polOM 2 (ZMod 2)).liftOf ν) := by
  sorry

end LeanUrat.MovesJ
