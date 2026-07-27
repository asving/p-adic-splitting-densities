/-
Unit U16.threshold_of_seeds  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD §2 Threshold/TW row (`Threshold.jets` = presentations at EVERY level
≥ NP; TW constructs `Threshold` from PRESENT-EXIST).
deps: U15.  difficulty: easy.  hypothesis_fields: hseed, hnorm.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The note's threshold object, from the seeds: `jets N hNP := (U15 …).some`. -/
theorem threshold_of_seeds {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n}
    (hseed : ∀ (i : PrefIdx n (polOM p F) P) (N : ℕ), P.NP (polOM p F) ≤ N →
       ∃ keys : ℕ → Polynomial ℤ_[p], KeysLawful (reprOf i) keys ∧
         Nonempty (PresentSeed p F (reprOf i) n N keys))
    (hnorm : PresentNorm n (polOM p F) P) :
    Nonempty (Threshold p F n (polOM p F) P) := by
  sorry

end LeanUrat.MovesJ
