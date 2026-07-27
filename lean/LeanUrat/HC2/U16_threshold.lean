/-
Unit U16.threshold_of_seeds  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD §2 Threshold/TW row (`Threshold.jets` = presentations at EVERY level
≥ NP; TW constructs `Threshold` from PRESENT-EXIST).
deps: U15.  difficulty: easy.  hypothesis_fields: hseed, hnorm.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U15_presentExist
import LeanUrat.MovesD.D4R4all_wrapper

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
  -- U16 = MovesD.TW ∘ U15: `present_exist_of_seeds hseed hnorm` supplies PRESENT-EXIST
  -- (the `hex` argument), from which `TW_threshold_witness` builds the threshold by
  -- choice on L12's exact range (blueprint §5 Layer C, deps U15 + MovesD TW row).
  exact TW_threshold_witness (present_exist_of_seeds hseed hnorm)

end LeanUrat.MovesJ
