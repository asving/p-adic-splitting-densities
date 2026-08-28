import Uniformity.ChapC.C136t

/-!
# G5F probe — a unit refinement is operator data, not a `DeepTower` rung

This probe checks only the machine-decidable boundary used by gate G5F.  The
source-faithfulness adjudication itself is recorded, with primary-source page and
clause citations, in the campaign blueprint and `runs/wave-c/verdict_G5F.md`.
-/

namespace G5FProbe

open Uniformity.Density
open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ r : ℕ} {hpin : F.Pin H₀}

/-- Every live `DeepTower` stage from stage two onward rejects the unit row
`e_i = f_i = 1`, directly from `DeepTower.hproper`. -/
theorem unit_row_not_a_proper_stage
    (W : DeepTower F H₀ hpin r) {i : ℕ} (hi2 : 2 ≤ i) (hir : i ≤ r)
    (he : W.e i = 1) (hf : W.f i = 1) : False := by
  have hp := W.hproper i hi2 hir
  norm_num [he, hf] at hp

/-- In particular, `(1,1,171)` cannot be installed as stage five of a
depth-five `DeepTower`; the height coordinate cannot repair failed properness. -/
theorem one_one_one_seventy_one_not_stage_five
    (W : DeepTower F H₀ hpin 5)
    (he5 : W.e 5 = 1) (hf5 : W.f 5 = 1) (_hu5 : W.u 5 = 171) : False := by
  exact unit_row_not_a_proper_stage W (by norm_num) (by norm_num) he5 hf5

/-- The FGMN key-degree multiplier of the refinement is one, so the degree stays 16. -/
example : 1 * 1 * 16 = 16 := by norm_num

/-- Hence the same row cannot satisfy strict degree growth. -/
example : ¬(16 < 1 * 1 * 16) := by norm_num

end G5FProbe
