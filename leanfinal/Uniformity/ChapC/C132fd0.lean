/-
[M3-FD0, 2026-08-27] — the μ₃ SOURCE RECORDS at depth 2 (unit MFD0, assembled by the
orchestrator after two Sonnet storm deaths; blueprint row:
`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 M3-FD0).

`s2SourceDataTwo` : the SEVEN landed μ₃ operators packaged as
`FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 21` — the corrected
depth-2 triple `(e', f', u') = (2, 1, 21)` (U15/MADJ adjudications), with every operator
read pinned by `rfl` (the anti-drift discipline of the depth-1 record `s2SourceDataOne`,
`C130fd0.lean`).

`s2SourceLawsTwo_of` : the THIRTEEN-field laws record, **CONDITIONAL on exactly the two
honestly-open suppliers** (both machine-certified as genuinely open, not vacuous):

* `hex` — the `normalized_exists` field.  M3-RP10 (`C132rp10.lean`,
  `verdict_MRP10.md`) landed the two-element-field collapse (`ψ = X + 1` forced), the
  monic degree-8 candidate `gEight`, and the BLOCKED-BECAUSE certificates
  (`s2Mu3_recipe_correction_input_impossible`, `s2Mu3_gEight_recipe_input_impossible`):
  the only landed recipe engine cannot evaluate `s2Mu3NormRes` on the candidate — a
  NON-recipe evaluation route is the open node **M3-RP10b**.
* `hconv` — the converse half of `initial_iff_residual`.  M3-KP6 (`C132kp6.lean`,
  `verdict_MKP6.md`) proved the forward direction universally
  (`s2Mu3_initial_to_residual`); the converse needs the μ₃ key-structure bank — the open
  node **M3-KP6b**.

The other ELEVEN fields are discharged by the landed C132 stack (per-field table in
`runs/wave-b/verdict_MFD0.md`).  Once M3-RP10b/M3-KP6b land, `s2SourceLawsTwo_of` fires
unconditionally and M3-SG packages the calculus.  The one deliberately-vacuous discharge
(`normalized_recipe` at the printed grade numerals) mirrors the RECORDED depth-1 defect
(`tooth_recipe_printed_numerals_vacuous`, `C130fd0.lean`): RP-9's
`s2Mu3_recipe_grade_twenty_one_vacuous` certifies the printed odd grade `21` clears no
even-fenced input — the abstract field's numerals, not the realization, are at fault.
-/
import Uniformity.ChapC.C130fd0
import Uniformity.ChapC.C132nv6
import Uniformity.ChapC.C132rp3
import Uniformity.ChapC.C132rp6
import Uniformity.ChapC.C132rp7
import Uniformity.ChapC.C132rp8
import Uniformity.ChapC.C132rp9
import Uniformity.ChapC.C132rp10
import Uniformity.ChapC.C132kp3
import Uniformity.ChapC.C132kp4
import Uniformity.ChapC.C132kp5
import Uniformity.ChapC.C132kp6

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132fd0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130np6
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp0
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132rp9
open Uniformity.Density.Tower.C132kp0 Uniformity.Density.Tower.C132kp3
open Uniformity.Density.Tower.C132kp4 Uniformity.Density.Tower.C132kp5
open Uniformity.Density.Tower.C132kp6

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- ★★ **M3-FD0, the DATA record**: the seven landed μ₃ operators at the corrected
depth-2 triple `(2, 1, 21)`. -/
noncomputable def s2SourceDataTwo :
    FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 21 where
  nextValue := s2Hgt₃ h2 hq
  gradedResidual := s2Mu3GradedRes h2 hq
  normalizedResidual := s2Mu3NormRes h2 hq
  PrevGrade := S2Mu3PrevGrade
  keyPolynomial := S2Mu3KeyPoly h2 hq
  initialEquiv := S2Mu3InitialEquiv h2 hq
  letter := s2Letter h2 hq

/-- read pin: `nextValue` is the μ₃ table `s2Hgt₃`. -/
theorem s2SourceDataTwo_nextValue :
    (s2SourceDataTwo h2 hq).nextValue = s2Hgt₃ h2 hq := rfl

/-- read pin: `gradedResidual` is `s2Mu3GradedRes`. -/
theorem s2SourceDataTwo_gradedResidual :
    (s2SourceDataTwo h2 hq).gradedResidual = s2Mu3GradedRes h2 hq := rfl

/-- read pin: `normalizedResidual` is `s2Mu3NormRes`. -/
theorem s2SourceDataTwo_normalizedResidual :
    (s2SourceDataTwo h2 hq).normalizedResidual = s2Mu3NormRes h2 hq := rfl

/-- read pin: `PrevGrade` is the evenness predicate `S2Mu3PrevGrade`. -/
theorem s2SourceDataTwo_PrevGrade :
    (s2SourceDataTwo h2 hq).PrevGrade = S2Mu3PrevGrade := rfl

/-- read pin: `keyPolynomial` is `S2Mu3KeyPoly`. -/
theorem s2SourceDataTwo_keyPolynomial :
    (s2SourceDataTwo h2 hq).keyPolynomial = S2Mu3KeyPoly h2 hq := rfl

/-- read pin: `initialEquiv` is `S2Mu3InitialEquiv`. -/
theorem s2SourceDataTwo_initialEquiv :
    (s2SourceDataTwo h2 hq).initialEquiv = S2Mu3InitialEquiv h2 hq := rfl

/-- read pin: `letter` is NP-6's forced `s2Letter` (constant `1`, depth-2 typed). -/
theorem s2SourceDataTwo_letter :
    (s2SourceDataTwo h2 hq).letter = s2Letter h2 hq := rfl

set_option maxHeartbeats 1600000 in
/-- ★★ **M3-FD0, the LAWS record — CONDITIONAL on the two open suppliers** (M3-RP10b's
non-recipe `normalized_exists` evaluation and M3-KP6b's converse; see the file header).
The other eleven projections are discharged by named landed theorems. -/
theorem s2SourceLawsTwo_of
    (hex : ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 2 * 1 * (((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree) ∧
          s2Mu3NormRes h2 hq g = ψ)
    (hconv : ∀ g h : Polynomial O,
      S2Mu3KeyPoly h2 hq g → S2Mu3KeyPoly h2 hq h →
        s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h → S2Mu3InitialEquiv h2 hq g h) :
    FGMNSourceLaws (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 21
      (s2SourceDataTwo h2 hq) where
  graded_zero_of_above := fun _ _ h => s2Mu3GradedRes_zero_of_above h2 hq h
  graded_add := fun _ _ _ hg hh hgh => s2Mu3GradedRes_add h2 hq hg hh hgh
  graded_mul := s2Mu3_graded_mul_fills h2 hq (s2DepthTwoKeyChain h2 hq)
    (s2SourceDataTwo h2 hq) rfl rfl rfl
  graded_scalar_nonzero := s2Mu3_graded_scalar_nonzero_fills h2 hq
    (s2DepthTwoKeyChain h2 hq) (s2SourceDataTwo h2 hq) rfl rfl
  normalized_mul := fun g h => s2Mu3NormRes_mul h2 hq g h
  normalized_recipe := fun khat hgr hdeg => s2Mu3_normalized_recipe h2 hq khat hgr hdeg
  normalized_exists := fun _ ψ hm hirr hd hc => hex ψ hm hirr hd hc
  key_criterion := s2Mu3_key_criterion_fills h2 hq (s2DepthTwoKeyChain h2 hq)
    (s2SourceDataTwo h2 hq) rfl rfl
  key_irreducible := fun _ hkp _ => s2Mu3_key_irreducible h2 hq hkp
  carried_key_is_key := fun _ => s2Mu3KeyPoly_Φ₂ h2 hq
  carried_key_residual := fun _ => s2Mu3NormRes_Φ₂ h2 hq
  initial_iff_residual := fun g h hg hh =>
    ⟨fun he => s2Mu3_initial_to_residual h2 hq he, fun hr => hconv g h hg hh hr⟩
  letter_ne_zero := fun i h1 hr => s2Letter_ne_zero h2 hq i h1 hr

end Uniformity.Density.Tower.C132fd0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_nextValue
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_gradedResidual
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_normalizedResidual
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_PrevGrade
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_keyPolynomial
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_initialEquiv
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceDataTwo_letter
#print axioms Uniformity.Density.Tower.C132fd0.s2SourceLawsTwo_of

end AxCheck
