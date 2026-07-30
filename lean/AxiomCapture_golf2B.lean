-- scratch: golf-pass-2 axiom capture part B (GradedHensel)
import LeanUrat.OM.GradedHensel

open LeanUrat.OM

-- GradedHensel (public)
#print axioms GradedHensel.cdiv
#print axioms GradedHensel.cdiv_le_iff
#print axioms GradedHensel.le_w_mul_cdiv
#print axioms GradedHensel.cdiv_zero_left
#print axioms GradedHensel.cdiv_mono
#print axioms GradedHensel.cdiv_add_le_cdiv_add
#print axioms GradedHensel.sideFloor
#print axioms GradedHensel.sideDepth
#print axioms GradedHensel.SaturatedAt
#print axioms GradedHensel.patternCell_saturatedAt
#print axioms GradedHensel.patternCell_sub_dvd
#print axioms GradedHensel.patternCell_finite
#print axioms GradedHensel.dvd_coeff_mul_slot
#print axioms GradedHensel.mul_eq_zero_of_slot_dvd
#print axioms GradedHensel.graded_mulVec_upgrade
#print axioms GradedHensel.graded_ker_bound
#print axioms GradedHensel.GradedUpgradeAt
#print axioms GradedHensel.polyKer
#print axioms GradedHensel.fiber_sub_dvd_graded
#print axioms GradedHensel.ker_shift_graded
#print axioms GradedHensel.fiberEquivPolyKer
#print axioms GradedHensel.pair_fiber_card_graded
#print axioms GradedHensel.pair_card_graded
#print axioms GradedHensel.gate_margin_graded_A
#print axioms GradedHensel.gate_margin_graded_B
#print axioms GradedHensel.gate_margin_graded_C
#print axioms GradedHensel.bA₀
#print axioms GradedHensel.bB₀
#print axioms GradedHensel.bFlo
#print axioms GradedHensel.bDep
#print axioms GradedHensel.bQb
#print axioms GradedHensel.bSA
#print axioms GradedHensel.bSB
#print axioms GradedHensel.caseB_upgrade
#print axioms GradedHensel.caseB_ker_card
#print axioms GradedHensel.caseB_card_SA
#print axioms GradedHensel.caseB_card_SB
#print axioms GradedHensel.caseB_law_graded
#print axioms GradedHensel.caseB_image_card
#print axioms GradedHensel.caseB_matches_gateB
#print axioms GradedHensel.GradedChain
#print axioms GradedHensel.blocks_card_graded
-- GradedHensel (private declarations potentially touched)
open private dvd_of_isUnit_mul from LeanUrat.OM.GradedHensel
#print axioms dvd_of_isUnit_mul
