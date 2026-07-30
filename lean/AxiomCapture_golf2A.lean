-- scratch: golf-pass-2 axiom capture part A (LinearFiber, HenselCount)
import LeanUrat.OM.LinearFiber
import LeanUrat.OM.HenselCount

open LeanUrat.OM

-- LinearFiber
#print axioms LinearFiber.instNeZeroPPow
#print axioms LinearFiber.not_isUnit_cast_p
#print axioms LinearFiber.not_dvd_of_isUnit
#print axioms LinearFiber.pow_cast_ne_zero
#print axioms LinearFiber.exists_mul_pow_of_pow_mul_eq_zero
#print axioms LinearFiber.pval
#print axioms LinearFiber.pval_zero
#print axioms LinearFiber.pval_spec
#print axioms LinearFiber.dvd_of_pval_le
#print axioms LinearFiber.le_of_pow_mul_eq_pow_mul_unit
#print axioms LinearFiber.exists_unit_pow_sub_of_pow_mul_eq
#print axioms LinearFiber.card_range_mul_pow
#print axioms LinearFiber.card_ker_mul_pow
#print axioms LinearFiber.card_ker_reindex
#print axioms LinearFiber.det_submatrix_equiv
#print axioms LinearFiber.card_ker_mul_left
#print axioms LinearFiber.card_ker_mul_right
#print axioms LinearFiber.one_sub_mul_one_add_of_sq
#print axioms LinearFiber.clearL_mul
#print axioms LinearFiber.mul_clearR
#print axioms LinearFiber.vecMulVec_single_sq_left
#print axioms LinearFiber.vecMulVec_single_sq_right
#print axioms LinearFiber.card_ker_pivot_block
#print axioms LinearFiber.det_pivot_block
#print axioms LinearFiber.card_ker_mulVec_of_det
#print axioms LinearFiber.fiber_card
#print axioms LinearFiber.image_index
#print axioms LinearFiber.card_target
#print axioms LinearFiber.mulVec_fiber_card_of_det
#print axioms LinearFiber.mulVec_bijective_iff_isUnit_det
#print axioms LinearFiber.c_eq_zero_iff_isUnit_det
#print axioms LinearFiber.c_eq_zero_iff_isUnit
#print axioms LinearFiber.c_eq_zero_iff_bijective
-- HenselCount
#print axioms HenselCount.leftPart
#print axioms HenselCount.rightPart
#print axioms HenselCount.polyOf
#print axioms HenselCount.coeff_polyOf
#print axioms HenselCount.coeff_polyOf_of_lt
#print axioms HenselCount.coeff_polyOf_of_le
#print axioms HenselCount.polyOf_coeff
#print axioms HenselCount.coeff_mul_monomial'
#print axioms HenselCount.vecOf
#print axioms HenselCount.vecOf_castAdd
#print axioms HenselCount.vecOf_natAdd
#print axioms HenselCount.leftPart_vecOf
#print axioms HenselCount.rightPart_vecOf
#print axioms HenselCount.polyOf_leftPart_vecOf
#print axioms HenselCount.polyOf_rightPart_vecOf
#print axioms HenselCount.sylvester_apply_castAdd
#print axioms HenselCount.sylvester_apply_natAdd
#print axioms HenselCount.sylvester_term_eq
#print axioms HenselCount.sylvester_mulVec_coeff
#print axioms HenselCount.coeff_mul_polyOf_eq_zero
#print axioms HenselCount.coeff_combo_eq_zero
#print axioms HenselCount.polyOf_sylvester_mulVec
#print axioms HenselCount.mulVec_eq_zero_iff_combo
#print axioms HenselCount.dvd_coeff_mul
#print axioms HenselCount.dvd_det_sub
#print axioms HenselCount.dvd_sylvester_sub
#print axioms HenselCount.cell
#print axioms HenselCount.mem_cell_self
#print axioms HenselCount.sub_coeff_eq_zero_of_ge
#print axioms HenselCount.cell_sub_dvd
#print axioms HenselCount.monic_add_of_coeff
#print axioms HenselCount.det_sylvester_stable
#print axioms HenselCount.resultant_stable
#print axioms HenselCount.dvd_of_mulVec_dvd
#print axioms HenselCount.dvd_of_mulVec_eq_zero
#print axioms HenselCount.mul_eq_zero_of_coeff_dvd
#print axioms HenselCount.fiber_sub_dvd
#print axioms HenselCount.mulVec_vecOf_eq_zero
#print axioms HenselCount.ker_shift_mem_fiber
#print axioms HenselCount.fiberEquivKer
#print axioms HenselCount.fiber_card
#print axioms HenselCount.cell_finite
#print axioms HenselCount.image_card
#print axioms HenselCount.sylvesterMulVec_eq
