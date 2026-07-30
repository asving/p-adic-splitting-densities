-- scratch: axiom-footprint capture for golf pass 2 chunk (LimitGlue/LimitRecurrence/
-- LimitSpine/SchwartzZippel/Discriminant/SparseResultant). NOT part of the build.
import LeanUrat.OM.LimitGlue
import LeanUrat.OM.LimitRecurrence
import LeanUrat.OM.LimitSpine
import LeanUrat.OM.SchwartzZippel
import LeanUrat.OM.Discriminant
import LeanUrat.OM.SparseResultant

-- LimitRecurrence
#print axioms LeanUrat.OM.LimitRecurrence.vanishing_forcing_tendsto_zero
#print axioms LeanUrat.OM.LimitRecurrence.firstOrder_recurrence_limit
#print axioms LeanUrat.OM.LimitRecurrence.firstOrder_recurrence_limit_err

-- LimitGlue (F3)
#print axioms LeanUrat.OM.F3.invPow_tendsto_zero
#print axioms LeanUrat.OM.F3.vertexFactor_tendsto_one
#print axioms LeanUrat.OM.F3.bb1Value_share_tendsto_one
#print axioms LeanUrat.OM.F3.boxVolume_normalized_limit
#print axioms LeanUrat.OM.F3.selfLoopRatio_mem_Ioo
#print axioms LeanUrat.OM.F3.selfLoop_resummation
#print axioms LeanUrat.OM.F3.selfLoop_resummation_leaf
#print axioms LeanUrat.OM.F3.children_product_limit
#print axioms LeanUrat.OM.F3.firstOrder_recurrence_limit_rat
#print axioms LeanUrat.OM.F3.selfLoopRatio_mem_Ico
#print axioms LeanUrat.OM.F3.nodeTrunc_tendsto_of_recurrence
#print axioms LeanUrat.OM.F3.nodeTrunc_tendsto_of_corrected_GLUE1
#print axioms LeanUrat.OM.F3.node_limit_assembly

-- LimitSpine
#print axioms LeanUrat.OM.LimitSpine.boxCount_normalized_eq_columnMeasure_prod
#print axioms LeanUrat.OM.LimitSpine.boxCount_normalized_eq_bb1Value
#print axioms LeanUrat.OM.LimitSpine.nodeMeasure_boxSum_of_spineLimit
#print axioms LeanUrat.OM.LimitSpine.nonSelfLoopNorm
#print axioms LeanUrat.OM.LimitSpine.nodeTrunc_step_of_rec
#print axioms LeanUrat.OM.LimitSpine.nodeNum_selfLoop_resummation
#print axioms LeanUrat.OM.LimitSpine.spine_nodeMeasure_boxSum

-- SchwartzZippel
#print axioms LeanUrat.OM.SchwartzZippel.redHom
#print axioms LeanUrat.OM.SchwartzZippel.redHom_surjective
#print axioms LeanUrat.OM.SchwartzZippel.castHom_fiber_card
#print axioms LeanUrat.OM.SchwartzZippel.fiber_finset_card
#print axioms LeanUrat.OM.SchwartzZippel.card_roots_zmod_ppow_le
#print axioms LeanUrat.OM.SchwartzZippel.card_roots_zmod_ppow_le'
#print axioms LeanUrat.OM.SchwartzZippel.field_zero_count_le
#print axioms LeanUrat.OM.SchwartzZippel.tail_fiber_card
#print axioms LeanUrat.OM.SchwartzZippel.finSuccEquiv_map
#print axioms LeanUrat.OM.SchwartzZippel.slice_reduce_natural
#print axioms LeanUrat.OM.SchwartzZippel.totalDegree_map_le
#print axioms LeanUrat.OM.SchwartzZippel.mvRed
#print axioms LeanUrat.OM.SchwartzZippel.schwartz_zippel_local

-- Discriminant (M_F4)
#print axioms LeanUrat.OM.M_F4.discr_monic_eq_resultant
#print axioms LeanUrat.OM.M_F4.discr_map_monic
#print axioms LeanUrat.OM.M_F4.univMonic
#print axioms LeanUrat.OM.M_F4.univMonic_tail_degree_lt
#print axioms LeanUrat.OM.M_F4.univMonic_monic
#print axioms LeanUrat.OM.M_F4.univMonic_natDegree
#print axioms LeanUrat.OM.M_F4.univMonic_coeff_lt
#print axioms LeanUrat.OM.M_F4.Delta
#print axioms LeanUrat.OM.M_F4.coeffTuple
#print axioms LeanUrat.OM.M_F4.coeffEval
#print axioms LeanUrat.OM.M_F4.map_coeffEval_univMonic
#print axioms LeanUrat.OM.M_F4.disc_is_coeff_polynomial
#print axioms LeanUrat.OM.M_F4.resultant_deriv_eq_default
#print axioms LeanUrat.OM.M_F4.discr_ne_zero_of_separable_monic
#print axioms LeanUrat.OM.M_F4.squarefreeMonicCount_pos
#print axioms LeanUrat.OM.M_F4.exists_separable_monic_zmod
#print axioms LeanUrat.OM.M_F4.Delta_nonzero_mod_p
#print axioms LeanUrat.OM.M_F4.discZeroSet
#print axioms LeanUrat.OM.M_F4.discZeroCount
#print axioms LeanUrat.OM.M_F4.coeffToMonicVal
#print axioms LeanUrat.OM.M_F4.coeffToMonicVal_monic_deg
#print axioms LeanUrat.OM.M_F4.coeffToMonicVal_coeff_lt
#print axioms LeanUrat.OM.M_F4.coeffEquivMonicBox
#print axioms LeanUrat.OM.M_F4.discZeroCount_eq_eval_card

-- SparseResultant
#print axioms LeanUrat.OM.SparseResultant.resultant_X_pow_sub_C_expand
#print axioms LeanUrat.OM.SparseResultant.resultant_expand
#print axioms LeanUrat.OM.SparseResultant.isNilpotent_p_zmod
#print axioms LeanUrat.OM.SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal
#print axioms LeanUrat.OM.SparseResultant.det_eq_pow_mul_unit_of_colWeights
#print axioms LeanUrat.OM.SparseResultant.sparseTwist
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_eq_sum
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_coeff_mul
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_coeff_of_not_dvd
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_coeff_zero
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_coeff_top
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_natDegree
#print axioms LeanUrat.OM.SparseResultant.sparseTwist_monic
#print axioms LeanUrat.OM.SparseResultant.crossPerm
#print axioms LeanUrat.OM.SparseResultant.crossPerm_castAdd_val
#print axioms LeanUrat.OM.SparseResultant.crossPerm_natAdd_val
#print axioms LeanUrat.OM.SparseResultant.resultant_sparseTwist
#print axioms LeanUrat.OM.SparseResultant.resultant_sparseTwist_isUnit
#print axioms LeanUrat.OM.SparseResultant.resultant_sparseTwist_cross
