import LeanUrat.OM.Order0Fiber
import LeanUrat.OM.Order0Hull
import LeanUrat.OM.Order0RealDensity
import LeanUrat.OM.Order0Root
import LeanUrat.OM.Necklace
import LeanUrat.OM.FDescentCensus

-- Order0Fiber
#print axioms LeanUrat.OM.Order0.classifyAux_head_payload
#print axioms LeanUrat.OM.Order0.classify_head_payload
#print axioms LeanUrat.OM.Order0.npVertices_mem_support
#print axioms LeanUrat.OM.Order0.latticePolygon_height0_eq
#print axioms LeanUrat.OM.Order0.encodeCells_map_dS
#print axioms LeanUrat.OM.Order0.sorted_attach_map_coe
#print axioms LeanUrat.OM.Order0.classify_eq_sepShape_only_if

-- Order0Hull
#print axioms LeanUrat.OM.Order0.getLastD_map_pair
#print axioms LeanUrat.OM.Order0.head_zero_of_pairwise
#print axioms LeanUrat.OM.Order0.getLastD_of_pairwise
#print axioms LeanUrat.OM.Order0.collinear₃_of_flat
#print axioms LeanUrat.OM.Order0.dropCollinear_flat
#print axioms LeanUrat.OM.Order0.flat_pair_mem_validLines
#print axioms LeanUrat.OM.Order0.npHeight_flat
#print axioms LeanUrat.OM.Order0.hullDots_flat
#print axioms LeanUrat.OM.Order0.zero_mem_hullAbscissae
#print axioms LeanUrat.OM.Order0.n_mem_hullAbscissae
#print axioms LeanUrat.OM.Order0.mem_hullAbscissae_bound
#print axioms LeanUrat.OM.Order0.npVerticesFull_flat
#print axioms LeanUrat.OM.Order0.npVertices_of_flat
#print axioms LeanUrat.OM.Order0.npSides_of_flat
#print axioms LeanUrat.OM.Order0.flatSide_slope
#print axioms LeanUrat.OM.Order0.flatSide_e
#print axioms LeanUrat.OM.Order0.flatSide_h
#print axioms LeanUrat.OM.Order0.flatSide_length
#print axioms LeanUrat.OM.Order0.flatSide_residualDeg

-- Order0RealDensity
#print axioms LeanUrat.OM.Order0.montes_order0_realDensity
#print axioms LeanUrat.OM.Order0.montes_order0_certified_density_pos
#print axioms LeanUrat.OM.Order0.stratumCount_sepShape_general
#print axioms LeanUrat.OM.Order0.montes_order0_perShape_density_general
#print axioms LeanUrat.OM.Order0.montes_order0_density_general_prime
#print axioms LeanUrat.OM.Order0.montes_order0_density_general_prime_pos

-- Order0Root
#print axioms LeanUrat.OM.Order0.zero_zero_mem_boxValSupport
#print axioms LeanUrat.OM.Order0.n_zero_mem_boxValSupport
#print axioms LeanUrat.OM.Order0.boxValSupport_fst_le
#print axioms LeanUrat.OM.Order0.rootSide_eq_flat
#print axioms LeanUrat.OM.Order0.rootFace_eq_flatFace
#print axioms LeanUrat.OM.Order0.valuation_ite_eq_castHom
#print axioms LeanUrat.OM.Order0.boxCoeffData_flatSide
#print axioms LeanUrat.OM.Order0.residualPoly_flat_eq_reduction
#print axioms LeanUrat.OM.Order0.rootResidual_eq_reduction
#print axioms LeanUrat.OM.Order0.rootResidual_natDegree
#print axioms LeanUrat.OM.Order0.fRootCtx_dr
#print axioms LeanUrat.OM.Order0.fRootCtx_Rr
#print axioms LeanUrat.OM.Order0.fRootCtx_Nr

-- Necklace
#print axioms LeanUrat.OM.Necklace.necklaceSum
#print axioms LeanUrat.OM.Necklace.necklaceSum_flip
#print axioms LeanUrat.OM.Necklace.sum_moebius_divisors
#print axioms LeanUrat.OM.Necklace.necklaceSum_nonneg
#print axioms LeanUrat.OM.Necklace.prime_pow_dvd_pow_sub_pow
#print axioms LeanUrat.OM.Necklace.sum_divisors_eq_sum_coprime_part
#print axioms LeanUrat.OM.Necklace.prime_pow_dvd_necklaceSum
#print axioms LeanUrat.OM.Necklace.dvd_necklaceSum
#print axioms LeanUrat.OM.Necklace.necklaceQ
#print axioms LeanUrat.OM.Necklace.necklaceQ_nonneg
#print axioms LeanUrat.OM.Necklace.necklaceQ_eq_natCast

-- FDescentCensus
#print axioms LeanUrat.OM.FDescentCensus.card_base_eq
#print axioms LeanUrat.OM.FDescentCensus.galoisField_card_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.galoisField_card_eq_base_pow
#print axioms LeanUrat.OM.FDescentCensus.monicCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.squarefreeCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.residualCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.irreducibleCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.avail_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.shapeCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.residualCensus_child_eq_base_at_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.monicCensus_child_eq_base_at_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.conjugateBlock_orbit_count
