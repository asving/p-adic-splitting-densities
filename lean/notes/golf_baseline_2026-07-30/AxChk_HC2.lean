import LeanUrat.HC2.Defs
import LeanUrat.HC2.K1_vertexPin
import LeanUrat.HC2.U10_zcStep
import LeanUrat.HC2.U11_rootHeight
import LeanUrat.HC2.U13_assembly
import LeanUrat.HC2.U14_npFits
import LeanUrat.HC2.U15_presentExist
import LeanUrat.HC2.U16_threshold
import LeanUrat.HC2.U17a_liftSwap
import LeanUrat.HC2.U17b_galois
import LeanUrat.HC2.U17c_total
import LeanUrat.HC2.U18_unique
import LeanUrat.HC2.U19_runCoherent
import LeanUrat.HC2.U1_keysExist
import LeanUrat.HC2.U1_negWitness
import LeanUrat.HC2.U1b_nodeLift
import LeanUrat.HC2.U20_NA
import LeanUrat.HC2.U20a_NAtransportRoot
import LeanUrat.HC2.U20b_NAtransportIncrement
import LeanUrat.HC2.U20c_NAtransportRecentering
import LeanUrat.HC2.U21_HV
import LeanUrat.HC2.U22E1_spanStrict
import LeanUrat.HC2.U22E2_vertexEq
import LeanUrat.HC2.U22_SAE
import LeanUrat.HC2.U23_runRealizable
import LeanUrat.HC2.U24_runCanon
import LeanUrat.HC2.U25_polTotal
import LeanUrat.HC2.U26_fiberWelldef
import LeanUrat.HC2.U27_gateInert
import LeanUrat.HC2.U28_gateSep
import LeanUrat.HC2.U29_gateNP
import LeanUrat.HC2.U2_freshDisj
import LeanUrat.HC2.U30_gatePol
import LeanUrat.HC2.U31_gateReadsOf
import LeanUrat.HC2.U3_freshBand
import LeanUrat.HC2.U4_freshCover
import LeanUrat.HC2.U5_freshAssembled
import LeanUrat.HC2.U6_mstarEq
import LeanUrat.HC2.U7_sigmaRec
import LeanUrat.HC2.U8_inhImplied
import LeanUrat.HC2.U9_zcRoot

#print axioms LeanUrat.MovesJ.boxChart_sorted
#print axioms LeanUrat.MovesJ.boxChart_lt
#print axioms LeanUrat.MovesJ.isNodeLift_iff
#print axioms LeanUrat.MovesJ.valueSlots_spanSlot
#print axioms LeanUrat.MovesJ.mkFreshClauses_disj
#print axioms LeanUrat.MovesJ.pinTransportSystem_spec
#print axioms LeanUrat.MovesJ.isDevelopment_extend
#print axioms LeanUrat.MovesJ.strFrame_pos
#print axioms LeanUrat.MovesJ.K1_readVertexPin_nonrec
#print axioms LeanUrat.MovesJ.K1_readVertexPin
#print axioms LeanUrat.MovesJ.K1_NA_transport_root
#print axioms LeanUrat.MovesJ.K1_NA_transport_increment
#print axioms LeanUrat.MovesJ.K1_SAE_vertexEq_endpoint
#print axioms LeanUrat.MovesJ.zc_step_transport
#print axioms LeanUrat.MovesJ.zc_step_freshExact
#print axioms LeanUrat.MovesJ.zc_step_interiorZero
#print axioms LeanUrat.MovesJ.zc_step_confine
#print axioms LeanUrat.MovesJ.zc_step
#print axioms LeanUrat.MovesJ.root_height_of_inBox
#print axioms LeanUrat.MovesJ.jetSetup_of_seed
#print axioms LeanUrat.MovesJ.NP_fits
#print axioms LeanUrat.MovesJ.NP_fits_box
#print axioms LeanUrat.MovesJ.present_exist_of_seeds
#print axioms LeanUrat.MovesJ.threshold_of_seeds
#print axioms LeanUrat.MovesJ.lift_swap
#print axioms LeanUrat.MovesJ.galois_root_swap
#print axioms LeanUrat.MovesJ.galois_transport
#print axioms LeanUrat.MovesJ.galois_normalize_upTo
#print axioms LeanUrat.MovesJ.galois_normalize
#print axioms LeanUrat.MovesJ.presentNorm_total
#print axioms LeanUrat.MovesJ.presentNorm_polOM
#print axioms LeanUrat.MovesJ.nextField_le_galFixed
#print axioms LeanUrat.MovesJ.canonRoot_congr
#print axioms LeanUrat.MovesJ.presentNorm_unique
#print axioms LeanUrat.MovesJ.readsOf_coherent
#print axioms LeanUrat.MovesJ.keys_exist_of_run
#print axioms LeanUrat.MovesJ.U1neg.last_lt
#print axioms LeanUrat.MovesJ.U1neg.zeroLast_getElem
#print axioms LeanUrat.MovesJ.U1neg.zeroLast_map_e
#print axioms LeanUrat.MovesJ.U1neg.zeroLast_strFrame
#print axioms LeanUrat.MovesJ.U1neg.zeroLast_coherent
#print axioms LeanUrat.MovesJ.U1neg.zeroLast_no_keys
#print axioms LeanUrat.MovesJ.retiredKeysExist_false_of_witness
#print axioms LeanUrat.MovesJ.keysLawful_of_hcoh_false_of_witness
#print axioms LeanUrat.MovesJ.nodeLift_exists
#print axioms LeanUrat.MovesJ.readsOf_NA
#print axioms LeanUrat.MovesJ.NA_transport_root
#print axioms LeanUrat.MovesJ.NA_transport_increment
#print axioms LeanUrat.MovesJ.NA_transport_recentering
#print axioms LeanUrat.MovesJ.readsOf_HV_of_pin
#print axioms LeanUrat.MovesJ.readsOf_HV
#print axioms LeanUrat.MovesJ.SAE_spanStrict_endpoint
#print axioms LeanUrat.MovesJ.SAE_vertexEq_endpoint
#print axioms LeanUrat.MovesJ.readsOf_SAE
#print axioms LeanUrat.MovesJ.readsOf_realizable
#print axioms LeanUrat.MovesJ.readsOf_canonical
#print axioms LeanUrat.MovesJ.polOM_total
#print axioms LeanUrat.MovesJ.polOM_liftOf_spec
#print axioms LeanUrat.MovesJ.class_fiber_welldef
#print axioms LeanUrat.MovesJ.U27.keysLawful₀
#print axioms LeanUrat.MovesJ.gate_order0_inert
#print axioms LeanUrat.MovesJ.gate_order0_sep
#print axioms LeanUrat.MovesJ.gate_NP_value
#print axioms LeanUrat.MovesJ.gate_NP_fits
#print axioms LeanUrat.MovesJ.gate_NP_attained
#print axioms LeanUrat.MovesJ.mkFresh_disj
#print axioms LeanUrat.MovesJ.gate_polOM
#print axioms LeanUrat.MovesJ.U31.ρ_eq_zero_iff
#print axioms LeanUrat.MovesJ.U31.θ_C
#print axioms LeanUrat.MovesJ.U31.bw_eq
#print axioms LeanUrat.MovesJ.U31.fq_monic
#print axioms LeanUrat.MovesJ.U31.fq_natDegree
#print axioms LeanUrat.MovesJ.U31.is_const
#print axioms LeanUrat.MovesJ.U31.NF_const
#print axioms LeanUrat.MovesJ.U31.bw_const_nonneg
#print axioms LeanUrat.MovesJ.U31.dev_coeff
#print axioms LeanUrat.MovesJ.U31.coherent_H₀
#print axioms LeanUrat.MovesJ.U31.landingKey_ν₀
#print axioms LeanUrat.MovesJ.U31.sideReads_ν₀
#print axioms LeanUrat.MovesJ.gate_readsOf_inert2
#print axioms LeanUrat.MovesJ.mkFresh_band
#print axioms LeanUrat.MovesJ.levelSet_no_straddle
#print axioms LeanUrat.MovesJ.mkFresh_cover
#print axioms LeanUrat.MovesJ.mkFresh_assembled
#print axioms LeanUrat.MovesJ.mkFresh_mstar
#print axioms LeanUrat.MovesJ.mkSigma_init
#print axioms LeanUrat.MovesJ.freshAttach_exists
#print axioms LeanUrat.MovesJ.mkSigma_recursion_of_unpinned
#print axioms LeanUrat.MovesJ.mkSigma_recursion_zero
#print axioms LeanUrat.MovesJ.mkSigma_recursion
#print axioms LeanUrat.MovesJ.mkStratum_inh
#print axioms LeanUrat.MovesJ.zc_root_downset_mp
#print axioms LeanUrat.MovesJ.zc_root_downset_mpr
#print axioms LeanUrat.MovesJ.zc_root_interior_zero
#print axioms LeanUrat.MovesJ.zc_root
#print axioms LeanUrat.MovesJ.u9c_probe_tail
