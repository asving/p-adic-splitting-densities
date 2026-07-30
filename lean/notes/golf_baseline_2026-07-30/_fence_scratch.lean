import Mathlib
import LeanUrat.MovesT.C1_capHen
import LeanUrat.MovesT.C2_capIrr
import LeanUrat.MovesT.C3_nsLump
import LeanUrat.MovesT.C4_nsLadder
import LeanUrat.MovesT.C5_nsFree
import LeanUrat.MovesT.C6_nsPrice
import LeanUrat.MovesT.C7_nsNull
import LeanUrat.MovesT.C8_nsTreeBound
import LeanUrat.MovesT.D10_classTreeCtbl
import LeanUrat.MovesT.D11_fibOf
import LeanUrat.MovesT.D12_packages
import LeanUrat.MovesT.D13_ifaceGate
import LeanUrat.MovesT.D14_chainCharges
import LeanUrat.MovesT.D15_w3Rekey
import LeanUrat.MovesT.D1_eligible
import LeanUrat.MovesT.D2_eligGate
import LeanUrat.MovesT.D3_verdictModel
import LeanUrat.MovesT.D4_cellLevel
import LeanUrat.MovesT.D5_d4rcyl
import LeanUrat.MovesT.D6_cfw
import LeanUrat.MovesT.D7_npid
import LeanUrat.MovesT.D8_pathOrder
import LeanUrat.MovesT.D9_shapeCtbl
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E10_perShape
import LeanUrat.MovesT.E11_treeN
import LeanUrat.MovesT.E12_treeNns
import LeanUrat.MovesT.E13_tgtFinAdd
import LeanUrat.MovesT.E1_jcRootPart
import LeanUrat.MovesT.E2_jcRootCard
import LeanUrat.MovesT.E3_jcSingle
import LeanUrat.MovesT.E4_jcMultiBranch
import LeanUrat.MovesT.E5_rootSplit
import LeanUrat.MovesT.E6_segStep
import LeanUrat.MovesT.E7_firstSplit
import LeanUrat.MovesT.E8_treeExp
import LeanUrat.MovesT.E9_fiberDisjoint
import LeanUrat.MovesT.F0_preHalt
import LeanUrat.MovesT.F1_oneF
import LeanUrat.MovesT.F2_dictPtwise
import LeanUrat.MovesT.F3_dictSum
import LeanUrat.MovesT.F4_belowHalt
import LeanUrat.MovesT.G1_toyGate
import LeanUrat.MovesT.G2_toyOneF
import LeanUrat.MovesT.S1_sibDefs
import LeanUrat.MovesT.S2_sibFalse
import LeanUrat.MovesT.S3_sibRoot
import LeanUrat.MovesT.V1_vdDeg
import LeanUrat.MovesT.V2_vdDegNs
import LeanUrat.MovesT.V3_accKeyDeg
import LeanUrat.MovesT.V4_satW1
import LeanUrat.MovesT.V5_tauDisjoint
import LeanUrat.MovesT.V6_tauTotal
import LeanUrat.MovesT.V7_vdFin
import LeanUrat.MovesT.V8_shapeOf
import LeanUrat.MovesT.V9_irrSat

#print axioms LeanUrat.MovesT.redPoly_congr
#print axioms LeanUrat.MovesT.tbcap_hen
#print axioms LeanUrat.MovesT.tbcap_hen_cells
#print axioms LeanUrat.MovesT.unitri_preimage_agree
#print axioms LeanUrat.MovesT.shz_top_local
#print axioms LeanUrat.MovesT.strictMono_fin_eq_id
#print axioms LeanUrat.MovesT.coordOf_key_eq
#print axioms LeanUrat.MovesT.coordOf_fst
#print axioms LeanUrat.MovesT.levelIdx_coordOf
#print axioms LeanUrat.MovesT.le_sup_of_transported
#print axioms LeanUrat.MovesT.capIrr_uniform
#print axioms LeanUrat.MovesT.tbcap_irr
#print axioms LeanUrat.MovesT.tbcap_irr_family
#print axioms LeanUrat.MovesT.tbcap_irr_npband
#print axioms LeanUrat.MovesT.ns_lump
#print axioms LeanUrat.MovesT.ns_ladder
#print axioms LeanUrat.MovesT.nsZ_free
#print axioms LeanUrat.MovesT.ns_price
#print axioms LeanUrat.MovesT.ns_null
#print axioms LeanUrat.MovesT.ns_tree_bound
#print axioms LeanUrat.MovesT.fibOf_fiber_disjoint
#print axioms LeanUrat.MovesT.fibOf_partition
#print axioms LeanUrat.MovesT.chain_charge
#print axioms LeanUrat.MovesT.chainReads_ne
#print axioms LeanUrat.MovesT.readLedgerOf_bdy
#print axioms LeanUrat.MovesT.w3_rekey_typed
#print axioms LeanUrat.MovesT.eligibleT_iff_child
#print axioms LeanUrat.MovesT.eligibleT_root_sub
#print axioms LeanUrat.MovesT.eligibleT_cell_data
#print axioms LeanUrat.MovesT.rootOnly_childless_rejected
#print axioms LeanUrat.MovesT.no_childless_vacuity
#print axioms LeanUrat.MovesT.cellOf_nonconstant
#print axioms LeanUrat.MovesT.toyχ_injective
#print axioms LeanUrat.MovesT.eligible_nonvacuity_toy
#print axioms LeanUrat.MovesT.constFalse_childCover_false
#print axioms LeanUrat.MovesT.constFalse_no_cellAssign
#print axioms LeanUrat.MovesT.vdict_cell_of_child_cell
#print axioms LeanUrat.MovesT.henPayload_cell
#print axioms LeanUrat.MovesT.cellLevel_local_sound
#print axioms LeanUrat.MovesT.capEnvelope_cellLocal_holds
#print axioms LeanUrat.MovesT.d4rcyl_canonical
#print axioms LeanUrat.MovesT.cfw_canonical
#print axioms LeanUrat.MovesT.mem_foldr_union
#print axioms LeanUrat.MovesT.exists_of_mem_foldr_union
#print axioms LeanUrat.MovesT.level_lt_npband
#print axioms LeanUrat.MovesT.mem_bandLevels
#print axioms LeanUrat.MovesT.bandLevels_mem_elim
#print axioms LeanUrat.MovesT.npband_eq_sup_bandLevels
#print axioms LeanUrat.MovesT.np_id_sub
#print axioms LeanUrat.MovesT.np_id
#print axioms LeanUrat.MovesT.np_id_pin
#print axioms LeanUrat.MovesT.vtree_pathOrder
#print axioms LeanUrat.MovesT.is
#print axioms LeanUrat.MovesT.nsNull_of_pricing_growth
#print axioms LeanUrat.MovesT.vtree_ext_eq
#print axioms LeanUrat.MovesT.shapeClass_finite
#print axioms LeanUrat.MovesT.AofTr_shape_const
#print axioms LeanUrat.MovesT.perShape_law
#print axioms LeanUrat.MovesT.treeN
#print axioms LeanUrat.MovesT.treeN_stable
#print axioms LeanUrat.MovesT.treeN_stable_stmt
#print axioms LeanUrat.MovesT.treeN_ns
#print axioms LeanUrat.MovesT.tgt_finadd
#print axioms LeanUrat.MovesT.jcRoot_partition
#print axioms LeanUrat.MovesT.jcRoot_card
#print axioms LeanUrat.MovesT.jc_single
#print axioms LeanUrat.MovesT.jcMulti_branching
#print axioms LeanUrat.MovesT.rootSplit_exists
#print axioms LeanUrat.MovesT.fiber_root_split
#print axioms LeanUrat.MovesT.spectator_conditional_mass
#print axioms LeanUrat.MovesT.fiber_seg_step
#print axioms LeanUrat.MovesT.presents_imply_jcMultiAt
#print axioms LeanUrat.MovesT.fiber_first_split
#print axioms LeanUrat.MovesT.shared_split_state_forced
#print axioms LeanUrat.MovesT.shared_split_siteExp_forced
#print axioms LeanUrat.MovesT.f1_two_leaf_discharge
#print axioms LeanUrat.MovesT.shared_read_forces
#print axioms LeanUrat.MovesT.parentSt_of_deep
#print axioms LeanUrat.MovesT.treeExp
#print axioms LeanUrat.MovesT.tree_fiber_disjoint
#print axioms LeanUrat.MovesT.history_ext
#print axioms LeanUrat.MovesT.mem_of_prefix
#print axioms LeanUrat.MovesT.preHalt_prunedMem
#print axioms LeanUrat.MovesT.oneF
#print axioms LeanUrat.MovesT.preHalt_dict_ptwise
#print axioms LeanUrat.MovesT.vtree_eq_of_fiberAt
#print axioms LeanUrat.MovesT.preHalt_dict_sum
#print axioms LeanUrat.MovesT.belowHalt_decomp
#print axioms LeanUrat.MovesT.belowHalt_empty_shape
#print axioms LeanUrat.MovesT.belowHalt_excess
#print axioms LeanUrat.MovesT.toyStage_card
#print axioms LeanUrat.MovesT.toyK_two_eq_zero
#print axioms LeanUrat.MovesT.toyK_two_poly
#print axioms LeanUrat.MovesT.toyK_X_sub_C
#print axioms LeanUrat.MovesT.toyK_add_sq
#print axioms LeanUrat.MovesT.toyK_head_ord
#print axioms LeanUrat.MovesT.toyK_leaf_ord
#print axioms LeanUrat.MovesT.toyHead_root
#print axioms LeanUrat.MovesT.toyLeafA_nonroot
#print axioms LeanUrat.MovesT.toyLeafB_nonroot
#print axioms LeanUrat.MovesT.toy_gate
#print axioms LeanUrat.MovesT.toy_sib
#print axioms LeanUrat.MovesT.toy_vdict_nonconstant
#print axioms LeanUrat.MovesT.toy_fiber_ne
#print axioms LeanUrat.MovesT.toy_e5_instance
#print axioms LeanUrat.MovesT.toy_henflip_unrealizable
#print axioms LeanUrat.MovesT.toy_jcmulti_site
#print axioms LeanUrat.MovesT.toy_state_cell
#print axioms LeanUrat.MovesT.toy_v8_wchain
#print axioms LeanUrat.MovesT.toyStage3_card
#print axioms LeanUrat.MovesT.toyK3_three_eq_zero
#print axioms LeanUrat.MovesT.toyK3_three_poly
#print axioms LeanUrat.MovesT.toyK3_two_ne_zero
#print axioms LeanUrat.MovesT.toyPat3_root
#print axioms LeanUrat.MovesT.toy_v8_monic
#print axioms LeanUrat.MovesT.toy_oneF
#print axioms LeanUrat.MovesT.toy_belowHalt_pos
#print axioms LeanUrat.MovesT.sibCount_pair_form
#print axioms LeanUrat.MovesT.sibNode2_species
#print axioms LeanUrat.MovesT.sibNode2_root
#print axioms LeanUrat.MovesT.toyHead_ne_sibNode2
#print axioms LeanUrat.MovesT.t1_nodes
#print axioms LeanUrat.MovesT.t2_nodes
#print axioms LeanUrat.MovesT.t1_ne_t2
#print axioms LeanUrat.MovesT.canonRoot_toyHead
#print axioms LeanUrat.MovesT.canonRoot_sibNode2
#print axioms LeanUrat.MovesT.laws_t1
#print axioms LeanUrat.MovesT.laws_t2
#print axioms LeanUrat.MovesT.contfib_set
#print axioms LeanUrat.MovesT.sib_falsifier
#print axioms LeanUrat.MovesT.sib_root_instance
#print axioms LeanUrat.MovesT.vd_deg_hen
#print axioms LeanUrat.MovesT.vd_deg_ns
#print axioms LeanUrat.MovesT.accEF_keyDeg
#print axioms LeanUrat.MovesT.sat_iff_W1
#print axioms LeanUrat.MovesT.sat_iff_selNone
#print axioms LeanUrat.MovesT.tau_disjoint
#print axioms LeanUrat.MovesT.tau_total
#print axioms LeanUrat.MovesT.vdAt_nontrivial
#print axioms LeanUrat.MovesT.shapeOfH_matches
#print axioms LeanUrat.MovesT.acc_pos
#print axioms LeanUrat.MovesT.readOf_guards_dead
#print axioms LeanUrat.MovesT.acc_childWidth
#print axioms LeanUrat.MovesT.irr_iff_mu_one
