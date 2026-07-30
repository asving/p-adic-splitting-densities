import LeanUrat.MovesD.D0a_topLocus
import LeanUrat.MovesD.D0b_thmCtop
import LeanUrat.MovesD.D0c_fiberPos
import LeanUrat.MovesD.D10_sumLaw
import LeanUrat.MovesD.D11a_multSum
import LeanUrat.MovesD.D11b_eventMult
import LeanUrat.MovesD.D12_evBound
import LeanUrat.MovesD.D13_evIff
import LeanUrat.MovesD.D14a_emptyShape
import LeanUrat.MovesD.D14b_emptyPref
import LeanUrat.MovesD.D14c_emptyEvent
import LeanUrat.MovesD.D1c_encCard
import LeanUrat.MovesD.D2a_finite
import LeanUrat.MovesD.D3a_poolBound
import LeanUrat.MovesD.D3b_corD4R2
import LeanUrat.MovesD.D4R4all_wrapper
import LeanUrat.MovesD.D4a_chartBij
import LeanUrat.MovesD.D4b_chartCount
import LeanUrat.MovesD.D5a_dwidthPos
import LeanUrat.MovesD.D5b_lineShape
import LeanUrat.MovesD.D6a_strShape
import LeanUrat.MovesD.D6b_kappaShape
import LeanUrat.MovesD.D6c_innerslotShape
import LeanUrat.MovesD.D6d_htShape
import LeanUrat.MovesD.D6e_prevRimShape
import LeanUrat.MovesD.D7a_staircaseShape
import LeanUrat.MovesD.D7b_floorShape
import LeanUrat.MovesD.D7c_slotValShape
import LeanUrat.MovesD.D8_bandShape
import LeanUrat.MovesD.D9_L9
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.E10_towerCard
import LeanUrat.MovesD.E1_digitPool
import LeanUrat.MovesD.E2_poolCard
import LeanUrat.MovesD.E3_frameField
import LeanUrat.MovesD.E4_ranchDeg
import LeanUrat.MovesD.E5_gmuLe
import LeanUrat.MovesD.E6_eligibleCard
import LeanUrat.MovesD.E7_rankLt
import LeanUrat.MovesD.E8_rankInj
import LeanUrat.MovesD.E9_encInj
import LeanUrat.MovesD.F1_enum
import LeanUrat.MovesD.F2_absCount
import LeanUrat.MovesD.F3_emptyBridge
import LeanUrat.MovesD.G1_gates
import LeanUrat.MovesD.G2_gatesClassifier
import LeanUrat.MovesD.L9s_Astable
import LeanUrat.MovesD.NPu_threshold
import LeanUrat.MovesD.NPv_npid
import LeanUrat.MovesD.PolPin
import LeanUrat.MovesD.SW1_shapeWF
import LeanUrat.MovesD.SW2_scaleCoherence
import LeanUrat.MovesD.T1a_prefixClosed
import LeanUrat.MovesD.W1_wellformed
import LeanUrat.MovesD.W2_MfacLe
import LeanUrat.MovesD.W3_coarseBound

open LeanUrat.MovesD in
#print axioms LeanUrat.MovesD.A'_nil
#print axioms LeanUrat.MovesD.A_stable
#print axioms LeanUrat.MovesD.CD_canonical
#print axioms LeanUrat.MovesD.CD_correspondence
#print axioms LeanUrat.MovesD.CD_eq
#print axioms LeanUrat.MovesD.D4R1_EV
#print axioms LeanUrat.MovesD.D4R1_EV_iff
#print axioms LeanUrat.MovesD.D4R1_SUM
#print axioms LeanUrat.MovesD.D4R2'
#print axioms LeanUrat.MovesD.D4R2'_full
#print axioms LeanUrat.MovesD.D4R2_cor
#print axioms LeanUrat.MovesD.D4R4_all
#print axioms LeanUrat.MovesD.D4R4_all_noteRange
#print axioms LeanUrat.MovesD.D4R4_emptyPref
#print axioms LeanUrat.MovesD.Dwidth_pos
#print axioms LeanUrat.MovesD.EtaGalEq.refl
#print axioms LeanUrat.MovesD.EtaGalEq.symm
#print axioms LeanUrat.MovesD.EtaGalEq.trans
#print axioms LeanUrat.MovesD.L9_A
#print axioms LeanUrat.MovesD.Mfac_le
#print axioms LeanUrat.MovesD.NP_eq_noteNP
#print axioms LeanUrat.MovesD.NP_le_Nshape
#print axioms LeanUrat.MovesD.NP_le_of_noteNP_le
#print axioms LeanUrat.MovesD.NP_pos
#print axioms LeanUrat.MovesD.NP_stab
#print axioms LeanUrat.MovesD.OffsetPPin.lift_center_realizer
#print axioms LeanUrat.MovesD.OffsetPPin.lift_ne_zero
#print axioms LeanUrat.MovesD.OffsetPPin.no_pin_of_wrong_value
#print axioms LeanUrat.MovesD.OffsetPPin.no_pin_of_wrong_weight
#print axioms LeanUrat.MovesD.OffsetPPin.not_realizes_bare_ne_zero
#print axioms LeanUrat.MovesD.Phat0_A'
#print axioms LeanUrat.MovesD.Phat0_wf
#print axioms LeanUrat.MovesD.PhatStar_A'
#print axioms LeanUrat.MovesD.PhatStar_Mfac
#print axioms LeanUrat.MovesD.PhatStar_NPband
#print axioms LeanUrat.MovesD.PhatStar_Nshape
#print axioms LeanUrat.MovesD.PhatStar_W
#print axioms LeanUrat.MovesD.PhatStar_wf
#print axioms LeanUrat.MovesD.PrefOpt_empty
#print axioms LeanUrat.MovesD.PrefOpt_nonempty
#print axioms LeanUrat.MovesD.Pref_empty_shape
#print axioms LeanUrat.MovesD.Presented.event_empty_shape
#print axioms LeanUrat.MovesD.Presented.event_of_ne
#print axioms LeanUrat.MovesD.Presented.mult_empty_shape
#print axioms LeanUrat.MovesD.Presented.mult_of_ne
#print axioms LeanUrat.MovesD.Ranch_deg
#print axioms LeanUrat.MovesD.Shape.mbar_pos
#print axioms LeanUrat.MovesD.ShapeWF_of_matches
#print axioms LeanUrat.MovesD.TW_threshold_witness
#print axioms LeanUrat.MovesD.advII_not_wf
#print axioms LeanUrat.MovesD.advI_not_wf
#print axioms LeanUrat.MovesD.advVI_not_wf
#print axioms LeanUrat.MovesD.band_lt_Nshape
#print axioms LeanUrat.MovesD.band_shape
#print axioms LeanUrat.MovesD.card_classes
#print axioms LeanUrat.MovesD.card_classes_abs
#print axioms LeanUrat.MovesD.chart_bij
#print axioms LeanUrat.MovesD.chart_count
#print axioms LeanUrat.MovesD.digit_in_pool
#print axioms LeanUrat.MovesD.eligible_card_le
#print axioms LeanUrat.MovesD.emptyShape_law
#print axioms LeanUrat.MovesD.encIdx_inj
#print axioms LeanUrat.MovesD.encTargetP_card
#print axioms LeanUrat.MovesD.encTargetP_empty
#print axioms LeanUrat.MovesD.etaData_reprOf
#print axioms LeanUrat.MovesD.event_empty_law
#print axioms LeanUrat.MovesD.event_iff_mult
#print axioms LeanUrat.MovesD.event_mult_empty_shape
#print axioms LeanUrat.MovesD.fiber_pos
#print axioms LeanUrat.MovesD.fieldTower_card
#print axioms LeanUrat.MovesD.floorH_shape
#print axioms LeanUrat.MovesD.frameField_eq_pool
#print axioms LeanUrat.MovesD.gamTie_stage_form
#print axioms LeanUrat.MovesD.gmu_le_len
#print axioms LeanUrat.MovesD.htH_shape
#print axioms LeanUrat.MovesD.innerslot_shape
#print axioms LeanUrat.MovesD.kappaH_shape
#print axioms LeanUrat.MovesD.lineS_at_jstar
#print axioms LeanUrat.MovesD.line_shape
#print axioms LeanUrat.MovesD.mult_sum
#print axioms LeanUrat.MovesD.mult_sum_opt
#print axioms LeanUrat.MovesD.noteNP_le_iff
#print axioms LeanUrat.MovesD.pool_card_le
#print axioms LeanUrat.MovesD.prefSet_subset_any
#print axioms LeanUrat.MovesD.prevRim_shape
#print axioms LeanUrat.MovesD.rank_inj
#print axioms LeanUrat.MovesD.reprOf_mem
#print axioms LeanUrat.MovesD.selRank_lt
#print axioms LeanUrat.MovesD.slotVal_shape
#print axioms LeanUrat.MovesD.staircase_shape
#print axioms LeanUrat.MovesD.strFrame_shape
#print axioms LeanUrat.MovesD.thmC_top
#print axioms LeanUrat.MovesD.topLocus_admissible
#print axioms LeanUrat.MovesD.topLocus_numPinned
#print axioms LeanUrat.MovesD.topLocus_sol
#print axioms LeanUrat.MovesD.totalPins_top
#print axioms LeanUrat.MovesD.tree_prefix_closed
#print axioms LeanUrat.MovesD.tree_root_of_mem
#print axioms LeanUrat.MovesD.wellformed_of_wf
