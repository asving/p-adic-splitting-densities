import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.Moves.L0_GRa
import LeanUrat.Moves.L0_GRb
import LeanUrat.Moves.L0_GRc
import LeanUrat.Moves.L0_GRd
import LeanUrat.Moves.L0_GRe
import LeanUrat.Moves.L0_GRf
import LeanUrat.Moves.L0_GRg
import LeanUrat.Moves.L1_baseResidual_R4
import LeanUrat.Moves.L1_baseWeight_R3
import LeanUrat.Moves.L1_gaussVal
import LeanUrat.Moves.L2_P6i_R5_final
import LeanUrat.Moves.L2_P6ii_R3
import LeanUrat.Moves.L2_anchorCong
import LeanUrat.Moves.L2_iaugRecenter
import LeanUrat.Moves.L2_iaugRoot
import LeanUrat.Moves.L2_iaugStep
import LeanUrat.Moves.L2_keyResidualPow
import LeanUrat.Moves.L2_psiNotDvd_R3
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L3_K1
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L3_liftExists
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.L3_liftWeight
import LeanUrat.Moves.L4_TRANSi_R3
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSiii_R3
import LeanUrat.Moves.L4_TRANSiv
import LeanUrat.Moves.L4_TRANSv_R3
import LeanUrat.Moves.L4_TRANSvii_R4
import LeanUrat.Moves.L4_TRANSviii_a_R5_final
import LeanUrat.Moves.L4_TRANSviii_b_R4
import LeanUrat.Moves.L4_TRANSviii_c_R1
import LeanUrat.Moves.L5_landBox
import LeanUrat.Moves.L5_landTransport_R4
import LeanUrat.Moves.L5_landTwoSided_repair
import LeanUrat.Moves.L5_landVertex
import LeanUrat.Moves.L5_landVertexDigit_repair
import LeanUrat.Moves.L5_realCofin_R3
import LeanUrat.Moves.L5_realConclusion
import LeanUrat.Moves.L5_realDomination_R3
import LeanUrat.Moves.L5_realRecursion_R3
import LeanUrat.Moves.L5_recLiftIndep_R4
import LeanUrat.Moves.L5_recRSland_R4
import LeanUrat.Moves.L5_recSpecies_R4
import LeanUrat.Moves.L5_recSubst_R4
import LeanUrat.Moves.L5_recVV_R4
import LeanUrat.Moves.L6_ledgerCount
import LeanUrat.Moves.L6_measureExact_R4
import LeanUrat.Moves.L6_moveAffineBij
import LeanUrat.Moves.L6_moveReduceCommute_R4

#print axioms LeanUrat.Moves.Stage.le_nextField  -- Defs.lean
#print axioms LeanUrat.Moves.Stage.grRes_mul_T_neg  -- DefsL.lean
#print axioms LeanUrat.Moves.L0_FactA_exists  -- L0_FactA_exists.lean
#print axioms LeanUrat.Moves.L0_FactB_unique  -- L0_FactB_unique.lean
#print axioms LeanUrat.Moves.L0_GRa  -- L0_GRa.lean
#print axioms LeanUrat.Moves.L0_GRb  -- L0_GRb.lean
#print axioms LeanUrat.Moves.L0_GRc  -- L0_GRc.lean
#print axioms L0_GRd  -- L0_GRd.lean
#print axioms LeanUrat.Moves.L0_GRe  -- L0_GRe.lean
#print axioms LeanUrat.Moves.L0_GRf  -- L0_GRf.lean
#print axioms LeanUrat.Moves.L0_GRg  -- L0_GRg.lean
#print axioms LeanUrat.Moves.L1_baseResidual_laws  -- L1_baseResidual_R4.lean
#print axioms LeanUrat.Moves.L1_baseWeight_valuation  -- L1_baseWeight_R3.lean
#print axioms LeanUrat.Moves.L1_gaussVal_mul  -- L1_gaussVal.lean
#print axioms LeanUrat.Moves.L2_P6i  -- L2_P6i_R5_final.lean
#print axioms LeanUrat.Moves.L2_P6ii  -- L2_P6ii_R3.lean
#print axioms LeanUrat.Moves.L2_anchorCong  -- L2_anchorCong.lean
#print axioms LeanUrat.Moves.L2_iaugRecenter  -- L2_iaugRecenter.lean
#print axioms LeanUrat.Moves.L2_iaugRoot  -- L2_iaugRoot.lean
#print axioms LeanUrat.Moves.L2_iaugStep  -- L2_iaugStep.lean
#print axioms LeanUrat.Moves.L2_keyResidualPow  -- L2_keyResidualPow.lean
#print axioms LeanUrat.Moves.L2_psiNotDvd  -- L2_psiNotDvd_R3.lean
#print axioms LeanUrat.Moves.L2_slotDecomp  -- L2_slotDecomp_R4.lean
#print axioms LeanUrat.Moves.L2_strideRule  -- L2_strideRule.lean
#print axioms LeanUrat.Moves.L2_widthBound  -- L2_widthBound.lean
#print axioms LeanUrat.Moves.L3_DIV  -- L3_DIV.lean
#print axioms LeanUrat.Moves.L3_K1  -- L3_K1.lean
#print axioms LeanUrat.Moves.L3_digPrime_nonzero  -- L3_digPrime_nonzero.lean
#print axioms LeanUrat.Moves.L3_liftExists  -- L3_liftExists.lean
#print axioms LeanUrat.Moves.L3_liftMonic  -- L3_liftMonic.lean
#print axioms LeanUrat.Moves.L3_liftResidual  -- L3_liftResidual.lean
#print axioms LeanUrat.Moves.L3_liftWeight  -- L3_liftWeight.lean
#print axioms LeanUrat.Moves.TRANSi_ge_core  -- L4_TRANSi_R3.lean
#print axioms LeanUrat.Moves.L4_TRANSi  -- L4_TRANSi_R3.lean
#print axioms LeanUrat.Moves.L4_TRANSii  -- L4_TRANSii.lean
#print axioms LeanUrat.Moves.TRANSiii_le_core  -- L4_TRANSiii_R3.lean
#print axioms LeanUrat.Moves.L4_TRANSiii  -- L4_TRANSiii_R3.lean
#print axioms LeanUrat.Moves.L4_TRANSiv  -- L4_TRANSiv.lean
#print axioms LeanUrat.Moves.L4_TRANSv  -- L4_TRANSv_R3.lean
#print axioms LeanUrat.Moves.L4_TRANSvii  -- L4_TRANSvii_R4.lean
#print axioms LeanUrat.Moves.L4_TRANSviii_a  -- L4_TRANSviii_a_R5_final.lean
#print axioms LeanUrat.Moves.L4_TRANSviii_b  -- L4_TRANSviii_b_R4.lean
#print axioms LeanUrat.Moves.L4_TRANSviii_c  -- L4_TRANSviii_c_R1.lean
#print axioms LeanUrat.Moves.L5_landBox  -- L5_landBox.lean
#print axioms LeanUrat.Moves.L5_landTransport  -- L5_landTransport_R4.lean
#print axioms LeanUrat.Moves.L5_landTwoSided  -- L5_landTwoSided_repair.lean
#print axioms LeanUrat.Moves.L5_landVertex  -- L5_landVertex.lean
#print axioms LeanUrat.Moves.L5_landVertexDigit  -- L5_landVertexDigit_repair.lean
#print axioms LeanUrat.Moves.L5_realCofin  -- L5_realCofin_R3.lean
#print axioms LeanUrat.Moves.L5_realConclusion  -- L5_realConclusion.lean
#print axioms LeanUrat.Moves.L5_realDomination  -- L5_realDomination_R3.lean
#print axioms LeanUrat.Moves.L5_realRecursion  -- L5_realRecursion_R3.lean
#print axioms LeanUrat.Moves.L5_recLiftIndep  -- L5_recLiftIndep_R4.lean
#print axioms LeanUrat.Moves.L5_recRSland  -- L5_recRSland_R4.lean
#print axioms LeanUrat.Moves.L5_recSpecies  -- L5_recSpecies_R4.lean
#print axioms LeanUrat.Moves.L5_recSubst  -- L5_recSubst_R4.lean
#print axioms LeanUrat.Moves.L5_recVV  -- L5_recVV_R4.lean
#print axioms LeanUrat.Moves.L6_ledgerCount  -- L6_ledgerCount.lean
#print axioms LeanUrat.Moves.L6_measureExact  -- L6_measureExact_R4.lean
#print axioms LeanUrat.Moves.L6_moveAffineBij  -- L6_moveAffineBij.lean
#print axioms LeanUrat.Moves.L6_moveReduceCommute  -- L6_moveReduceCommute_R4.lean
