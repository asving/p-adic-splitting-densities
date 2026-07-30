import LeanUrat.HC1.C1_LST
import LeanUrat.HC1.C2_TYPa
import LeanUrat.HC1.C3_TYPb
import LeanUrat.HC1.C4_DOM
import LeanUrat.HC1.C5_typToClause
import LeanUrat.HC1.C6_alphabetCard
import LeanUrat.HC1.D1_carryRing
import LeanUrat.HC1.D2_carryGrading
import LeanUrat.HC1.D3_carryDomain
import LeanUrat.HC1.D4_carryAdjoinRoot
import LeanUrat.HC1.D5_carryE1
import LeanUrat.HC1.D6_carryHomogUnits
import LeanUrat.HC1.D7_digD_mul
import LeanUrat.HC1.D8_digD_recenter
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.DefsD
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.DefsTower
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.G1_divGate
import LeanUrat.HC1.G2_carryGate
import LeanUrat.HC1.G3_caseJGate
import LeanUrat.HC1.G4_caseKGate
import LeanUrat.HC1.G5_spanGate
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.R1_LSTStmt
import LeanUrat.HC1.R2_TYPStmt
import LeanUrat.HC1.R3_DOMStmt
import LeanUrat.HC1.R4_SecB1Stmt
import LeanUrat.HC1.R5_EQ2Pass
import LeanUrat.HC1.R6_carrierInstance
import LeanUrat.HC1.S10_recStage
import LeanUrat.HC1.S11_towerSpine
import LeanUrat.HC1.S11a_coreTransport
import LeanUrat.HC1.S12_iaugPersist
import LeanUrat.HC1.S13_realPersist
import LeanUrat.HC1.S14_wellTypedAnchor
import LeanUrat.HC1.S15_anchoredSubst
import LeanUrat.HC1.S16_levelLanding
import LeanUrat.HC1.S17_levelMeasureExact
import LeanUrat.HC1.S1_transHypGate
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.HC1.S4_childSubmult
import LeanUrat.HC1.S5_childValuation
import LeanUrat.HC1.S6_childS4field
import LeanUrat.HC1.S7_childPin
import LeanUrat.HC1.S8_childS6
import LeanUrat.HC1.S9_transStage
import LeanUrat.HC1.S9a_stageLiteral
import LeanUrat.HC1.S9b_childWeightSet
import LeanUrat.HC1.S9c_coreAssembly
import LeanUrat.HC1.S9d_pinVerify
import LeanUrat.HC1.S9r_childR
import LeanUrat.HC1.S9w_residualLaws
import LeanUrat.HC1.ScratchC6
import LeanUrat.HC1.ScratchS17
import LeanUrat.HC1.ScratchT10
import LeanUrat.HC1.T10_floorStaircase
import LeanUrat.HC1.T11_attainDichotomy
import LeanUrat.HC1.T12_coordFin
import LeanUrat.HC1.T1_baseStage
import LeanUrat.HC1.T2_baseGate
import LeanUrat.HC1.T3_htChainWeight
import LeanUrat.HC1.T4_slotMinHt
import LeanUrat.HC1.T5_levelSetInGamma
import LeanUrat.HC1.T6_carrierLaws
import LeanUrat.HC1.T7_alphabetSpan
import LeanUrat.HC1.T8_alphabetStep
import LeanUrat.HC1.T9_blockDisjoint
import LeanUrat.HC1.V10_transportWindow
import LeanUrat.HC1.V1_readWPack
import LeanUrat.HC1.V2_readResidual
import LeanUrat.HC1.V3_readLift
import LeanUrat.HC1.V4_readLanding
import LeanUrat.HC1.V6_alignedOrbits
import LeanUrat.HC1.V7_stripDischarge
import LeanUrat.HC1.V8_childResidual
import LeanUrat.HC1.V9_K1nonrec

#print axioms LeanUrat.HC1.C1_LST
#print axioms LeanUrat.HC1.C2_TYPa
#print axioms LeanUrat.HC1.C3_TYPb
#print axioms LeanUrat.HC1.C4_DOM
#print axioms LeanUrat.HC1.C5_typToClause
#print axioms LeanUrat.HC1.C6_alphabetCard
#print axioms LeanUrat.HC1.C6_attain_automatic
#print axioms LeanUrat.HC1.C6_cardK_bridge
#print axioms LeanUrat.HC1.C6_conjunct1_closable
#print axioms LeanUrat.HC1.C6_conjunct2_rhs_always
#print axioms LeanUrat.HC1.C6_conjunct3_hyp_false
#print axioms LeanUrat.HC1.C6_forces_unconditional_fullness
#print axioms LeanUrat.HC1.D1_carryRing
#print axioms LeanUrat.HC1.D2_carryGrading
#print axioms LeanUrat.HC1.D3_carryDomain
#print axioms LeanUrat.HC1.D4_carryAdjoinRoot
#print axioms LeanUrat.HC1.D5_carryE1
#print axioms LeanUrat.HC1.D6_carryHomogUnits
#print axioms LeanUrat.HC1.D7_digD_mul
#print axioms LeanUrat.HC1.D8_digD_recenter
#print axioms LeanUrat.HC1.G1_divGate
#print axioms LeanUrat.HC1.G2_carryGate
#print axioms LeanUrat.HC1.G3_caseJGate
#print axioms LeanUrat.HC1.G4_caseKGate_i
#print axioms LeanUrat.HC1.G4_caseKGate_ii
#print axioms LeanUrat.HC1.G5_spanGate
#print axioms LeanUrat.HC1.K1_coeffLocC_of_pin
#print axioms LeanUrat.HC1.K1_frameVertexDigit
#print axioms LeanUrat.HC1.K1_tvecUnitLaw_of_pin
#print axioms LeanUrat.HC1.R6_carrierInstance
#print axioms LeanUrat.HC1.S10_recStage
#print axioms LeanUrat.HC1.S11_towerSpine
#print axioms LeanUrat.HC1.S11a_coreTransport
#print axioms LeanUrat.HC1.S12_iaugPersist
#print axioms LeanUrat.HC1.S13_realPersist
#print axioms LeanUrat.HC1.S14_wellTypedAnchor
#print axioms LeanUrat.HC1.S15_anchoredSubst
#print axioms LeanUrat.HC1.S16_levelLanding
#print axioms LeanUrat.HC1.S17_levelMeasureExact
#print axioms LeanUrat.HC1.S17_scratch_with_hcore_hzsol
#print axioms LeanUrat.HC1.S1_transHypGate_a
#print axioms LeanUrat.HC1.S1_transHypGate_b
#print axioms LeanUrat.HC1.S2_childW
#print axioms LeanUrat.HC1.S3_childK1
#print axioms LeanUrat.HC1.S4_childSubmult
#print axioms LeanUrat.HC1.S5_childValuation
#print axioms LeanUrat.HC1.S6_childS4field
#print axioms LeanUrat.HC1.S7_childPin
#print axioms LeanUrat.HC1.S8_childS6
#print axioms LeanUrat.HC1.S9_transStage
#print axioms LeanUrat.HC1.S9_ungated_corner_refuted
#print axioms LeanUrat.HC1.S9a_corner_fails_guard
#print axioms LeanUrat.HC1.S9a_stageLiteral
#print axioms LeanUrat.HC1.S9a_ungated_corner_refuted
#print axioms LeanUrat.HC1.S9b_childWeightSet
#print axioms LeanUrat.HC1.S9b_ungated_corner_refuted
#print axioms LeanUrat.HC1.S9c_coreAssembly
#print axioms LeanUrat.HC1.S9c_ungated_corner_refuted
#print axioms LeanUrat.HC1.S9d_pinVerify
#print axioms LeanUrat.HC1.S9d_stageCoreL
#print axioms LeanUrat.HC1.S9r_childR
#print axioms LeanUrat.HC1.S9w_residualLaws
#print axioms LeanUrat.HC1.T10_conjunct2_refuted
#print axioms LeanUrat.HC1.T10_floorStaircase
#print axioms LeanUrat.HC1.T11_attainDichotomy
#print axioms LeanUrat.HC1.T12_coordFin
#print axioms LeanUrat.HC1.T1_baseStage
#print axioms LeanUrat.HC1.T2_baseGate
#print axioms LeanUrat.HC1.T3_htChainWeight
#print axioms LeanUrat.HC1.T4_slotMinHt
#print axioms LeanUrat.HC1.T5_levelSetInGamma
#print axioms LeanUrat.HC1.T6_carrierLaws
#print axioms LeanUrat.HC1.T7_alphabetSpan
#print axioms LeanUrat.HC1.T8_alphabetStep
#print axioms LeanUrat.HC1.T9_blockDisjoint
#print axioms LeanUrat.HC1.Tower.side_w
#print axioms LeanUrat.HC1.V10_forcedKeyWeight
#print axioms LeanUrat.HC1.V10_readTransition_incompatible
#print axioms LeanUrat.HC1.V10_transportWindow
#print axioms LeanUrat.HC1.V1_readWPack
#print axioms LeanUrat.HC1.V2_readFrame
#print axioms LeanUrat.HC1.V2_readResidual
#print axioms LeanUrat.HC1.V3_equalWeights_lift
#print axioms LeanUrat.HC1.V3_readLift
#print axioms LeanUrat.HC1.V4_readLanding
#print axioms LeanUrat.HC1.V6_descentOrbits
#print axioms LeanUrat.HC1.V6_regradeOrbits
#print axioms LeanUrat.HC1.V7_stripDischarge
#print axioms LeanUrat.HC1.V8_childResidual
#print axioms LeanUrat.HC1.V8_digitUnit
#print axioms LeanUrat.HC1.V8_eval
#print axioms LeanUrat.HC1.V8_tiedPos_inj
#print axioms LeanUrat.HC1.V8a_carrierAdditive
#print axioms LeanUrat.HC1.V8b_carrierLaws
#print axioms LeanUrat.HC1.V8c_wStrict
#print axioms LeanUrat.HC1.V9_E1box_nonrec
#print axioms LeanUrat.HC1.V9_K1nonrec
#print axioms LeanUrat.HC1.V9_bottomSlot_of_wvEqStretch
#print axioms LeanUrat.HC1.V9_readPair
#print axioms LeanUrat.HC1.V9_readSteepness
#print axioms LeanUrat.HC1.V9_steepSide_frameDescent
#print axioms LeanUrat.HC1.V9_transSteepness
#print axioms LeanUrat.HC1.V9_wvEqStretch_of_bottomSlot
#print axioms LeanUrat.HC1.V9_wvGeStretch
#print axioms LeanUrat.HC1.VertexPin.to_child_dig_frame
#print axioms LeanUrat.HC1.childR_laws
#print axioms LeanUrat.HC1.levelSet_finite
