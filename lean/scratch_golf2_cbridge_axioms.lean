-- Scratch (golf pass 2, chunk ClassifierBridge*): axiom-footprint capture.
-- Run: lake env lean scratch_golf2_cbridge_axioms.lean
import LeanUrat.OM.ClassifierBridge
import LeanUrat.OM.ClassifierBridgeFiber
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.ClassifierBridgeChildful

-- theorems whose proof bodies the golf touches
#print axioms LeanUrat.OM.ClassifierBridgeFiber.menuPath_single_side
#print axioms LeanUrat.OM.ClassifierBridgeFiber.npVertices_eq_selfloop
#print axioms LeanUrat.OM.ClassifierBridgeFiber.rootResidual_eq_residualOf
#print axioms LeanUrat.OM.ClassifierBridgeFiber.classify_eq_selfloop_of_inCell
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.rootSide_eq_of_classify
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.chord_validLine_backward
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.rootResidual_natDegree_eq_of_classify
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.polyShape_residual_of_classify
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R
#print axioms LeanUrat.OM.ClassifierBridgeChildful.classify_eq_childful_iff

-- untouched capstones of the four modules (regression guard)
#print axioms LeanUrat.OM.ClassifierBridge.omCount_selfloop_eq_oneSideShape
#print axioms LeanUrat.OM.ClassifierBridge.stratumCount_selfloop
#print axioms LeanUrat.OM.ClassifierBridge.hnode_selfloop_over_Bclassify
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.classify_eq_selfloop_iff
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.stratumCount_selfloop_R
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.montes_order1_selfloop_density
#print axioms LeanUrat.OM.ClassifierBridgeChildful.classify_eq_childful_of_inCell
#print axioms LeanUrat.OM.ClassifierBridgeChildful.omCount_TselfloopChildful_eq
#print axioms LeanUrat.OM.ClassifierBridgeChildful.stratumCount_childful_R
