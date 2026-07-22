import LeanUrat
import LeanUrat.OM.RealInstance
import LeanUrat.OM.Order0Capstone
import LeanUrat.OM.Necklace
import LeanUrat.OM.Order0Alpha
import LeanUrat.OM.Order0RealDensity
import LeanUrat.OM.Development
import LeanUrat.OM.LinearFiber
import LeanUrat.OM.HenselCount
import LeanUrat.OM.SparseResultant
import LeanUrat.OM.FineCellResultant
import LeanUrat.OM.RphiRing
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.CellMenu
import LeanUrat.OM.CellCard
import LeanUrat.OM.RestartEquiv
import LeanUrat.OM.BlockProduct
import LeanUrat.OM.GradedHensel
import LeanUrat.OM.HNode1
import LeanUrat.OM.Drainage
import LeanUrat.OM.SelfLoopTower
import LeanUrat.OM.GradedCertificates
import LeanUrat.OM.ProductTheorem
import LeanUrat.OM.RphiRingGenH
import LeanUrat.OM.RphiGenHCount
import LeanUrat.OM.RestartEquivGenH
import LeanUrat.OM.FDescentCensus
import LeanUrat.OM.UnramifiedBase
import LeanUrat.OM.TowerRestartGenH
import LeanUrat.OM.TowerBase
import LeanUrat.OM.TowerRestartAbstract
import LeanUrat.OM.DevelopTower
import LeanUrat.OM.MontesAllOrders
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.SelfLoopIterate
import LeanUrat.OM.DecidedOrder1
import LeanUrat.OM.DecidedOmCountTie
import LeanUrat.OM.ShapeCountTie
import LeanUrat.OM.PathShape
import LeanUrat.OM.ClassifierBridge
import LeanUrat.OM.PathShapeChildful
import LeanUrat.OM.ClassifierBridgeFiber
import LeanUrat.OM.PathShapeMultiSide
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.PathShapeMultiSideTree
import LeanUrat.OM.ClassifierBridgeChildful
import LeanUrat.OM.ClassifierBridgeMultiSide
import LeanUrat.OM.ClassifierBridgeMultiSide2
import LeanUrat.OM.SelfLoopCensusK
import LeanUrat.OM.SelfLoopCensusFiltration
import LeanUrat.OM.SelfLoopCensusVerdict
import LeanUrat.OM.SelfLoopDensityConnect
import LeanUrat.OM.SelfLoopFixpoint
import LeanUrat.OM.SelfLoopFixpointGeneralMu
import LeanUrat.OM.ConditionalDensity
import LeanUrat.OM.TameRealDensity
import LeanUrat.MontesV2
import LeanUrat.OM.RealInstanceV2Prep
import LeanUrat.OM.RealInstanceV2
import LeanUrat.OM.RealInstanceV2Gates
import LeanUrat.OM.WildMenu
import LeanUrat.OM.WildMenuPrep
import LeanUrat.OM.RealInstanceW
import LeanUrat.OM.RealInstanceWGates
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeEisenstein
import LeanUrat.OM.WildMenuW3
import LeanUrat.OM.RealInstanceW3
import LeanUrat.OM.RealInstanceW3Gates
import LeanUrat.OM.QpTypeH3
import LeanUrat.OM.MultiSlopeMenu
import LeanUrat.OM.RealInstanceW4
import LeanUrat.OM.RealInstanceW4Gates
import LeanUrat.OM.QpTypeMixed
import LeanUrat.OM.ChainMenu
import LeanUrat.OM.RealInstanceW5
import LeanUrat.OM.RealInstanceW5Gates
open LeanUrat

-- Capstones
#print axioms LeanUrat.Goal.goal_theorem
#print axioms LeanUrat.clusterVolume_rational
-- (U1 fix 2026-07-02) the global `tame_functionalEquation` axiom is DELETED (it was FALSE-AS-STATED
-- over a free `F`); the tame input is the hypothesis `TameFunctionalEquation`.
-- (W4a 2026-07-21) the concrete named cite `M9.realDensity_tame_functionalEquation` and the old
-- vacuous capstone `M9.montes_unconditional` are RETIRED (their census entries removed here) —
-- superseded by the V2 chain, whose capstones now carry the canonical names (see the M9 REBASE V2
-- block below and `quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`).
-- (W4b 2026-07-21) the old-`MontesData` Goal bridge `Goal.goal_theorem_montes` /
-- `Goal.goal_theorem_via_montes` is RETIRED to `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`
-- (entries removed here); the canonical names now live on the V2 spine —
-- `MontesV2.goal_theorem_montes` / `MontesV2.goal_theorem_via_montes`, censused in the M9 REBASE V2
-- block below.
#print axioms LeanUrat.Witness.trivF_tame
-- Phase-A order-0 capstone + supporting machinery (2026-07-02)
#print axioms LeanUrat.OM.Order0.montes_order0
-- ★ the UNCONDITIONAL Phase-A capstone (h_node0 discharged, 2026-07-03) — MUST be core-only:
#print axioms LeanUrat.OM.Order0.montes_order0_unconditional
#print axioms LeanUrat.OM.Order0.h_node0_proved
-- ★ NON-VACUITY (V1 reversal, 2026-07-12): the genuine order-0 capstone's certified density is
--   STRICTLY POSITIVE for a concrete (inert n=2) type — the machine-checked A8.1 acceptance gate.
--   MUST be core-only:
#print axioms LeanUrat.OM.Order0.gate_rootCount_inert2
#print axioms LeanUrat.OM.Order0.montes_order0_certified_value_pos
#print axioms LeanUrat.OM.Order0.classify_eq_sepShape_iff
#print axioms LeanUrat.OM.Order0.rootCount_isRational_of_leaf
#print axioms LeanUrat.OM.Order0.cellsOfShapeWF_sepShape
#print axioms LeanUrat.OM.Necklace.dvd_necklaceSum
#print axioms LeanUrat.OM.Necklace.necklaceSum_nonneg
#print axioms LeanUrat.OM.Necklace.necklaceQ_eq_natCast
-- F-A: the φ-adic development bijection (RESTART_LEMMA §1 / Lemma A at level N; 2026-07-03)
#print axioms LeanUrat.OM.Development.developEquiv
#print axioms LeanUrat.OM.Development.develop_unique
#print axioms LeanUrat.OM.Development.developEquiv_card_consistency
-- F-B1: linear fiber count over ZMod(p^N) (RESTART_LEMMA §8 Master Lemma, linear model; 2026-07-04)
#print axioms LeanUrat.OM.LinearFiber.card_ker_mulVec_of_det
#print axioms LeanUrat.OM.LinearFiber.fiber_card
#print axioms LeanUrat.OM.LinearFiber.image_index
#print axioms LeanUrat.OM.LinearFiber.mulVec_fiber_card_of_det
#print axioms LeanUrat.OM.LinearFiber.mulVec_bijective_iff_isUnit_det
#print axioms LeanUrat.OM.LinearFiber.card_range_mul_pow
#print axioms LeanUrat.OM.LinearFiber.card_ker_mul_pow
-- F-B2/F-B3: quantitative level-N Hensel with fiber count (Master Lemma count form; 2026-07-04)
#print axioms LeanUrat.OM.HenselCount.sylvesterMulVec_eq
#print axioms LeanUrat.OM.HenselCount.resultant_stable
#print axioms LeanUrat.OM.HenselCount.fiber_card
#print axioms LeanUrat.OM.HenselCount.image_card
-- F-B4: sparse/twist resultant closed forms + dominant-transversal det (2026-07-04)
#print axioms LeanUrat.OM.SparseResultant.resultant_expand
#print axioms LeanUrat.OM.SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal
#print axioms LeanUrat.OM.SparseResultant.resultant_sparseTwist
#print axioms LeanUrat.OM.SparseResultant.resultant_sparseTwist_isUnit
#print axioms LeanUrat.OM.SparseResultant.resultant_sparseTwist_cross
-- ★ WILD-MATH FORMALIZATION Phase 1 (#56, 2026-07-13): fine-cell resultant-valuation constancy — the
--   deep-wild block-factorization exponent is a genuine CONSTANT lattice integer from Newton data (the
--   piece GAP1_RESIDUAL/MASTER_LEMMA closed at math level; now core-only Lean). NEW-1: v(Res Gi Gj) =
--   ∏ v(θi−θj) over root pairs (abstract Valuation; Monic+Splits, via mathlib resultant_eq_prod_roots_sub).
--   NEW-2: zmodValuation of the sparse-twist resultant = the fixed exponent di·dj·e·h (same/cross side),
--   below-cutoff hypothesis honest. Shrinks AX_cellRecursion toward exactly the (unformalizable) Haar CoV.
#print axioms LeanUrat.OM.FineCellResultant.vResultant_eq_prod_roots_sub
#print axioms LeanUrat.OM.FineCellResultant.vResultant_eq_prod_cross_pairs
#print axioms LeanUrat.OM.FineCellResultant.finecell_vResultant_const
#print axioms LeanUrat.OM.FineCellResultant.finecell_vResultant_const_cross
-- Phase-B W1: the level-N avatar of O_L (RphiRing; 2026-07-04)
#print axioms LeanUrat.OM.RphiRing.card_Rphi
#print axioms LeanUrat.OM.RphiRing.digitEquiv
#print axioms LeanUrat.OM.RphiRing.card_span_theta_pow
#print axioms LeanUrat.OM.RphiRing.card_residueField
#print axioms LeanUrat.OM.RphiRing.isUnit_iff_vphi_eq_zero
-- R1 / Layer C: the corrected per-node counting recursion (PIN §1.2 + R0 errata; 2026-07-04)
#print axioms LeanUrat.OM.OMCountV2.omCount_sepShape_eq_rootCount
#print axioms LeanUrat.OM.OMCountV2.omCount_isRational
#print axioms LeanUrat.OM.OMCountV2.omDensityV2_isRational
#print axioms LeanUrat.OM.OMCountV2.isRationalFn_compQpow
#print axioms LeanUrat.OM.OMCountV2.omCount_eq_mul
-- W2: the order-1 menu classifier (cellMenu shared with Layer C; W0-ground-truthed; 2026-07-04)
#print axioms LeanUrat.OM.CellMenu.cell_unique
#print axioms LeanUrat.OM.CellMenu.cell_exists
#print axioms LeanUrat.OM.CellMenu.classify1_eq_some_iff
#print axioms LeanUrat.OM.CellMenu.classify1_eq_none_of_tail
#print axioms LeanUrat.OM.CellMenu.residual_endpoint_units
-- W4a/W4b: the per-cell counting identity (partition + closed form, W0-census-gated; 2026-07-04)
#print axioms LeanUrat.OM.CellCard.cell_partition
#print axioms LeanUrat.OM.CellCard.cell_card_raw
#print axioms LeanUrat.OM.CellCard.cell_card_mCell
-- KEYSTONE (2026-07-07): the GENERAL shapeCount = choicePoly count identity. CRUX (multiplicativity
-- over degrees) FULLY closed; general tie REDUCED to the single-degree count `hSingle` (blueprint #2,
-- the one remaining obligation). Gate-confirmed true (35 cases). Discharges cell_card_mCell's hties.
#print axioms LeanUrat.OM.ShapeCountTie.shapeCount_eq_card
#print axioms LeanUrat.OM.ShapeCountTie.card_shapeSet_prod
#print axioms LeanUrat.OM.ShapeCountTie.choicePoly_eval_prod
#print axioms LeanUrat.OM.ShapeCountTie.shapeCount_tie_general_of_singleDegree
-- KEYSTONE CLOSED (2026-07-07): single_degree_count discharges hSingle ⟹ shapeCount_tie_general is
-- UNCONDITIONAL ⟹ cell_card_mCell_uncond = the per-cell census with NO hties hypothesis. The count
-- multinomial built via DomMulAct.stabilizer_card' (∏c_μ!) + Fintype.card_embedding_eq (descFactorial).
#print axioms LeanUrat.OM.ShapeCountTie.single_degree_count
#print axioms LeanUrat.OM.ShapeCountTie.shapeCount_tie_general
#print axioms LeanUrat.OM.ShapeCountTie.cell_card_mCell_uncond
-- S3 FIRST INCREMENT (2026-07-07): the engine↔classifier bridge. oneSideShape = the (s,pr,shape)→
-- ClusterShape constructor (one cell PER FACTOR), and configsOf_oneSideShape = [mkCell s [pr.1,pr.2]
-- [shape]] for single-side childless (all-μ=1) shapes — configOf of the engine shape reproduces the
-- classifier's mkCell field-for-field. First step of the S3 classifier→shape map. Multi-side diverges
-- (configOf aggregates faces; deferred). Adversarially verified sound (RHS genuine, not weakened/vacuous).
#print axioms LeanUrat.OM.PathShape.cellsOfShapeWF_oneSideShape
#print axioms LeanUrat.OM.PathShape.configsOf_oneSideShape
-- CLOSED FORM (2026-07-07): omCount(oneSideShape s pr shape) = shapeCount·p^{-(newtonExponent(mkPoly)+
-- sideDeg)} — the engine value of the constructor family in closed form, tied to the count keystone via
-- the bridge. The p^{run} in volExp (=Σceil+sideDeg) is the difference between ROOT omCount and the
-- cluster-conditional density (hnode_decided_order1): omCount(oneSideShape S2C1)=1/8=cluster(1/2)·p^{-run}.
#print axioms LeanUrat.OM.PathShape.omCount_oneSideShape_closed
-- FIRST GENUINE CLUSTER-SHAPE h_node (2026-07-07): mkCell_volExp_add_freeExp = the exponent identity
-- volExp(mkCell s P sh) + freeExp s N P = s*N (Newton-constrained + free digits fill the s×N box;
-- span=s telescoped via chainOK_run_sum). hnode_oneSideShape = stratumCount1(mkCell s P [shape])/p^{sN}
-- → omCount(oneSideShape s pr shape) for single-side childless shapes — the genuine stratum density of a
-- sloped order-1 cluster shape ties to the engine omCount, natural p^{sN} box, real limit. S2C1 → 1/8.
#print axioms LeanUrat.OM.PathShape.mkCell_volExp_add_freeExp
#print axioms LeanUrat.OM.PathShape.hnode_oneSideShape
-- S3 BRIDGE (2026-07-08): connects the order-1 single-side h_node to the REAL density (B.classify).
-- KEY: omCount is configsOf-agnostic to the tree-head order slot, so omCount_selfloop_eq_oneSideShape
-- (Tselfloop's order-0-head literal = oneSideShape's value) is UNCONDITIONAL. stratumCount_selfloop +
-- hnode_selfloop_over_Bclassify are the h_node in EXACTLY montes_allorders_of_hnode's shape, CONDITIONAL
-- on the one named fiber-iff hfiber (classify_eq_selfloop_iff, documented open; needs a Newton-polygon
-- uniqueness lemma). 3/4 of the bridge; the S1 skeleton connection is now one lemma away.
#print axioms LeanUrat.OM.ClassifierBridge.omCount_selfloop_eq_oneSideShape
#print axioms LeanUrat.OM.ClassifierBridge.stratumCount_selfloop
#print axioms LeanUrat.OM.ClassifierBridge.hnode_selfloop_over_Bclassify
-- S3 CHILDFUL (2026-07-08): μ≥2 descent-child constructor + closed form + h_node, via the empty-payload
-- child collapse (restart NOT needed). FINDING: at a childful cell limit ≠ omCount (differ by ∏ pivot);
-- proved omCount_eq_limit_mul_pivot honestly, NOT a false limit=omCount. Pivot arg is p^D (base-changed).
#print axioms LeanUrat.OM.PathShapeChildful.omChildCount_childShape
#print axioms LeanUrat.OM.PathShapeChildful.cellsOfShapeWF_oneSideShapeChildful
#print axioms LeanUrat.OM.PathShapeChildful.omCount_oneSideShapeChildful_closed
#print axioms LeanUrat.OM.PathShapeChildful.hnode_oneSideShapeChildful
#print axioms LeanUrat.OM.PathShapeChildful.omCount_eq_limit_mul_pivot
-- S3 FIBER CHARACTERIZATION (2026-07-08): the HARDEST piece of the bridge landed. npVertices_eq_selfloop
-- = the Newton-polygon hull UNIQUENESS lemma (npVertices(boxValSupport f) = [(0,H),(n,0)] from InCell's
-- vertex-exactness + SideAbove — new convex geometry, no template). classify_eq_selfloop_of_inCell = the
-- FORWARD direction of the fiber iff (InCell f → B.classify f = Tselfloop). Respelled Tselfloop (toSideFace
-- polygon). OPEN: backward direction (2 small named lemmas) → full iff → hfiber discharge → unconditional
-- real-density h_node. Forward + hull uniqueness = ~80% of the deepest S3 obligation, scariest part done.
#print axioms LeanUrat.OM.ClassifierBridgeFiber.npVertices_eq_selfloop
#print axioms LeanUrat.OM.ClassifierBridgeFiber.rootSide_eq_of_inCell
#print axioms LeanUrat.OM.ClassifierBridgeFiber.rootResidual_eq_residualOf
#print axioms LeanUrat.OM.ClassifierBridgeFiber.classify_eq_selfloop_of_inCell
#print axioms LeanUrat.OM.ClassifierBridgeFiber.omCount_selfloop_eq_oneSideShape
-- S3 MULTI-SIDE (2026-07-08): all-μ=1 multi-side h_node. FINDING: flat per-side polygon OVER-COUNTS for
-- ≥2 sides, so sideCeilSum_sum (Σ truncated per-side col sums = newtonExponent(mkPoly s P), telescoped) is
-- the correct reconciliation. hnode_multiSideShape = stratumCount1(mkCell s P sh)/p^{sN} → multiSideValue
-- (per-side product). OPEN: tie multiSideValue to a single ClusterShape omCount (children-per-side) for omDensityV2.
#print axioms LeanUrat.OM.PathShapeMultiSide.sideCeilSum_sum
#print axioms LeanUrat.OM.PathShapeMultiSide.omCount_multiSide_closed
#print axioms LeanUrat.OM.PathShapeMultiSide.hnode_multiSideShape
-- ★★★ FIRST UNCONDITIONAL ORDER-1 DENSITY THEOREM (2026-07-08). Fiber bridge COMPLETE:
-- classify_eq_selfloop_iff (full both-direction fiber characterization: B.classify realP n N f =
-- Tselfloop ↔ InCell f (mkCell n P [shape]), single-side childless; backward via sideAbove_of_npVertices
-- + rootSide_eq_of_classify). hfiber DISCHARGED ⟹ hnode_selfloop_over_Bclassify_R UNCONDITIONAL. Then
-- montes_order1_selfloop_density = montes_allorders_of_hnode on {Tselfloop}: the REAL B.classify stratum
-- density of a genuine sloped order-1 cluster shape is a rational function of q + the count limit = it.
-- First density result beyond order 0, tied to the real density engine. Core-only.
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.rootSide_eq_of_classify
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.sideAbove_of_npVertices
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.classify_eq_selfloop_iff
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.stratumCount_selfloop_R
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R
#print axioms LeanUrat.OM.ClassifierBridgeFiber2.montes_order1_selfloop_density
-- MULTI-SIDE → omDensityV2 semantics (2026-07-08): the multi-side stratum density factors as a PRODUCT
-- of independent per-side omCounts (product-theorem structure; NOT a single omCount). sideSubShape =
-- oneSideShape at the per-side 0-based sub-scale. multiSideValue_eq_prod_omCount + hnode_multiSideProduct.
#print axioms LeanUrat.OM.PathShapeMultiSideTree.omCount_sideSubShape_eq_sideFactor
#print axioms LeanUrat.OM.PathShapeMultiSideTree.multiSideValue_eq_prod_omCount
#print axioms LeanUrat.OM.PathShapeMultiSideTree.hnode_multiSideProduct
#print axioms LeanUrat.OM.PathShapeMultiSideTree.prod_omCount_eq_blockCardinality
-- S3 CHILDFUL FIBER BRIDGE (2026-07-08, Round 2): classifyAux_of_single_descent (the one-descent OM
-- expansion, NEW), classify_eq_childful_iff (B.classify f = TselfloopChildful ↔ InCell f (mkCell), for
-- single-side DISTINCT-DEGREE ALL-childful μ≥2 shapes — honest added hyps: classifier sorts by degree,
-- μ=1 erases to childless). stratumCount_childful_R (pivot-free discharge). Childful DENSITY deferred:
-- omCount = limit·∏pivot, and the pivot = the deeper-order self-loop resummation (k-fold census, the
-- known-hard SelfLoopResum REMAINING_OBLIGATION) — the recurring bottleneck, Round 3 target.
#print axioms LeanUrat.OM.ClassifierBridgeChildful.classifyAux_of_single_descent
#print axioms LeanUrat.OM.ClassifierBridgeChildful.classify_eq_childful_iff
#print axioms LeanUrat.OM.ClassifierBridgeChildful.omCount_TselfloopChildful_eq
#print axioms LeanUrat.OM.ClassifierBridgeChildful.stratumCount_childful_R
-- S3 MULTI-SIDE FIBER BRIDGE (2026-07-08, Round 2): classify_multiSide_firstSide_projection (a
-- classify=Tselfloop node forces the single-side hull), inCell_multiSide_imp_classify_firstSide (multi-side
-- InCell is a strict refinement), + hnode/prod reexports. Multi-side DENSITY into omDensityV2 deferred:
-- needs the product-theorem fiber_node_identity (Round 3 target).
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide.classify_multiSide_firstSide_projection
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide.inCell_multiSide_imp_classify_firstSide
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide.hnode_multiSideProduct_reexport
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide.prod_omCount_eq_blockCardinality_reexport
-- S3 MULTI-SIDE DENSITY (2026-07-08, Round 3): omDensityMultiSide_stratum_product (UNCONDITIONAL) = the
-- multi-side order-1 stratum density in CLOSED RATIONAL form (= product of per-side omCounts), the multi-
-- side analogue of montes_order1_selfloop_density on the InCell/stratumCount1 locus (correct, since
-- B.classify reads only the first side). omDensityMultiSide_of_sides_of_image_eq (CONDITIONAL on the
-- ProductTheorem image-equality) + gate-cell instances proving it non-vacuous. Unconditional version
-- bottlenecks on the PRE-EXISTING named obligation_hensel_surjective (graded-Hensel margin W4d2').
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide2.omDensityMultiSide_stratum_product
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide2.omDensityMultiSide_of_sides_of_image_eq
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide2.gate_omDensityMultiSide_instance
#print axioms LeanUrat.OM.ClassifierBridgeMultiSide2.gate_omDensityMultiSide_fiberCard
-- ═══ RELABEL (2026-07-10 RECONCILIATION) ═══ The SelfLoopCensusK / SelfLoopCensusFiltration /
-- SelfLoopCensusVerdict modules below are AUXILIARY PREDICATE MACHINERY, *** NOT the self-loop density. ***
-- The reconciliation (verified 2 ways: original wild-prime MC N=1e7 om_oracle_check.json + the SelfLoopResum
-- re-gate) CONFIRMED the true self-loop density = 1/(1-r) = countPivot⁻¹ = omCount, and that the verdict-chain
-- census here is a once-per-box TRUNCATION (→ 1+r, the K=2 partial sum with the WRONG bare ratio q^{-(w+1)}
-- instead of the ×q-exposed q^{-w}). These theorems are SOUND (true about the verdict-chain object) but are
-- NOT density steps. The DENSITY-correct object is SelfLoopIterate.aggSelfLoopBoxTower → depth0·countPivot⁻¹
-- (already closed via SelfLoopResum.tendsto_aggSelfLoopTower); the sole remaining gap is REMAINING_STEP1
-- (connect aggSelfLoopBoxTower to stratumCount1 with the per-level ×q residue-branching). VerdictEquidist /
-- TrueCensusCovariance are FALSE for-all-k; contingent theorems on them are vacuous. DO NOT treat as density.
-- S3 SELF-LOOP CENSUS (2026-07-08). census_step_equiv/censusEquivQ = a predicate-generic per-level census
-- bijection (SOUND, core-only). ⚠ ROUND-5 CORRECTION: with the FIXED-cell selfLoopChain predicate here,
-- census_step_equiv is VACUOUS for k≥2 (the real self-loop-again cell DEEPENS its polygon path per level —
-- a0 valuation 2→4→…; at (2,5,2) level-1 read = cellB1 ≠ selfLoopCell 2, so selfLoopChain k is EMPTY for
-- k≥2). So this is NOT yet the meaningful census. census_base (depth-0 = RestartEquiv closed form) is genuine.
-- CORRECT target = a DEPTH-INDEXED chain predicate; the genuine OPEN lemma = verdict-conditioned coset
-- equidistribution (does the depth-k self-loop verdict cut each of the p^{s(s+1)/2} cosets to the same
-- slBoxRatio fraction). This is the recurring multi-round bottleneck (childful density / deeper resummation).
#print axioms LeanUrat.OM.SelfLoopCensusK.census_step_equiv
#print axioms LeanUrat.OM.SelfLoopCensusK.censusEquivQ
#print axioms LeanUrat.OM.SelfLoopCensusK.census_base
#print axioms LeanUrat.OM.SelfLoopCensusK.census_depth_one
#print axioms LeanUrat.OM.SelfLoopCensusK.selfLoopChain_succ
#print axioms LeanUrat.OM.SelfLoopCensusK.gate_census_base_2_5_2
-- S3 CENSUS, FILTRATION FRAME (2026-07-08, Round 6): the reframing RELOCATED the obstruction. The gapped-
-- digit filtration RESOLVES the a0-deepening (selfLoop_floor_ratio_uniform: per-level floor-coset index =
-- fixed p^(selfLoopExponent+1), level/N-independent — deepening confirmed a NON-issue). But it is residue-
-- BLIND: counts the FLOOR event (p^k|aᵢ), strictly larger than the self-loop VERDICT (residual repeated root
-- (y-c)^s). So the census DECOMPOSES: floor part DONE × verdict fraction. selfLoopCell_floor +
-- selfLoopChain_le_floorChain (verdict⟹floor containment); selfLoopCensus_filtration_step(_ratio) = the
-- per-level census step CONTINGENT on the ONE named residue lemma VerdictTranslationInvariant (the residual-
-- repeated-root verdict cuts every GammaPattern coset to the same fraction — a residualOf covariance under
-- coset translation, ZMod/Newton-polygon, NOT filtration-theoretic). This is the clean single remaining target.
#print axioms LeanUrat.OM.SelfLoopCensusFiltration.selfLoopCell_floor
#print axioms LeanUrat.OM.SelfLoopCensusFiltration.selfLoopChain_le_floorChain
#print axioms LeanUrat.OM.SelfLoopCensusFiltration.selfLoop_floor_ratio_uniform
#print axioms LeanUrat.OM.SelfLoopCensusFiltration.selfLoopCensus_filtration_step
#print axioms LeanUrat.OM.SelfLoopCensusFiltration.selfLoopCensus_filtration_step_ratio
-- S3 CENSUS ON THE VERDICT PREDICATE (2026-07-09, Round 7): the census is now on the CORRECT, NON-VACUOUS
-- object. selfLoopVerdict = residual repeated-root shape [(1,μ)] (cell-label-INDEPENDENT); selfLoopCell_
-- verdict + cellB1_verdict = both the fixed self-loop cell AND the deepened cellB1 feed the SAME verdict
-- (the widening that fixes the fixed-cell vacuity). ★ gate_verdict_nonvacuous_depth2_2_5_2 PROVES
-- verdictChain 2 inhabited at (2,5,2) — where selfLoopChain 2 was EMPTY (the mandatory anti-vacuity guard).
-- census_step_equiv_verdict = reduction reused verbatim (censusEquivQ predicate-generic). Census reduced to
-- VerdictEquidist (contingent step PROVED). FINDING: VerdictEquidist is DEPTH-NON-UNIFORM — the coset
-- covariance holds on the shallow self-loop side but FAILS on the deepened cellB1 side (gapped ⟨e,h⟩ h≥2:
-- recentering cannot reset scale). The equidistribution coset must deepen with the level.
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.selfLoopCell_verdict
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.cellB1_verdict
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.census_step_equiv_verdict
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.census_base_verdict
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.selfLoopCensusVerdict_step
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.gate_verdict_nonvacuous_depth2_2_5_2
#print axioms LeanUrat.OM.SelfLoopCensusVerdict.gate_census_base_verdict_2_5_2
-- ★ S3 SELF-LOOP DENSITY, CORRECT OBJECT (2026-07-10, re-aim): the genuine density connected to omCount.
-- stratumCount1_selfLoop_eq_fiber = the ACTUAL order-1 stratum count IS the FLOOR fiber (p-1)·p^{s(N-1)-
-- (selfLoopExp+1)} (NOT the retired verdict-chain object). stratumCount1_selfLoop_ratio/index = the per-level
-- FLOOR ratio slBoxRatio on the genuine count, uniform in N (REMAINING_STEP1 at k=1). floorAgg_eq_
-- aggSelfLoopBoxTower + hnode_selfloop_box_order1 = the full box h_node limit → depth0·countPivot⁻¹;
-- hnode_selfloop_box_child_q2 = omChildCount halfCluster 2 = 2/3 (ENGINE VALUE reached on the CORRECT object).
-- not_uniformCosetDensity_general = the honest refutation (VerdictEquidist ⟹ cluster_1≥32 vs brute 36 ⟹ FALSE).
-- Remaining: the general-k (k≥2) grouping of the ACTUAL stratumCount1 by self-loop depth (now on the floor object).
#print axioms LeanUrat.OM.SelfLoopDensityConnect.stratumCount1_selfLoop_eq_fiber
#print axioms LeanUrat.OM.SelfLoopDensityConnect.stratumCount1_selfLoop_index
#print axioms LeanUrat.OM.SelfLoopDensityConnect.stratumCount1_selfLoop_ratio
#print axioms LeanUrat.OM.SelfLoopDensityConnect.floorAgg_eq_aggSelfLoopBoxTower
#print axioms LeanUrat.OM.SelfLoopDensityConnect.hnode_selfloop_box_order1
#print axioms LeanUrat.OM.SelfLoopDensityConnect.hnode_selfloop_box_child_q2
#print axioms LeanUrat.OM.SelfLoopDensityConnect.not_uniformCosetDensity_general
-- ★★ S3 SELF-LOOP FIXPOINT (2026-07-10) — the CORRECT proof structure, found by numerically gating the
-- proof structure (Asvin's method), then formalized. The wild self-loop resummation is the FIXPOINT
-- b = depth0 + slExposedRatio·b (self-referential/restart), NOT the depth-decomposition (refuted).
-- selfLoopFixpoint_eq/_unique/_eq_limit: unique fixpoint = depth0·countPivot⁻¹ = the geometric tower.
-- selfLoopFixpoint_omChild_q2: = omChildCount halfCluster 2 = 2/3 (engine value). stratumCount1_seed_ratio:
-- the ACTUAL stratumCount1(selfLoopCell)/p^{s(N-1)} = (p-1)·slBoxRatio (k=1 seed on the genuine count, uniform
-- in N). ★ stratumCount1_hnode_fixpoint_q2: the ACTUAL box census → omChildCount = 2/3 at (2,2), genuinely
-- (NOT 1+r, NOT vacuous). Scope: μ=2 instance (μ≥3 EFFSEED unresolved — agents disagreed 16/31 vs 20/31);
-- general-k per-depth uniform identity still open but the fixpoint clarifies its role.
#print axioms LeanUrat.OM.SelfLoopFixpoint.selfLoopFixpoint_eq
#print axioms LeanUrat.OM.SelfLoopFixpoint.selfLoopFixpoint_unique
#print axioms LeanUrat.OM.SelfLoopFixpoint.selfLoopFixpoint_eq_limit
#print axioms LeanUrat.OM.SelfLoopFixpoint.selfLoopFixpoint_omChild_q2
#print axioms LeanUrat.OM.SelfLoopFixpoint.stratumCount1_seed_ratio
#print axioms LeanUrat.OM.SelfLoopFixpoint.stratumCount1_hnode_fixpoint_q2
#print axioms LeanUrat.OM.SelfLoopFixpoint.stratumCount1_hnode_fixpoint_q2_value
-- SelfLoopFixpointGeneralMu (#48): μ=3 SETTLED = 20/31 (three-way gated: engine anchor padic_types
-- monic_cubic_pred '1c' + PARI oracle om_oracle_check.json + fresh 800k MC z=−0.01; naive scalar 16/31
-- REJECTED at z=+241). The general-μ structure is a COUPLED-DIAGONAL system: diagonal block = scalar
-- self-loop fixpoint b_μ = EFFSEED_μ + slExposedRatio μ q · b_μ (banked general in μ,q,depth0 via
-- selfLoopFixpoint_general_closure/_value), cross-fed by the child descent (EFFSEED_μ assembled from
-- β_{μ'<μ}). ★ selfLoopFixpointValue_mu3_q2 = 20/31 (fixpoint algebra on the gated seed EFFSEED_3=5/8).
-- ★ omChildCount_shape3Half_q2 = 32/93: a GENUINE cross-fed size-3 omChildCount through the WF recursion
-- (child step → gate3_cluster_q2 = β_2 = 2/3, size-3 pivot 31/32) — the coupled-diagonal cross-feed on the
-- ACTUAL engine. HONEST GAPS (in docstring): (1) configOf emits ONE config/shape but EFFSEED_3 is a
-- TWO-config sum (q−1)/q+(q−1)/q³, so 20/31's seed is gated not engine-reconstructed; (2) general-μ
-- UNCONDITIONAL still needs the uniform-in-(N,k) per-depth census induction (SelfLoopResum item 2).
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.slExposedRatio_3_q2
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.countPivot_3_q2
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.EFFSEED3_q2
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.EFFSEED3_decomp
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.selfLoopFixpointValue_mu3_q2
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.selfLoopFixpoint_eq_mu3
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.selfLoopFixpoint_unique_mu3
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.selfLoopFixpoint_general_closure
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.selfLoopFixpoint_general_value
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.omChildCount_shape3Half_q2
#print axioms LeanUrat.OM.SelfLoopFixpointGeneralMu.omChildCount_shape3Half_crossfeed
-- ConditionalDensity (#49): the COMPLETE CONDITIONAL top-level theorem. density_eq_engine_conditional:
-- for any menu M + self-loop predicate, density = engine rational function, with the per-shape h_node
-- DISCHARGED unconditionally for non-self-loop shapes (hTame) and ASSUMED via the ONE honest AGGREGATE
-- hypothesis SelfLoopHNode (stratumCount/realP^nN → omCount on self-loop shapes; MC/PARI-true; NOT the
-- refuted per-depth FloorCensusPerDepth). density_eq_engine_tame: tame (p>n, no self-loop shape) is
-- FULLY UNCONDITIONAL (self-loop hyp discharged vacuously). hNodeLimit_unramified: separable h_node
-- unconditional from h_node0_proved. selfLoop_engine_is_fixpoint: the hyp target = general-μ fixpoint.
#print axioms LeanUrat.OM.ConditionalDensity.density_eq_engine_conditional
#print axioms LeanUrat.OM.ConditionalDensity.density_eq_engine_tame
#print axioms LeanUrat.OM.ConditionalDensity.hNodeLimit_unramified
#print axioms LeanUrat.OM.ConditionalDensity.selfLoop_engine_is_fixpoint
#print axioms LeanUrat.OM.CellCard.card_readableBox
#print axioms LeanUrat.OM.CellCard.consistency_s2
-- ★ W4d1: THE RESTART EQUIVALENCE at level N (RESTART_LEMMA §13.1 count form; 2026-07-04)
--   MUST be core-only — this is the project's central new lemma, machine-checked:
#print axioms LeanUrat.OM.RestartEquiv.restartEquiv
#print axioms LeanUrat.OM.RestartEquiv.inCellAt_iff_pattern
#print axioms LeanUrat.OM.RestartEquiv.card_restart_fiber
#print axioms LeanUrat.OM.RestartEquiv.card_freshPattern
#print axioms LeanUrat.OM.RestartEquiv.crosscheck_B
-- W4d2: the multi-block product law (flat-margin general form + gate instances; 2026-07-04)
#print axioms LeanUrat.OM.BlockProduct.pair_card
#print axioms LeanUrat.OM.BlockProduct.pair_card_pattern
#print axioms LeanUrat.OM.BlockProduct.blocks_card
#print axioms LeanUrat.OM.BlockProduct.mul_image_saturated
#print axioms LeanUrat.OM.BlockProduct.caseB_hres
#print axioms LeanUrat.OM.BlockProduct.gateB_law
-- W3a: B.8 discharged (via the decode degeneracy — see its honest docstring; 2026-07-04)
#print axioms LeanUrat.OM.B.classify_separable_leaf
-- ★ DE-STUB first genuine descent (#54, 2026-07-13): the classifier now reads f BELOW the root at the
--   first descent. childResidual = order-1 residual from the φ-adic development of f (genuinely
--   f-dependent, vs the Rr:=0 stub); classifyFirstDescent recurses via classifyAux on the f-built
--   fChildCtx; cells_fChildCtx_ne_nil = the non-vacuity witness (child produces genuine cells from f,
--   contrast cells_childCtxOfSize which is always []). Additive first increment of the de-stub; full
--   replacement blocked on (a) Fr-as-computable-field + (b) develop-reduction-stability (CERTLEVEL).
#print axioms LeanUrat.OM.B.clusterSize_fChildCtx
#print axioms LeanUrat.OM.B.classifyFirstDescent
#print axioms LeanUrat.OM.B.cells_fChildCtx_ne_nil
-- ★ DE-STUB blocker (b) proved standalone (#55, 2026-07-13): develop-reduction-stability.
--   Development.develop_map (develop commutes with Polynomial.map — general/reusable) →
--   B.childResidual_reduce_stable (childResidual stable under box-reduction of f below an honest
--   explicit per-digit cutoff hcut). This is the reduction-stability lemma the full de-stub needs to
--   restore the CERTLEVEL chain once classifyAux_indep becomes false. Blocker (a) [Fr-as-computable-
--   field] still remains for the full replacement.
#print axioms LeanUrat.OM.Development.develop_map
#print axioms LeanUrat.OM.B.childResidual_reduce_stable
-- ★ DE-STUB P1 additive increment (#57, 2026-07-14): the GENUINE multi-level f-reading classifier built
--   ALONGSIDE the stub (master green, additive; the CERTLEVEL-breaking swap is blueprinted for later in
--   notes/DESTUB_BLUEPRINT_2026-07-13.md). classifyGenuine/classifyGenuineAux descend reading f at EVERY
--   level via fChildCtx (Rr:=childResidual, Fr:=ZMod p; strict descent by ch.hChildSizeLt). Witnesses:
--   classifyGenuineAux_head_dr_pos (root tuple's dr-slot > 0 when residual deg>0 — distinguishes the genuine
--   reader from the f-blind stub AT THE ROOT TUPLE; NOT a tree.length≥2/"descent" claim, see docstring),
--   classifyGenuine_root_eq_classify (menu-correctness: agrees with the stub at the root, diverges only
--   below), treeSize_classifyGenuine (=n). All core-only.
#print axioms LeanUrat.OM.B.classifyGenuineAux_head_dr_pos
#print axioms LeanUrat.OM.B.classifyGenuine_root_eq_classify
#print axioms LeanUrat.OM.B.treeSize_classifyGenuine
-- ★ DE-STUB Ingredient B (#58, 2026-07-14): fChildCtx_reduce_stable — the genuine reader's per-node
--   CERTLEVEL content (child context stable under one-digit box reduction below the per-digit cutoff),
--   the multi-level analogue of fRootCtx_reduce_stable, consuming only banked childResidual_reduce_stable.
#print axioms LeanUrat.OM.B.fChildCtx_reduce_stable
-- W4d2′: the polygon-graded Hensel margin (holds at the real cells where flat margins fail; 2026-07-04)
#print axioms LeanUrat.OM.GradedHensel.graded_ker_bound
#print axioms LeanUrat.OM.GradedHensel.pair_card_graded
#print axioms LeanUrat.OM.GradedHensel.gate_margin_graded_B
#print axioms LeanUrat.OM.GradedHensel.caseB_law_graded
#print axioms LeanUrat.OM.GradedHensel.caseB_matches_gateB
#print axioms LeanUrat.OM.GradedHensel.blocks_card_graded
-- ★★ W4e: h_node1 — THE ORDER-1 RESTART IDENTITY, assembled (2026-07-04). MUST be core-only:
#print axioms LeanUrat.OM.HNode1.h_node1_single
#print axioms LeanUrat.OM.HNode1.h_node1_single_shape
#print axioms LeanUrat.OM.HNode1.h_node1_selfLoop
#print axioms LeanUrat.OM.HNode1.selfLoop_cost_tie
#print axioms LeanUrat.OM.HNode1.h_node1_census
#print axioms LeanUrat.OM.HNode1.h_node1_general
-- W5: order-1 drainage (exact undecided census + density identity; 2026-07-05)
#print axioms LeanUrat.OM.Drainage.card_tail
#print axioms LeanUrat.OM.Drainage.card_selfLoopFiber
#print axioms LeanUrat.OM.Drainage.card_undecided1
#print axioms LeanUrat.OM.Drainage.undecidedDensity_eq
#print axioms LeanUrat.OM.Drainage.tendsto_tailDensity_zero
-- W6-lite: the self-loop tower (two-level classification through the e=1 restart; 2026-07-05)
#print axioms LeanUrat.OM.SelfLoopTower.two_level_census
#print axioms LeanUrat.OM.SelfLoopTower.second_level_partition
#print axioms LeanUrat.OM.SelfLoopTower.read2_eq_none_iff
#print axioms LeanUrat.OM.SelfLoopTower.pattern_iso
#print axioms LeanUrat.OM.SelfLoopTower.gate_iterated_selfLoop
-- W4d2-surj (PARTIAL, named obligation): InCellMulti + the ⊇ containment; the classifier
-- multi-block fiber identity is hypothesis-gated on the theorem-of-product surjectivity (2026-07-05)
#print axioms LeanUrat.OM.CellMenu.inCellMulti_single
#print axioms LeanUrat.OM.ProductTheorem.imageSet_subset_concatCell
#print axioms LeanUrat.OM.ProductTheorem.cell_sideAbove
#print axioms LeanUrat.OM.ProductTheorem.fiber_node_identity_of_image_eq
#print axioms LeanUrat.OM.ProductTheorem.gate_fiber_B_card
-- W4d2-surj ⊇: residual multiplicativity CLOSED + vertex-exactness building blocks (2026-07-05)
#print axioms LeanUrat.OM.M4.residualPoly_mul
#print axioms LeanUrat.OM.ProductTheorem.residualOf_mul_of_conv
#print axioms LeanUrat.OM.ProductTheorem.zmodValuation_mul
#print axioms LeanUrat.OM.ProductTheorem.zmodUnitResidue_mul
-- The dominant-term valuation laws (crux of on_side_conv; scalar analogue of the transversal det; 2026-07-05)
#print axioms LeanUrat.OM.ProductTheorem.zmodValuation_sum_unique_min
#print axioms LeanUrat.OM.ProductTheorem.zmodUnitResidue_sum_common_min
-- Theorem-of-product refactor: P2 bridge (SidedBlock/cellOf) + engine wiring + ⊇ assembly (2026-07-05)
#print axioms LeanUrat.OM.ProductTheorem.cellOf_wf
#print axioms LeanUrat.OM.ProductTheorem.vertex_valuation_exact
#print axioms LeanUrat.OM.ProductTheorem.imageSet_subset_inCellMulti
#print axioms LeanUrat.OM.ProductTheorem.card_imageSet_le_fiber
-- on_side_conv CLOSED: the antidiagonal geometry facts + the wired convolution theorem (2026-07-06)
#print axioms LeanUrat.OM.ProductTheorem.coeff_mul_pow_factor
#print axioms LeanUrat.OM.ProductTheorem.antidiag_split_class
#print axioms LeanUrat.OM.ProductTheorem.on_side_conv_of_cofactor
-- R1/R2: shape multiplicativity (coprime) + SidedBlock on-side carriers + residual-shape leg (2026-07-06)
#print axioms LeanUrat.OM.CellMenu.polyShape_mul
#print axioms LeanUrat.OM.ProductTheorem.polyShape_residualOf_mul
#print axioms LeanUrat.OM.ProductTheorem.sideMatch_shape_mul
-- ⊇ CLOSED Matches-free for the gate cell shapes (1-block + 2-distinct-block; 2026-07-06)
#print axioms LeanUrat.OM.ProductTheorem.offBlock_unit_on_side
#print axioms LeanUrat.OM.ProductTheorem.product_matches_two_distinct
#print axioms LeanUrat.OM.ProductTheorem.imageSet_subset_inCellMulti_single_free
#print axioms LeanUrat.OM.ProductTheorem.imageSet_subset_inCellMulti_two_distinct_free
-- P3 cardinality route: independent fiber count + forcing → node identity (prodSC=1 cells; 2026-07-06)
#print axioms LeanUrat.OM.ProductTheorem.card_inCellMulti_fiber
#print axioms LeanUrat.OM.ProductTheorem.image_card_eq_pow_freeExp
#print axioms LeanUrat.OM.ProductTheorem.inCellMulti_eq_image
#print axioms LeanUrat.OM.ProductTheorem.gate_node_A
#print axioms LeanUrat.OM.ProductTheorem.gate_node_B
-- prodSC>1 fixed-pin: case C node identity CLOSED outright (all 3 gate cells now closed; 2026-07-06)
#print axioms LeanUrat.OM.ProductTheorem.cell_card_raw_fixed_single
#print axioms LeanUrat.OM.ProductTheorem.card_inCellMulti_fixedpin_fiber_single
#print axioms LeanUrat.OM.ProductTheorem.card_inCellMulti_fixedpin_caseC
#print axioms LeanUrat.OM.ProductTheorem.gate_node_C_closed
-- k-block ⊇ fold: Matches-free products-in-cell for general k (multi-side, distinct slopes; 2026-07-06)
#print axioms LeanUrat.OM.ProductTheorem.product_matches_klist
#print axioms LeanUrat.OM.ProductTheorem.imageSet_subset_inCellMulti_klist_free
#print axioms LeanUrat.OM.ProductTheorem.card_imageSet_le_fiber_klist
#print axioms LeanUrat.OM.ProductTheorem.product_matches_klist_k3
-- theorem-of-product completion: same-side-sibling ⊇ + multi-side fixed-pin node identity (2026-07-06)
#print axioms LeanUrat.OM.ProductTheorem.product_matches_sameside
#print axioms LeanUrat.OM.ProductTheorem.imageSet_subset_inCellMulti_sameside_free
#print axioms LeanUrat.OM.ProductTheorem.card_inCellMulti_fixedpin_multiside
#print axioms LeanUrat.OM.ProductTheorem.node_identity_fixedpin_multiside
-- ProductTheorem concretization: case-A multi-side node identity OUTRIGHT (2026-07-07)
#print axioms LeanUrat.OM.ProductTheorem.card_inCellMulti_fixedpin_caseA
#print axioms LeanUrat.OM.ProductTheorem.gate_node_A_multiside_closed
-- W6a: general-h RphiRing filtration (corrected: gapped ⟨e,h⟩ semigroup, span{θ,p}; 2026-07-06)
#print axioms LeanUrat.OM.RphiRingGenH.isLocalRing
#print axioms LeanUrat.OM.RphiRingGenH.maximalIdeal_eq_span_theta_p
#print axioms LeanUrat.OM.RphiRingGenH.card_residueField
#print axioms LeanUrat.OM.RphiRingGenH.vL_eq_vphi_of_h_one
-- W6a-residual: gapped per-digit product count (GENERAL e) + exact vL anchors (2026-07-06)
#print axioms LeanUrat.OM.RphiGenHCount.vL_theta_eq
#print axioms LeanUrat.OM.RphiGenHCount.vL_natCast_p_eq
#print axioms LeanUrat.OM.RphiGenHCount.card_filtIdeal
#print axioms LeanUrat.OM.RphiGenHCount.card_filtIdeal_h_one_collapse
-- ★ W6b-h: THE GENERAL-h single-block restart equivalence (referee-gap lemma at arbitrary slope; 2026-07-06)
#print axioms LeanUrat.OM.RestartEquivGenH.restartEquivGenH
#print axioms LeanUrat.OM.RestartEquivGenH.inCellAtGenH_iff_pattern
#print axioms LeanUrat.OM.RestartEquivGenH.card_restartGenH_fiber
#print axioms LeanUrat.OM.RestartEquivGenH.card_restartGenH_fiber_h_one_collapse
#print axioms LeanUrat.OM.RestartEquivGenH.gate_H
-- W6c-2: order-2 two-level restart census at general (e,h); order-r skeleton (deep recursion; 2026-07-06)
#print axioms LeanUrat.OM.TowerRestartGenH.two_level_census_genH
#print axioms LeanUrat.OM.TowerRestartGenH.card_two_level_genH
#print axioms LeanUrat.OM.TowerRestartGenH.card_two_level_genH_h_one_collapse
#print axioms LeanUrat.OM.TowerRestartGenH.gate_DG_order2_compounded_W13
-- ★ TowerBase: order-r coefficient-ring abstraction — the deep-recursion infra (2026-07-06)
#print axioms LeanUrat.OM.TowerBase.card_filtIdeal_gen
#print axioms LeanUrat.OM.TowerBase.instTowerBase_RphiGenH
#print axioms LeanUrat.OM.instTowerBase_ZMod
#print axioms LeanUrat.OM.instTowerBase_level1
#print axioms LeanUrat.OM.reduction_gate_2323_N5
-- ★★ Deliverable 5: abstract restart over [TowerBase R] + r_level_census card recursion + O'' instance
--    (count-native restart CLOSED at all orders; f≥2 subsumed via O''-as-TowerBase; 2026-07-07):
#print axioms LeanUrat.OM.TowerRestartAbstract.restartEquivAbstract
#print axioms LeanUrat.OM.TowerRestartAbstract.card_restartAbstract_fiber
#print axioms LeanUrat.OM.TowerRestartAbstract.card_freshPatternAbstract_ZMod_eq_perdigit
#print axioms LeanUrat.OM.TowerRestartAbstract.card_freshPatternAbstract_child
#print axioms LeanUrat.OM.TowerRestartAbstract.gate_reduce_H
#print axioms LeanUrat.OM.TowerRestartAbstract.instTowerBase_Oring
-- ★★★ D4d: the order-r restart EQUIVALENCE recursion — the count-native restart CLOSED at all orders
--     (genuine ≃, all (e,h), f≥2 subsumed via O''; developEquiv found base-general; 2026-07-07):
#print axioms LeanUrat.OM.DevelopTower.developTower
#print axioms LeanUrat.OM.DevelopTower.restartEquivTower
#print axioms LeanUrat.OM.DevelopTower.card_restartTower_fiber
#print axioms LeanUrat.OM.DevelopTower.r_level_census_equiv
#print axioms LeanUrat.OM.DevelopTower.card_r_level_census
#print axioms LeanUrat.OM.DevelopTower.gate_Oring_restart_card
-- S1: the all-orders assembly SKELETON (density from node-limit, arbitrary menu + omCount; 2026-07-07)
#print axioms LeanUrat.OM.MontesAllOrders.montes_allorders_of_hnode
#print axioms LeanUrat.OM.MontesAllOrders.montes_allorders_of_hnode_specializes
-- S2(i): genuine order-1 stratum count over classify1, bridged to CellCard + the order-1 partition (2026-07-07)
#print axioms LeanUrat.OM.StratumOrder1.stratumCount1_eq_cellCard
#print axioms LeanUrat.OM.StratumOrder1.stratumCount1_eq_closed
#print axioms LeanUrat.OM.StratumOrder1.stratumCount1_partition
-- S2 crux: the ×q self-loop resummation → countPivot (general s,q; the box-vs-M_e fix; 2026-07-07)
#print axioms LeanUrat.OM.SelfLoopResum.xqMultiplicity
#print axioms LeanUrat.OM.SelfLoopResum.aggSelfLoopTower_closed
#print axioms LeanUrat.OM.SelfLoopResum.tendsto_aggSelfLoopTower
#print axioms LeanUrat.OM.SelfLoopResum.countPivot_eq_one_sub_slExposedRatio
#print axioms LeanUrat.OM.SelfLoopResum.resum_omCount_root_q2
-- S2(iii)+(vi): k-fold self-loop census + the ORDER-1 self-loop h_node LIMIT (mass level, general s,q; 2026-07-07)
#print axioms LeanUrat.OM.SelfLoopIterate.boxMass_xq
#print axioms LeanUrat.OM.SelfLoopIterate.aggSelfLoopBoxTower_eq
#print axioms LeanUrat.OM.SelfLoopIterate.hnode_selfloop_order1
#print axioms LeanUrat.OM.SelfLoopIterate.hnode_selfloop_limit_child_q2
-- Order-1 DECIDED-shape h_node (h_node0 analogue; limit = explicit constant = W0 count; 2026-07-07)
#print axioms LeanUrat.OM.DecidedOrder1.stratumCount1_decided_density
#print axioms LeanUrat.OM.DecidedOrder1.hnode_decided_order1
#print axioms LeanUrat.OM.DecidedOrder1.gate_density_S2C1
-- Order-1 DECIDED omCount TIE + first order-1 engine ClusterShape literal decidedTc (2026-07-07):
-- childless-collapse eval (all orders), the T_c literal, tie at gate (S2C1/S3C1 → omCount = 1/2),
-- and the FIRST order-1 h_node fully tied to omCount OUTRIGHT (decided cell). General decided tie
-- needs the named mCell=prodSC-at-realP bridge.
#print axioms LeanUrat.OM.DecidedOmCountTie.omCount_childless_eval
#print axioms LeanUrat.OM.DecidedOmCountTie.omCount_childless_single
#print axioms LeanUrat.OM.DecidedOmCountTie.configsOf_decidedTc
#print axioms LeanUrat.OM.DecidedOmCountTie.configOf_decidedTc_childless
#print axioms LeanUrat.OM.DecidedOmCountTie.mCell_decidedConfig
#print axioms LeanUrat.OM.DecidedOmCountTie.volExp_decidedConfig
#print axioms LeanUrat.OM.DecidedOmCountTie.omCount_decidedTc
#print axioms LeanUrat.OM.DecidedOmCountTie.decided_omCount_tie_S2C1
#print axioms LeanUrat.OM.DecidedOmCountTie.decided_omCount_tie_S3C1
#print axioms LeanUrat.OM.DecidedOmCountTie.hnode_decided_order1_omCount_S2C1
-- W6b-f (census tier): f≥2 residual/child census = f=1 census at q^f (GaloisField tower; 2026-07-06)
#print axioms LeanUrat.OM.FDescentCensus.galoisField_card_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.residualCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.shapeCensus_f_eq_q_pow_f
#print axioms LeanUrat.OM.FDescentCensus.conjugateBlock_orbit_count
-- W6b-f2 infra: level-N unramified base ring O'' (ungapped p-filtration, residue GaloisField p m; 2026-07-06)
#print axioms LeanUrat.OM.UnramifiedBase.card_Oring_pow
#print axioms LeanUrat.OM.UnramifiedBase.isLocalRing
#print axioms LeanUrat.OM.UnramifiedBase.maximalIdeal_eq
#print axioms LeanUrat.OM.UnramifiedBase.card_residueField
#print axioms LeanUrat.OM.UnramifiedBase.card_span_p_pow
-- A/C certificates: h_node1_general fully discharged at all three gate cells (2026-07-05)
#print axioms LeanUrat.OM.GradedCertificates.caseA_law_graded
#print axioms LeanUrat.OM.GradedCertificates.caseA_matches_gateA
#print axioms LeanUrat.OM.GradedCertificates.h_node1_at_A
#print axioms LeanUrat.OM.GradedCertificates.caseC_law_graded
#print axioms LeanUrat.OM.GradedCertificates.caseC_matches_gateC
#print axioms LeanUrat.OM.GradedCertificates.h_node1_at_C
-- Decomposition / counting path — RETIRED (W4b 2026-07-21): the old-`MontesData` spine
-- (`MontesAxiom.MontesData` + `Decomposition.lean`) is quarantined in
-- `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`; its five census entries
-- (`MontesData.coeff_isRational` / `countingDensity_isRational` / `countingDensity_eq_sum_coeff` /
-- `nodeMultiplicativity` / `undecidedVanishes`, all core-only) are removed here. The V2 siblings
-- (`MontesDataV2.countingDensity_eq_sum_coeff` / `countingDensity_isRational`) are censused
-- in-module (`LeanUrat/MontesV2.lean` AxCheck section); the goal-layer entries are in the
-- M9 REBASE V2 block below.
-- PadicMeasure capstone
#print axioms LeanUrat.PadicMeasure.clusterMeasure_isRational_of_AX
#print axioms LeanUrat.PadicMeasure.clusterMeasureModel_rec
#print axioms LeanUrat.PadicMeasure.T_BB3
#print axioms LeanUrat.PadicMeasure.residualCountFn_isRational
#print axioms LeanUrat.PadicMeasure.cellCoeff_isRational
#print axioms LeanUrat.PadicMeasure.bb1_isRational
#print axioms LeanUrat.PadicMeasure.omPivot_isRational
#print axioms LeanUrat.PadicMeasure.natCard_Fr
#print axioms LeanUrat.PadicMeasure.descend_children_of_factors
#print axioms LeanUrat.PadicMeasure.cell_stratum_of_residual
-- OMInduction / RatFn
#print axioms LeanUrat.OMInduction.clusterVol_isRational
#print axioms LeanUrat.RatFn.isRationalFn_listSum
#print axioms LeanUrat.RatFn.isRationalFn_div
#print axioms LeanUrat.RatFn.isRationalFn_qpow
-- L7
#print axioms LeanUrat.L7.isPalindromic_of_agree
#print axioms LeanUrat.L7.tame_to_all_primes
#print axioms LeanUrat.L7.ratfunc_agree_of_infinite
#print axioms LeanUrat.L7.eval_reflect_eq
-- L3 family
#print axioms LeanUrat.L3.card_monicDegree
#print axioms LeanUrat.L3.irreducible_separable
#print axioms LeanUrat.L3Squarefree.card_squarefreeMonicDegree
#print axioms LeanUrat.L3Gauss.gauss_necklace_count
#print axioms LeanUrat.L3Gauss.sum_e_mul_card_eq_pow
-- L4 / L5fix / L6M4 / M1 / R1
#print axioms LeanUrat.L4.cellVolume_eq
#print axioms LeanUrat.L4.cellVolume_pIndependent
#print axioms LeanUrat.L5fix.selfLoop_geometric
#print axioms LeanUrat.L6M4.density_rational
#print axioms LeanUrat.L6M4.sum_clusterVol_rational
#print axioms LeanUrat.M1.projPointCount_mul
#print axioms LeanUrat.M1.clusterLaw_baseChange
#print axioms LeanUrat.R1.treeDistanceWeight_values
-- BB3inf RETIRED to quarantine 2026-07-07 (R5 Step 0): 3 measure-route axioms off all count-native
-- footprints, imported by nothing but the root. Prints removed; module in quarantine/.
-- NestedCollapse
#print axioms LeanUrat.NestedCollapse.nested_reproduces_I2
#print axioms LeanUrat.NestedCollapse.nested_reproduces_I3
#print axioms LeanUrat.NestedCollapse.nested_block_lt
#print axioms LeanUrat.NestedCollapse.geometricLimit_of_selfLoop
#print axioms LeanUrat.MontesAxiom.RescaleC1.selfLoopExponent_eq_blockExponent_sub_one
-- CountingModel
#print axioms LeanUrat.CountingModel.CountingModel.density_le_decided_add_undecided
#print axioms LeanUrat.CountingModel.CountingModel.decided_le_density
#print axioms LeanUrat.CountingModel.countingDensity_is_squeezed_limit
-- Witness (W4b 2026-07-21: montes_full_instance / montes_bundle_nonempty PORTED onto the V2 spine
-- — same names, same semantic content, now over MontesDataV2/trivD2 firing
-- MontesV2.goal_theorem_montes; MUST stay core-only)
#print axioms LeanUrat.Witness.montes_full_instance
#print axioms LeanUrat.Witness.montes_bundle_nonempty
#print axioms LeanUrat.Witness.DensityFoundation_nonempty
-- ★★★ ORDER-1 (single-slope) REAL DENSITY, σ-keyed + general-prime + certified non-vacuity gate
-- (2026-07-12, ADDITIVE — TameRealDensity). montes_order1_tame_realDensity = the σ-keyed order-1
-- single-slope real density theorem (same shape as Order0.montes_order0_realDensity): density = engine
-- rational fn, real counts at realP converge, certified value = engine per-shape sum.
-- montes_order1_tame_certified_density_pos = the CERTIFIED strictly-positive gate (value =
-- (realP−1)·(realP^k)⁻¹ > 0 at the concrete self-loop n=2,P=[(0,1),(2,0)],shape=[(1,1)]) — NOT vacuous.
-- General-prime standalone (gap #2, order-1): stratumCount_selfloop_general / hnode_selfloop_general /
-- montes_order1_selfloop_density_general_prime (+ its _pos). hnode_multiSideProduct is ALREADY general-
-- prime. Full σ-keyed disjoint tame ASSEMBLY (order-0 ⊕ order-1) DEFERRED (RealInstance-scale surgery).
#print axioms LeanUrat.OM.TameRealDensity.stratumCount_selfloop_general
#print axioms LeanUrat.OM.TameRealDensity.hnode_selfloop_general
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_selfloop_density_general_prime
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_tame_realDensity
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_tame_certified_density_pos
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_selfloop_density_general_prime_pos
-- ★ CONDITIONAL TAME ASSEMBLY (#53): montes_tame_realDensity_of_exhaustive — the genuine tame density
--   (order-0 sepShapes ⊕ order-1 Tselfloop, σ-keyed menu) = engine rational function, per-shape h_nodes
--   DISCHARGED from the proven order-0/order-1 theorems, with ONLY drainage/exhaustiveness (TameMenuExhaustive)
--   as an explicit honest hypothesis (genuinely open per Drainage.lean; NOT faked, does not fix the value).
--   Non-vacuous: montes_tame_realDensity_certified_value_pos > 0 (dominated by the order-1 gate). Core-only.
#print axioms LeanUrat.OM.TameRealDensity.montes_tame_realDensity_of_exhaustive
#print axioms LeanUrat.OM.TameRealDensity.montes_tame_realDensity_certified_value_pos
-- ★★★ M9 REBASE V2 (W2-W4b) — the corrected σ-keyed capstone chain (notes/M9_REBASE_BLUEPRINT_2026-07-19.md).
-- W1: MontesV2.goal_theorem_montes / goal_theorem_via_montes = the Goal-layer siblings over the
-- abstract-coefficient MontesDataV2 (D2); they carry the canonical names since W4b (2026-07-21,
-- renamed from goal_theorem_montes_v2 / goal_theorem_via_montes_v2 after the old-`MontesData`
-- Goal bridge was retired). W2 (renamed in W4a, 2026-07-21):
-- RealInstanceV2.montes_unconditional(_exhaustive) — formerly montes_unconditional_v2(_exhaustive) —
-- = THE capstones over the REAL instance (realM2/realD2/realF2, C := omCount over the σ-keyed omMenu):
-- (R) uniform rationality + (V) decided-density tie UNCONDITIONAL; palindromy via the HYPOTHESIS
-- htameFE (D4 — the old axiom realDensity_tame_functionalEquation is RETIRED in W4a), so the
-- footprints MUST be Lean core ONLY (an axiom appearing here is a stop-the-line event). W3 gates
-- (RealInstanceV2Gates): G1 non-vacuity at the capstone's own density (inert n=2 menu sum = 1/4 > 0
-- at realP, + the realM2 countingDensity pin), G2 σ-separation (split 1/9 ≠ inert 1/3 at q'=3;
-- ramified menu ∅, sum 0 ≠ 1/4) — the V1/O1 reversals, machine-checked. MUST all be core-only:
#print axioms LeanUrat.MontesV2.goal_theorem_montes
#print axioms LeanUrat.MontesV2.goal_theorem_via_montes
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional_exhaustive
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_value_inert2
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_nonvacuous
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_countingDensity_inert2
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_split_q3
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_inert_q3
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_sigma_separation
#print axioms LeanUrat.OM.RealInstanceV2Gates.omMenu_ramified_empty
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_ramified_zero
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_ramified_vs_inert
-- G1-tame (semantic-audit item 2, 2026-07-19): htameFE's value clause quantifies over TAME primes
-- q > n; this pins realF2.density > 0 at the tame prime 3 (inert n=2, value 1/3), so the capstone's
-- palindromy hypothesis constrains a genuinely NONZERO rational function (num = 0 witness excluded):
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_htameFE_nontrivial
-- ★★★ WILD WAVE 1 (2026-07-21, notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md) — the σ-keyed WILD menu:
-- omMenuW n σ = sepShapesOf n σ ∪ (ramShape n σ).toFinset, with constant-e ramified σ carrying the
-- ONE canonical minimal-H terminating Tselfloop stratum (the PROVED order-1 counting legs; NO new
-- axiom — the ramified leg is the banked THEOREM hnode_selfloop_over_Bclassify_R). Capstones
-- RealInstanceW.montes_unconditional_w(_exhaustive) = statements VERBATIM the V2 capstones with
-- omMenuW for omMenu, fired at (realMW, realDW, realFW). HONEST SCOPE: the certified ramified value
-- is the MINIMAL-H canonical-stratum density (the leading term of the type's density), NOT the
-- H-tower sum; mixed-e types / order ≥ 2 / exhaustiveness NOT covered. Gates: G1W first wild
-- non-vacuity (ramType2 = ⟨{(2,1)}⟩ menu-sum = (p−1)·p⁻³ at every prime, = 1/8 at realP, > 0; the
-- V2 value of the SAME type was 0 — genuine de-vacuification; instance pin countingDensity = 1/8);
-- G2W σ-separation (ramified 1/8 ≠ inert 1/4; n=4 constant-e pair ⟨{(2,1),(2,1)}⟩ vs ⟨{(2,2)}⟩ →
-- 0 vs 1/256, the honest-empty pattern shapeCount_split_two machine-checked); G4W mutation
-- (C := 0 copy fails to compile — evidence block in OM/RealInstanceWGates.lean). MUST all be
-- Lean core ONLY (an axiom appearing here is a stop-the-line event):
#print axioms LeanUrat.OM.WildMenu.eq_of_mem_omMenuW
#print axioms LeanUrat.OM.WildMenu.omMenuW_ram_of_constE
#print axioms LeanUrat.OM.WildMenuPrep.sum_stratumCount_le_box_W
#print axioms LeanUrat.OM.WildMenuPrep.normSum_omMenuW_mono
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive
#print axioms LeanUrat.OM.RealInstanceWGates.omCount_Tselfloop_closed
#print axioms LeanUrat.OM.RealInstanceWGates.constERam_ramType2
#print axioms LeanUrat.OM.RealInstanceWGates.omMenuW_ramType2
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_omCount_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_nonvacuous
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_countingDensity
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_inert_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_ram_vs_inert
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_sigmaA_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_sigmaB_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_wild_sigma_separation
-- ★★★ WILD WAVE 2 (om_leaf_faithful) (2026-07-21, notes/WILD_WAVE2_BLUEPRINT_2026-07-21.md §2 W2b/W2c)
-- — the ONE Wave-2 axiom: GMN Thm 1.15/1.19/Cor 1.20 (order-≤1 instances of Thm 3.1/3.7/Cor 3.8)
-- + Def 3.10/eq.(37) + local-field structure theory (Serre I–II), packaged as LocalFactorData
-- existence, MENU-FIBER-SCOPED (only over polynomials the level-N classifier ACTUALLY sends to the
-- σ-keyed menu; no uniformity/rationality/measure/density term; non-imports: drainage,
-- equidistribution). ★ RE-SCOPED W3c (2026-07-21, blueprint WILD_WAVE3 §2 item 4): the menu
-- hypothesis is now (K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ) — the K-windowed menu, all
-- admissible heights H = fSum σ·k, gcd(k, e) = 1; Cor 1.20 applies verbatim per window leg (same
-- sideDeg = fSum σ, same all-μ=1 residual, keystone WildMenuW3.gcd_admissible); everything else
-- byte-identical. The old (K = 1) form is now the THEOREM om_leaf_faithful_w1 (via omMenuW3_one),
-- printing core + om_leaf_faithful EXACTLY, and consumers are re-pointed through it (statements
-- UNCHANGED). Faithfulness theorems om_leaf_faithful_w1 / menuFiber_hasType / gateFiber_hasType /
-- gate_axiom_coherent MUST print core + om_leaf_faithful EXACTLY. Probe legs
-- (gate_mem_omMenuW, gateFiber_nonempty = the inhabited gate fiber at the concrete X²+2X+2, N=3)
-- MUST be core-only. Mutation evidence (split-type mutation ⟹ False against
-- QpType.wildGateFiber_eisenstein) recorded in OM/OmLeafFaithful.lean (scratch not committed);
-- the W3c re-run of BOTH probes at the H = 3 window stratum is recorded in OM/QpTypeH3.lean
-- (see the WILD WAVE 3c block at the bottom of this file).
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w1
#print axioms LeanUrat.OM.OmLeafFaithful.menuFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gate_mem_omMenuW
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_nonempty
#print axioms LeanUrat.OM.OmLeafFaithful.gate_axiom_coherent
-- RE-PRINT (REQUIRED): the density capstones REMAIN Lean core ONLY — om_leaf_faithful is consumed
-- ONLY by the faithfulness theorems above and must NOT enter the capstone cones (a wild-wave-2
-- axiom appearing in either footprint below is a stop-the-line event):
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
-- ★★★ WILD WAVE 2 FLAG-1 (2026-07-21, guardian-audit follow-up) — the AXIOM-FREE Eisenstein
-- (e,f) theorem (OM/QpTypeEisenstein.lean): for monic Eisenstein g of positive degree, EVERY
-- LocalFactorData bundle has eOf = deg g and fOf = 1 (root descends to O; y^n = p·unit forces
-- map(p·ℤ_p) = m_O^(k·n) hence e = k·n by ramificationIdx_spec; e·f = [L:ℚ_p] = n collapses
-- k = 1, f = 1). Gate corollary gate_ef_forced: the Wave-1 wild gate fiber forces efOf = (2,1)
-- for every bundle — the fine-(e,f) swap mutation {(1,2)} (singleton type, INVISIBLE to the old
-- factor-count probe) now derives False (evidence block in OM/QpTypeEisenstein.lean; scratch not
-- committed). MUST all be Lean core ONLY (an axiom appearing here is a stop-the-line event):
#print axioms LeanUrat.OM.QpTypeEisenstein.isUnit_add_of_mem_maximalIdeal
#print axioms LeanUrat.OM.QpTypeEisenstein.ef_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.eOf_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.fOf_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.efOf_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.gate_ef_forced
#print axioms LeanUrat.OM.QpTypeEisenstein.gate_eOf_forced
-- non-vacuity gate (U1 lesson): the theorem's hypothesis set is inhabited (g = X + p, trivial
-- bundle) and fires with the correct value (1,1):
#print axioms LeanUrat.OM.QpTypeEisenstein.isEisensteinAt_X_add_p
#print axioms LeanUrat.OM.QpTypeEisenstein.eisWitnessData
#print axioms LeanUrat.OM.QpTypeEisenstein.eisWitness_ef
#print axioms LeanUrat.OM.QpTypeEisenstein.efOf_mem_qpType
#print axioms LeanUrat.OM.QpTypeEisenstein.qpType_singleton_forces
-- RE-PRINT (REQUIRED): the density capstones REMAIN Lean core ONLY after the FLAG-1 wave:
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
-- ★★★ WILD WAVE 3 (H-window) (2026-07-21, notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md §2 items 1-3)
-- — the K-parameterized WINDOW of terminating wild strata per constant-e ramified type:
-- omMenuW3 n K σ = sepShapesOf n σ ∪ ramShapes3 n K σ, one Tselfloop stratum per admissible
-- multiplier k ∈ admissibleK (n/fSum σ) K (height H = fSum σ · k, gcd(k, e) = 1 — the keystone
-- gcd_admissible; Wave 1 IS the K = 1 window: omMenuW3_one). Capstones
-- RealInstanceW3.montes_unconditional_w3(_exhaustive) = statements VERBATIM the Wave-1 capstones
-- with omMenuW3 n K for omMenuW n, fired at (realMW3, realDW3, realFW3 K); recovery gate
-- montes_w3_one_recovers: the K = 1 instance's countingDensity IS Wave 1's, every n and σ.
-- HONEST SCOPE: window-K certifies the K-TRUNCATED decided density of each constant-e type — a
-- strictly larger leading sum than Wave 1, NOT the full type density (the geometric tail = the
-- recursive self-loop wall); mixed-e / order ≥ 2 / exhaustiveness NOT covered. Gates: G1 window
-- value (n=2, K=3, ramType2: admissibleK 2 3 = {1,3}, legs H=1 → 1/8 and H=3 → (p−1)·p⁻⁶ = 1/64
-- at realP=2, window sum 9/64 — the EXTERNAL Python gate pinned 1/8, 1/64, 9/64; instance pin
-- countingDensity = 9/64); G2 STRICT window growth (value(K=1) = 1/8 < 9/64 = value(K=3), both
-- through the real instances — machine-checked monotone-toward-the-tower, wall value 1/7 never
-- claimed); G4 mutation (C := 0 copy fails to compile — evidence block in
-- OM/RealInstanceW3Gates.lean). MUST all be Lean core ONLY (an axiom appearing here is a
-- stop-the-line event):
#print axioms LeanUrat.OM.WildMenuW3.gcd_admissible
#print axioms LeanUrat.OM.WildMenuW3.omMenuW3_one
#print axioms LeanUrat.OM.WildMenuW3.ramShapeAt_injective_k
#print axioms LeanUrat.OM.WildMenuW3.eq_of_mem_omMenuW3
#print axioms LeanUrat.OM.WildMenuW3.sum_stratumCount_le_box_W3
#print axioms LeanUrat.OM.WildMenuW3.normSum_omMenuW3_mono
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_w3_one_recovers
#print axioms LeanUrat.OM.RealInstanceW3Gates.admissibleK_two_three
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_menu
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_omCount_H3
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_value
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_countingDensity
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_one_countingDensity
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_growth
-- RE-PRINT (REQUIRED): the Wave-1 capstones REMAIN Lean core ONLY after the Wave-3 wave (leaf
-- modules only; nothing on the Wave-1 path was touched):
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive
-- ★★★ WILD WAVE 3c (axiom re-scope + the H = 3 axiom-free anchor) (2026-07-21,
-- notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md §2 item 4). The declared axiom om_leaf_faithful is
-- RE-SCOPED to the K-windowed menu (see the annotated WILD WAVE 2 block above — its entries
-- re-print the re-scoped axiom + the derived K = 1 form om_leaf_faithful_w1 + the re-pointed
-- consumers). OM/QpTypeH3.lean is the NEW axiom-free anchor at the H = 3 window leg
-- (Tselfloop 2 ((0,3),(2,0)) [(1,1)] = ramShapeAt 2 {(2,1)} 3, the k = 3 admissible multiplier):
-- wildH3_irreducible('') = the elementary two-root valuation contradiction (v(a₀) = 3,
-- a₁ ∈ (p)² ⟹ ℚ_p-irreducible; NO Newton polygon); wildH3Fiber_valuation/_irreducible = the
-- level-N (N ≥ 4) classifier-fiber link through classify_eq_selfloop_iff + the decode bridge;
-- h3Fiber_nonempty = the inhabited H = 3 fiber (X² + 4X + 8 over ℤ_[2] at N = 5, InCell proved
-- from the digit conditions — no banked N ≥ 4 gate existed); ef_of_wildH3/gate_h3_ef_forced =
-- route (a), the PARITY argument (e·f = 2, e = 1 refuted by ϖ-divisibility in the DVR: y² =
-- −(a₀ + a₁y) with orders 2k / exactly 3 / ≥ 2+k), forcing efOf = (2,1) for EVERY bundle on the
-- H = 3 fiber. Both mutation probes RE-RUN against the RE-SCOPED hypotheses at H = 3 (split-type
-- {(1,1),(1,1)} AND fine-swap {(1,2)} ⟹ machine-checked False; evidence blocks in
-- OM/QpTypeH3.lean; scratches not committed). MUST all be Lean core ONLY (an axiom appearing
-- here is a stop-the-line event):
#print axioms LeanUrat.OM.QpTypeH3.sidePairs_h3Path
#print axioms LeanUrat.OM.QpTypeH3.menuPath_h3
#print axioms LeanUrat.OM.QpTypeH3.shapesFor_h3
#print axioms LeanUrat.OM.QpTypeH3.ramShapeAt_h3
#print axioms LeanUrat.OM.QpTypeH3.h3_mem_omMenuW3
#print axioms LeanUrat.OM.QpTypeH3.mem_maximalIdeal_pow_of_le_zmodValuation
#print axioms LeanUrat.OM.QpTypeH3.wildH3_irreducible'
#print axioms LeanUrat.OM.QpTypeH3.wildH3_irreducible
#print axioms LeanUrat.OM.QpTypeH3.wildH3Fiber_valuation
#print axioms LeanUrat.OM.QpTypeH3.wildH3Fiber_irreducible
#print axioms LeanUrat.OM.QpTypeH3.h3Poly_monic
#print axioms LeanUrat.OM.QpTypeH3.h3Poly_natDegree
#print axioms LeanUrat.OM.QpTypeH3.toBox_h3Poly
#print axioms LeanUrat.OM.QpTypeH3.h3box_inCell
#print axioms LeanUrat.OM.QpTypeH3.h3Fiber_nonempty
#print axioms LeanUrat.OM.QpTypeH3.not_pow_succ_dvd_unit_mul_pow
#print axioms LeanUrat.OM.QpTypeH3.ef_of_wildH3
#print axioms LeanUrat.OM.QpTypeH3.gate_h3_ef_forced
-- RE-PRINT (REQUIRED): the faithfulness theorems after the W3c re-scope — footprints MUST be
-- core + om_leaf_faithful EXACTLY (nothing more, nothing less):
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w1
#print axioms LeanUrat.OM.OmLeafFaithful.menuFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gate_axiom_coherent
-- RE-PRINT (REQUIRED): ALL FOUR density capstones (Waves 1 and 3) + the V2 capstone REMAIN
-- Lean core ONLY after the W3c re-scope — om_leaf_faithful is consumed ONLY by the faithfulness
-- theorems above; a wild-wave axiom appearing in ANY footprint below is a stop-the-line event:
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
-- ★★★ WILD WAVE 4 (mixed-e) (2026-07-22, notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md §2-W4a/W4b)
-- — the multi-slope σ-keyed menu extension: omMenu4 n K σ = omMenuW3 n K σ ∪ (mixedShape n σ),
-- ONE canonical multi-slope stratum multiSideLit n (mixedPath σ) (mixedSh σ) per mixed-e type
-- (all side-e's ≥ 2 pairwise DISTINCT, ascending-e steepest-first — the erratum-corrected F4
-- order; per-side minimal height k = 1, all-μ=1 residuals). The COEFFICIENT IS C4, NOT omCount
-- (first wave with a non-omCount coefficient): the per-side product ∏ omCount (sideSubShape …)
-- on the mixed literal (no single omCount carries the product — PathShapeMultiSideTree header,
-- candidate (c) refuted), omCount unchanged on every old shape; the COUNT is stratumCount4:
-- GENUINE order-1 classify1 fibers (stratumCount1) on the mixed leg, B.classify fibers on the
-- old legs — both subsets of the SAME box, pairwise disjoint across families and σ
-- (fiber4_disjoint: unit-a₀ vs hull; vertex exactness vs the ≥2-side polygon; mkCell
-- injectivity back to σ). The m×C decomposition split routes through per-factor
-- omCount_eq_mul_all (multiplicity := ∏ omMultiplicity (sideSubShape …), a genuine polynomial;
-- prodSC : ℕ is p-dependent, NOT polynomial-shaped — the blueprint's prodSC question resolved
-- WITHOUT a new shapeCount-as-polynomial tie). Capstones
-- RealInstanceW4.montes_unconditional_w4(_exhaustive) = statements VERBATIM the Wave-3
-- capstones with omMenu4 n K for omMenuW3 n K and C4 T q' for omCount T q' (the ONE
-- coefficient change), fired at (realMW4, realDW4, realFW4 K); recovery gate
-- montes_w4_recovers: on every NON-mixed σ the Wave-4 countingDensity IS Wave 3's, every n, K.
-- HONEST SCOPE: the mixed value is the ONE canonical stratum's density (the leading term of
-- the type's density, no tower/window resummation on the mixed leg); e=1-mixing / same-e
-- multi-side / per-side K-windows / order ≥ 2 / exhaustiveness NOT covered. Gates: G1 mixed
-- value (n=5, σ₅ = {(2,1),(3,1)}, K=3: menu = the canonical singleton on the path
-- (0,2)→(2,1)→(5,0), slopes −1/2 then −1/3; per-side factors (p−1)·p⁻⁵ [e=2 side, newton 4 +
-- sideDeg 1] × (p−1)·p⁻⁴ [e=3 side, newton 3 + sideDeg 1] = (p−1)²·p⁻⁹ = 1/512 at realP=2 —
-- the blueprint's EXTERNALLY verified exact value; volume reconciliation 5+4 = 7+2 = 9 pinned
-- by decide [whole-path newtonExponent 7, cross-term Σ sideDeg = 2]; instance pin
-- countingDensity = 1/512 through realDW4's decomposition theorem, consuming the GENUINE
-- order-1 mixed counting leg stratum_tendsto_C4_mixed ← hnode_multiSideProduct); G2
-- σ-separation (1/512 ≠ 1/64 = the constant-e5 type's K=1 value, both through the real Wave-4
-- instances, the e5 leg routed through the recovery gate); G4 mutation (C := 0 copy fails to
-- compile — evidence block in OM/RealInstanceW4Gates.lean; scratch deleted after capture).
-- MUST all be Lean core ONLY (an axiom appearing here is a stop-the-line event):
#print axioms LeanUrat.OM.MultiSlopeMenu.multiSideLit_injective
#print axioms LeanUrat.OM.MultiSlopeMenu.typeOf4_multiSideLit
#print axioms LeanUrat.OM.MultiSlopeMenu.omMenu4_of_mixed
#print axioms LeanUrat.OM.MultiSlopeMenu.omMenu4_eq_of_not_mixed
#print axioms LeanUrat.OM.MultiSlopeMenu.eq_of_mem_omMenu4
#print axioms LeanUrat.OM.MultiSlopeMenu.fiber4_disjoint
#print axioms LeanUrat.OM.MultiSlopeMenu.sum_stratumCount4_le_box
#print axioms LeanUrat.OM.MultiSlopeMenu.normSum_omMenu4_mono
#print axioms LeanUrat.OM.MultiSlopeMenu.stratum_tendsto_C4_mixed
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4_exhaustive
#print axioms LeanUrat.OM.RealInstanceW4.montes_w4_recovers
#print axioms LeanUrat.OM.RealInstanceW4Gates.mixedOK_sigma5
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_menu
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_side_e2
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_side_e3
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_volume_reconciliation
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_value
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_countingDensity
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_e5_countingDensity
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_separation
-- RE-PRINT (REQUIRED): ALL prior density capstones (Waves 1 and 3, the V2 capstone, and the
-- Wave-3 recovery gate) REMAIN Lean core ONLY after the Wave-4 wave (leaf modules only;
-- nothing on any prior path was touched); a wild-wave axiom appearing in ANY footprint below
-- is a stop-the-line event:
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_w3_one_recovers
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
-- ★★★ WILD WAVE 4c (axiom re-scope #3 + the mixed-gate axiom-free anchor) (2026-07-22,
-- notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md §W4c). The declared axiom om_leaf_faithful is
-- RE-SCOPED (third scope) to the mixed-e menu MultiSlopeMenu.omMenu4 n K σ, with the fiber
-- hypothesis re-scoped from the bare `B.classify … = T` equation to the PER-FAMILY DISPATCH
-- fiberOf4: on multi-slope literals (headOrd T = 1) the GENUINE order-1 classify1/InCell fiber
-- at the decoded cell `classify1 p (toBox …) = some (mkCell n (decodePath T) (decodeShapes T))`
-- (mirroring the PROVED counting fiber MultiSlopeMenu.Fiber4 exactly); on every old shape,
-- DEFINITIONALLY the old B.classify equation (fiberOf4_old). This dispatch is what avoids the
-- vacuity trap (V1 failure mode): B.classify reads only the first Newton side and can never
-- emit a multi-slope literal, so the naive re-scope would have made every mixed instance
-- vacuously true. The W3c form is now the THEOREM om_leaf_faithful_w3 (menu leg by union
-- injection, fiber leg definitional), and W1/W2 consumers route through om_leaf_faithful_w1
-- unchanged. GMN content of the mixed branch: a nonempty classify1 fiber pins the multi-slope
-- polygon + per-side all-μ=1 separable residuals; Thm 1.15 (slope dissection: one coprime
-- factor block per side) + per-side Thm 1.19/Cor 1.20 give the factorization with mixed
-- (e,f)-multiset = σ (= the definitional decode typeOf4_multiSideLit).
-- OM/QpTypeMixed.lean is the NEW axiom-free anchor at the n = 5 mixed-gate stratum
-- (multiSideLit 5 [(0,2),(2,1),(5,0)] [[(1,1)],[(1,1)]] = the canonical omMenu4 entry at
-- σ₅ = {(2,1),(3,1)}): mixedGateFiber_valuation = the fiber link (v(a₀) = 2 exact, a₁ ∈ (p)²,
-- v(a₂) = 1 exact, a₃, a₄ ∈ (p) — the two-slope digit conditions through
-- classify1_eq_some_iff + inCell_mkCell_iff + the decode bridge); mixedGate_no_root('/)
-- + mixedGate_no_linear_factor' + the fiber forms = the FULL-strength elementary anchor
-- (a ℚ_p-root descends to ℤ_[p]; p ∣ y forces p³ ∣ a₀ against exactness, p ∤ y forces
-- p ∣ y⁵ against primality — no ℚ_p-root, hence NO degree-1 factor over ℚ_p);
-- mixedGateFiber_nonempty = the inhabited mixed fiber (X⁵ + 2X² + 4 over ℤ_[2] at N = 4,
-- InCell proved from the digit conditions on BOTH sides, residuals X + 1 each);
-- ef_mul_eq_natDegree + natDegree_pos_of_irreducible_map = the degree-ledger probe plumbing
-- (eOf·fOf = [L:ℚ_p] = deg g for EVERY bundle). Both W4c mutation probes RE-RUN against the
-- RE-SCOPED hypotheses at the mixed gate (all-unramified {(1,1)}⁵ ⟹ a forced degree-1 factor
-- vs the no-linear-factor anchor, AND wrong-e singleton {(2,1)} ⟹ 2·1 = 5 vs the degree
-- ledger; both machine-checked False; evidence blocks in OM/QpTypeMixed.lean; scratches not
-- committed). MUST all be Lean core ONLY (an axiom appearing here is a stop-the-line event):
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4_mixed
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4_old
#print axioms LeanUrat.OM.QpTypeMixed.sidePairs_mixedGatePath
#print axioms LeanUrat.OM.QpTypeMixed.menuPath_mixedGate
#print axioms LeanUrat.OM.QpTypeMixed.shapesFor_mixedGate
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateLit_eq_canonical
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateLit_mem_omMenu4
#print axioms LeanUrat.OM.QpTypeMixed.headOrd_mixedGateLit
#print axioms LeanUrat.OM.QpTypeMixed.decodePath_mixedGateLit
#print axioms LeanUrat.OM.QpTypeMixed.decodeShapes_mixedGateLit
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_valuation
#print axioms LeanUrat.OM.QpTypeMixed.mixedGate_no_root'
#print axioms LeanUrat.OM.QpTypeMixed.mixedGate_no_root
#print axioms LeanUrat.OM.QpTypeMixed.mixedGate_no_linear_factor'
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_no_root
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_no_linear_factor
#print axioms LeanUrat.OM.QpTypeMixed.mixedGatePoly_monic
#print axioms LeanUrat.OM.QpTypeMixed.mixedGatePoly_natDegree
#print axioms LeanUrat.OM.QpTypeMixed.toBox_mixedGatePoly
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateBox_inCell
#print axioms LeanUrat.OM.QpTypeMixed.mixedGateFiber_nonempty
#print axioms LeanUrat.OM.QpTypeMixed.natDegree_pos_of_irreducible_map
#print axioms LeanUrat.OM.QpTypeMixed.ef_mul_eq_natDegree
-- RE-PRINT (REQUIRED): the re-scoped axiom + the faithfulness theorems after the W4c re-scope
-- — footprints MUST be core + om_leaf_faithful EXACTLY (nothing more, nothing less); the W3c
-- form om_leaf_faithful_w3 is now a theorem in this list:
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w3
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w1
#print axioms LeanUrat.OM.OmLeafFaithful.menuFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gate_axiom_coherent
-- probe legs MUST stay core-only:
#print axioms LeanUrat.OM.OmLeafFaithful.gate_mem_omMenuW
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_nonempty
-- RE-PRINT (REQUIRED): ALL density capstones (Waves 1, 3 and 4, the V2 capstone, and both
-- recovery gates) REMAIN Lean core ONLY after the W4c re-scope — om_leaf_faithful is consumed
-- ONLY by the faithfulness theorems above; a wild-wave axiom appearing in ANY footprint below
-- is a stop-the-line event:
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_w3_one_recovers
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4_exhaustive
#print axioms LeanUrat.OM.RealInstanceW4.montes_w4_recovers
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional

-- ══ Wave W5b (2026-07-22): the n=2 DESCENT-CHAIN menu + depth-windowed real instance ══
-- OM/ChainMenu.lean + OM/RealInstanceW5.lean + OM/RealInstanceW5Gates.lean (leaf modules; no
-- existing file modified except this census). Menu omMenu5 n D K σ = omMenu4 n K σ ∪
-- chainShapes n D K σ: chainLit ms leaf literals (tree head (2, 2, depth) — order-slot 2
-- discriminates from every W1/W3 order-0 head and the W4 multi-slope order-slot 1 — then the
-- ms entries, then the leaf head; exact decode + injectivity), emitted at n = 2 ONLY
-- (general-n chains are the accepted note's OPEN-D3/D5 territory). Counts: stratumCount5 =
-- genuine Nat.card of the ChainCell digit fibers (the W5a staircase bijection
-- stratumPairEquiv transported per step via descendPair — descendPair_eq_stratumPairEquiv —
-- with the c̃-digit pool counted per step: card_chainPair = (p−1)^depth · leafCount, thresholds
-- + small-N vanishing + level constancy exact). Coefficient C5 = chainC = (q−1)^depth ·
-- leafPool(q) · q^{−(3Σms + eLeaf)} on chain literals (rationality: (poly)·q^{−V}), C4 else.
-- Leaves: ram H (odd rungs, type (2,1)), inert m (root-free residual pool q(q−1)/2 — counted
-- exactly via the Sym2/Vieta parametrization, two_mul_card_noRootPairs), split k (two-sided,
-- pool q−1, with the note-§7 readability gate 2k+1 ≤ L₀ — the two-sided bookkeeping caveat).
-- Disjointness: chain-vs-chain by the pinned digit ledgers (chainPair_disjoint: v-pins /
-- (c̃²,−2c̃) field pin / double-root-vs-root-free), chain-vs-old by the exact root valuation
-- v(a₀) = 2m₁ EVEN vs sepShape v(a₀) = 0 and W3-window v(a₀) = k ODD (gcd(k,2)=1), old-vs-old
-- banked (fiber4_disjoint); box bound sum_stratumCount5_le_box; monotone staircases
-- normSum_omMenu5_mono. Capstones montes_unconditional_w5(_exhaustive) = statements VERBATIM
-- Wave-4's with omMenu5 n D K for omMenu4 n K and C5 for C4, fired at (realMW5, realDW5,
-- realFW5 D K); recovery montes_w5_recovers: at D = 0 the Wave-5 countingDensity IS Wave 4's,
-- every n, σ, K. HONEST SCOPE: chain fibers are COUNTING-side digit fibers — per-fiber Montes
-- TYPE faithfulness (translation invariance [COUNT] + Cor 1.20 in the recentered frame) is
-- W5c's boundary #4/#5 (typeOf5 keying is definitional); the (D, K) window is a PARTIAL SUM
-- of the descent tower (W6 resums); odd-p even-height split-residual leaf deferred (pool
-- empty at realP = 2); no exhaustiveness claim (hExhaust explicit). Gates: the §7 Case-A
-- ledger ABSOLUTE values at p = 2 (cluster-conditional ledger × the one-time 2⁻²
-- normalization): (1)→ram1 = 1/64 (Case C, x²−12), (1,1)→ram1 = 1/512, (1)→ram3 = 1/512,
-- (1)→inert1 = 1/256, (1)→split1 = 1/256; the COUNT gate (4 points of 256 at N = 4); the
-- depth-window growth 1/8 = value(D=0) < value(D=1) = 9/64 through the REAL instances'
-- countingDensity; G4 mutation (C := 0 copy fails to compile — evidence block in
-- OM/RealInstanceW5Gates.lean; scratch deleted after capture).
-- MUST all be Lean core ONLY (an axiom appearing here is a stop-the-line event):
#print axioms LeanUrat.OM.ChainMenu.chainLit_injective
#print axioms LeanUrat.OM.ChainMenu.typeOf5_chainLit
#print axioms LeanUrat.OM.ChainMenu.two_mul_card_noRootPairs
#print axioms LeanUrat.OM.ChainMenu.descendPair_eq_stratumPairEquiv
#print axioms LeanUrat.OM.ChainMenu.card_chainPair
#print axioms LeanUrat.OM.ChainMenu.card_chainCell
#print axioms LeanUrat.OM.ChainMenu.chainPair_disjoint
#print axioms LeanUrat.OM.ChainMenu.fiber5_disjoint
#print axioms LeanUrat.OM.ChainMenu.sum_stratumCount5_le_box
#print axioms LeanUrat.OM.ChainMenu.normSum_omMenu5_mono
#print axioms LeanUrat.OM.ChainMenu.stratum_tendsto_C5_chain
#print axioms LeanUrat.OM.ChainMenu.omMenu5_zero
#print axioms LeanUrat.OM.ChainMenu.eq_of_mem_omMenu5
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5_exhaustive
#print axioms LeanUrat.OM.RealInstanceW5.montes_w5_recovers
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_caseC
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_depth2
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_ram3
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_inert
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_split
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_count_at_threshold
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_menu
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_D0
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_D1
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_window_growth
-- RE-PRINT (REQUIRED): ALL prior density capstones (Waves 1, 3 and 4, the V2 capstone, and
-- the recovery gates) REMAIN Lean core ONLY after the Wave-5b wave (leaf modules only;
-- nothing on any prior path was touched); a wild-wave axiom appearing in ANY footprint below
-- is a stop-the-line event:
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_w3_one_recovers
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4_exhaustive
#print axioms LeanUrat.OM.RealInstanceW4.montes_w4_recovers
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
