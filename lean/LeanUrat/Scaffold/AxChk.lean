/-  Scaffold/AxChk.lean — BP_VI §1.5 axiom-census extension (standalone; NOT
    imported by anything; `AxChk_baseline.lean` untouched).
    Gate: `lake env lean LeanUrat/Scaffold/AxChk.lean` at every division
    checkpoint. Acceptance bar: Lean core only (`propext`, `Classical.choice`,
    `Quot.sound`) for EVERY row; a regression is stop-the-line.
    Units: VI-A1 (scaffold VI-H*/VI-S*/VI-B* — landed below), VI-A2 (VI-N* +
    gate wrappers — landed below at REVISION 3), VI-A3 (theoremU/bridge + OM
    quarry — landed below), VI-A4
    (ksub/O12PoleFree/RegPFinite/O5CountingB/UE_vtxUpper enumeration).
    VI-A1 census rows (finite, declaration-by-declaration; no wildcards) —
    every named VI-H*/VI-S*/VI-B* theorem of the landed scaffold core
    (waves VI-0/VI-1). REVISION-3 record: VI-B3 (`SlotAssignment`, a structure,
    not a theorem — no census row of its own) and VI-B4
    (`rootC_fired_at_slots`) landed under the compile-gated REVISION-3
    statement repairs (BP_VI.md REVISION 3; the Revision-2 displays were
    compiler-refuted):
      LeanUrat.Scaffold.clauseR_of_clauseUB (VI-H2, Hypotheses.lean) ·
      LeanUrat.Scaffold.trivialRootHyps_ub (VI-H3, Hypotheses.lean) ·
      LeanUrat.Scaffold.RootC_iff_tuple (VI-S3, Spine.lean) ·
      LeanUrat.Scaffold.rootC_of_theoremU (VI-B1, CorpusBridge.lean) ·
      LeanUrat.Scaffold.rootC_fired (VI-B2, CorpusBridge.lean) ·
      LeanUrat.Scaffold.rootC_fired_at_slots (VI-B4, CorpusBridge.lean)
    VI-A2 census rows (finite, declaration-by-declaration; no wildcards) —
    every named VI-N* theorem and its four named gate wrappers (BP_VI §1.4/§1.5):
      LeanUrat.Scaffold.AnchorN2.anchor_n2 (VI-N1) ·
      LeanUrat.Scaffold.AnchorN2.anchor_n2_drainage (VI-N2) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_value_inert2 (VI-N3) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_split_q3 (VI-N3) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_inert_q3 (VI-N3) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_sigma_separation (VI-N3)
    REVISION-3 record (VI-A2): the six targets landed 2026-08-01 under the
    compile-gated §1.4 statement repairs (BP_VI.md REVISION 3 — the Revision-2
    `Nonempty <proof term>` displays were compiler-refuted category errors;
    each anchor now states the gate's ACTUAL proposition + a consumption
    theorem re-firing the gate term verbatim). Rows unfenced below.
    VI-A3 census rows (finite, declaration-by-declaration; no wildcards):
      LeanUrat.MovesU.theoremU · LeanUrat.MovesU.theoremU_fired ·
      LeanUrat.OM.UniformCapstone.montes_uniform_n2 ·
      LeanUrat.OM.RealInstanceV2.montes_unconditional ·
      LeanUrat.OM.SeriesAssembly.hExhaust_n2 ·
      LeanUrat.MovesV.skeleton_finite ·
      LeanUrat.MovesD.runRealizerExists_zmod ·
      LeanUrat.MovesJ.HK11a.sigmaV_vertexLaw
    VI-A4 census rows (finite, declaration-by-declaration; no wildcards) —
    the five quarry families, selection = the BP_VI §3 corpus-map pins.
    ksub family (MovesS/Ksub*.lean — ALL public declarations; ns
    LeanUrat.MovesS): ksub · ksub_eval · ksub_pool · routedMass · ksub_regroup
    ksub family supplement (MovesU/KsubGeneral.lean — the ksub-named rows
    BP_IV's quarry map routes through, + the module's n=2 instance; ns
    LeanUrat.MovesU): ksubM1C1T_of_degCons · UCarriers.cl11_ksub_general ·
      ksub_exists_form · ksubM1C1T_n2_viaGeneral
    O12PoleFree (MovesU/O12PoleFree.lean — §3 pins no line range, so ALL 42
    public declarations; ns LeanUrat.MovesU):
      cycGens · cycS · X_mem_cycS · Xpow_sub_one_mem_cycS · Xpow_mem_cycS ·
      cycS_eval_pos · cycS_ne_zero · MemRcyc · memRcyc_algebraMap ·
      memRcyc_zero · memRcyc_one · MemRcyc.add · MemRcyc.mul · MemRcyc.neg ·
      MemRcyc.sub · memRcyc_inv_cycS · MemRcyc.eq_div · MemRcyc.definedAt ·
      MemRcyc.eval_ne_zero_of_inv · cycS_expand · powSubst_algebraMap ·
      MemRcyc.powSubst · Gram · Gram.memRcyc · eval_ratio · marginO1 ·
      marginO2 · marginO3 · unit_of_cycS_ratio · detO1 · detO2 · detO3 ·
      detO1_unit · detO3_unit · detO1_margin · detO2_margin · detO3_margin ·
      AbsSolveTable · AbsSolveTable.RegAt · AbsSolveTable.RcycDiscipline ·
      AbsSolveTable.regAt_of_discipline · AbsSolveTable.regAt_primePow
    RegPFinite (MovesU/RegPFinite.lean:69–147, the §3 line pin; ns
    LeanUrat.MovesU): UCarriers.detHyp · RegPin.act_agree · RegData.detFull ·
      RegP.detFull_clause · RegP.detFull_ne_zero · RegPin.detFull_eq ·
      RegPin.detFull_ne_zero · blockZeroPole · mem_blockZeroPole
    O5CountingB (MovesU/O5CountingB.lean:44–90, the §3 line pin; ns
    LeanUrat.MovesU): surj_of_injOn_checksum · bijOn_of_injOn_checksum ·
      card_eq_of_injOn_checksum
    UE_vtxUpper (HC2/UE_vtxUpper.lean:70–153, the §3 line pin; ns
    LeanUrat.MovesJ.UE): childW_ge_estar_mul_w · regrade_ge_estar_mul_w ·
      vtx_m6bi_n4upper · vtx_htUpper_div  -/
import LeanUrat.Scaffold.Hypotheses
import LeanUrat.Scaffold.Spine
import LeanUrat.Scaffold.CorpusBridge
import LeanUrat.Scaffold.AnchorN2
import LeanUrat.MovesU.U10_theoremU
import LeanUrat.MovesU.BridgeMk
import LeanUrat.OM.UniformCapstone
import LeanUrat.OM.RealInstanceV2
import LeanUrat.OM.SeriesAssembly
import LeanUrat.MovesV.SkeletonFinite
import LeanUrat.MovesD.R7_runRealizer
import LeanUrat.HC2.HK11a_vertexTransport
import LeanUrat.MovesS.Ksub
import LeanUrat.MovesS.KsubEval
import LeanUrat.MovesS.KsubPool
import LeanUrat.MovesS.KsubRegroup
import LeanUrat.MovesU.KsubGeneral
import LeanUrat.MovesU.O12PoleFree
import LeanUrat.MovesU.RegPFinite
import LeanUrat.MovesU.O5CountingB
import LeanUrat.HC2.UE_vtxUpper

-- ## VI-A1: scaffold-core census (every named VI-H*/VI-S*/VI-B* theorem)
#print axioms LeanUrat.Scaffold.clauseR_of_clauseUB
#print axioms LeanUrat.Scaffold.trivialRootHyps_ub
#print axioms LeanUrat.Scaffold.RootC_iff_tuple
#print axioms LeanUrat.Scaffold.rootC_of_theoremU
#print axioms LeanUrat.Scaffold.rootC_fired
#print axioms LeanUrat.Scaffold.rootC_fired_at_slots

-- ## VI-A2: VI-N* anchor census (every named VI-N* theorem + its four named
-- gate wrappers) — landed at REVISION 3 (see header record).
#print axioms LeanUrat.Scaffold.AnchorN2.anchor_n2
#print axioms LeanUrat.Scaffold.AnchorN2.anchor_n2_drainage
#print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_value_inert2
#print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_split_q3
#print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_inert_q3
#print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_sigma_separation

-- ## VI-A3: theoremU/bridge + OM quarry census
#print axioms LeanUrat.MovesU.theoremU
#print axioms LeanUrat.MovesU.theoremU_fired
#print axioms LeanUrat.OM.UniformCapstone.montes_uniform_n2
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
#print axioms LeanUrat.OM.SeriesAssembly.hExhaust_n2
#print axioms LeanUrat.MovesV.skeleton_finite
#print axioms LeanUrat.MovesD.runRealizerExists_zmod
#print axioms LeanUrat.MovesJ.HK11a.sigmaV_vertexLaw

-- ## VI-A4: quarry-family census (ksub / O12PoleFree / RegPFinite /
-- O5CountingB / UE_vtxUpper; the finite enumeration is in the header)
-- ksub family (MovesS/Ksub*.lean, all public) + KsubGeneral supplement
#print axioms LeanUrat.MovesS.ksub
#print axioms LeanUrat.MovesS.ksub_eval
#print axioms LeanUrat.MovesS.ksub_pool
#print axioms LeanUrat.MovesS.routedMass
#print axioms LeanUrat.MovesS.ksub_regroup
#print axioms LeanUrat.MovesU.ksubM1C1T_of_degCons
#print axioms LeanUrat.MovesU.UCarriers.cl11_ksub_general
#print axioms LeanUrat.MovesU.ksub_exists_form
#print axioms LeanUrat.MovesU.ksubM1C1T_n2_viaGeneral
-- O12PoleFree (MovesU/O12PoleFree.lean, all 42 public declarations)
#print axioms LeanUrat.MovesU.cycGens
#print axioms LeanUrat.MovesU.cycS
#print axioms LeanUrat.MovesU.X_mem_cycS
#print axioms LeanUrat.MovesU.Xpow_sub_one_mem_cycS
#print axioms LeanUrat.MovesU.Xpow_mem_cycS
#print axioms LeanUrat.MovesU.cycS_eval_pos
#print axioms LeanUrat.MovesU.cycS_ne_zero
#print axioms LeanUrat.MovesU.MemRcyc
#print axioms LeanUrat.MovesU.memRcyc_algebraMap
#print axioms LeanUrat.MovesU.memRcyc_zero
#print axioms LeanUrat.MovesU.memRcyc_one
#print axioms LeanUrat.MovesU.MemRcyc.add
#print axioms LeanUrat.MovesU.MemRcyc.mul
#print axioms LeanUrat.MovesU.MemRcyc.neg
#print axioms LeanUrat.MovesU.MemRcyc.sub
#print axioms LeanUrat.MovesU.memRcyc_inv_cycS
#print axioms LeanUrat.MovesU.MemRcyc.eq_div
#print axioms LeanUrat.MovesU.MemRcyc.definedAt
#print axioms LeanUrat.MovesU.MemRcyc.eval_ne_zero_of_inv
#print axioms LeanUrat.MovesU.cycS_expand
#print axioms LeanUrat.MovesU.powSubst_algebraMap
#print axioms LeanUrat.MovesU.MemRcyc.powSubst
#print axioms LeanUrat.MovesU.Gram
#print axioms LeanUrat.MovesU.Gram.memRcyc
#print axioms LeanUrat.MovesU.eval_ratio
#print axioms LeanUrat.MovesU.marginO1
#print axioms LeanUrat.MovesU.marginO2
#print axioms LeanUrat.MovesU.marginO3
#print axioms LeanUrat.MovesU.unit_of_cycS_ratio
#print axioms LeanUrat.MovesU.detO1
#print axioms LeanUrat.MovesU.detO2
#print axioms LeanUrat.MovesU.detO3
#print axioms LeanUrat.MovesU.detO1_unit
#print axioms LeanUrat.MovesU.detO3_unit
#print axioms LeanUrat.MovesU.detO1_margin
#print axioms LeanUrat.MovesU.detO2_margin
#print axioms LeanUrat.MovesU.detO3_margin
#print axioms LeanUrat.MovesU.AbsSolveTable
#print axioms LeanUrat.MovesU.AbsSolveTable.RegAt
#print axioms LeanUrat.MovesU.AbsSolveTable.RcycDiscipline
#print axioms LeanUrat.MovesU.AbsSolveTable.regAt_of_discipline
#print axioms LeanUrat.MovesU.AbsSolveTable.regAt_primePow
-- RegPFinite (MovesU/RegPFinite.lean:69–147, the §3 line pin)
#print axioms LeanUrat.MovesU.UCarriers.detHyp
#print axioms LeanUrat.MovesU.RegPin.act_agree
#print axioms LeanUrat.MovesU.RegData.detFull
#print axioms LeanUrat.MovesU.RegP.detFull_clause
#print axioms LeanUrat.MovesU.RegP.detFull_ne_zero
#print axioms LeanUrat.MovesU.RegPin.detFull_eq
#print axioms LeanUrat.MovesU.RegPin.detFull_ne_zero
#print axioms LeanUrat.MovesU.blockZeroPole
#print axioms LeanUrat.MovesU.mem_blockZeroPole
-- O5CountingB (MovesU/O5CountingB.lean:44–90, the §3 line pin)
#print axioms LeanUrat.MovesU.surj_of_injOn_checksum
#print axioms LeanUrat.MovesU.bijOn_of_injOn_checksum
#print axioms LeanUrat.MovesU.card_eq_of_injOn_checksum
-- UE_vtxUpper (HC2/UE_vtxUpper.lean:70–153, the §3 line pin)
#print axioms LeanUrat.MovesJ.UE.childW_ge_estar_mul_w
#print axioms LeanUrat.MovesJ.UE.regrade_ge_estar_mul_w
#print axioms LeanUrat.MovesJ.UE.vtx_m6bi_n4upper
#print axioms LeanUrat.MovesJ.UE.vtx_htUpper_div
