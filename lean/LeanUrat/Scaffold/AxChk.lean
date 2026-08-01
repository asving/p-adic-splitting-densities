/-  Scaffold/AxChk.lean — BP_VI §1.5 axiom-census extension (standalone; NOT
    imported by anything; `AxChk_baseline.lean` untouched).
    Gate: `lake env lean LeanUrat/Scaffold/AxChk.lean` at every division
    checkpoint. Acceptance bar: Lean core only (`propext`, `Classical.choice`,
    `Quot.sound`) for EVERY row; a regression is stop-the-line.
    Units: VI-A1 (scaffold VI-H*/VI-S*/VI-B* — landed below), VI-A2 (VI-N* +
    gate wrappers — BLOCKED, rows fenced below), VI-A3 (theoremU/bridge + OM
    quarry — landed below), VI-A4
    (ksub/O12PoleFree/RegPFinite/O5CountingB/UE_vtxUpper enumeration).
    VI-A1 census rows (finite, declaration-by-declaration; no wildcards) —
    every named VI-H*/VI-S*/VI-B* theorem of the landed scaffold core
    (waves VI-0/VI-1). Completeness record: VI-B3 (`SlotAssignment`) is parked
    BLOCKED as a comment (CorpusBridge.lean:95, binder-interface mismatch
    awaiting blueprint adjudication) and VI-B4 (`rootC_fired_at_slots`) is not
    landed — neither contributes a declaration, so neither has a census row:
      LeanUrat.Scaffold.clauseR_of_clauseUB (VI-H2, Hypotheses.lean) ·
      LeanUrat.Scaffold.trivialRootHyps_ub (VI-H3, Hypotheses.lean) ·
      LeanUrat.Scaffold.RootC_iff_tuple (VI-S3, Spine.lean) ·
      LeanUrat.Scaffold.rootC_of_theoremU (VI-B1, CorpusBridge.lean) ·
      LeanUrat.Scaffold.rootC_fired (VI-B2, CorpusBridge.lean)
    VI-A2 census rows (finite, declaration-by-declaration; no wildcards) —
    every named VI-N* theorem and its four named gate wrappers (BP_VI §1.4/§1.5):
      LeanUrat.Scaffold.AnchorN2.anchor_n2 (VI-N1) ·
      LeanUrat.Scaffold.AnchorN2.anchor_n2_drainage (VI-N2) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_value_inert2 (VI-N3) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_split_q3 (VI-N3) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_inert_q3 (VI-N3) ·
      LeanUrat.Scaffold.AnchorN2.anchor_v2_sigma_separation (VI-N3)
    BLOCKED(VI-A2): none of the six targets exists at HEAD (2026-08-01).
    VI-N1 is BLOCKED at the blueprint level (AnchorN2.lean module header:
    §1.4 applies `Nonempty` to a proof TERM — a category error needing
    statement sign-off), VI-N2/VI-N3 are undelivered, and a compile probe
    (`lake env lean`, 2026-08-01) shows their §1.4 statements fail
    identically: `Nonempty LeanUrat.OM.SeriesAssembly.hExhaust_n2` and
    `Nonempty LeanUrat.OM.RealInstanceV2Gates.gate_v2_value_inert2` both
    give "has type … of sort `Prop` but is expected to have type Sort ?u".
    The fenced rows below are this unit's exact content; when the anchors
    land, add `import LeanUrat.Scaffold.AnchorN2` and delete the leading
    `-- `. No substitute rows (e.g. the underlying `gate_v2_*` corpus
    theorems) are censused here — substitution would silently weaken the unit.
    VI-A3 census rows (finite, declaration-by-declaration; no wildcards):
      LeanUrat.MovesU.theoremU · LeanUrat.MovesU.theoremU_fired ·
      LeanUrat.OM.UniformCapstone.montes_uniform_n2 ·
      LeanUrat.OM.RealInstanceV2.montes_unconditional ·
      LeanUrat.OM.SeriesAssembly.hExhaust_n2 ·
      LeanUrat.MovesV.skeleton_finite ·
      LeanUrat.MovesD.runRealizerExists_zmod ·
      LeanUrat.MovesJ.HK11a.sigmaV_vertexLaw  -/
import LeanUrat.Scaffold.Hypotheses
import LeanUrat.Scaffold.Spine
import LeanUrat.Scaffold.CorpusBridge
import LeanUrat.MovesU.U10_theoremU
import LeanUrat.MovesU.BridgeMk
import LeanUrat.OM.UniformCapstone
import LeanUrat.OM.RealInstanceV2
import LeanUrat.OM.SeriesAssembly
import LeanUrat.MovesV.SkeletonFinite
import LeanUrat.MovesD.R7_runRealizer
import LeanUrat.HC2.HK11a_vertexTransport

-- ## VI-A1: scaffold-core census (every named VI-H*/VI-S*/VI-B* theorem)
#print axioms LeanUrat.Scaffold.clauseR_of_clauseUB
#print axioms LeanUrat.Scaffold.trivialRootHyps_ub
#print axioms LeanUrat.Scaffold.RootC_iff_tuple
#print axioms LeanUrat.Scaffold.rootC_of_theoremU
#print axioms LeanUrat.Scaffold.rootC_fired

-- ## VI-A2: VI-N* anchor census (every named VI-N* theorem + its four named
-- gate wrappers) — BLOCKED(VI-A2): no target exists at HEAD (see header for
-- the probe record); rows fenced, unfence when VI-N1–VI-N3 land.
-- #print axioms LeanUrat.Scaffold.AnchorN2.anchor_n2
-- #print axioms LeanUrat.Scaffold.AnchorN2.anchor_n2_drainage
-- #print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_value_inert2
-- #print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_split_q3
-- #print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_inert_q3
-- #print axioms LeanUrat.Scaffold.AnchorN2.anchor_v2_sigma_separation

-- ## VI-A3: theoremU/bridge + OM quarry census
#print axioms LeanUrat.MovesU.theoremU
#print axioms LeanUrat.MovesU.theoremU_fired
#print axioms LeanUrat.OM.UniformCapstone.montes_uniform_n2
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
#print axioms LeanUrat.OM.SeriesAssembly.hExhaust_n2
#print axioms LeanUrat.MovesV.skeleton_finite
#print axioms LeanUrat.MovesD.runRealizerExists_zmod
#print axioms LeanUrat.MovesJ.HK11a.sigmaV_vertexLaw
