/-
Kernels/KD8 — BP4-c7 E-phase RECORD UNIT (verify-only) for unit KD8: the KD
assembly + fence audit — the (CD)-pinned reading check
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.D fence + §4 KD8; adjudications
per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block; the X1B adjudication =
tasks 57/58, 2026-07-29).

THE FENCE BEING AUDITED (blueprint §3.D, verbatim): "the X1B adjudication
(tasks 57/58) fixed the layer-(i) READING — d_cert counts only certified
nodes, row-0 = no bound certified.  All units here must consume the
(CD)-pinned reading; the refuted over-broad reading is a recorded
countermodel, not a target."

AUDIT DUTY (executed at the VERIFY pass, once KD2-KD5 + KD10 are all on
disk; deps KD2/KD3/KD4 are sibling-cluster units not yet written at this
E-phase write):
  · KD2 (`recentering_vdisc_pos`): population counts via `MovesX.countPop`
    (node-population census) — must NOT consume `dCert`; no reading
    exposure expected.  [E-phase pre-check: pending — file absent.]
  · KD3/KD4 (`weightChargeFull/T4_of_trackCount`): same countPop-only
    surface.  [Pending — files absent.]
  · KD5 (`x3aRoute_of_weightCharge_align`, Kernels/KD5.lean): consumes
    `X1aAlignP n X ⟨true, false⟩` — `dCert` enters ONLY through
    `MovesX.X1aAlignP`, whose `certified`/`dCert` chain
    (MovesX/Defs.lean:98-106) is the (CD)-pinned reading A by the X1B
    adjudication's own re-key.  [E-phase pre-check: CLEAN — the ⟨true,
    false⟩ state is verbatim X3aRouteP's right disjunct.]
  · KD10 (`weightChargeFull_of_ladderCap`, Kernels/KD10.lean): countPop +
    vdisc only; no d_cert consumption.  [E-phase pre-check: CLEAN.]
  · KD6/KD7 (Kernels/KD6.lean, KD7.lean): KeyWeightData/ind/vdisc surface;
    no d_cert consumption.  [E-phase pre-check: CLEAN.]
The verify-pass deliverable: re-run this table against the as-built files,
flip every "pending" to CLEAN/VIOLATION, and record the outcome in the
campaign ledger (a VIOLATION is a stop-the-line fence event).

RECORDED RESOLUTION: KD8 is record-only (no mathematical statement); per
the E-phase discipline it carries a trivial ANCHOR declaration (below, no
sorry) so the unit is buildable and referenceable; the record lives in this
header and is updated in place at the verify pass.

deps: KD2-KD5, KD10 (audit targets).
Build: cd lean && lake build LeanUrat.Kernels.KD8
-/

namespace LeanUrat.Kernels

/-- KD8 (record anchor — verify-only unit): the KD-cluster (CD)-pinned
reading audit record lives in this file's header; this declaration is the
buildable anchor only (record units carry no mathematical statement). -/
theorem kd8_cd_pinned_reading_audit : True := trivial

end LeanUrat.Kernels
