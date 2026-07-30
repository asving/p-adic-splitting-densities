/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG9_m4bConst
import LeanUrat.MovesU.SlotsG10_jcInvHist

/-!
# IB-G11c — non-vacuity audit, SEAM FAMILY (bridge campaign BP1, cluster c12;
E-phase skeleton — PARTIAL, see the blocked record below)

Blueprint: `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (non-vacuity
audit paragraph) + §4 group G (IB-G11c; split of G11 post-Codex finding 11).
Deps per blueprint: IB-G7 (Slot_m1m5Echo), IB-G8 (Slot_x1aDict), IB-G9
(Slot_m4bConst), IB-G10 (Slot_jcInvHist).

THE WAVE-2 DOCTRINE (the audit's charge): every formulated slot Prop must be
FALSE for a degenerate instance the note would reject — a compiled falsifier
per slot, killing the True-instantiation escape recorded at U10's wave-4
boundary paragraph.  The E-phase skeleton states each falsifier as an
∃-degenerate-instance negation with a `sorry` body; the prover owes the
explicit degenerate construction.

PARTIAL AT WRITE TIME (2026-07-30, cluster c12): the seam family is
(m1m5Echo, x1aDict, m4bConst, jcInvHist), but `Slot_m1m5Echo` (IB-G7) and
`Slot_x1aDict` (IB-G8) are owned by a sibling cluster and are NOT on disk —
their falsifiers cannot elaborate and are BLOCKED, recorded in the cluster
report.  When G7/G8 land, the two missing falsifiers go in a NEW file
(new-files-only discipline; this file is not edited).

PROVER SKETCHES (from the slot formulations' failure modes):
* `slot_m4bConst_falsifiable`: a degenerate `CtsMeasured` whose `entInst`
  census READS A HEIGHT COORDINATE of the written shape (e.g. census :=
  hentCode of the written ε) — two `Order0Perimeter`-certified points of one
  listed component with different height slots then give different
  `instCensus` values at a landing cell, refuting the constancy conjunct.
  Care: the degenerate instance must still satisfy `CtsMeasured`'s own laws
  (`ent_card` etc.) — the toy witness `V1_witnessC.Ctoy`-style n = 1 carrier
  is the recommended chassis.
* `slot_jcInvHist_falsifiable`: a degenerate `CellData` whose joint read
  `cellOf (.st H)` depends on the LENGTH of the history H (legal: `cellOf` is
  free per-entrance data, `cell_local` only constrains the box argument) —
  two realized histories with `NodeRetainedKeyEq` last nodes but different
  chain lengths then price the same joint cell differently, refuting the
  cross-multiplied law equality.  The G1-toy diagonal read
  (`branchCellOf es ν := cellOf es`) is the recommended chassis.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

/-- IB-G11c falsifier 1/4 (m4bConst): `Slot_m4bConst` is FALSE at some
    degenerate MovesV measured carrier — the formulated Prop is not
    True-instantiable across all instances (wave-2 doctrine).  Prover: build
    the height-reading census toy (file-header sketch). -/
theorem slot_m4bConst_falsifiable :
    ∃ (n : ℕ) (Cv : MovesV.CtsFamily n) (Sv : MovesV.StepSys n)
      (V : MovesV.CtsMeasured n Cv Sv), ¬ Slot_m4bConst n V :=
  sorry

/-- IB-G11c falsifier 2/4 (jcInvHist): `Slot_jcInvHist` is FALSE at some
    degree n — witnessed by a degenerate history-reading `CellData` inside the
    ∀-quantified instance (wave-2 doctrine).  Prover: build the chain-length
    joint read toy (file-header sketch). -/
theorem slot_jcInvHist_falsifiable :
    ∃ n : ℕ, ¬ Slot_jcInvHist n :=
  sorry

/- BLOCKED (recorded; not elaborable at write time):
   falsifier 3/4 (m1m5Echo) — needs `Slot_m1m5Echo` (IB-G7, sibling cluster);
   falsifier 4/4 (x1aDict)  — needs `Slot_x1aDict`  (IB-G8, sibling cluster).
   Disposition: NEW follow-up file once G7/G8 land (this file stays unedited). -/

end LeanUrat.MovesU
