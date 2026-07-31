/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE10 — the sharpening audit (the area's exit report; RECORD UNIT)

BRIDGE CAMPAIGN unit **KE10** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E + §4 KE10; deps: ALL KD/KE
outputs). E-PHASE STATEMENT MODULE — the record skeleton; the table is filled
at area exit, feeding the CL ledger.

THE DUTY: tabulate, per X-kernel Prop, which n=3-sealed layer now has a
GENERAL-n theorem (KD/KE outputs) vs a NAMED OBSTRUCTION — the "general-n
exhaustion sharpening" is exactly this conversion, never widening any
statement (blueprint §3.E closing paragraph). Rows to be tabulated at exit
(the kernel surface of MovesX/Defs.lean §D, plus the KD-owned rows):

* `NsNullP`            — KE1  (port; conditional on the per-fiber lump chains)
* `X2AffP`             — KE2  (attempt behind gate KE11)
* `X2CapP`             — KE3  (attempt behind gate KE11)
* `X2TailsP`           — KE5  (attempt behind two-phase gate KE4)
* `X2BridgeP` clause 1 — KE6  (attempt behind gate KE12)
* `X2BridgeP` clause 2 — KE7  (assembly; null legs KE1/XF10/XG2d)
* `X1aAlignP ⟨true,false⟩` (ALIGN-inc) — KE8 (attempt behind gate KE13)
* `X2ProgressP` linear — KE9  (deferrable; √N form PROVED at XD4)
* `WeightChargeT4P`/`WeightChargeFullP` — KD3/KD4/KD10 (owner: cluster KD)

RECORDED RESOLUTION: the blueprint marks this "routine-opus, record-only"; the
E-phase deliverable is the typed table skeleton below (a `def` to be filled
with the literal rows at exit — the one `sorry` is the unfilled record, not a
mathematical gap). Per-row status vocabulary matches the blueprint fence: a
stalled attempt exits as a SHARPENED OBSTRUCTION RECORD, never a silent sorry.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- KE10 status vocabulary — the disposition of one X-kernel Prop at area exit:
a general-n theorem (unconditional over the context), a conditional theorem
(named ⚑ hypothesis surface, as ratified), a named obstruction record (the
fallback deliverable of a stalled attempt), a still-open attempt, or deferred
(Q3-genre: out of the campaign graph). -/
inductive SharpStatus
  | generalTheorem
  | conditionalTheorem
  | namedObstruction
  | openAttempt
  | deferred
  deriving DecidableEq, Repr

/-- **KE10 — the audit table** (record unit; deps: ALL of KE1-KE9 + the KD
cluster). FILLED 2026-07-31 at area exit: one row per kernel Prop listed in the
module docstring, each `String` naming the Prop and its discharge artifact, the
`SharpStatus` its disposition. -/
def sharpeningAudit : List (String × SharpStatus) :=
  [ ("NsNullP — KE1 (nsNullP_of_lumpChains); conditional on the per-fiber lump chains",
      .conditionalTheorem),
    ("X2AffP — KE2 (x2Aff_of_thresholdStep); conditional on the threshold-step law",
      .conditionalTheorem),
    ("X2CapP — KE3 (x2Cap_of_capStep); conditional on the cap-step law",
      .conditionalTheorem),
    ("X2TailsP — KE5 (x2Tails_of_route); conditional on the tails route",
      .conditionalTheorem),
    ("X2BridgeP clause 1 — KE6 (x2Bridge_cover); unconditional Undec-cover",
      .generalTheorem),
    ("X2BridgeP clause 2 — KE7 (x2Bridge_assembled); null legs KE1/XF10/XG2d, 2≤n",
      .conditionalTheorem),
    ("X1aAlignP inc — KE8 (x1aAlignInc_of_orderAccounting); conditional on order accounting",
      .conditionalTheorem),
    ("X2ProgressP linear — KE9 (x2Progress_of_pricing); conditional on ProgressPricing ⚑ (√N form general at XD4 x2hypAssembled)",
      .conditionalTheorem),
    ("WeightChargeT4P/WeightChargeFullP — KD10 (weightChargeFull_of_ladderCap); conditional on the ladder-cap law",
      .conditionalTheorem) ]

end LeanUrat.MovesX
