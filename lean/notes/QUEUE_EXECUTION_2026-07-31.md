# QUEUE EXECUTION LOG — 2026-07-31 (append-only)

Per-item execution records for THE CONSOLIDATED SIGN-OFF QUEUE + QUEUE
ADDITIONS of notes/BRIDGE_ADJUDICATIONS_2026-07-30.md (Asvin sign-off
2026-07-31, all 21 items at preferred options). Each executing agent appends
its own section atomically; never edit another item's section.

## Item 20 — KA4c ka4c_nsFiberUnion_null (executed 2026-07-31, agent: item-20)

AUTHORIZATION: Asvin 2026-07-31 verbatim "Sign-off granted on all 21 items as
preferred, execute the queue" (BRIDGE_ADJUDICATIONS_2026-07-30.md, ASVIN
SIGN-OFF block; preferred option for item 20 = add the 2 ≤ n hypothesis unless
frac_empty demonstrably ripples less).

DECISION CHECK (the adjudicated first step, `rg XCtx` census):
- XCtx constructions in the build graph: ZERO — every module (Kernels/KA4c,
  Kernels/E0Route, Kernels/WeightChargeRed, MovesX/KE1-KE9, XG2*, XG3, XD1,
  XF10, MovesU/SlotsG12b) takes `C : XCtx n p` as a PARAMETER; the one real
  instance is the open Phase-B XFamily inhabitation obligation.
- BUT two note-side compiled refutation witnesses CONSTRUCT XCtx and would
  break on a new field: notes/XE2_refutation_witness.lean:73 (`ctx0`),
  notes/XE3_REFUTATION_2026-07-27.lean:106 (`ctxD`).
- AND three standing in-file adjudications freeze the interface — "never a
  new `XCtx` field": MovesX/KE1.lean:25, KE2.lean:20-23, KE3.lean:21.
- Both null anchors already require 2 ≤ n: XF10 `discZeroNull (h2 : 2 ≤ n)`,
  XF8 `tailZero`; the XG3.lean:31 precedent derives `frac ∅ = 0` exactly by
  `frac_mono` into the null `discZero` under `hn : 2 ≤ n`.
- Downstream Lean consumers of ka4c_nsFiberUnion_null: NONE at HEAD (rg; no
  module imports Kernels.KA4c; `escape_of_x3drain` inlines its own
  Option-reindexed glue anchored on the null InfTree leg, hypothesis-free).
DECISION: 2 ≤ n (the preferred option) — frac_empty ripples strictly MORE
(2 note-side witnesses + 3 frozen-interface rulings + a bigger XFamily
inhabitation obligation), not less.

EXECUTED (LeanUrat/Kernels/KA4c.lean):
- `ka4c_nsFiberUnion_null` gains `(h2 : 2 ≤ n)` (before `C`, the XF10
  convention); import LeanUrat.MovesX.XF10 added.
- Empty-nsIdx corner PROVED: union = ∅ by `Set.iUnion_of_empty`; `frac ∅ = 0`
  by `frac_mono` into `discZero` + `discZeroNull n p h2 C` + `frac_nonneg`
  (the XG3.lean:31 corpus precedent). The BLOCKED-CORNER obstruction record
  is superseded and condensed into the theorem's STATEMENT-REPAIR RECORD
  docstring (in-file record, per rule 5).
- R10 fallback KEPT untouched: `DrainIdent` (the pre-typed named
  identification hypothesis) + both proved seam theorems
  `blockDrain_of_drainIdent`, `escape_of_x3drain`.

VERIFICATION:
- `lake env lean LeanUrat/Kernels/KA4c.lean` GREEN, zero output.
- `lake build LeanUrat.Kernels.KA4c` SUCCESS (8573 jobs).
- #print axioms (fresh oleans): ka4c_nsFiberUnion_null,
  blockDrain_of_drainIdent, escape_of_x3drain ALL Lean-core
  {propext, Classical.choice, Quot.sound}. (First check hit the stale
  pre-repair olean and showed sorryAx — rebuilt, clean.)
- KA4c.lean sorry count: 0. THE ROW CLOSES (census row
  REMAINING_CENSUS_2026-07-31.md:101 = Kernels/KA4c.lean:114 discharged).

M1 HYGIENE (rule 3): no compiled countermodel/probe of the OLD form exists
(the corner was sorried with a prose obstruction record, never refuted by a
leaf module; rg "nsFiberUnion" hits only KA4c + ledger/census notes) — no
leaf note owed.

CAPSTONE PATH (rule 4): not touched — KA4c is a leaf module imported by
nothing; AxChk_baseline diff not required.

NOTE FOR THE ORCHESTRATOR (per the item text): with the row closed,
`DrainIdent`'s named-hypothesis status can be REVISITED — the prover attempt
to construct a `DrainIdent` instance at the real pool from the
SeriesData/XCtx vocabulary is now unblocked as its own unit (it waits on the
same Phase-B XCtx/XFamily inhabitation as everything else; nothing in KA4c
fences it).
