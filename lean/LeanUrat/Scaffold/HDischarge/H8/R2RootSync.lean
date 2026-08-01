/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-! # H8-R2 (documentary) — ROOT (H8)-row re-scope spec, executed as a DRAFT
for the ROOT owner

**Unit**: H8-R2, `lean/blueprints/HDISCHARGE_H8.md` §6 + unit table
("(documentary) | ROOT (H8)-row re-scope spec | R1 + waves | orchestrator").
**This file contains NO declarations** — it is the durable record of the
ROOT-sync execution. STATEMENT-FENCE RECORD: the blueprint pins NO Lean
statement for H8-R2 (documentary row; no file path assigned — this filename
is synthesized per the R1Adjudication precedent). EXECUTION BOUNDARY: the
ROOT edit itself (`docs/ROOT_ASSEMBLY_2026-08-02.md` §3.1, the (H8) row) is
a ledgered revision with its OWN VC pass, which this unit may NOT perform
(the blueprint: "this blueprint does not touch ROOT"; the dispatch forbids
edits outside `lean/LeanUrat/Scaffold/`). This unit VERIFIES the firing
conditions and DRAFTS the delta; the ROOT owner executes.

## §A. Firing-condition ledger (verified this session)

§6's condition: "after waves 0–2 land green and H8-R1 records its
adjudication". BOTH HOLD — and two units landed BEYOND it:

| unit(s) | commit | status |
|---|---|---|
| H8-D0 `CutDefs` (wave 0) | a04e3a8 | landed |
| H8-A1 `CutFirst` + H8-A3 `Lemma33` (wave 1a) | 0d960e5 | landed |
| H8-A2 `CutPartition` (wave 1b) | f464f90 | landed |
| H8-B1 `SiteExpCut` + H8-B2 `CutSeam` + H8-G1 `ToyGate` (wave 2) | 1786ce6 | landed |
| H8-B3 `CutExtract` (wave 2, the C-1/C-2/C-5 unit) | 1cb9cab | landed — BEYOND the firing condition |
| H8-C1 `KCutReduce` (wave 3) | ff17323 | landed — BEYOND the firing condition |
| H8-R1 `R1Adjudication` (documentary wave A) | 951b30c | adjudication ON FILE |

Green re-verified this session: `lake build` of
`LeanUrat.Scaffold.HDischarge.H8.{KCutReduce, ToyGate, R1Adjudication}`
(covering the full H8 import graph) — "Build completed successfully
(8667 jobs)"; `grep sorry` over `Scaffold/HDischarge/H8/` = ZERO hits; one
pre-existing style warning only (`ToyGate.lean:161` `show` linter). Axiom
footprints checked via `#print axioms` this session — ALL Lean-core
`[propext, Classical.choice, Quot.sound]` — for: `firstEntAbove_unique`,
`read_cut_exhaustive`, `shallow_block_disjoint`, `block_block_disjoint`,
`bdy_display`, `seriesSum_cut`, `seriesSum_cut_conv`, `siteExp_cut`,
`fiber_count_cut`, `toy_cut_display`, `cut_injective`, `typemult_cut`,
`cutFamily_countable`, `kcut_reduce`.

H8-R1's recorded verdicts (`R1Adjudication.lean`, Codex fresh-context):
(vi-a) FAIL, (vi-b-1) NO (combinatorial legs individually DEMONSTRATED;
residues = ROUTING display + the (1b) consumer-bijection level), (vi-b-2)
NO. Per §2.5's PRE-REGISTERED disposition rule: **NO retirement** — the
(H8) row PERSISTS at the §6 reduced scope; the O-11 r3 serving map
"CUT-WD ← D-14 + CU-3" may NOT be re-pointed as demonstrated.

HONESTY GATE, displayed for the ROOT owner's VC pass: the H8 Lean units are
machine-checked (the compiler is the verifier for Lean content) but NO
unit-level hostile pass has run on the prover fan-out — the blueprint's own
fold note ("the prover fan-out's own hostile pass is the next gate") stands
un-executed. The only adversarial record is the blueprint-level Codex review
(§7, VERDICT REVISE, all folded) and R1's adjudication run.

## §B. The governing display spec (blueprint §6, VERBATIM)

> (H8) = (K-CUT), REDUCED (blueprint `lean/blueprints/HDISCHARGE_H8.md`):
> members (K-CUT-1) at level (1a), (K-CUT-2), and the (†)-regroup of
> (K-CUT-3) are PROVED Lean-core once waves 0–2 land
> (`Scaffold/HDischarge/H8/` — first-entrance uniqueness,
> exhaustive-exclusive read ownership with the (BDY) boundary law, the
> count-form and series-form regroupings incl. M04 Lemma 3.3 as
> `seriesSum_cut_conv`), killing the G-2 falsifier channels at the ownership-
> partition level; the row's remaining content is (a) the extraction layer
> H8-B3 (the concrete (Ŝ,(D_ε)) constructions + cut-map injectivity =
> (K-CUT-1) level (1b) — in-blueprint open WORK) and (b) the THREE-field seam
> `VTreeCutSeam`:
> (K-CUT-s) entrance-predicate cell-data supply [owner: CTS-M(i)/(iii)/CL-13,
> (H1)-adjacent census rows], (K-CUT-g) graft completeness [owner: the
> D-14 + CU-3 + REL.2 arc; charge-(vi) record at H8-R1], (K-CUT-m) measured
> mass tie [owners: (H7)/sibjc TREE-EXP rows + [2r]/CL-8 + O-1/O-3 count-tie].
> No formal bridge to the M04 consumer exists until H8-B3 + the typed seam
> re-keys land (H8-C1); that absence is displayed, not elided.
> Consumption sites unchanged (Step 18 K1, clause (R); clause (UB) at q ↦ q^δ).

## §C. Landed-state deltas (the spec was conditional on waves 0–2 only;
B3 + C1 have since landed — transcribing §B verbatim would now UNDERSTATE)

* **DELTA 1 (clause (a) discharged in its forward half).** H8-B3 landed
  (`CutExtract.lean`, design (a) per its in-file design-gate record): the
  concrete constructions `shallowDataOf`/`blockDerivOf`/`cutOf`, cut-map
  injectivity `cut_injective` (up to the corpus `VTree.ext` tuple), the
  conformance clauses (`cut_keying`, `blockDerivOf_below`,
  `blockDerivOf_cone`, `haltsOf_leafLaw`/`nsOf_leafLaw`, `typemult_cut`),
  and the countability transport `cutFamily_countable` — (K-CUT-1) level
  (1b)'s FORWARD direction, PROVED Lean-core. The Equiv's missing half is
  exactly graft completeness (K-CUT-g): hypothesis-grade, per R1's (vi-b-2)
  NO.
* **DELTA 2 (the "no formal bridge" sentence is stale).** H8-C1 landed
  (`KCutReduce.lean`): the bridge to the M04 consumer EXISTS as the
  CONDITIONAL display theorem `kcut_reduce` — GIVEN the typed re-keys (the
  `KCutReKeys` structure's binder rows + `graft`/`graft_cut`/`cut_graft`/
  `mass_eq`), the σ fiber series equals the shallow convolution of measured
  block totals, the exact Step-18 K1 form. Every re-key is an UNPINNED
  named [M]-grade assumption with owners unchanged; `supplyDec` deliberately
  UNDER-types (K-CUT-s) (per-node-decidability face only); NOTHING in C1
  discharges a seam field. The residual conditionality is now TYPED and
  binder-displayed instead of opaque-Prop — the C-3/C-5 cure, landed.
* **R1 fold.** The (K-CUT-g) owner clause gains R1's verdict: charge (vi)
  ADJUDICATED — (vi-a) FAIL (no retirement; serving map not re-pointable),
  (vi-b-2) NO (graft completeness underivable from on-file displays).

## §D. The composed replacement row text (the draft the ROOT owner executes
at `docs/ROOT_ASSEMBLY_2026-08-02.md` §3.1, (H8) row, Status column)

> Status: REDUCED (blueprint `lean/blueprints/HDISCHARGE_H8.md`; all 8 Lean
> units + 2 documentary units LANDED, green + Lean-core verified at
> `Scaffold/HDischarge/H8/R2RootSync.lean`). PROVED Lean-core
> (`lean/LeanUrat/Scaffold/HDischarge/H8/`): (K-CUT-1) level (1a) —
> first-entrance uniqueness (`firstEntAbove_unique`) + exhaustive-exclusive
> read ownership with the (BDY) boundary law (`read_cut_exhaustive`,
> `shallow_block_disjoint`, `block_block_disjoint`, `bdy_display`) — killing
> the G-2 falsifier channels at the ownership-partition level; (K-CUT-1)
> level (1b) FORWARD half — the concrete (Ŝ,(D_ε)) extraction + cut-map
> injectivity (`cutOf`, `cut_injective`) + conformance + countability
> transport; (K-CUT-2) count-form (`siteExp_cut`, `fiber_count_cut`); the
> (†)-regroup of (K-CUT-3) incl. M04 Lemma 3.3 as `seriesSum_cut_conv`; the
> positive gate (`toy_cut_display`). The formal bridge to the M04 consumer
> EXISTS as the CONDITIONAL theorem `kcut_reduce` (Step 18 K1's exact form);
> its binder rows are the row's ENTIRE remaining content, each typed,
> [M]-grade, UNPINNED: (K-CUT-s) entrance-predicate cell-data supply [owner:
> CTS-M(i)/(iii)/CL-13, (H1)-adjacent census rows; enters `kcut_reduce` only
> at its under-typed `supplyDec` face], (K-CUT-g) graft completeness =
> `graft`/`graft_cut`/`cut_graft` [owner: the D-14 + CU-3 + REL.2 arc;
> charge (vi) ADJUDICATED at H8-R1: (vi-a) FAIL ⇒ NO retirement, serving map
> NOT re-pointable as demonstrated; (vi-b-2) NO], (K-CUT-m) measured mass
> tie = `mass_eq` + the `W`/`weight` rows [owners: (H7)/sibjc TREE-EXP rows
> + [2r]/CL-8 + O-1/O-3 count-tie], plus the [3t]↦`VTree` realization +
> verdict-keying rows (`real`/`verdict_key` — TREE-N/[3t] seam territory).
> Consumption sites unchanged (Step 18 K1, clause (R); clause (UB) inherits
> at q ↦ q^δ). Retirement route: charge (vi-a) FAILED — the row PERSISTS at
> this reduced scope; no [V]-debt retirement.

## §E. Execution discipline (for the ROOT owner)

1. The ROOT's end-to-end acceptance counter stood at ZERO of 2 after VC13 →
   REVISION 12 (VC14 next, per the ROOT's own §3.2 ledger read this
   session). Executing §D is a TEXT CHANGE: fold it into the next ledgered
   revision; the counter discipline applies (it does not advance on this
   edit); the revision takes its own VC pass, which should check §C's two
   deltas against the landed declarations named there.
2. The one-line `RootHyps` extension (`h8_kcut : Prop` field) remains the
   ORCHESTRATOR-owned SHARED edit across the nine leads — re-flagged here,
   NOT landed by any H8 unit.
3. The un-run unit-level hostile pass on the H8 fan-out (§A honesty gate)
   is the division's next owed gate; it does not block the ROOT sync (§6's
   firing condition names landings + R1 only) but should be priced in the
   VC pass.
-/

namespace LeanUrat.Scaffold.HDischarge.H8.R2
-- Documentary unit: intentionally empty. See the module docstring.
end LeanUrat.Scaffold.HDischarge.H8.R2
