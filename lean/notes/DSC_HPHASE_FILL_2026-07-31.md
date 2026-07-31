# D-SC H-PHASE FILL RECORD (2026-07-31)

The H-phase fill of the eleven D-SC carrier-layer slot bodies, executed behind
the Q5 Codex re-review **ACCEPT** (2026-07-31, `/tmp/bridge/ratify/dsc_review2.jsonl`;
design record: DESIGN ADDENDUM D-SC + REVISION 2 in
`lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md`).  Per the E-phase contract, each
fill is a transcription of the file-header DISPLAYED TARGET as ratified — no
statement design happened in this round.

## What was filled (11 bodies, 0 deviations)

* `SlotsG16_sitedLaws.lean` — `SitedSlot_rel2a` (a1 ∧ a2 ∧ a3 ∧ a5 ∧ a6, the
  four G19b probe legs conjoined in header order), `SitedSlot_rel2b`,
  `SitedSlot_rel2d` (incl. the R-17 fourth conjunct), `SitedSlot_rel2e` (the
  REVISION-2 form: (e1) ∧ (e4 unique agreement) ∧ (e5 coverage+determination at
  `S.Tj`) ∧ (e3 `Slot_rel1` + MASS = ENTRY pinned at `S.Tj`)).
* `SlotsG17_rel3Display.lean` — `SitedSlot_rel3` (population ∧ coverage ∧
  per-leg certification/keying/consumption-tie, R-19/R-20 form).
* `SlotsG18_relPack.lean` — `RelRow_rel1/rel2a/rel2b/rel2d/rel2e/rel3`: the
  ∀-closures over `(RP.fam p).mem` (rel3: over `p` alone) of the audited slot
  Props at the supplied `RelCarrierPack`, exactly as the G18 header displays;
  no content beyond the closure (the header's G4–G10 mention is the G13′
  consumption shape, not row content — nothing added).

BYTE-FIDELITY CHECK (mechanical): token-level comparison (comments/whitespace
stripped) of each filled body against the compiled G19b elaboration probes —
`rel2b`/`rel2d`/`rel2e`/`rel3` EXACT; `rel2a` = the four probe legs verbatim in
header order.  `SitedSlot_rel2e`/`SitedSlot_rel3` therefore also coincide with
G19c's probe-local copies (G19b probe 7 = `ProbeTarget_rel2e`, probe 8 =
`ProbeTarget_rel3`).  Where the G16 header's (a1) prose lists its three
conjuncts in a different order than the compiled probe, the COMPILED G19b
elaboration (what the Q5 audit reviewed) was taken as the ratified byte form.

## IB-G19b hygiene gate (run BEFORE the fills) — PASS

Re-ran the G2 closure analysis (BLOCKED record, `SlotsG2_relFamily.lean:200–224`)
at the 11 slot signatures:

* (a) NO ∀/∃ over carrier-supplied data inside any body beyond the displayed
  targets: every carrier (`S`, `SD`, `CI`, `tableConv`, `consumed`, `Fam`,
  `RA`, `CD`, `RP`) is a bound parameter; internal quantifiers range only over
  ELEMENTS of supplied carriers (`∀ W ∈ CI.C.V.events`, `∀ f : S.Cont`,
  `∀ T ∈ consumed`, `∀/∃ l : CD.Leg` — the ratified R-20 coverage shape).
  Fills transcribe the compiled probes, so nothing new could enter.  The G18
  rows close over the SUPPLIED family only (the G2 junk-site ∀-falseness
  ranged over abstract sites; does not apply).
* (b) each slot FALSE at its designated degenerate (the G19c class): compiled
  pre-fill in G19c against byte-faithful copies; re-proved post-fill against
  the CANONICAL definitions (below).
* (c) True-escape dead at the G18 rows: rows are named defs pinned to
  `Slot_rel1`/`SitedSlot_*` at the caller's `RelCarrierPack` binder — no bare
  instantiation point; row-level canonical falsifiers compiled (below).

## Falsifier re-point (IB-G19a degenerate class) — ALL CLOSED, 0 sorry

NEW `SlotsG19d_canonFalsifiers.lean` (G19c untouched except a doc-only fence
update pointing here), against the CANONICAL definitions:

* `sitedSlot_rel2e_refuted_at_empty_consumed` — ¬slot at `consumed = ∅`.
* `sitedSlot_rel2e_refuted_at_trivial_tableConv` — ¬slot at `fun _ => True`.
* `sitedSlot_rel2e_refuted_at_two_elements` — ¬slot at two distinct consumed.
* `sitedSlot_rel3_refuted_at_empty_pack` — ¬slot at `IsEmpty CD.Leg`.
* ROW-LEVEL: `relRow_rel2e_refuted_at_empty_consumed`,
  `relRow_rel2e_refuted_at_trivial_tableConv`,
  `relRow_rel3_refuted_at_empty_pack` — a `RelCarrierPack` degenerate at any
  single family site refutes the whole row.

No REVISION-2 regression: every canonical falsifier closed on the first
attempt.  Axiom footprints of all seven: `[propext, Classical.choice,
Quot.sound]` (Lean-core only).

## Build record

`lake env lean` green per touched module (G16, G17, G18, G19b, G19c, G19d);
`lake build LeanUrat.MovesU.SlotsG18_relPack` and
`lake build LeanUrat.MovesU.SlotsG19d_canonFalsifiers` green (8570/8571 jobs).
Sorry census on G16/G17/G18/G19d: **0 sorry tokens** (two doc-comment mentions
of the word remain, in G16's historical E-phase quote and G19d's header).  The
only `sorry` warnings in the build are the four UNTOUCHED G2 BLOCKED records
(`Slot_rel2a/b/d/e` in `SlotsG2_relFamily.lean`), which stand as compiled
failure evidence per the D-SC contract.  Capstone path untouched (nothing
imports the D-SC modules).

## What remains open (unchanged by this round)

IB-G19a value-level falsifiers (prerequisites listed in G19c's header);
IB-G13′ (`theoremU_bridged′`) behind escalation E-1; the [3]/MovesS export,
[4]'s pack population (Q15/E-3), and wave-D's instances — the discharge
suppliers, per REVISION 2 finding 6.
