# Verdict GCW1 — the GC-13 wiring law SIGNED (A-I.5), the DT0 demand wired sitewise, GCW-2 closed

Unit GCW1 (Fable), 2026-08-27.  Charge: node GCW-1 of
`docs/in-progress/GC13_WIRING_2026-08-27.md` (GCW-0's decision record + the orchestrator's
F2=P2 adjudication inherited; print-read basis `runs/wave-b/verdict_GCW0.md`).
No commit was made.

## What was signed (leanspec AMENDMENT A-I.5, `leanspec/Leanspec/ChapI.lean`)

* **NODE I.10c `LeanspecI.GC13Wiring`** — GCW-0's decision-record statement VERBATIM (the
  sitewise scalar-read relation at the abstract D.44 surface: `R (N.n (s*q)) =
  φ (I.Rgr (e'*(s*u')) (I.chainNormBelow r (s*u')))` on `1 ≤ s ≤ f'`; grade = OPEN-DICT-2's
  full-current clearing, normalizer = the decided below-current `n̂_i`).  Dated comments cite
  GCW-0's print-read (EFF.T3.21's "Define", GENTOW2 S5.1/S5.2) and FGCW's underdetermination
  certificates — `IFC2.s2_hread_refuted_at_landed_exports` (refutation half) and
  `IFC2.s2_gentowW_of_read_one` marked as the **D-D12-FENCED freedom half, NOT SUPPLY**.
* **NODE I.10d `LeanspecI.WiredGentowDemand`** — the amended DT0 demand, SITEWISE:
  `GC13Wiring N q R I φ ∧ GentowW A q R w` at one consumed live level, at the guard's own
  `(N, q j, R j, A j, w j)` exports and the supplied calculus/receiver.  A per-site
  STRENGTHENING (gate (20) pins both projections) — nothing weakened.
* **The fork adjudication enacted**: the SUPPLIER gains the wiring leg (P2); the
  `CanonicalDeepTwistConfig` guard-extension fork is REJECTED (gate-(a) change of the signed
  socket + chapter-C coupling).  Socket, `CapstoneHypotheses` field list, and all previously
  signed declarations are BYTE-UNCHANGED; the `deepTwist` field carries an [A-I.5]
  interpretive rider only.
* Census: `#axiom_core LeanspecI.GC13Wiring` / `LeanspecI.WiredGentowDemand` added (both
  PASS — the enforced guard, not an eyeballed print); gate examples (18)–(20) executed;
  header STATE UPDATE + census-table brackets recorded.

## What was landed (`leanfinal/Uniformity/ChapI/IFC3.lean`, 10 declarations)

Twins byte-identical to the signed binder blocks, plus:

* **GCW-2 CLOSED** (it was within the signing round's reach): `s2Mu3_gentowWWindow_of_wiring`
  replaces IFC2's `hread` binder by the `GC13Wiring` leg at the plug point —
  `hwire.read_norm 1 le_rfl le_rfl` IS the `hread` argument, no rewrite/cast; general form
  `gentowWWindow_of_wiring` upgrades IFC1's translation lemma the same way
  (`hwire.read_norm` slots in as the whole `hread` premise).
* `s2_wiring_forces_read_one` — GCW-3's assembly datum: a law-satisfying S2 read is `1` at
  the level-2 ladder point.
* `s2_wiring_refuted_at_landed_exports` — the anti-cook tooth (blueprint falsifier §3.1
  survives the signing): the law is FALSE at the landed witness's own zero-read exports, so
  no "it's rfl" discharge exists; GCW-3 must RE-assemble.
* `gc13Wiring_vacuous_of_f'_zero` + `wiredGentowDemand_iff_of_f'_zero` — the fabricability
  fences: at `f' = 0` the law is vacuous and the wired demand collapses to the unwired one.

## The honest BLOCKED-BECAUSE (recorded in all three artifacts)

**No UNIVERSAL wired `DeepGentowSupplier` twin is landed, and none is statable honestly
today.**  Missing mechanism, named: a per-level calculus/receiver EXPORT from the arising
witness (the `WleCleared` truncation exporter — blueprint §4, FIELDLIST §8; the DT0 analogue
of W0's missing weld-site exporter).  Fabricability analysis, anchored on the `f' = 0`
fence: guard-side or `∃`-bound level sites collapse the wired supplier to the refutable
unwired one through a junk site; `∀`-bound sites are false at wrong calculi; a def-parameter
site family has the wrong dependency shape (the canonical sites depend on the witness hidden
in the guard's existential).  IFC0's `DeepGentowSupplier` is byte-untouched and RETIRED AS A
CAMPAIGN TARGET — it stays GCW-6's tension record (zero-read depth-`≥ 4` witness refutes it;
stop-the-line inherited by the deep-witness campaign).

## VAUD coordination (noted, NOT enacted)

`verdict_VAUD.md`'s parallel IFC0 finding (L0's `LadderVarthetaSupplier` needs live-index
range-restriction bound to the same witness; `CanonicalLadderLiveAt` proposed in
`scratch/VAUD_probe.lean`) is cross-referenced in IFC3's module doc and the A-I.5 record; it
rebinds a capstone-field range and stays owner-gated.  Neither unit edited `IFC0.lean`.

## Review rows

`docs/REVIEW_QUEUE_2026-08-26.md`: Tier 2 row **A-I.5** (top, newest-first) + Tier 3 row for
IFC3's flagged declarations.  Blueprint updated with the `[GCW-1] ENACTED` record.

## Validation (AxChk)

```text
leanfinal$ lake env lean Uniformity/ChapI/IFC3.lean     # exit 0
leanspec$  lake env lean Leanspec/ChapI.lean            # exit 0, 0 errors, AXCHK census (72 guards) all pass
```

`#print axioms`, all ten IFC3 declarations (`GC13Wiring`, `gc13Wiring_vacuous_of_f'_zero`,
`gentowWWindow_of_wiring`, `s2Mu3_gentowWWindow_of_wiring`, `s2_wiring_forces_read_one`,
`s2_wiring_refuted_at_landed_exports`, `WiredGentowDemand`, `.wiring`, `.gentowW`,
`wiredGentowDemand_iff_of_f'_zero`):
`[propext, Classical.choice, Quot.sound]` — Lean core exactly, zero `sorry`, zero new axiom.
The leanspec twins are additionally guarded by the enforced `#axiom_core` census (a non-core
footprint is a build failure, not a report line).

## Files delivered

* `leanspec/Leanspec/ChapI.lean` — AMENDMENT A-I.5 (6 hunks: header STATE UPDATE, two census
  brackets + AXCHK-count bracket, NODES I.10c/I.10d section with gates (18)–(20), `deepTwist`
  rider, two `#axiom_core` lines)
* `leanfinal/Uniformity/ChapI/IFC3.lean` — NEW
* `docs/REVIEW_QUEUE_2026-08-26.md` — Tier 2 A-I.5 row + Tier 3 IFC3 row
* `docs/in-progress/GC13_WIRING_2026-08-27.md` — the `[GCW-1] ENACTED` record
* `runs/wave-b/verdict_GCW1.md` — this file

NEXT (not this unit): GCW-3 (re-assemble S2 with a law-satisfying read; prove `GC13Wiring`
at that witness's own exports; fire `s2Mu3_gentowWWindow_of_wiring`), GCW-4/GCW-5 (θ beyond
`s = 1`; the `s = 0`/tail clauses), and the `WleCleared` exporter for the universal wired
supplier (later recorded amendment).
