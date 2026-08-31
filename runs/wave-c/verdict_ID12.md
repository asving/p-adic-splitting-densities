# UNIT ID12 — the three I-D12 capstone fields — VERDICT (FINAL, 2026-08-31)

## Re-grounding

`CapstoneHypotheses n` (`leanfinal/Uniformity/ChapI/I10_I15_I18.lean:164`) is the
hypothesis structure the capstone `UniformityStatement` reduces to inhabiting.  Three of
its fields had no active lane (PROJECT_STATE §4 coverage gap): `windowPinning :
WindowPinningAt n`, `genhnHE : 6 ≤ n → GenhnHEAt n`, `genhnTow1 : 8 ≤ n → GenhnTow1At n`.
Charge: scope the three (definitions, prior partial work, post-blitz reachability), prove
what closes, name the remainders.

## ★ THE HEADLINE — all three fields close at EVERY n, AS SIGNED, and the honest frame

**THE CENTRAL SCOPING FACT: all three carriers are `True`-bodied STUB-STAGE SIGNED
BODIES** (blueprint defect I-D12, BLOCKED-UNTIL-RESOLUTION): `WindowPinningAt n := True`
(I05.lean:93), `GenhnHEAt n := True` (I06.lean:98), `GenhnTow1At n := True` (I07.lean:92).
So the capstone-field kill is REAL but DEFLATIONARY: the fields impose zero marginal
proof obligation on `CapstoneHypotheses n` at any `n` — same mechanical class as the
`jd0`/`genhnBox2` I-D7 placeholders — and closing them certifies NO window pinning, NO
σ-decision, NO tower census.  The coverage gap is an HONESTY-LEDGER gap (the eventual
owner re-sign of the three bodies), not an inhabitation gap.

Landed accordingly in **`leanfinal/Uniformity/ChapI/ID12.lean`** (NEW; imported by
nothing; no landed file touched; IFCG53 untouched):

* §1 the three as-signed suppliers — `windowPinningAt_asSigned (n) : WindowPinningAt n`,
  `genhnHEAt_asSigned (n) : 6 ≤ n → GenhnHEAt n`, `genhnTow1At_asSigned (n) : 8 ≤ n →
  GenhnTow1At n` — each `trivial`, each AXIOM-FREE (`does not depend on any axioms`),
  each named `_asSigned` with a disclosure docstring so no use site can read them as
  certificates (this respects I05–I07's "would dress a triviality as a certificate"
  fence: the names carry the disclosure, and they BREAK BY DESIGN at any re-sign —
  tripwires forcing the re-sign through real proofs).
* §2 **the frontier reduction — the mechanically valuable new theorem**:
  `capstoneHypotheses_of_frontier (n) : NS7Termination → (ladder) → (deepTwist) →
  DecidedSliceAt n → CapstoneHypotheses n` — **Lean-core** — wiring the census blitz's
  two all-`n` closures (`IFC6.menuLawAt_all` for a1, `IFCG52.drainageAt_all` for a2)
  into the capstone for the first time; and `capstoneHypotheses_of_three (n)` dropping
  `ns7` via I01's `ns7Termination_of_cite` — footprint Lean-core + the previously
  declared allowlisted cite `agnprw_termination`, nothing else.
  **Consequence, stated plainly: inhabiting `CapstoneHypotheses n` now reduces,
  machine-checked, to exactly the three live campaign fronts {ladder, deepTwist, a0}.**
  The ladder/deepTwist hypothesis types are byte-copies of the capstone's field types
  (post-A-I.8), so any capstone field drift breaks this file at build.
* §3 the remainder ledger (doc section, per-field exact open state — below).

## Per-field table (real bodies)

| field | as-signed | real body state | exact remainder |
|---|---|---|---|
| `windowPinning` (I.05) | CLOSED all n (`windowPinningAt_asSigned`) | OPEN — re-sign target `IFC0.WindowPinningBody Arises n` ((CS-1Q.a) at every arising stage-window datum; unguarded reading REFUTED by IFC0's tooth; empty guard fabricates) | THE canonical `Arises` guard = the GENHN-CAP-GEN reader rule, which chapter H holds a STANDING RECORDED DECISION not to formalize (owner-adjacent to reverse). Supplier is NOT the gap (H89w is general-e₁, CHA correction). Blitz movement: IFCG5 §6/IFCG6's `genreDatumOfChildEntry` substrate — a feed for the future `StageOccurrence`, not a bridge. |
| `genhnHE` (I.06, n ≥ 6) | CLOSED all n ≥ 6 (`genhnHEAt_asSigned`) | PARTIAL — μ=3 arm landed at dictionary level (`IFC6.mu3_stage_sigma_decided`, repackaging H73w = THEOREM HE3.A) | (a) the STAGE-LEAF BRIDGE (no leanfinal decl ties a polynomial stage occurrence to `StageLeaf3`; freeze `StageOccurrence` is the vehicle); (b) the μ ≥ 4 arm `HE3Box6Decision` — transcription from EFF.HE3.16/.17 + HYP.143, research-open. Blitz irrelevant here (density-layer, not the chapter-H σ-decision). |
| `genhnTow1` (I.07, n ≥ 8) | CLOSED all n ≥ 8 (`genhnTow1At_asSigned`) | CENSUS 5/7 — the "5/7" decoded: LANDED = (1) `towerLocus_iff_budget`, (2) `refine_invariants` (A-C.23), (3) `shadow_floor`, (5) `window_band1`, (6α) `gentow5_key_certificate_cleared` | THE MISSING TWO: **item (4)** `partial_floor_and_datum`'s clause (a), the frame-opening floor `ℓ·((e₁·f₁)·h) < u` from `hopen` (clause (b) landed conditionally in C135c93; (a) UNATTEMPTED per CCUR — a real derivation node); **item (6β)** `towerLocus_depth3_floor` (signed without `hh`/`[Finite (ResidueField O)]`, which every landed C.54-family route needs — needs the unlanded C.54 node-floor family or a new hypothesis-independent lattice argument). Freeze rule: I.07's real body may not land until 7/7. No post-C135c93 movement (grep at HEAD). |

**TypeOfFaithful (the "possible fourth"): NOT a capstone field** — `CapstoneHypotheses`
consumes exactly the three names above; I21's `TypeOfFaithful : Prop := True` is a
standalone trust-boundary label.  Its (unchanged) ledger row stays at verdict_CHA's
structural analysis (B.56 carrier or gate-(b) cite; human audit A-1 before any consumer).

## Named next nodes (ranked)

1. **CENSUS-4a** — derive item (4)'s clause (a) from `hopen` (feeds
   `C135c93.partial_floor_and_datum_of_floor`, making unconditional
   `partial_floor_and_datum` one application away). Real math, single-node scale.
2. **CENSUS-6β** — adjudicate C.55's hypothesis mismatch (owner-adjacent: either the
   signed axiom gains `hh`/`[Finite …]` by amendment, or a new lattice argument).
3. **HE-BRIDGE** — the `StageOccurrence` type + stage-leaf bridge (unlocks the μ=3 arm
   end-to-end; also the substrate WIN0's guard needs).
4. **WIN-GUARD** — owner decision: reverse chapter H's recorded no-formalize on the
   GENHN-CAP-GEN reader rule (blocks I.05's real body entirely).
5. HE3-BOX-6 transcription (μ ≥ 4) — research-open (HYP.143).

## Stale-text notice (orchestrator)

PROJECT_STATE §4's row "(windowPinning/genhnHE/genhnTow1) — ⚠ COVERAGE GAP … NO active
lane" is now dischargeable: fields supplied as-signed + frontier reduction at
`ChapI/ID12.lean`; real bodies tracked at ID12 §3 (this verdict's table).

## Verification record

`cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/ID12.lean` —
run after EACH of the three increments, exit 0 each time, zero errors/warnings/`sorry`.
Final AxCheck output: §1's three suppliers axiom-FREE; `capstoneHypotheses_of_frontier`
`[propext, Classical.choice, Quot.sound]`; `capstoneHypotheses_of_three` those three +
`Uniformity.Density.Tower.agnprw_termination` (previously-declared allowlisted cite,
disclosed in the docstring and the AxCheck comment). No new axiom, no `sorry`, no
statement change to any landed file, no git operations.
