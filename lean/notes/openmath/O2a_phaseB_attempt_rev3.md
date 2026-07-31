# O2a — engine↔GMN dictionary — Phase-B attempt REV 3 (Fable, 2026-07-31)

Repair of the V14 hostile verification (`V14_o2ar2.jsonl`, verdict UNSOUND;
1 critical / 1 gap) of the rev-2 attempt (`O2a_phaseB_attempt_rev2.md`) /
brief (`O2a_phaseB_verifybrief_rev2.md`). Campaign context: this is the
THIRD document revision (verification rounds V10 → V14 → next), under the
round-4 acceptance bar of two consecutive clean passes. The repaired
self-contained brief is `O2a_phaseB_verifybrief_rev3.md`, produced by COPYING
the rev-2 brief and editing only the finding sites — byte-stability of every
confirmed section is by construction.

## 0. V14 findings → dispositions (no silent drops)

| V14 finding | class | disposition |
|---|---|---|
| 1: Theorem 2(D)'s level-1 (c1)/(c2) rests on (D3), which is a CONDITIONAL ("a first read that computes exactly these objects…"); no OL asserts the engine's first read computes the displayed formulas (OL-2/OL-3 start at orders ≥ 2; OL-4 gives only (c0)) — so (D) cannot establish Cons_f for emitted histories with k' ≥ 1 | CRITICAL | **FIXED** brief §4: **OL-5 (first-read semantics, order 1) DECLARED** — the engine's first read is performed by the (D3)-displayed development/hull/positional/residual formulas w.r.t. φ₁ = Lift₀(ψ̂₀), clauses (a)–(c); (D3) (PROVED, V10/V14-confirmed) converts it to (c1)+(c2) at i = 1. §5: Theorem 2(D)'s hypothesis list and proof base re-founded on OL-5 + (D3). Checklist item 12 added |
| 2: OL-2(a)–(b) (valuation tie on every admissible coefficient; whole-polygon identity) are materially stronger than Theorem 2(D)'s consumption ((c)–(d) suffice); advertised minimality fails | GAP | **FIXED** brief §4: consumption split — **OL-2-min [(c′)+(d′)]** displayed as an intrinsic standalone statement (no window polygon, no "corresponding side": verbatim (c1) at level i + 1) and made (D)'s ONLY OL-2 hypothesis; the (a)+(b) ⇒ OL-2-min collapse displayed (one-side-per-slope); (a)–(b) re-advertised to their ACTUAL consumer — the O-3 design's unit JC-2, which targets the full rev-2 (a)–(d) — and retained as OL-2-min's intended proof route (the HK52 stretch trap lives in (b)) |

Both of V14's positive remarks are preserved: the entire rev-2 seam audit
(intrinsic positional recovery, all-continuing injectivity restriction,
k' = 0 corners, OL-4's exactness for what it states, Theorems 1 and 2(A)–(C),
the arXiv source identity) is carried byte-stable.

## 1. Findings classification (the round-4 churn audit, per the charge)

* **V14-1 (critical) = class (a): a deepening/remnant of the V10-C8 family**
  (undeclared engine-emission dependence in Theorem 2(D)). V10-C8 charged the
  W-law/well-formedness half, repaired by declaring OL-4; V14-1 is the
  read-semantics half at level 1, which rev 1 had hidden under the SAME
  deleted scope remark (3) and which rev 2's explicit-induction rewrite made
  visible but did not declare. The verifier's own words: "another undeclared
  emission-semantics dependence, distinct from the repaired W-law
  discipline." NOT a defect introduced by the repair — the dependence predates
  it; the repair exposed it.
* **V14-2 (gap) = class (b): introduced by the rev-2 repair** — the V10-G2
  fix over-strengthened OL-2 relative to its in-note consumer. But it is an
  ADVERTISED-MINIMALITY defect, not a correctness defect ("does not
  invalidate the conditional implication"), and the extra strength has a real
  downstream consumer (O3design JC-2).

**Repair-vs-rescope decision: REPAIR.** (b) does not dominate — one minor
advertising gap vs. one (a)-class critical; findings fell 12 → 2 across
rounds; every element of the rev-2 re-architecture passed V14's seam audit.
This is convergence, not churn. Both repairs are DECLARATION-layer (a new
open lemma; a consumption re-pointing) — no proved content changes, no proof
mechanism is added. **Pre-registered rescope target if round 5 finds fresh
dictionary-layer churn:** the Cons_f-conditional order ≤ 1 theorem (Theorem 1
+ Theorem 2(A)–(C), the twice-confirmed core) as the accepted deliverable;
the carrier as DESIGN consumed by O3design; the engine seam (Theorem 2(D))
dissolved into the named OL-2a family outright.

## 2. What changed (edit sites; everything else byte-identical to rev 2)

Diff perimeter of `O2a_phaseB_verifybrief_rev3.md` vs rev 2 (produced by cp +
seven local edits): title/header (rev bump, FIVE open lemmas); deliverable-3
bullet (five OLs + minimality direction); non-claims paragraph
(OL-2/3/4/5); NEW §0′ rev-3 changelog; §4 heading + intro (five, OL-5
listed); OL-2 block — clauses (a)–(d) BYTE-STABLE, the "Consumed by" line
replaced by the consumption split + OL-2-min display + the (a)+(b) ⇒
OL-2-min collapse; NEW OL-5 block after OL-4; Theorem 2 statement clause (D)
hypothesis list; proof paragraph (D) (level-1 base via OL-5 + (D3); step via
OL-2-min; "no clause of OL-2 beyond OL-2-min is consumed"); checklist item 6
(consumption + minimality audit), item 11 (OL-5 attackability), NEW item 12
(level-1 base instantiation), final charge line (five). NOT touched: §§1–3
(literature incl. (L3+), carriers, Lemma R, Theorem 1 complete proof), OL-1,
OL-2(a)–(d) text, OL-3, OL-4, Theorem 2 (A)/(B)/(C) statement and proofs,
scope remarks (1)/(2)/(3′)/(4), §6 falsifiers F1–F5.

## 3. Falsifier note (falsifier-first check)

No new mechanism is PROVED in this rev — both repairs declare or re-point
statements — so no new falsifier is owed. The mathematical content OL-5
points at ((D3)'s displayed order-1 formulas) is already falsifier-covered:
F1 (3600 samples, order-1 reads vs `idealprimedec` ground truth) and F5 (871
forced j₀ = 1 samples, 0 findings). What F1/F5 do NOT and cannot check from
this note is OL-5 itself (that the ENGINE's first read computes those
formulas) — exactly why it is declared OPEN, like OL-4. An engine-side
falsifier (emitted level-1 records vs direct (L2)/(L3) computation) belongs
to the O-3 design's gate suite; recorded there as the natural extension of
its G-EMIT/U6-fidelity harness.

## 4. Cross-unit note (no files of other units edited)

`O3design_phaseB_attempt.md` line 18 targets "the STRONGER rev-2 positional
form of OL-2a-2, clauses (a)–(d)" (unit JC-2) — unaffected: the full (a)–(d)
statement is retained verbatim, now with ITS consumer correctly advertised.
O3design's step F1 consumes "OL-2a-2(c,d)/3" for "the read just made =
(c1)/(c2) data"; at its OWN induction base the analogous level-1 read appears
— its JC ledger should gain OL-2a-5 (this rev's OL-5) as a sibling of JC-4's
emission unit. Flagged here for the O3design maintainer; not edited.

## 5. Honesty ledger (rev 3)

**Proved here (order ≤ 1, Theorem 1):** unchanged from rev 2 (V14-confirmed):
all clauses per case, k' = 0 cases, j₀ corner, Lemma R injectivity on
all-continuing histories with the displayed terminal non-claim.

**Proved here (all orders, Theorem 2):** (A)/(B)/(C) — landing, placement,
restricted injectivity, invariant matching, saturation (k' ≥ 1 guard),
charging, k' = 0 degenerations — GIVEN Cons_f and OL-2a-1 (V14-confirmed);
the engine seam (D) GIVEN OL-2a-1 + OL-2a-2-min + OL-2a-3 + OL-2a-4 +
OL-2a-5.

**Open (the exact residue of O-2a): FIVE lemmas now** — OL-2a-1 (lift
admissibility), OL-2a-2 (frame crossing + positional transport; only its
displayed minimal core OL-2a-2-min is consumed in-note; the full (a)–(d)
serves O3design JC-2), OL-2a-3 (residual identification; shared with O-9's
twisted-residue leg), OL-2a-4 (emission discipline), **OL-2a-5 (first-read
semantics, order 1 — NEW,** the V14-1 declaration; rev 2's implicit reliance
on (D3)'s conditional alone is RETRACTED as an undeclared dependence, the
same retraction pattern as rev 2's OL-2a-4).

**Literature consumption:** unchanged from rev 2 — (†) = Thm 4.18(1) +
Def 4.15/4.11 nonnegativity over F_rep, Thm 1.15/1.19/Cor 1.20, Thm 2.11/
Def 2.12, Cor 3.8/Def 3.9/3.10, (L3+) slope-−∞ convention — all
LITERATURE-CONDITIONAL pending printed-TAMS confirmation (V14 confirmed the
arXiv v2 source identity).

**Not attempted (unchanged):** O-2b, O-3 realization, BNS/LIT-5, any engine
conformance proof (that is exactly the OL-2a family).

## VERDICT

O-2a rev 3: **both V14 findings repaired at the declaration layer (1
critical, 1 gap; dispositions §0, both accepted, no rebuttals); the
twice-confirmed core (type-tree induction, degree recursion, saturation,
per-order index charge given Cons_f; Theorem 1 in full) carried byte-stable
by construction; Theorem 2(D) now reduced to FIVE exactly-stated open lemmas
with a minimality-audited hypothesis list.** Churn audit: (a)-class deepening
dominated; repair chosen over rescope; rescope target pre-registered (§1).
Pending: hostile re-verification of `O2a_phaseB_verifybrief_rev3.md` (pass 1
of the required 2).
