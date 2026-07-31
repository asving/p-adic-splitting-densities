# O2a — engine↔GMN dictionary — Phase-B attempt REV 4 (Fable, 2026-07-31)

Repair of ROUND 5's pair of model-diverse hostile verifications of rev 3
(`O2a_phaseB_verifybrief_rev3.md`): V20 (Codex, `V20_o2ar3.jsonl`; verdict
SOUND-WITH-GAPS, 2 gaps) and P2 (fresh-context Fable,
`O2a_pass2_fable_verify.md`, first report not consulted; verdict UNSOUND,
1 critical + 3 gaps; V20's gap 1 = P2-3). Campaign context: FOURTH document
revision (V10 → V14 → round 5 → next), acceptance bar = two consecutive
clean passes. The repaired self-contained brief is
`O2a_phaseB_verifybrief_rev4.md`, produced by COPYING the rev-3 brief and
editing only the finding sites — byte-stability of every confirmed section
is by construction (diff perimeter audited, §2).

## 0. Round-5 findings → dispositions (both reports; no silent drops)

| finding | class | disposition |
|---|---|---|
| P2-1: Theorem 2(D)'s induction at levels ≥ 2 applies OL-2-min/OL-3 to the run's records, but NO declared law binds the run's (i+1)-th emitted record to "the engine's stage read at level i+1 on f over c" with c = the emitted prefix's chain; [F.0]'s c is unbound; OL-5 internalized exactly this glue at level 1 only — (D) unlicensed at every level ≥ 2 (the V14-1 class, one level up) | CRITICAL | **FIXED** brief §4: **OL-6 (run decomposition + chain binding, every level) DECLARED** — ONE general law, not per-level patches: for every complete run, each continuing record ν_j IS the record emitted by the engine's level-j read on f over the chain of its emitted prefix, the binding displayed — (a) j = 1: the base read over ρ₀ with key φ₁ = Lift₀(ψ̂₀); (b) j = i+1 ≥ 2: the stage read over c := Θ(𝐇_{≤i}) (Θ total and formal, so c needs no consistency/OL-1 input) with key Φ̂_{i+1} = Lift_i(c). The stage interface now displays c as the stage's OWN parameter (the [F.0] unbound-c fixed). §5: (D)'s base and step both re-founded on OL-6 |
| P2-2: Theorem 1's unconditional (L9)-at-r = 1 cites presuppose the (L5) Convention, instantiated in-note only under (D4) + OL-1; the level-0-only bridge missing; side tension with checklist item 7 | GAP | **FIXED** brief §3: **Lemma B (order-1 family bridge) displayed WITH proof** — ind₁ depends only on the level-0 layer (admissible by (D4)); Thm-2.11 recursion + choice extends it to a full (L5) family; (L9) there + transport. All three cite sites re-pointed; checklist item 7 rescoped (Theorem 2(C) k' ≥ 1 only; Theorem 1 through Lemma B); scope remark (2) annotated |
| P2-3 (= V20 gap 1): OL-5's clause (a) (engine-internal development/hull computation) exceeds (D)'s consumption — (b)+(c) suffice; V14-2's minimality defect reintroduced at level 1 | GAP | **FIXED** brief §4: OL-5 restated as its minimal core **(b′)+(c′)**, STAGE-wise (parameterized by (f, ρ₀), sibling of OL-2-min/OL-3; the run glue now lives in OL-6), with (b′)'s frame anchored intrinsically ((c1)'s positional plane); rev 3's (a) re-advertised to the O-3 seam and retained as the intended proof route via the PROVED (D3) — the exact pattern of the V14-2 OL-2/OL-2-min split |
| P2-4: OL-1 as independently-quantified per-i statements is not well-posed ("its type over F_rep" at order i needs OL-1(b) below i) | GAP | **FIXED** brief §4: OL-1's cumulative reading displayed in-statement — ONE JOINT statement by strong induction on the order |
| V20 gap 2: (L6) transcribes Thm 1.15 as "N_φ(F_i) = S_i one-sided"; the paper gives equality up to translation | GAP | **FIXED** brief §1 (L6): "EQUAL TO S_i UP TO TRANSLATION" restored, with the note that every downstream use (slope, length, height, degree, residual) is translation-invariant |

Both reports' positive remarks preserved: P2 confirmed the carrier design,
Theorem 1 (modulo P2-2), Lemma R, Theorem 2(A)–(C) as conditional proofs
(all k' = 0 corners, both lattice witnesses independently recomputed, F3's
4k+2 recomputed exactly); V20 confirmed the OL-2-min collapse, (D)'s
OL-2-consumption discipline, and the level-1 base — all carried byte-stable.

## 1. Findings classification (round-5 churn audit, per the protocol)

* **P2-1 (critical) = class (a): the SAME defect family (undeclared
  run→read emission dependence, V10-C8 → V14-1) surfacing at successive
  levels** — V10-C8 the W-law half, V14-1 the read-semantics half at level 1,
  P2-1 the read-binding half at levels ≥ 2. The verifier's own words: "exact
  parity with V14-1 … the same shape one level down". NOT churn by the
  protocol's class-(a) test; but the class-(a) discipline BINDS the repair
  shape: since the same glue was needed at yet another seam, rev 4 declares
  ONE general lemma (OL-6, all levels, subsuming the run-wise half of rev 3's
  OL-5) instead of a third per-level patch. If a round-6 verifier finds this
  glue needed at yet ANOTHER seam, OL-6 is the single statement to widen —
  no new lemma.
* **P2-3/V20-1 (gap) = class (b): introduced by the rev-3 repair** (OL-5
  declared with a mechanism clause its consumer does not need) — the same
  over-strengthening pattern as V14-2, caught symmetrically by BOTH round-5
  verifiers. Advertising defect, not correctness.
* **P2-2, P2-4, V20-2 (gaps) = statement hygiene**, present since rev 1 in
  sections whose mathematics both verifiers confirmed; none threatens a
  conditional implication (P2: "none of which threatens the mathematics").

**Repair-vs-rescope decision: REPAIR.** The pre-registered rescope trigger
(rev-3 attempt §1: "fresh DICTIONARY-layer churn") did not fire: round 5
found zero new dictionary-layer defects — the critical is the engine seam's
known family, and the dictionary core (carrier + Theorem 1 + Lemma R +
Theorem 2(A)–(C)) is now THRICE confirmed (V14, V20, P2). Findings by round:
12 → 2 → 5-with-1-critical-in-one-family — the seam is converging on a
single statement (OL-6), which is what "the exact residue of O-2a" should
look like. Rescope target stays pre-registered unchanged if round 6 breaks
the pattern.

## 2. What changed (edit sites; everything else byte-identical to rev 3)

Diff perimeter of `O2a_phaseB_verifybrief_rev4.md` vs rev 3 (cp + ~20 local
edits, 23 diff hunks; verified by `diff` — every hunk at a declared repair
site): header
(rev bump, round-5 record, SIX lemmas); deliverable-3 bullet (six); non-
claims paragraph (OL-6 added); NEW §0″ rev-4 changelog (5 rows); §1 (L6)
translation fix; §3 NEW Lemma B + proof + the two cite-site re-points +
"*Proof (of Theorem 1).*" label; §4 heading/intro (six; per-lemma roles),
interface preamble (run vocabulary declared) + stage parameterization (c
bound); OL-1 joint-induction display; OL-5 restated (minimal core, stage-
wise); NEW OL-6 block; §5 (D) statement hypothesis list + proof paragraph;
scope remark (2); checklist items 6/7/11/12 + NEW item 13 (run/read-seam
sweep) + final charge line (six). NOT touched: (L1)–(L5)/(L7)–(L9), (L6)
outside the one clause, §2 carriers/Θ/Cons_f/Lemma R, Theorem 1's statement
and all case proofs, OL-2 (a)–(d) and OL-2-min and the collapse display,
OL-3, OL-4, Theorem 2 (A)/(B)/(C) statement and proofs, scope remarks
(1)/(3′)/(4), §6 falsifiers F1–F5, checklist items 1–5/8–10.

## 3. Unbound-c sweep (P2-1's "the V14-1 class persists" — swept)

Every consumer of the run/read seam audited for the unbound-c pattern:

* **In-note:** Theorem 2(D) is the ONLY theorem consuming engine lemmas
  (each OL's "Consumed by" line); its base and step now fire OL-5/OL-2-min/
  OL-3 exclusively at reads bound by OL-6(a)/(b). OL-4 is run-wise with no
  stage read (no c). (C4)/Lemma R/Theorems 1, 2(A)–(C) consume no run or
  read (P2 ledger items 2–3 confirmed). The interface's c is now a displayed
  stage parameter. NEW checklist item 13 charges the round-6 verifier with
  re-running exactly this sweep.
* **Cross-unit (flagged, not edited):** `O3design_phaseB_attempt.md` step F1
  consumes "OL-2a-2(c,d)/3" for "the read just made = (c1)/(c2) data" inside
  ITS run induction — the SAME unbound-c pattern one repo over. Its JC
  ledger should consume OL-6 (= OL-2a-6) as the binding premise, not
  re-derive per-level glue; rev 3's flag (gain OL-2a-5 as a JC sibling)
  upgrades to: gain OL-2a-5-min AND OL-2a-6. For the O3design maintainer.

## 4. Falsifier note (falsifier-first check)

No new mechanism is PROVED in rev 4 — Lemma B is the only new proof, and it
is a literature-plumbing bridge (family extension + transport) whose
numerical content is already exercised by F2/F5 (ind₁ ≤ ind_p on 4471
samples, exact arithmetic — those falsifiers compute ind₁ from the level-0
data alone and compare against the family-free ind_p, which is precisely
Lemma B's shape). OL-6 is engine-side and OPEN, like OL-4/OL-5: the natural
falsifier (instrument a run; check each emitted record equals the stage read
recomputed over Θ(emitted prefix)) belongs to the O-3 design's G-EMIT/U6
gate suite; recorded there alongside rev 3's OL-5 flag.

## 5. Honesty ledger (rev 4)

**Proved here (order ≤ 1, Theorem 1):** unchanged from rev 2/3 (thrice
confirmed), PLUS Lemma B (the order-1 family bridge), making Theorem 1's
(L9) consumption genuinely unconditional as advertised.

**Proved here (all orders, Theorem 2):** (A)/(B)/(C) GIVEN Cons_f and
OL-2a-1 (thrice confirmed); the engine seam (D) GIVEN OL-2a-1 + OL-2a-2-min
+ OL-2a-3 + OL-2a-4 + OL-2a-5-min + **OL-2a-6**.

**Open (the exact residue of O-2a): SIX lemmas** — OL-2a-1 (lift
admissibility; now displayed as one joint induction), OL-2a-2 (frame
crossing; only OL-2a-2-min consumed in-note), OL-2a-3 (residual
identification; shared with O-9), OL-2a-4 (emission discipline), OL-2a-5
(first-read conformance, order 1 — now MINIMAL and stage-wise; rev 3's
mechanism clause (a) re-advertised to O-3), **OL-2a-6 (run decomposition +
chain binding, every level — NEW,** the P2-1 declaration; rev 3's implicit
level-≥2 binding is RETRACTED as an undeclared dependence, the third and —
by generality — intended-last member of the V10-C8/V14-1 retraction family).

**Literature consumption:** as rev 3 ((†) = Thm 4.18(1), Thm 1.15 — now
transcribed with "up to translation" — /1.19/Cor 1.20, Thm 2.11/Def 2.12,
Cor 3.8/Def 3.9/3.10, (L3+)), PLUS Thm 2.11's recursive existence + choice
inside Lemma B; all LITERATURE-CONDITIONAL pending printed-TAMS confirmation.

**Not attempted (unchanged):** O-2b, O-3 realization, BNS/LIT-5, any engine
conformance proof (exactly the OL-2a family).

## VERDICT

O-2a rev 4: **all five round-5 findings repaired (1 critical, 4 gaps, two
coincident; dispositions §0, all accepted, no rebuttals); the critical
repaired by ONE general run/read binding law (OL-6) per the class-(a) churn
discipline rather than per-level patches; the thrice-confirmed core carried
byte-stable by construction (diff perimeter audited); Theorem 2(D) now
rests on SIX exactly-stated open lemmas, each minimality-audited, with the
stage interface's chain parameter bound.** Churn audit: repair over rescope
(no fresh dictionary-layer churn; rescope target unchanged, §1). Pending:
hostile re-verification of `O2a_phaseB_verifybrief_rev4.md` (pass 1 of the
required 2; new checklist item 13 = the run/read-seam sweep).
