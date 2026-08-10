# GENTOW4 passPE2 — HOSTILE VERIFIER REPORT (second pass; fresh context, zero prior stake), 2026-08-10

**Target:** `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` at HEAD
(note last touched eb526a0d, the r1 gauge-annex round; pre-round
body md5 5272bb855a4cbd6f445aaf18a47b2bb3 / 31,014 bytes verified =
`git show c43505d3` = the PE1 target). Arc: seal → PE1
1 GAP(CONFIRMED)/2 MINOR @ 8ae71864 → r1 annex (aa92a9d4/abd25133/
eb526a0d). AS-OF states read: HETOW at [r1 2026-08-09] restatements
(5335ae38); GENHN erratum 59c1966; HE7 ANNEX F-1 (HE7-13′);
GENTOW3/6 in parallel repair (GENTOW3 read at PE3-report state
17545B, GENTOW6 at its PE1 state — neither consumed by this note).
Protocol: quote-and-classify, fix nothing.

## VERDICT: **CLEAN — 0 CRITICAL, 0 GAP, 5 MINOR. Counter 0/2 ⇒ 1/2.**

The r1 gauge annex survives independent re-derivation at all four
sites; the bouquet/projection/decision chain at the wrap-corrected
key survives a fresh machine stress at TWO new geometries (first
non-linear wrap profile W = (1,1,0) anywhere; first gauge-live
TWO-BLOCK compound anywhere): **93 checks / 0 violations, dual PARI
routes, every preregistered prediction exact — including the naive
key's σ predicted in advance from the skewed letter polynomial.**
Sealed leg + PE1 leg isolated re-runs reproduce the committed
artifacts (1,740/0 identical mod line-1 timestamp; 93/0 identical
byte-for-byte). Nothing at GAP-or-worse found on any surface.

---

## FINDINGS (all MINOR)

### m-A (MINOR — S8 supply audit: HE7-13′'s route misattributed; the conclusion is true by HE7-13′'s own statement form)

Quote (S8.1): "every item on 4.1(c)'s list except LEMMA HE6R1-2 +
RIDER and ANNEX HE7-13', which 4.1(c)'s own proof supplies through
HE7-12(c)'s transport". Two inaccuracies: (i) 4.1(c)'s proof body
(S2) walks only HE6R1-2's consumption list — it never mentions
HE7-13′; (ii) HE7-12(c)'s displayed list (HE7_PROOF S5.8) contains
"LEMMA HE6R1-2's read" — so THAT leg is exactly right — but not
HE7-13′ (which postdates it; ANNEX F-1 is 2026-08-09). The
conclusion stands anyway, and by a SHORTER route the same S8
sentence half-states ("reads only the conclusion Phi2 = Psi − w and
is key-shape-blind"): ANNEX-LEMMA HE7-13′ is STATED at
"Ψ̃ = Ψ − W with W = 0 or as in LEMMA HE7-12(d)" (HE7_PROOF
L1671-ish), and the restated HETOW-2 gives Φ₂ = Ψ with w = 0 under
the (LIFT)-slot form — Φ₂ is literally in HE7-13′'s hypothesis
class. Failure scenario if uncorrected: a reader auditing supply
routes finds HE7-13′ absent from HE7-12(c)'s list and wrongly
suspects an unsupplied consumption; one clause naming HE7-13′'s own
Ψ−W hypothesis form closes it.

### m-B (MINOR — S3(iii)'s composed "the three fullness rows" vs the S2 [GT4-r1] five-row recount)

Quote (S3(iii) proof, composed text): "discharged row by row by
HETOW_RECON's S1 table with the three fullness rows replaced by
GENTOW-4.1(a)(b) (datum + label rows) and by (ii) here (the
f_S/mu2 row)". Quote (S2 [GT4-r1], the m-1 repair): "TWO
lemma-level places spanning FIVE table rows: HETOW-1's r-row (one
row), and HETOW-3 across four rows (the Psi ∤ f_S peel convention,
the label row, the f_S/mu2 row, the level-1 Phi' ∤ f frame row)".
I verified the five-row census against HETOW_RECON's S1 table
directly — it is exact (the ladder row's "equality at full side" is
annotation). As one text the counts now disagree: (iii) names three
replaced rows; the two unnamed fullness rows (peel convention,
Φ′ ∤ f frame) are in fact discharged by 4.1(d)'s peels, which the
theorem's preamble assumes ("after the S2 peels") — so no content
hinges, but the r1 round fixed the S2 count and left (iii)'s
"three" unreconciled. Failure scenario: a reader cross-checking
(iii) against the recount concludes two fullness rows went
undischarged.

### m-C (MINOR — S8.4 edit-manifest shape sentence vs the actual diff)

Quote (S8.4): "Edit shape: [GT4-r1]-bracketed INSERTIONS plus this
S8 … LEMMA GENTOW-4.1's (c) clause and the S2 count sentence carry
bracketed insertions with the composed text standing." Checked
`git diff d7ddf2e..HEAD` on the file: 265 insertions, 14 deletions;
all 14 deletion lines sit at the manifest's disclosed sites, and
the statement displays of THEOREM GENTOW-4.A, LEMMA GENTOW-4.2,
COR GENTOW-4.C are untouched — but at TWO sites the composed text
did NOT stand: the S2 count word was changed in place (THREE → TWO,
original quoted inside the bracket) and the S4 parenthetical was
rewritten in place ("(Δb is forced even; the x- and pi-relations
have residue 1 at f1 = 1)" → the corrected two-clause form, with
the bracket recording the original said "at f1 = 1"). Both original
wordings are preserved inside the [GT4-r1] brackets, so the edits
are honest and auditable; only the manifest's "insertions /
composed text standing" description is imprecise. Failure scenario:
a diff-auditor trusting the manifest sentence flags the 14
deletions as undisclosed.

### m-D (MINOR — PE1-instrument check-count padding, inherited by the annex's "93 checks" figure)

The adopted machine rows (S8.1) cite `gentow4_pe1_fresh.py` "GREEN,
93 checks / 0 violations". In that instrument's FR-M keyval loop
the else-branch check `chk(tag, 4 * v_ <= E2 * e_, 'sep')` tests
the very condition that selected the branch — it can never fire —
padding the count by roughly 15 vacuous checks (3 members × 2 keys
× the 2–3 non-class rows each). The separator's semantics are still
enforced bidirectionally by the class-degree-sum checks (a
misclassified row moves the sum off 8), and every NUMBER the annex
quotes from those rows (σ, pins, c_g, keyvals, degree sums) is a
real measured quantity that I re-verified against the committed
output and reproduced in an isolated re-run — so substance is
unaffected; the raw check-count is inflated. Failure scenario: the
"93 checks" figure is quoted as if all 93 were falsifiable.

### m-E (MINOR — BOX-4's supplier-grade stack is stale; PE1 assigned the refresh to this annex and the annex omitted it)

Quote (S7 BOX-4, composed): "HETOW-1/2 (HETOW 0/2), … GENTOW-1
(0/2)". PE1's sibling-lesson (6) bullet recorded "the stack line's
next refresh belongs inside F-1's annex"; S8 does not refresh it.
As of this pass HETOW and GENTOW-1 are accepted (per the arc
records) — the staleness is in the CONSERVATIVE direction
(understates supplier grades), so nothing weakens; the record is
merely out of date at a place the prior pass had already pointed
to. Failure scenario: a grade-box consumer prices the chain at
0/2-supplier conditionality that no longer exists.

---

## CLEAN CHARGES (verified, nothing GAP-or-worse)

**(1) The r1 annex, all four sites, independently re-derived.**
* **(a) S0 gauge pin.** Re-derived the wrap cocycle myself from the
  normalizer grammar (i(a)+i(b) = i(a+b) + e₁·wrap; heights add;
  telescoping gives n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^h)^{W(t)},
  W(t) = ⌊(f₂−t)i(u₂)/e₁⌋), checked the pin against the erratum
  source display (GENHN_PROOF L1997–98: same lift object, same
  (LIFT) f₁ ≥ 2 clause) and re-derived FR-G's key numerically
  (i(3) = 1, W = (1,0), c₀ ≡ 1, c₀η = 2, −2·27 = −54; t = 1 slot
  gauge-blind) — matches the annex's hand re-derivation and the
  committed instrument constants. The f₂ = 1 degeneration
  (W(0) = 0) and the η = 1 coincidence clause both check.
* **(b) The restated-bridge supply, consumption WALKED.** The
  [r1]-restated LEMMA HETOW-2 concludes Φ₂ = Ψ − w with **w = 0
  under the (LIFT)-slot form at any f₁** — strictly stronger than
  4.1(c)'s consumed "w = 0 or dv₂(w) > T₂" — and its "hence" clause
  hands over the §S5 package, HE7.A(1)(2), the refine package, and
  the §S1 CONVENTION + HE6R1-3 peel. Its proof's two legs are
  side-blind as the [GT4-r1] audit bracket claims: the F-4 leg
  consumes degree/height bookkeeping + the node floor + HE6's
  NON-PROPAGATION + HETOW-1(c); the F-2 carry leg consumes the
  Φ′ constant-term pin and the node floor, per slot. HETOW-1's
  restated clause (b) is verified pointwise/wrap-free at source
  ("only the single height u₂ is normalized — no product of
  normalizers occurs"), and the one full-side step in HETOW-1's
  proof (ψ₂(0) ≠ 0 via the left endpoint) is exactly what
  4.1(b)'s endpoint-vertex argument replaces. The two items beyond
  the hence-clause: HE6R1-2's read is ON HE7-12(c)'s displayed
  transport list (HE7_PROOF S5.8, verified verbatim), with RIDER
  consumed inside 4.1(c)'s walked list; HE7-13′ is available by its
  own statement form (m-A records the route misattribution). Net:
  4.1(c)'s full consumption is supplied at the corrected key.
* **(c) BOX-3 withdrawal.** The [GT4-r1] bracket's failure list at
  the naive key (4.1(c) key clause, (ii)'s deg f_S = D₂μ₂*,
  GENTOW-1(d) floor transport) matches FR-G's committed rows, which
  I re-verified number-by-number against the committed output AND
  reproduced in an isolated re-run; the battery-blindness sentence
  verified at the sealed runner's constants (PA = x²−2, PB = x²−3
  — all five families η = 1; P2 the only f₂ = 2 family). My fresh
  leg extends the failure geography to f₂ = 3 and to two-block
  compounds (below).
* **(d) The S4 re-scope f₁ = 1 → η = 1.** The corrected clause
  ("the x-relation x^{e₁} = η·π^h(1+small) has residue η") is
  immediate from the (T1)-locus definition; f₁ = 1 with η = 2 is
  instance-witnessed at FR-G and now at BOTH of this pass's fresh
  frames — the composed "residue 1 at f₁ = 1" was false and the
  replacement is the honest scope. The annex's slope-layer survival
  claim ("FR-G's members decide 2SIDED/RAM consuming no residual
  digits") verified IN CODE (the PE1 reader's verdict logic reads
  pins only; its digit branch is unreachable on those rows) and now
  re-witnessed at η = 2 on five more members. The disclosed hole
  (no η ≠ 1 coh() row in any leg) is accurately disclosed — my
  fresh frames deliberately stay on the slope layer too, so the
  hole STANDS as named.

**(2) Bouquet + projection at NEW geometries** — via the fresh
machine leg below: deg f_S = D₂μ₂* with μ₂* = 2 read from f, c_g
constancy and exact right-endpoint height, GENTOW-1(c) floors
through the projection (j = 1 exactly at the floor at all three
frames' designs), GENTOW-4.2's tie at an f₂ = 3 pure-power side and
at two pure-power sides simultaneously, 4.C's parity flip (both
verdict genres), GENTOW-1(d)'s strict separator — all PARI-exact at
frames none of the prior legs touched.

**(3) One-text audit.** S0 pin ↔ S2/S3/S5 usages consistent (PE2-P
degenerates to Φ′² − 4x correctly under the pin; P2's η = 1
coincidence disclosed at source); header arc ↔ S8 consistent; S8.2
recount verified against HETOW_RECON's table; S8.3 disclosure
verified against sealed-runner L871–878 verbatim; FR-M's c_g
arithmetic ("20 + 7 and 20 + 5") re-derived by hand from the
normalizer heights; edit manifest md5/bytes verified. Residues: m-B,
m-C, m-E above.

## MACHINE LEGS

* **Seals:** all four S8.4 md5s verified at HEAD
  (runner 98cdd4a4…, output 58f35305…, PE1 instrument 5dc455dd…,
  PE1 output dac5110c…).
* **Isolated re-runs (fresh /tmp copies):** sealed battery — GREEN,
  **1,740 checks / 0 violations**, 6/6 teeth census identical (49
  NOCG, 8 NOTWIST, 71 c_g-odd), output IDENTICAL to the committed
  artifact from line 2 (line-1 timestamp only); PE1 instrument —
  GREEN, **93 / 0**, output byte-IDENTICAL to the committed
  artifact.
* **Tautology spot-audit:** m-2's L871–878 branch matches the S6
  disclosure exactly; family constants match the S1/S6 tables; PE1's
  negative tautology audit of the sealed reader not re-walked
  (cited); the one padding defect found in the PE1 instrument is
  m-D.

## FRESH ROUTE (`gentow4_pe2_fresh.py`, md5 b4d795cb…, output
## 8e404c4c…, committed): **GREEN — 93 checks / 0 violations, dual
## PARI routes, all preregistered predictions exact**

Two frames disjoint from the battery and from FR-G/FR-M/FR-W, both
p = 3, Φ′ = x² − 6 (η = 2, f₁ = 1):

* **FR-T — the first NON-LINEAR wrap profile in any leg** (f₂ = 3,
  u₂ = 3, ψ₂ = Z³−Z+1, μ₂ = 2 on side [1,7] of genre (2,1,7);
  every prior η ≠ 1 contact had f₂ = 2 = one live W value; here
  W = (1,1,0), which no single rescale can absorb). Corrected key
  Φ′³ − 54Φ′ − 81x hand-derived from the S0 pin; PARI: σ = {(2,3)}
  = carrier. THREE-KEY tooth, all as predicted in advance: the
  NAIVE key Φ′³ − 27Φ′ − 162x has σ = {(2,1),(2,2)} — predicted
  exactly from the skewed letter polynomial Z³−2Z−2 = (Z−1)(Z²+Z+2)
  — and reads μ₂* = 0 (class invisible, pins (0,21),(1,12),(2,3)
  on the T₂ = 9 line); the λ = 2 RESCALED-DATUM key
  Φ′³ − 54Φ′ − 162x is a CARRIER (σ = {(2,3)}; 2β ∉ Galois orbit
  of β since β³ = β+1, β⁹ = β+2) yet ALSO reads μ₂* = 0 — first
  machine demonstration that carrier-σ alone does not certify the
  reader's key; the datum keying is load-bearing. Corrected-key
  reads: 2SIDED and RAM members exact (μ₂* = 2, c_g = 3, floors
  19/10 with j = 1 exact, σ = {(2,1),(2,3),(2,3)} / {(2,1),(4,3)}
  both routes); nfeltval: class rows 20,22,42 > 18 = E₂e strict
  with degree sums 12 = D₂μ₂*, naive rows 18 = 18 and 36 = 36
  exactly (floor collapse), sibling 18 = 18 at both keys.
* **FR-C — the first gauge-live TWO-BLOCK compound anywhere**
  (PE1's two firsts combined): genre (2,1,9), n = 18, side A [1,5]
  slope 5 carrying (Z²+Z+2)² (W = (1,0), key Φ′² − 18xΦ′ − 486,
  T₂ = 10), side B [5,9] slope 3 carrying (Z²+2Z+2)² (key
  Φ′² − 3xΦ′ − 54, T₂ = 6), sibling x² − 33; hull
  (0,38),(1,32),(5,12),(9,0). Three 2SIDED/RAM label combos: both
  classes read through their own corrected keys, μ₂* = 2 both
  (GENTOW-4.2's tie at two gauge-live pure sides simultaneously),
  c_g^A = 17 and c_g^B = 15 exactly as hand-derived (cross-block
  absorption 12 + 5 and 12 + 3), floors cleared with j = 1 exact at
  both, verdicts = design, σ = PARI both routes (σ_A ∪ σ_B ∪
  {(2,1)}). Both naive keys are non-carriers of a NEW shape pair
  (σ(KAN) = {(2,1),(2,1)}, σ(KBN) = {(4,1)} — the degenerate
  (Z+2)² letter, consistent with the erratum lineage's derived
  shapes) and read μ₂* = 0 at BOTH classes; nfeltval: strict
  separator + degree sums 8 at both corrected keys (companion rows
  AT E₂ on the steeper flank, BELOW on the shallower — P-5's
  geography reproduced), naive collapse exact at both.

## GRADE LINE

**CLEAN at passPE2: 0 CRITICAL, 0 GAP, 5 MINOR (m-A supply-route
attribution; m-B fullness-row count dissonance; m-C manifest shape
sentence; m-D check-count padding in the adopted PE1 rows; m-E
stale BOX-4 stack). Counter 0/2 ⇒ 1/2.** The r1 annex held under
independent re-derivation at all four sites; the corrected-key
mechanism held at two fresh geometries including the first
non-linear wrap profile and the first carrier-but-wrong-datum
tooth; sealed and PE1 legs reproduce bit-exactly. The minors are
one-clause-each repairs for the next dated append; none blocks the
arc.
