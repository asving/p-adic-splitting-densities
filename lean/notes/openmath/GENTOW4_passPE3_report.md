# GENTOW4 passPE3 — HOSTILE VERIFIER REPORT (acceptance attempt; fresh context, zero prior stake), 2026-08-10

**Target:** `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` at HEAD
(6e1a0f8c; arc: seal → PE1 1 GAP(CONFIRMED)/2m @ 8ae71864 → r1
annex (aa92a9d4/abd25133/eb526a0d) → PE2 CLEAN 0C/0G/5m @ 80280b66
→ rider a6587325/6e1a0f8c, the five minors folded; both hashes
verified in git). AS-OF states read: HETOW / GENTOW1 / GENTOW2 /
GENTOW5 accepted; GENTOW3/6 acceptance attempts in parallel (note
states read, not consumed). Protocol: quote-and-classify, fix
nothing. Prior routes NOT re-walked (PE1's bouquet re-derivation +
projection statement-vs-use audit + tautology audit; PE2's
four-site annex re-derivation and FR-G/FR-M/FR-W/FR-T/FR-C).

## VERDICT: **CLEAN — 0 CRITICAL, 0 GAP, 2 MINOR. Counter 1/2 ⇒ 2/2: GENTOW4 ACCEPTED.**

All five rider folds survive re-derivation at their primary sources
(each walked at the source display, not at the report's text). COR
GENTOW-4.C carries exactly what GENTOW-6.4(c)/6.2C(d)'s displayed
consumption needs, and its pin display now has an explicit-f_S
machine confirmation. The two-layer text reads as one system
(statement fence verified across all five rider commits). Machine:
six seals verified; all three prior instruments reproduce their
committed artifacts in isolated re-runs. Fresh route: two
out-of-battery geometries (first THREE-BLOCK member anywhere; first
f₂ = 4 frame anywhere) — 159/159 note-relevant checks GREEN, dual
PARI routes; the single instrument violation is this verifier's own
side-prediction, adjudicated below (it confirms, rather than
touches, the note's thesis).

---

## FINDINGS (all MINOR)

### m-i (MINOR — COR GENTOW-4.C's proof line "Translation: HE6R1-2(b)": the pin-level equality at side-INTERIOR hull abscissas also rides (c)'s residual correspondence)

Quote (4.C proof): "Right endpoint: displayed inside
GENTOW-4.A(ii)'s proof. Translation: HE6R1-2(b)." LEMMA HE6R1-2(b)
(HE6R1_RECON §S3.4, re-read this pass) is a SUPPORT-FUNCTION
identity — h_{F₂,f}(κ₂) = h_{F₂,f_S}(κ₂) + c_g on (T₂,∞), hence
same breakpoints/slopes/lengths. From (b) alone, at an abscissa j
where (j, p_j) lies on the >T₂ hull one gets p_j − c_g =
hull_{f_S}(j) ≤ p_j^S — the ≤ direction of 4.C's displayed equality
p_j^S = p_j − c_g is not yet supplied. At VERTICES of the segment
it follows from (b) + the vertex-attainment argument (4.1(b)'s
mechanism at the level-2 pin set). At side-INTERIOR lattice points
(the j = 1 of a one-side μ₂* = 2 shape) it needs the attainment
correspondence: f's residual and f_S's agree up to γ_g (the display
R^f_{λ₂} = γ_g·R^{f_S}_{λ₂} closing HE6R1-2(c)'s proof — quoted at
source this pass: "the term-residue assembly gives R^f_{λ₂} =
γ_g·R^{f_S}_{λ₂}"), so a nonzero interior residual coefficient on
one side is nonzero on the other, and interior attainment matches.
The claim is TRUE and the note's own (ii) already cites
"HE6R1-2(a)(b)(c) + RIDER" for the projection package; only 4.C's
one-word proof line under-cites. Nothing downstream is touched: the
floors consequence needs only slopes > T₂ + pin integrality, and
GENTOW-6.4(c)/6.2C(d) consume c_g = p_{μ₂*} + the floors + the
height correspondence, all carried. Machine: this pass's fresh leg
tested the equality AGAINST EXPLICIT f_S at every hull abscissa of
the block read on 11 members (incl. interior j = 1 at five 2SIDED
blocks) — held exactly, 0 violations. Failure scenario if
uncorrected: a reader reconstructing 4.C from "(b)" alone can prove
only p_j − c_g ≤ p_j^S at interior points and stalls on the
displayed equality. One clause ("(b) for the hull, (c)'s scalar
correspondence for interior attainment") closes it.

### m-ii (MINOR — the PE2 instrument's class-degree-sum checks are one-sided ≥; the note's S9 head adopts its "93/0" without an instrument-strength clause)

The adopted PE2 instrument (`gentow4_pe2_fresh.py`, cited at S9
head) tests strict-separator class mass with
`chk(tag, ncls >= want_sum, …)` — one-sided ≥, where the PE1
instrument (and this pass's) use ==. A row erroneously ABOVE E₂
would inflate ncls and still pass in strict mode. No vacuous branch
exists (the m-D defect is NOT present: its collapse-mode else emits
a real violation), the quoted numbers are all measured in the
committed output, and the artifact's rows (re-parsed this pass)
have exact class masses — so nothing is wrong at HEAD; the check is
merely weaker than the prose "class rows … with degree sums 12 =
D₂μ₂*" suggests. Same genre as m-D at one grade milder. Failure
scenario: a future frame adopted through the same instrument could
pass strict mode with a misclassified companion row. One disclosure
clause at the next dated append (or == in future instruments — this
pass's instrument already does).

---

## CLEAN CHARGES

**(1) The rider's five folds — each RE-DERIVED at source (surface
(1); none transcribed).**
* **m-A (the HE7-13′ supply route).** Walked at HE7_PROOF ANNEX
  F-1: ANNEX-LEMMA HE7-13′ is stated at "Let Ψ̃ = Ψ − W with W = 0
  or as in LEMMA HE7-12(d), and let f_S satisfy the standing
  convention at Ψ̃ (Ψ̃ ∤ f_S), all roots level-2 points" (L1664–67)
  — and the [r1]-restated LEMMA HETOW-2 (HETOW_RECON S2, L207–209)
  concludes "either w = 0 (in particular under the (LIFT)-slot
  coefficient form, at any f₁) or dv₂(w) > T₂", its F-4 proof leg
  deriving w = 0 outright under the (LIFT) form the S0 pin fixes.
  With w = 0, Φ₂ = Ψ literally, i.e. Φ₂ IS in HE7-13′'s hypothesis
  class at W = 0; the remaining hypotheses are supplied at the
  application site (Φ₂ ∤ f_S by 4.1(d)'s peel + the (ii) proof's
  equivalence; all-roots-level-2 by 4.1(b)). The other leg checked
  too: LEMMA HE7-12(c)'s displayed transport list DOES carry "LEMMA
  HE6R1-2's read" (HE7_PROOF L838) and does NOT carry HE7-13′
  (ANNEX F-1 postdates §S5.8). The bracket's routing is exact.
* **m-B (the five-row recount vs S3(iii)'s three).** Recounted
  against HETOW_RECON's S1 table directly: fullness enters at
  HETOW-1's r-row (its ψ₂(0) ≠ 0 step — confirmed in the restated
  HETOW-1(a)'s proof, which still consumes "at a FULL side the left
  endpoint … is an attained pin", exactly the step 4.1(b)'s
  endpoint-vertex argument replaces) and at HETOW-3's four rows
  (§S1-CONVENTION Ψ ∤ f_S; the label row "HETOW-3(b) (full side)";
  the f_S/μ₂ row "f_S = f"; the frame row "Φ′ ∤ f automatic at a
  full side"). Five rows; the ladder row's "equality at full side"
  is a tightness annotation on HE7.C's bound μ₁ ≥ μ₂e₂f₂ (which
  partial sides satisfy strictly), not a consumed hypothesis. The
  bracket's reconciliation (three replaced as named; the peel and
  frame rows discharged by 4.1(d) via the theorem's "after the S2
  peels" preamble) is exact.
* **m-C (the manifest shape).** `git diff d7ddf2e..eb526a0d`
  re-run: 265+/14−. All 14 deletion lines mapped this pass to the
  manifest's disclosed sites: 3 at the S2 count rewrite (THREE →
  TWO, original preserved in the [GT4-r1 (m-1)] bracket), 1 at the
  S2 audit bracket, 2 at 4.1(c)'s re-point, 1 at the S3 r̃ bracket,
  5 at the S4 remark (the parenthetical rewrite + scope pin; the
  composed "at f1 = 1" wording preserved in brackets at both the
  site and the S8.4 record), 1 at BOX-3, 1 at the T-2 disclosure.
  Exactly TWO in-place rewrites, as the bracket names them; the
  rider-round diff itself (eb526a0d..HEAD) deletes only 4 re-wrap
  lines, all in proof prose/audit records — the statement displays
  of THEOREM GENTOW-4.A, LEMMA GENTOW-4.2, COR GENTOW-4.C are
  untouched across the whole arc (statement fence verified).
* **m-D (the 14/79 recount).** Re-derived WITHOUT running the
  instrumented copy: the else-branch `chk(tag, 4*v_ <= E2*e_,
  'sep')` (gentow4_pe1_fresh.py L482) fires once per non-class
  factor row per key; FR-M's members carry 4/4/3 factor rows, so
  non-class rows = (3+2) + (2+3) + (2+2) = 14 across 3 members × 2
  keys — EXACTLY the bracket's census (79 falsifiable). The
  degree-sum backstop is real: 6 checks `ncls == 8`, two-sided.
* **m-E (the BOX-4 refresh).** All three re-dated grades verified
  at the arc records: HETOW "1/2 → 2/2 — HETOW ACCEPTED"
  (HETOW_RECON L615, PE3); GENTOW-1 "counter closed 1/2 -> 2/2 —
  ACCEPTED" @ 4aff731 with "the 2/2 acceptance stands" through
  R2a/b/c (GENTOW1_PROOF L737/L854); HE6R1 "ACCEPTED (2/2) and
  FROZEN" (HE6R1_RECON L797–98). Staleness was conservative, as the
  bracket says.

**(2) COR GENTOW-4.C vs GENTOW6's cap lemma (the
conditionality-upgrade surface).** LEMMA GENTOW-6.4(c) consumes: "(block value at block
height m) = (f-value at height m + c_g) − c_g (HE6R1-2(b) + COR
GENTOW-4.C …)" and "(c_g = p_{μ₂*} is itself a computed value …)";
COR GENTOW-6.2C(d) consumes "COR GENTOW-4.C proved p_j^S = p_j −
c_g on the >T2 hull and already transported the node floors". 4.C's
statement carries all three consumed items: (i) c_g = the height of
P₂(f) at abscissa μ₂* — re-derived: the >T₂ initial segment is
P₂(f_S)+c_g (HE6R1-2(b)) with right endpoint (μ₂*, 0)+c_g, and that
right endpoint is a slope-transition vertex of P₂(f), hence an
attained pin, giving c_g = p_{μ₂*} exactly as 6.4(c) needs; (ii)
the pin translation on the >T₂ hull (m-i's citation note; the
equality itself TRUE and machine-confirmed vs explicit f_S); (iii)
the floor transport — re-derived: f_S is monic of degree D₂μ₂* =
D′(e₂f₂μ₂*) with all roots in the class (level-1 polygon = ONE side
of slope κ₂, residual forced ψ₂^{μ₂*} by degree + radical), i.e.
GENTOW-1's 𝒯 definition (GENTOW1_PROOF S2) at genre (Q; e₁,f₁,
e₂f₂μ₂*; h) with the same (u₂,e₂,ψ₂), so GENTOW-1(a)(c)(d) fire at
the block and translate up by c_g. The cap lemma's citation
discipline ("at GENTOW4's 0/2 attempt grade, conditional") is
GENTOW6's own bookkeeping; with this acceptance the named
conditionality upgrades on GENTOW6's side.

**(3) The two-layer text as one system.** Header ARC ↔ S9 ↔ the
five fold sites consistent (sites: S8.1 ×2, S3(iii), S8.4, S7
BOX-4 — all located and read in place); [GT4-r1] vs [rider
(post-PE2)] brackets dated and non-overlapping; 4.1(c)'s bracket
matches the restated HETOW-2's hence-list verbatim (§S5 package,
HE7.A(1)(2), refine package, §S1 CONVENTION + HE6R1-3 — with
HE6R1-2/RIDER and HE7-13′ routed per m-A); the S3 r̃ bracket
matches the restated HETOW-1 exactly (one definition
η^{−Qd_r}·r(η^{Q}Z); clause (b) pointwise/wrap-free "no product of
normalizers occurs"; slot-residue clause (c) at the corrected key
only); S9's "counter HOLDS at 1/2 (a rider is not a pass)" and
"PE3 next" consistent with the arc. PE1/PE2 report hashes 8ae71864
/ 80280b66 verified as the actual report commits.

## MACHINE LEGS

* **Seals:** all six md5s verified at HEAD — gentow4_checks.py
  98cdd4a4…, output 58f35305…, gentow4_pe1_fresh.py 5dc455dd…,
  output dac5110c…, gentow4_pe2_fresh.py b4d795cb…, output
  8e404c4c… .
* **Isolated re-runs (fresh /tmp copies, one detached batch):**
  sealed battery — GREEN, 1,740 checks / 0 violations, output
  IDENTICAL to the committed artifact from line 2 (line-1 timestamp
  only); PE1 instrument — GREEN 93/0, byte-identical; PE2
  instrument — GREEN 93/0, byte-identical.
* **Tautology/padding audit (this pass's own):** the m-D recount
  above (14 vacuous, arithmetic-derived); the PE2 instrument has NO
  vacuous branch (its collapse-mode else emits real violations) but
  carries the one-sided ≥ of m-ii; this pass's instrument uses
  two-sided == sums and no self-testing branch.

## FRESH ROUTE (`gentow4_pe3_fresh.py` md5 74787ac0…, SEALED with
## prereg docstring @ bad9177c BEFORE the run; output ec1330b0…
## committed as-run @ e3a0c359): **159/159 note-relevant checks
## GREEN, dual PARI routes; 1 instrument-side prereg misfire,
## disclosed and adjudicated below. Frames disjoint from the
## battery and from FR-G/FR-M/FR-W/FR-T/FR-C.**

* **FR-3B — the first THREE-BLOCK partial member anywhere,
  gauge-live** (p = 3, Φ′ = x²−6, η = 2, genre (2,1,13), n = 26:
  three inner classes (T₂ = 14/10/6, ψ₂ = Z²+Z+2 / Z²+2Z+2 / Z²+1)
  on three sides plus a slope-8 sibling; battery/prior-leg max was
  two blocks). Three members, all label mixes: every class read
  through ITS OWN corrected key with μ₂* = 2 (LEMMA GENTOW-4.2's
  tie at THREE pure-power sides simultaneously — first exercise),
  c_g = 39/37/27 exactly as hand-derived (each class's c_g absorbs
  BOTH other blocks + the sibling: 20+12+7, 20+12+5, 12+12+3),
  floors cleared with j = 1 EXACT at every 2SIDED block, verdicts =
  design, σ = PARI both routes (σ_A ∪ σ_B ∪ σ_C ∪ {(2,1)});
  nfeltval separators strict with class degree sums == 8 at all
  NINE (member, key) pairs; GENTOW-4.A(iv)'s co-class recursion at
  three simultaneous tower classes. TOOTH: all three naive keys
  collapse (μ₂* = 0) on every member, each with initial hull slope
  AT T₂ exactly — 9/9 kills; naive-key σ measured: KAN
  {(2,1),(2,1)}, KCN {(2,1),(2,1)} (the GHOST-SPLIT datum: the
  naive key IS the corrected key of the reducible datum Z²−1,
  predicted in advance), KBN — see the adjudication.
* **FR-Q — the first f₂ ≥ 4 frame anywhere** (p = 3, Φ′ = x²−6,
  (e₂,f₂) = (1,4), ψ₂ = Z⁴+Z+2 irreducible /F₃, u₂ = 3, genre
  (2,1,9), n = 18, D₂ = 8, W = (2,1,1,0) — non-linear with the
  first even entry; η² = 1 makes W-even slots gauge-blind, so the
  entire correction lives at t = 1). Corrected key Φ′⁴ − 81xΦ′ −
  729 hand-derived from the S0 pin; both members read exactly
  (μ₂* = 2, c_g = 3, floors 25/13 with j = 1 exact, σ =
  {(2,1),(2,4),(2,4)} / {(2,1),(4,4)} both routes, class degree
  sums == 16 = D₂μ₂*, sibling AT E₂). **THE MERGED TOOTH
  (preregistered and confirmed):** the naive key Φ′⁴ − 162xΦ′ − 729
  is BYTE-IDENTICAL to the corrected key of the λ = 2 rescaled
  datum (minpoly of 2β, Z⁴−Z−1) — at f₂ = 4 with η² = 1 the
  gauge-naive and carrier-but-wrong-datum teeth MERGE: σ(KQN) =
  {(2,4)}, a genuine carrier, yet the read at it collapses (μ₂* = 0
  both members, naive class rows at 2v = 12e exactly). Datum keying
  alone separates them — PE2's FR-T thesis at the first f₂ = 4
  contact.
* **COR GENTOW-4.C explicit-f_S leg (first anywhere):** on all 11
  blocks-in-members above, the pin display p_j^S = p_j − c_g was
  tested as an EQUATION against the explicitly constructed f_S at
  every hull abscissa of the block read (j = 0,1,2 at 2SIDED
  blocks incl. the side-interior j = 1; j = 0,2 at RAM) — 0
  violations. m-i's interior-equality leg is machine-witnessed.
* **The one violation, adjudicated:** prereg side-bet "σ(KBN) ≠
  {(2,2)}" misfired — PARI: KBN = Φ′² − 9xΦ′ − 243 IS a
  (2,2)-carrier, though its coherent letter datum is the degenerate
  (Z−2)². This is a claim NO line of the note makes (the note's
  naive-σ sentences are frame-specific and measured); the misfire
  is this verifier's over-generalization of FR-C's observed naive
  shapes, and its content — a third carrier-with-wrong-datum
  instance — CONFIRMS the corpus thesis that carrier-σ does not
  certify the reader's key. The load-bearing tooth at that same key
  (naive collapse, μ₂* = 0) fired on all three members. Instrument
  sealed pre-run, output committed as-run, nothing edited.

## GRADE LINE

**CLEAN at passPE3: 0 CRITICAL, 0 GAP, 2 MINOR (m-i the 4.C proof
line's (b)-only citation at interior pins; m-ii the PE2
instrument's one-sided sum). Counter 1/2 ⇒ 2/2 — GENTOW4 ACCEPTED
(the partial-sides note through the bar).** The rider held at all
five folds under source re-derivation; COR GENTOW-4.C supplies
exactly what GENTOW6's cap lemma displays as consumed (its
conditional citation may now upgrade on GENTOW6's side); the
corrected-key mechanism held at two new geometries (first
three-block member; first f₂ = 4 frame, with the merged
naive/rescale tooth); all sealed legs reproduce bit-exactly. The
two minors are one-clause next-append items; neither blocks
acceptance.
