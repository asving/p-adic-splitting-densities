# HEX3 passPE6 report — hostile verification of HEX3_PROOF_2026-08-08.md at r4 (fa7b70d)

**VERDICT: CLEAN under this pass's charge bar (0 CRITICAL + 0
JUSTIFICATION GAPS + 2 MINOR) — nothing GAP-or-worse survived
verification. Counter 0/2 → 1/2 per the PE6 charge ("CLEAN only if
nothing GAP-or-worse survives"). ADJUDICATION FLAG, displayed
honestly:** under the arc's PE4/PE5-era convention ("a finding,
however small, is not a clean pass") the same result would read NOT
CLEAN 0C+0G+2m with the counter staying 0/2 — the two conventions
disagree exactly here, and the adjudicator owns the choice. Both
findings are display-level, in non-theorem prose (one in the OPEN
HEX3-BOX-1's mechanism gloss, one pure record-keeping), with verified
zero blast radius on HEX3.A/B/C, the transport lemmas, the species
table, and every consumer. Neither dents the (hExhaust-3) discharge.

**Pass:** PE6 (sixth hostile pass; arc PE1 0C+2G+2m @ d177fd8 → r1 →
PE2 0C+1G+1m @ f60348b → r2 → PE3 CLEAN @ fca1a97 (1/2) → PE4
0C+0G+1m @ 34a946b (counter reset) → r3 @ b6a1d69 → PE5 NOT CLEAN
0C+0G+2m → r4 @ fa7b70d = the target audited here). **Verifier:**
fresh-context Fable, 2026-08-09, zero prior stake; the five prior
reports read first, their routes not re-walked. **Target byte-state:**
HEX3_PROOF at HEAD == fa7b70d; runner md5 83faf7ed… == seal e3f3459
(`git diff e3f3459..HEAD -- hex3_checks.py` empty); committed artifact
md5s == §S10's display (6e4b3207…, ce6f4116…) — the r4 commit's
"sealed artifacts untouched" claim verified at byte level.

---

## m1 [MINOR] — HEX3-BOX-1's mechanism gloss "every drain event happens inside a transported W-11 block frame" (L441-442) is false at the B0ZERO and α-recentering drains — 100% of the drains of committed row (Zp,2,4)

Quote (S6, HEX3-BOX-1, the mechanism-display sentence):

> The mechanism is displayed by this note's own machinery: every drain
> event happens inside a transported W-11 block frame, where R(M) =
> q^{M−1} [strictly hidden] + ⌊(M−1)/2⌋(q−1)q^{M−2} [W-11 SPLIT-TAIL
> states, block-certifiable] — so the certifiable candidates are
> exactly the transported SPLIT-TAIL masses plus the B0ZERO states
> with visible separated B₁-vertex, and a certification lemma would
> turn the same species table into the U₃^σ law by replacing R with
> its certified/uncertified split.

The universal first clause is contradicted by the note's own S5.1
species table and by the committed artifacts: (i) B0ZERO members
(locus q^{2N−2} per center — the DOMINANT drained mass) exit at the
TRP frame with no W-11 block frame in sight; (ii) α-chain drains exit
at an α-recentered TRP frame (the scaled window's B0ZERO), also
block-free. Machine anchor, read from the committed
`hex3_checks_results.json` this pass: row (Zp, 2, 4) has species tally
B0ZERO (64, 64) + ALPHA(1) (8, 8) + DECIDED (440, 0) and NO β keys —
all 72 drains of that committed row happen at TRP frames, so the
clause is false at 100% of them. The sentence's own continuation
("plus the B0ZERO states with visible separated B₁-vertex")
self-corrects the candidate list, and the trailing "replacing R with
its certified/uncertified split" is a shorthand that under-covers the
B0ZERO row (whose drained column is q^{2N−2}, not an R-expression —
its certified/uncertified split is ALSO needed for the U₃^σ law).
FAILURE SCENARIO: a W-13 prover consuming BOX-1 as the priced work
order (S0 advertises "priced with its exact mechanism") takes the
universal clause literally and builds the U₃^σ law by splitting R
alone, silently dropping the dominant B0ZERO leg. BLAST RADIUS inside
HEX3: zero — no theorem, count, lemma, or consumer (S0, S8.1, S8.2,
W-12's applied annex) consumes the clause; the candidates list itself
names the B0ZERO leg. Repair shape (one clause): "every drain event
happens either at a (possibly α-scaled) TRP frame's B0ZERO exit or
inside a transported W-11 block frame", + extend the final shorthand
to name the B0ZERO row's own split. This sentence is seal-era text
untouched by r1-r4 and unflagged by PE1-PE5.

## m2 [MINOR] — the r4 repair broke the arc-record convention: the header, HEX3-BOX-2, and §S10 all still end at "r3 … counter 0/2; PE5 next" while the two [r4] brackets cite PE5's findings — the note at HEAD is internally inconsistent about its own arc state

The r4 diff (fa7b70d, 27 insertions) touched exactly the two repair
sites (S0 L81-93, S6 L450-462). Each prior repair (r1 @ 2580f12, r2 @
a707430, r3 @ b6a1d69) also appended its arc block to §S10 and
updated the header + BOX-2 records; r4 did not. At HEAD: the header
(L11-17) ends "r3 THIS REPAIR … counter 0/2; PE5 next"; BOX-2
(L466-481) ends "r3 applied, counter 0/2 [r3]"; §S10's bracket
(L811-829) ends "counter 0/2; PE5 next" — while L82 and L453 carry
"[r4, PE5 m1: …]" / "[r4, PE5 m2: …]". FAILURE SCENARIO: a reader
consuming the note's grade box at HEAD (the corpus convention: the
note IS the record) concludes PE5 has not run and prices the arc one
pass short. BLAST RADIUS: zero mathematical content; the grade 0/2
itself is currently correct. Repair shape: the standard [r4] arc-cont.
block at the three record sites (and it can fold this pass's outcome
in the same touch).

---

## Charge-by-charge record

**(1) The r4 lines, attacked clause by clause — CORRECT and faithful.**
* S0 [r4] bracket: the counter-instance transcription (eq-char 3,
  in-window TRP-RAM3(h) member, 3∤h, b₁ = b₂ = 0, lift F = y³ + b₀,
  F′ ≡ 0, disc = 0, no σ) matches W-12's own [r4] m2 record at its
  S2.3 site (W12_PROOF L598-607) clause for clause; disc(y³+b₀) =
  −27b₀² = 0 in char 3 re-derived here. The counter-instance member IS
  conservative-DECIDED (RAM3 row of S2.4's table), so the restriction
  is load-bearing, and the repaired warrant ("Ore applies to every
  disc ≠ 0 lift — W-12 S2.3, post-[r4] form") matches the surviving
  S2.3 sentence ("(A0)-strongly (every disc ≠ 0 lift has this σ)").
* The inequality's re-derivation in the bracket is valid: U₃^σ's S0
  definition quantifies over disc ≠ 0 lifts only (first bullet,
  verbatim), post-r4 S2.3 pins one σ across a decided member's
  disc ≠ 0 lifts, so no conservative-DECIDED member enters U₃^σ; the
  disc = 0 lifts witness nothing. U₃^σ ≤ U₃^conv stands at the pinned
  notion.
* The cited sweep row exists and says what is claimed: W12_PROOF L1768
  dispositions "HEX3_PROOF L80–81 … SAME loose phrasing, conclusion
  UNAFFECTED … A phrasing correction owed at HEX3's own arc; no number
  and no box moves" — the owed correction is exactly what r4 landed.
* S6 [r4] bracket (PE5 m2): "W12-S3.2's species is b₁ = b₀ = 0 with b₂
  FREE (q centers × q^{N−1} free b₂)" matches LEMMA W12-S3.2's
  statement + count verbatim (W12_PROOF L837-839, L870-871); the
  four consuming sites of the q^N lower bound enumerated in the
  bracket (S0 cite, S1 display, the box's own bracket, S8.1) each
  checked — each carries the bare inequality/statement form.

**(2) The (hExhaust-3) discharge handoff at W-12's CURRENT text
(fa3acb2-era HEAD, post-PE7 acceptance, r5 + ANNEX 2) — FAITHFUL.**
What (A2) at n = 3 needs (W-12.D display L292-295 + the S3.4
conditionality paragraph L1080-1101): r(3,N)/q^{3N} → 0 with r =
σ-undecided DBL (PROVED, S3.1) + DBL boundary tails (PROVED, the [r2]
leg, mass ⌊(N−1)/2⌋(q−1)²q^{2N−2}) + the TRP legs + non-menu decided
mass ((hMenu-3), not HEX3's charge). What HEX3.B hands: under W-12's
r3 σ-pin (BOX-7 clause 1), U₃^conv = (σ-undecided TRP) ⊔ (σ-certified
TRP boundary tails) EXACTLY — the disjoint union re-derived this pass
from the pin's dichotomy — so THEOREM HEX3.B's single bound
U₃^conv ≤ N·q^{2N−1} covers BOTH TRP legs at once (sum exactly
U₃^conv, not 2×), which is precisely S3.4's parenthetical requirement
("whose conservative-convention bound also drains the TRP members
σ-decided only by tail certification … no TRP tail leg is separately
owed", L1098-1101). W12-BOX-3's named obligation ("a vanishing U₃^TRP
upper bound", U₃^TRP = the pinned σ-undecided TRP mass per the [r3]
pin) is supplied by q^N ≤ U₃^σ ≤ U₃^conv ≤ N·q^{2N−1}. Byte checks
this pass: HEX3 S0's "W12-BOX-3, verbatim" quote == the W12-BOX-3
text (machine-normalized diff, True); HEX3 §S8.1 == the applied annex
at W12_PROOF L1672-1683 (True). The r5-era additions (the HMENU3
ANNEX 2 + firing-table row) consume HEX3 only through the same
annexed chain; HEX3-BOX-4's "No claim that W-12.D fires at n = 3 yet"
is now a conservative under-claim given ANNEX 2's composition-grade
closure — harmless staleness, not a finding (it under-claims).

**(3) The σ-pin scope sentence (HEX3-BOX-1) — re-derived, CORRECT.**
From BOX-7 clause 1 ("Decided = certified on window digits for all
disc ≠ 0 lifts"): U₃^conv − U₃^σ = the conv-UNDECIDED members whose
visible data force one σ on all disc ≠ 0 lifts = exactly the tail-exit
states BOX-1's sentence asks about ("when does a B₀ = 0 exit state's
VISIBLE data pin σ for all disc ≠ 0 lifts?"). The box's quantifier
already carries the post-r4 disc ≠ 0 restriction — no correction owed
there. The only defect found in the box is m1's mechanism gloss.

**(4) q-uniformity of the displayed derivation at non-prime q —
NO-GAP.** Sites audited for hidden primality: the α pins (universal
(y−z)³ identities; char-3 degeneration to (0,0,−z³) stays one pinned
triple per letter, z ↦ z³ Frobenius-injective on any F_q); the β2 pin
pair z ↦ (−2z, z²) (injective via −2z in odd char, via Frobenius in
char 2 — stated in S2 and correct for q = p^d); the β1 letter count
(q−1)(q−2) (pure field-size count; exact zero at q = 2, which the
battery's FULL11SQ-absent rows confirm); S4's instance bracket
Σ_H (q−1)^t = q^{w−1} (binomial identity in q); S5's assembly (pure
algebra in q). No step consults primality, primitive roots, or ℤ/q
structure; digit slots count |F_q| = q throughout. Machine coverage
of non-prime q: eq-char rows q = 4, 8, 9 (battery) + 16, 25, 27
(PE5); mixed-characteristic prime-power DVRs (W(F_4)-type, ramified
O) have NO machine row anywhere in the corpus — an ALREADY-DISCLOSED
seam (HEX3-BOX-3 "eq-char prime powers carried by Fqt rows only",
inheriting W12-BOX-6). The derivation itself was re-read for
O-genericity: the pins compute in the residue field with integer
coefficients reduced mod p (checked to hold verbatim for ramified
mixed-char O, e.g. ℤ_3[√3], where 3 = π²·unit still reduces to 0),
and carries move upward in any complete DVR. Not a finding.

**(5) Free hunt (beyond the two findings).** The S1 anchor u(2,7) =
5664 re-verified in both displayed decompositions (telescoped 4096 +
1440 + 128; first-step 4096 + 1504 + 64); HEX3.B's chain re-checked
((q−1+N)q^{2N−1} ≤ (1+N)q^{2N}; B0ZERO alone gives q^{2N−1} ≤
U₃^conv; Nq^{2N−1} ≤ q^{3N−2} ⟺ N ≤ q^{N−1}); R(1) = 1 consistent
across S1/S4; the S5.1 k-bracket collapse (q−2)+1+1 → q re-checked.

## Machine leg (fresh this session)

* PINS: the four md5s in the runner's pin block (w12_checks.py 7dc0…,
  w11_checks.py 500a…, w10_checks.py a9c3…, w12 JSON 0577…) re-hashed
  == pinned; runner md5 83faf7ed… == seal e3f3459.
* ISOLATED full re-run: import closure (21 .py + the w12 JSON)
  computed by AST walk and copied to /tmp/hex3_pe6_run, run OUTSIDE
  the repo: **GREEN, 158,512 checks / 0 violations** — PIN 4, LAW 92,
  SPECIES 172, XREAD 158,204, W12TIE 23, CHAR 17; teeth fired
  10/20/13 == preregistered; 46/46 rows, 330.5 s. Recursive JSON diff
  vs the committed artifact: 21 leaves, all elapsed-timing, ZERO
  non-timing. Repo artifacts byte-untouched by the run.
* TAUTOLOGY AUDIT (own read of the runner, end to end): u_measured
  comes only from `read_fresh` enumeration; `u_law`/`species_pred`
  are separate closed-form evaluators; the three teeth compare
  CORRUPTED predictions to MEASUREMENT and go RED if a corruption
  matches (checked at the code: `viol(... 'corrupted law matched
  measurement')`); W12TIE compares q·u_measured (not the law) to the
  committed JSON; CHAR compares raw tallies; XREAD ties the fresh
  reader pointwise to the sealed `W12.read_trp`. Non-tautological in
  each family.

## Fresh route — the W-12 (A2)/σ-pin handoff machine-checked END-TO-END at one wild cell (disjoint from PE1-PE5's routes; first PARI/σ leg of this arc — HEX3-BOX-3 disclosed "no PARI leg here")

Cell (Zp, q = 3, N = 4): mixed characteristic, p = 3 — the wild prime
for cubics, and not one of HMENU3's four oracle rows. Instruments
written fresh this pass (/tmp/hex3_pe6_fresh/{reader.py, make_lifts.py,
sigma.gp, compare.py}): my own conservative TRP reader implemented
from HEX3 S1's spec alone, plus a PARI σ-oracle (gp 2.17.4,
factorpadic + per-factor nfinit([G,[3]]) + idealprimedec — the
corpus-standard nfinit route, written fresh; 6 preregistered
calibration cases incl. the wild x³−3 ↦ (3,1), abort-on-mismatch).
* Reader validation: u(3,4) measured 837 == THEOREM HEX3.A's law (own
  transcription) == the committed w12 JSON's (Zp,3,4) U3TRP/q = 2511/3;
  the decided-σ histogram == W12-S2.4's family counts re-derived from
  the table at this cell (RAM3 14,580 = 2·3⁸+2·3⁶; LINRAM2 3,888 =
  4·3⁶+4·3⁵; FULL-(3) 216 = 8·27; FULL-(1,2) 162 = 6·27).
* σ-PIN TOOTH (the S0 warrant, post-r4 form, at the wild prime): for
  each of the 18,846 conservative-DECIDED members of the cell, 3
  random disc ≠ 0 lifts (disc computed exactly over ℤ; 56,538 lifts):
  **0 pin violations** (each member's three lifts share ONE σ) and
  **0 read-tie violations** (that σ == my reader's Ore σ) — 14,580 of
  the members are wild RAM3 whose lifts PARI scores (3,1). A single
  decided member with two sampled disc ≠ 0 lifts of distinct σ would
  have refuted the repaired S0 inequality's warrant; none exists in
  the sample.
* AMBIGUITY TOOTH (the q^N lower-bound leg, mechanism-free): each of
  the 27 W12-S3.2 species members of the cell (b₁ = b₀ = 0, b₂ free;
  center 0) yielded ≥ 2 distinct σ among 60 random disc ≠ 0 lifts —
  no F_A/F_B transcription, pure random search; the b₂ = 0 member
  (the r4-repaired branch of W12-S3.2) shows five distinct σ incl.
  (3,1) and (1,3). All 27 are conv-UNDECIDED under my reader (B₀ = 0
  at once). Together the two teeth machine-instantiate, at one wild
  cell, exactly the two inequalities HEX3 hands (A2): σ-ambiguity
  lives inside conv-UNDECIDED (≥ 81 = 3⁴ members), and
  conservative-DECIDED members carry one pinned σ.
* FRESH-ROUTE VERDICT: GREEN (58,158 oracle lifts, 0 violations).
* Own-instrument disclosures (caught by own calibration/validation,
  note untouched): (a) first oracle draft used nfinit(G) full-disc
  factorization — PARI stack overflow + ~200× slowdown; replaced by
  the corpus idiom nfinit([G,[3]]); (b) one comparator regex bug,
  fixed before any scoring.

## Grade line

**PE6 = CLEAN under the charge bar (0C + 0G + 2m; nothing
GAP-or-worse): counter 0/2 → 1/2.** The two MINORs (m1 the BOX-1
mechanism gloss, m2 the r4 arc-record staleness) are one-touch display
repairs owed at the next fold; under the strict PE4/PE5-era
any-finding convention this pass would instead read NOT CLEAN with
counter 0/2 — adjudicator's call, both readings displayed. Nothing
else in the note is known-unmined to this verifier: the theorems, the
transports, the r4 lines, the (A2) handoff at W-12's accepted HEAD,
the σ-pin scope, q-uniformity, the seal, and the first σ-oracle leg
of the arc all held.

*(Machine-leg artifacts: /tmp/hex3_pe6_run/{full_run.log,
hex3_checks_results.json}; fresh-route artifacts:
/tmp/hex3_pe6_fresh/{reader.py, make_lifts.py, sigma.gp, compare.py,
oracle_out.txt, decided.txt}.)*
