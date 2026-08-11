# WFRAME passPE2 — hostile verification report (second pass, RCT round 1)
## Target: WFRAME_NOTE_2026-08-10.md @ 520491ad (post-r1; PE1 was 0C/1G/3m @ 3db65096) — 2026-08-10

**VERDICT: CLEAN — nothing at GAP-or-worse survives. Grade ⇒ 1/2.**
(1 MINOR residual F-2′; details + full verification log below,
fresh-leg headline: the 9th prime MEASURED the first w-avatar = 1
geography and the note's enumerative discipline held exactly.)

Surfaces this pass: (1) the r1 folds (LP1 row vs sources; avatar
re-keying completeness — every "w ≠ 1" site; R-7 numbers); (2) the §4
table under the r1-minted sanity rule deg Φ′ = e₁f₁, row-wise;
(3) the note as one text post-r1; (4) free hunt. Machine: seal,
isolated re-run, tautology audit. Fresh route: disjoint from GF29 and
the committed record.

## Findings ledger (running)
- F-2′ (MINOR): §5 counts not swept by the r1 R-7 adoption (OPEN-3
  "7-prime record"/"4 frames"; OPEN-4 "7 measured primes" —
  source-dated but un-bracketed). No false claim; undercounts only.
- Machine leg: PENDING
- Fresh route: PENDING

**Resume note (session 2, same pass).** The session that committed
"1 of 3" (ee9a2d5f) died before the machine leg. This session
re-verified its surface-1 claims from the sources before resuming
(hostile discipline: nothing inherited unchecked): Φ′_LP1 =
x⁴+2x²+4 re-confirmed at GENTOW2_PROOF ~L1140 + pe4 L18 + pe6 L50;
the w-language grep re-run at HEAD (15 sites) and the classification
re-checked site-by-site — consequence (i)/F19 avatar-keyed, R-6's
"at measured w != 1" is PE3 LEG W's own sentence (L286 verified),
OPEN-4's "7 measured primes" is GENTOW5's [GT5-r3 DATED] wording
(L1321–22 verified), §7's joint-frame phrase is the byte-frozen
docstring; the LW3 citation re-verified against GENTOW5_WI ("avatar
w_av = 2 = w_3 * (gap unit 2)", L454). All held; F-2′ stands as the
one residual.

## Verification log (running)

**r1 fold, F-1 (the GAP).** §4 tower row now reads Φ′_LP1 =
x⁴+2x²+4. Verified against all three cited sources: GENTOW2_PROOF
~L1140 ("Φ′_LP1 = x⁴ + 2x² + 4, Φ₂_LP1 = Φ′² − 8x³, (e, f) =
(4, 2)"), gentow2_pe4_fresh.py L18 ("PHIP = x^4 + 2x^2 + 4"),
gentow2_pe6_fresh.py L50 ("LP1: PHIP = x^4+2x^2+4, PHI2 =
PHIP^2-8x^3"). The rest of the row's LP1/GB data re-checked against
the pe6 runner header (e₁,f₁,z₁ live/e₂,f₂,z₂=1,u₂=9,V₂=4,e(µ₂)=4;
GB: u₂=5,V₂=2,π₃=Φ′/x²): match. HOLDS.

**The sanity rule, row-wise (surface 2).** deg Φ′ = e₁f₁: LP1 deg 4 =
2·2 ✓; GB deg 2 = 2·1 ✓. The table's rows carry no Φ′ of their own
(towers named LP1/GB only), so the rule binds at the two tower
declarations — both green. Floors re-checked: LD1 κ₃ = 19 > e₂f₂u₂ =
18 (LP1); GA1 21, GA3 41, GF29 29 > 20 (GB). HOLDS.

**r1 fold, F-2 (IDY caveat) vs the instrument's actual code.**
wframe_note_checks.py: U0 ratio vector = n̂₂(2u₃) − 2u₃·π₃ =
[n̂₂(2u₃) − 2n̂₂(u₃)] + 2[n̂₂(u₃) − u₃π₃] = TH0 + 2·W vectors
identically; split() is linear where defined; the {f}.IDY check
compares lhs = U0-split letter vs rhs = TH0[f] + 2·PRED_W[f] — with
WAVA green these coincide, so IDY is entailed exactly as the folded
§7 caveat states. The discriminating rows are WAVA/TH0/U0 against
PRED_* = the PE6-measured pins, as the caveat says. FAITHFUL.

**r1 fold, F-3 (as-of dating of OPEN-1).** GENTOW5_WI_passPE2 is
in-flight (skeleton committed 17:10, AFTER the r1 fold 17:03;
verdict PENDING at this writing), so "arc at 1/2, not yet ACCEPTED"
was true at commit and remains true. The LW3 citation in consequence
(i) re-verified against GENTOW5_WI_2026-08-10.md: "avatar w_av = 2 =
w_3 * (gap unit 2)", "w = 1 ... MEASURED (= 1 at LW3's prime)" —
w₃ = 1, avatar 2, gap unit 2 as the note states. HOLDS.

**r1 fold, F-4 (avatar re-keying) — the grep sweep.** Every
"w ≠ 1"/"w = 1"/"w ≡ 1" site at HEAD classified:
* Re-keyed correctly: consequence (i) (avatar subject + LW3 rider);
  the F19 rule (subject = the measured avatar, w-reading on the
  row-23 leg). Both read clean.
* Genuinely about w (no action): §1 DEF W-1 ("w = 1 is a possible
  value"); §6 leg (c) and the F19 audit's hypothesis names ("assume
  w = 1/w ≠ 1"); OPEN-4's question itself.
* Source-attributed carriage (survives, see F-2′ below): the charge
  preamble's "the w ≠ 1 measurement records" + the blueprint name
  "w ≠ 1 as-of note" (proper names); R-6's cell "at measured w ≠ 1"
  (= PE3 LEG W's own sentence, L286 "verified on the nose at
  measured w != 1"); §7's joint-frame "measured w != 1" (= the
  sealed instrument's own docstring, byte-frozen); OPEN-4's "at the
  7 measured primes w ≠ 1" (= GENTOW5's dated-note wording, L1321-2
  "w is MEASURED != 1 at the 7 measured primes", attributed inline).
* Residual (new finding F-2′, MINOR): §5's counts were not swept by
  the r1 R-7 adoption — OPEN-3 says "the 7-prime record measures w
  at its frames" and "a measured pattern at 4 frames" (now 8 primes
  / 5 frames incl. GF29, per §4's own header and consequence (iii));
  OPEN-4 says "at the 7 measured primes" (source-dated wording, but
  un-bracketed). No false claim (true of the 7/4 named; undercounts
  only), subjects partly w-keyed where the sources' own sentences
  are w-keyed. MINOR.

**r1 fold, R-7 adoption numbers.** Row R-7 vs the PE1 addendum:
frame (GB; 1,2,29), target y²+y+z₂, 1 prime, avatar z₂ ≠ 1 ≠ z₂²
(third u₃-discrimination pair vs R-3), ϑ(0) = z₂², u(β₀) = z₂,
naive twin y²+z₂y+z₂² → TWO (4,2) vs law ONE (4,4), twin's two
primes same avatar — all match the addendum. Artifact md5s
re-computed: runner 15935529… ✓, run-2 output 3e45cc3e… ✓, run-1
0189b034… ✓ (RED kept). Preregistration order verified: 63890e5e
(14:17, report + predictions only) strictly precedes the run/verdict
commit 3db65096 (14:34, runner + outputs). Hand re-derivation of the
R-7 letters redone independently: n̂₂(29) = 2⁶Φ′ (24+5 = 29), IDY
z₂ = z₂²·z₂⁴⁻² (2+2·1 ≡ 1 mod 3), twist w²ψ(y/w) = y²+z₂y+1
irreducible /F₄ (0 roots), twin y²+z₂y+z₂² = (y+1)(y+z₂²) via
1+z₂² = z₂. All EXACT. HOLDS.

**Machine leg.** All GREEN, re-verified this session:
* Seal: `git show 2840d78c:...wframe_note_checks.py | md5sum` =
  e9495dfcbf866baef09bea60f70d0dbc = working tree; seal commit
  12:52:39, strictly before the verdict commit 940ee7f3 (12:55);
  contains runner + §7 prose only (2 files).
* Isolated re-run from a fresh /tmp copy: exit 0, output md5
  470d157b1cff29f31e06cb27e22fe715 = the committed
  wframe_note_checks_output.txt — BIT-IDENTICAL. 47/0, teeth 4/4.
* PE1 fresh artifacts at HEAD: runner 15935529…, run-2 output
  3e45cc3e…, run-1 RED 0189b034… — all match §4 R-7's citations.
* `statement_ledger.py --check` at HEAD: GREEN — 166 baseline, 0
  changed, 0 deleted, 0 added.
* Tautology audit (post-r1 delta only; PE1's full audit stands): the
  instrument's WAVA/TH0/U0 rows compare recomputed splits against
  hard-coded PRED_* pins (L78–80, the PE6-measured values) — real
  content; the IDY rows compare U0 vs TH0 + 2·PRED_W exponents
  (L145–146) — entailed, exactly as the folded §7 caveat now
  states. The caveat is FAITHFUL to the code.

**Fresh route (SEAL — predictions preregistered BEFORE any run).**
Frame LP23, disjoint from GF29 and the committed record: the LP1
tower (Φ′ = x⁴+2x²+4, Φ₂ = Φ′²−8x³, u₂ = 9, π₃ = Φ′/x⁴, heights
x:2, 2:4, Φ′:9, γ₁ = x²/2, γ₂ = Φ′²/x⁹) with a NEW key at u₃ = 23
(e₃ = 1, f₃ = 2; κ₃ = 23 > floor 18; committed LP1 keys use 19/37
only; GENHN's u₃ = 23 is a DIFFERENT tower, dv(Φ′) = 5, no w
record), target ψ₃ = y²+y+z₁². Hand predictions from the note's own
laws: n̂₂(23) = 8xΦ′, n̂₂(46) = 2¹¹x; **W-avatar split (93,3,−22) =
−3γ₁ − 11γ₂ → z₁⁻³ = 1 — the FIRST measured avatar = 1 geography
(every committed row is ≠ 1; OPEN-4 probed live; DEF W-1's "w = 1
is a possible value" exercised)**; ϑ(0) split (−1,5,−2) → z₁ ≠ 1
(LAW W-E live); u(β₀) split (185,11,−46) → z₁; IDY z₁ = z₁·1²
with the w = 1 signature u₀ = ϑ(0) (contrast GF29's u₀ ≠ ϑ(0));
law key Φ₂² − 8xΦ′Φ₂ − 2¹⁰x³ (c₀ = ϑ(0)⁻¹a₀ = z₁, lift x²/2-letter)
realizes ψ₃ irreducible /F₄ → ONE prime (4,4); naive twin
Φ₂² − 8xΦ′Φ₂ − 2⁹x⁵ (c₀ = a₀ = z₁²) realizes y²+y+z₁·z₁² = y²+y+1
split → TWO primes (4,2) — a PURE-ϑ naive-twin kill at a w = 1
frame (LAW W-C's iff, only-if leg: u(β₀) = z₁ ≠ 1 though w = 1);
avatar = 1 at the twin's two primes too (key-independence). Laws
live: W-B, W-C, W-E (≥2 met). Instrument
`verification/openmath/wframe_pe2_fresh.py` (own poly/F₄/lattice
code; gp dual routes factorpadic + idealprimedec/nfmodpr). RED runs
will be kept as-is with diagnosis. Result: see addendum below
(written only after this seal commit).

## ADDENDUM — FRESH-LEG RESULT (LP23, run after the seal commit f4492442)

**Run 1 — GREEN 34/0, exit 0, first try**
(`wframe_pe2_fresh_output_run1.txt`, md5 40292469; runner md5
df062a49; isolated re-run from a scratch copy BIT-IDENTICAL, exit
0). Every preregistered prediction met at the NEW geography (9th
prime; LP1 at u₃ = 23, in no committed record):
* **THE HEADLINE: w-avatar MEASURED = 1** at the new prime (nfmodpr
  route; hand split z₁⁻³ = 1 confirmed) — the FIRST avatar = 1
  geography on record. This ANSWERS OPEN-4's question ("is w = 1
  somewhere / at which geographies") affirmatively at a fresh frame
  and exercises DEF W-1's "w = 1 is a possible value of this
  definition". It contradicts NOTHING: §4 is enumerative
  (consequence (i) scoped to the 8 measured primes; consequence (v)
  explicitly disclaims unmeasured u₃), and OPEN-4's "NOT the
  generic one" is dated to the then-measured record. An append
  candidate for §4 per §8's rule (dated row LP23), not a defect —
  the note's no-universal-quantifier discipline is what SURVIVES
  this measurement, and is hereby tested live.
* ϑ(0) MEASURED = z₁ ≠ 1, u(β₀) = z₁: LAW W-E's letter value live
  at an avatar-dead frame; LAW W-B(6) closed with all three
  residues measured at an actual prime, in the w = 1 signature
  u₀ = ϑ(0) (the committed GF29 leg measured the u₀ ≠ ϑ(0) side —
  the pair now brackets both sides of the dichotomy).
* LAW W-C both legs: the multiplicative key realized ψ₃ = ψ₃^{(1)}
  exactly (ONE prime (4,4), factorpadic [16]); the naive twin
  (c₀ = a₀) realized y²+y+z₁·z₁² = y²+y+1 split → TWO primes (4,2),
  factorpadic [8,8] — a verdict-level naive-twin kill that is PURE ϑ
  (w = 1), disjoint in mechanism from every committed kill (all at
  w ≠ 1); the iff's only-if leg (u(β₀) = z₁ ≠ 1 though w = 1)
  observed live.
* Twin's two primes carry avatar 1 and ϑ(0) = z₁ each
  (key-independence of the frame data at avatar level).
* v(x), v(Φ′), v(2), v(π₃) = 2, 9, 4, 1 (Lemma 3.13(1) leg);
  z₁ live / z₂ = 1 letter pattern as committed for LP1.
Laws live at the fresh frame: W-B, W-C (both legs), W-E — ≥2 met
with margin. Dual oracles (factorpadic + idealprimedec/nfmodpr)
agree. Instrument honesty: of the 34 checks, one L2 line is a
prose-carrier with no discriminating power (`... or True`, the
"naive fails even at w = 1" note — content carried by the FPADN/YRT
rows) and the L1 IDY-letters line is an entailed closure exactly as
the note's folded §7 caveat classifies its own IDY rows; the
remaining 32 are discriminating. The fresh leg found NO defect in
the note's laws, fences, or record discipline — it probed the
note's sharpest edge (the avatar ≠ 1 record vs the w = 1 open case)
and the note's scoping held exactly.

## SURFACE 3 — the note as one text post-r1

Read end-to-end at HEAD. The r1 folds knit in cleanly: §4's
preamble bracket, the sanity rule, consequence (i)'s avatar
re-keying + LW3 rider, the §7 IDY caveat, OPEN-1's as-of line, §8's
r1 record all cross-reference consistently; the §4 header's "at
composition ... now 8 primes, 6 keys" counts re-verified (8 = R-1:1
+ R-2:1 + R-3:2 + R-4:2 + R-6:1 + R-7:1; 6 keys = LD1, LD3, GA1,
GA3, GA3*, GF29). Consequence (ii)'s "dead twice over ... adds a
third pair" is internally consistent (two pairs at composition,
third from R-7). The one whole-text residual is F-2′ (§5's
unswept counts), already filed. Nothing new at GAP-or-worse.

## SURFACE 4 — free hunt

* LAW W-C's iff clause vs the fresh leg: only-if direction now
  measured live (above) — the clause survives its first w = 1 test.
* DEF W-4's refutation scope ("REFUTED at letter-live grades"):
  LP23 is letter-live (ϑ(0) ≠ 1) with w = 1, and the nose
  prescription indeed still failed there (twin kill) while the nose
  READ of the law key's residual is valid (ψ^{(1)} = ψ) — the
  scoping "letter-live grades", not "w ≠ 1 grades", is exactly
  right. No defect.
* OPEN-3's gate (row-23 two-leg elevation) untouched by the fresh
  leg: my avatar measurement rides the same disclosed descriptive
  leg — consistent with the note's asymmetry caution (§2 W-E).
* Grep sweep for stray universal quantifiers over the record
  ("every prime", "all primes", "generic"): the only generic-flavor
  sentence is OPEN-4's "NOT the generic one", dated + source-keyed
  (GENTOW5's dated note) — and now bracketed by LP23 as an append
  candidate. No undated universal found in §4/§5.

## VERDICT

**CLEAN. Grade line: 1/2.** Nothing at GAP-or-worse survives this
pass. Sole residual: F-2′ (MINOR — §5 OPEN-3/OPEN-4 prime/frame
counts not swept by the r1 R-7 adoption; no false claim,
undercounts of the note's own record). Non-finding observations
for the next fold, per §8's append rule: (1) append LP23 (9th
prime, avatar = 1) as a dated §4 row — it answers OPEN-4's
question at one geography and brackets the IDY dichotomy; (2) sweep
§5's counts (F-2′) in the same fold. The r1 folds all HOLD against
sources; the §4 table passes the r1-minted sanity rule row-wise;
the machine leg re-verified bit-identical under the seal; the
fresh route (sealed predictions, dual oracles, GREEN 34/0 first
try) found no defect.

## GRADE LINE: **CLEAN ⇒ 1/2** (PE1 0C/1G/3m folded at r1; this pass: 0 CRITICAL, 0 GAP, 1 MINOR residual F-2′)
