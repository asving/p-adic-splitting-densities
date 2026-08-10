# WFRAME passPE2 — hostile verification report (second pass, RCT round 1)
## Target: WFRAME_NOTE_2026-08-10.md @ 520491ad (post-r1; PE1 was 0C/1G/3m @ 3db65096) — 2026-08-10

**VERDICT: PENDING (skeleton commit; sections follow).**

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

**Machine leg.** PENDING (seal md5, isolated re-run, ledger check).

**Fresh route.** PENDING (design: a 9th prime — the LP1 tower at a
NEW u₃ = 23, no committed key uses it; predictions to be sealed
before the run).

## GRADE LINE: PENDING
