# GENTOW1 passPE2 — hostile verification report

**VERDICT: CLEAN — 0 CRITICAL / 0 GAP / 1 MINOR. The acceptance
counter starts: 0/2 → 1/2.** The r1 gauge annex survived a
site-by-site walk with the S2 Step 5 value-LIVE residue computation
independently re-derived at the corrected key (the pin is NOT
cosmetic — the common-unit assembly goes through, and a
minimal-polynomial argument closes the one apparent scope gap in
the annex's favor); the P-1 scorer's transcription was verified at
source against both S1's table and the sealed constructors; the
machine leg is bit-identical on three isolated re-runs; and a
two-frame fresh route (the program's first η ≠ 1 × e₂ = 2 budget
frame and its FIRST μ₂ = 3 contact anywhere) came back GREEN 181/0
with the μ₂ = 3 refine pins landing EXACTLY on the hand-derived
values.

Target: `GENTOW1_PROOF_2026-08-09.md` at HEAD (r1 = 0d75026 +
477b1b1 over the PE1 target 5eca905). Protocol: quote-and-classify,
fix nothing. Verifier: fresh context, zero prior stake. PE1 report
(606e85c) and the GENHN dated erratum (59c1966) read first.

## FINDINGS

### m-1 (MINOR): S7.1's η ≠ 1 coverage line conflates instrument
### legs with distinct frames

QUOTE (S7.1): "The eta != 1 machine coverage is the fresh route's
F1 frame plus the erratum's own frame X + hetowr1_supp.py's three
frames." PE1's F1 IS the erratum's frame X as a frame — identical
genre data (p = 3, Φ′ = x²−6, (e₂,f₂) = (1,2), u₂ = 3,
ψ₂ = Z²+Z+2, W(0) = 1); and frame X is also the first of
hetowr1_supp's three. The distinct η ≠ 1 frames on record at r1
number THREE (X/F1; p = 5 Φ′ = x²−10 ord(η) = 4; p = 5 Φ′ = x³−10
e₁ = 3), reached by three instruments — not the five-item list the
sentence suggests. FAILURE SCENARIO: a downstream coverage audit or
box reading counts 5 gauge-live confirmations where 3 distinct
frames exist and overestimates seam diversity (note all three sit
at i(u₂) = 1, W ∈ {0,1}). No mathematical content is affected; the
wrap-immunity legs the annex actually leans on (PE1 Step 0
re-derivation; F1 at 373/0) are real and were re-verified here.

## CLEAN CHARGES (attacked, held under independent verification)

1. **The [GT1-r1] gauge annex, site by site (attack 1).** All 9
   manifest sites walked against erratum 59c1966: the S0 governing
   pin, Step 0, Step 1, Step 5, S3's lift convention, S6's stack,
   header, S7, back-pointer — displays match the erratum's
   corrected form ĉ_t := lift(c_t·η^{W(t)}), W(t) =
   ⌊(f₂−t)i(u₂)/e₁⌋, including the f₁ ≥ 2 (LIFT) parenthetical.
   THE VALUE-LIVE SITE: I re-derived Step 5's residue computation
   AT the corrected key from the normalizer cocycle alone —
   n̂(u₂)^t = n̂(tu₂)·(x^{e₁}/π^h)^{⌊t·i(u₂)/e₁⌋} plus the
   two-term cocycle gives the floor identity W(t) + W″_t + c″_t =
   W(0), so term t's coherent height-E₂ residue is
   c_t·η̄₂^t·η^{W(0)} — the S4 cocycle enters every term through
   the SAME unit η^{W(0)}, and the sum is η^{W(0)}·ψ₂(η₂(x₀)):
   Step 5's display is exactly right at the corrected ĉ_t, and the
   naive term-t residue carries the relative extra factor
   η^{−W(t)} as the bracket states. The pin is substantive, not
   cosmetic. BONUS CLOSURE (in the note's favor): the bracket's
   "(d) then FAILS at eta != 1" is rigorous wherever the naive and
   corrected displays differ — the twisted residual ψ̃ is monic of
   degree f₂ = deg ψ₂ and differs from ψ₂ in some coefficient, so
   ψ̃ ≠ minpoly(η₂) forces ψ̃(η₂) ≠ 0 (at f₂ = 1:
   c₀(1 − η^{−W(0)}) ≠ 0); no accidental-vanishing frame exists.
   Step 0's value-blindness re-checked (corrected and naive lifts
   at height 0 alike; the Φ′-carry prices heights only). Step 3
   consumes Step 1's pinned reading transitively.
2. **Byte-freeze + manifest (S7.4).** `git show
   5eca905:<note> | md5sum` = dc99fc25... as displayed; the r1
   diff is insertion-shaped at the 9 listed sites; the statement
   displays of LEMMA GENTOW-1/2/5 and COR GENTOW-1.1 sit outside
   the [GT1-r1] brackets, byte-unchanged from the PE1 target.
3. **The P-1 scorer's decorrelation, verified at source
   (attack 2).** The five (p, e₁, e₂, f₂, u₂, Φ′, Φ₂) tuples in
   `gentow1_r1_p1.py` match S1's table entry-for-entry (I
   recomputed FAM-C's full floor row, the node floors
   [21,11]/[29,15]/[13,7]/[43,22]/[13,7], anchor heights, and the
   E₂/dv₂/n columns by hand), AND match the sealed constructors in
   `gentow1_checks.py` (so the scorer scores the objects the
   battery ran). Check semantics = the sealed P-1 text exactly:
   factorpadic 1 row × mult 1 × deg D₂; one prime (e,f) =
   (e₁e₂, f₁f₂); e₁·v(x) = h·pr.e; e₁e₂·v(Φ′) = u₂·pr.e.
   Tautology audit NEGATIVE: PARI is the only oracle consulted;
   nothing in the scorer derives from the floors or the composed
   parameterization. S7.2's disclosure (post-hoc to seal; the
   η ≠ 1 base-key ef row lives in the PE1 fresh route) is accurate.
4. **The m-2 back-pointer.** GENTOW5_PROOF S1.5 exists and says
   what S6's [GT1-r1] sentence attributes to it ("RETIRED as a
   mathematical box; the residue is grade-only", 0/2 stated
   there); the layer-3-inherits-layer-1 conditionality caution is
   carried verbatim.
5. **The [pin] clause boundary (attack 4) — executed as the fresh
   route's PIN-STRADDLE tooth.** At the new η ≠ 1 × e₂ = 2 frame,
   at the SAME digit valuation v = 5: the lattice slot (0,0,0)
   (wt = 20 = μ₂E₂, pin-violating) breaks the entry endpoint via
   the hand-derived 486 + 243 = 729 carry (gate fails, dv(A₀) =
   12 ≠ 10) while the off-lattice slot (0,1,0) (wt = 22) sits on
   𝒯 with pins (22, None) — the +1 is decided by the slot
   congruence alone; and the digit AT the pinned floor v = 6
   auto-bumps to p₀ = 24 = μ₂E₂ + e₁e₂, matching Step 3's
   one-digit-higher display on the nose. The "≥ 0" proviso in the
   [pin] display is unreachable inside legal slots (max w =
   (D′−1)e₂h + (e₂f₂−1)u₂ < E₂ since u₂ > e₂D′h) — vacuous, as
   PE1 recorded; no straddle exists there to construct.
6. **Hand re-derivations (free hunt).** Refine rows A5-R1 (old
   (26,14): q = 2 lam-pin dies, C₀ reduction 16Φ′² = 16Φ₂ + 64x
   traced) and D-R2 (old (20,10) tDBL with the η₂-flavored
   normalizer, new (21,13)) re-derived by full polynomial
   division; FAM-B's two-pin floor rows ((0,0)/(1,1) at both
   heights) recomputed; COR GENTOW-1.1's min-slope and E₂ >
   D₂e₂h arithmetic; Step 2's outer-grammar identity
   μ₂E₂ + 1 − (μ₁−1)(u₂−e₂D′h) = u₂ + (μ₁−1)e₂D′h + 1 > n·e₂h;
   GENTOW-2(i)'s x-height bound; S3's a₀ ≥ 0 display (E₂ ≥
   (e₁−1)e₂h + (e₂−1)u₂ + 1) and deg lift < D₂; Step 4's
   two-step CRT. Every one checks.

## MACHINE LEG (integrity verified)

* Pins at HEAD: runner md5 6df4b213..., output 25667bf6...,
  scorer output 93a2cd6f..., PE1 fresh a655800b.../225c6212... —
  all match the note's figures and the pinned commits (PE1 fresh
  blob at 6993b7c = HEAD blob). Seal chain: 982abe7 (seal, runner
  blob d5cfd47a) → 07f41e0 (post-seal redisclosure) → verdict
  runner = HEAD runner, as the note discloses.
* Isolated re-runs (fresh /tmp copies, this pass): all three
  BIT-IDENTICAL to the committed artifacts — gentow1_checks GREEN
  1,128 checks / 0 violations, 5/5 teeth, tally as printed in S5;
  gentow1_r1_p1 GREEN 20/0; gentow1_pe1_fresh GREEN 373/0 with
  GAUGE-NODE ×20, GAUGE-SIGMA ×2, REFWRONG ×2.
* Tautology audit: NEGATIVE on the r1 scorer (see clean charge 3)
  and re-confirmed on the fresh instruments (members built by
  level-1 recipes, floors checked against them; PARI decorrelated).
  Standing instrument caveat re-observed at a fresh frame: the
  level-1 gate checks the polygon clause of 𝒯 only — my PB0
  diagnostic (Φ₂² + 486, residual-clause violator) passes the
  polygon gate as PE1's caveat predicts (disclosed, unscored).

## FRESH ROUTE (disjoint frames; sealed 27d353e, run-1 RED
## redisclosed 8606593, GREEN at 89dbec6)

Frames disjoint from the battery's five families and PE1's F1/F2:
**G1** = p 3, Φ′ = x²−6 (η = 2), (e₂,f₂) = (2,1), u₂ = 5, μ₂ = 2 —
the first frame combining η ≠ 1 with inner ramification e₂ ≥ 2
(gauge-DEAD by W(0) = 0 at f₂ = 1, disclosed; η enters the coherent
residues, and the recipe constants carry the η^{−1} leg). **G2** =
same outer, Φ₂ = Φ′² − 18x, μ₂ = 3 (μ₁ = 6, n = 12) — the FIRST
μ₂ ≥ 3 contact in the program's record (all prior rows μ₂ = 2).

RUN 1: RED 181/2 — both violations MY sealed PB3 σ, derived
wrap-naively from the raw slot residue; the coherent residual
carries the n̂₂(11)²/n̂₂(22) wrap (xΦ′²/27 → η = 2) and SPLITS
(both PARI routes {(4,1)},{(4,1)} against my {(4,2)}). Redisclosed
before re-run; the run-1 RED is itself a live machine demonstration
that GENTOW-2(iv)'s "coherent normalization, wrap units included"
clause is LOAD-BEARING at η ≠ 1 — an unplanned tooth in the note's
favor. RUN 2: **GREEN — 181 checks / 0 violations, 4/4 teeth**
(PIN-STRADDLE, BN3, REFWRONG ×2 ×2 frames):

* G1: floors = hand table (8 slots); anchor Φ₂² + 81Φ′ pins
  (21, None) tRAM σ {(8,1)} BOTH routes; 8 η-corrected recipe
  members + deep perturbations through gate/floors/pins/
  strict-above; node oracle strict at 20 scored prime rows
  (2v(x) = pr.e, 4v(Φ′) = 5·pr.e, 4v(Φ₂) > 10·pr.e); refine
  (22,11) → (23,12) tRAM {(8,1)} both routes, Kp ef {(4,1)},
  wrong-height and wrong-residue normalizers leave the pin alive.
* G2 (μ₂ = 3): floors = hand table (12 slots); anchor pins
  (31, None, None) σ {(12,1)} both routes; 6 recipe members green;
  below-node tooth fB = Φ₂³ + 2187x fails the gate at the
  hand-derived dv(A₀) = 17; THE μ₂ = 3 REFINE (first contact):
  old-key pins EXACTLY the hand-derived (33, 23, 14) — at
  p = μ₂ = 3 both middle binomials ≡ 0, the event carried by
  p₀ = 3λ alone with p₁ = 2λ+1 realizing layer 2's bound tightly —
  new-key kills (37, None, None), σ {(12,1)} both routes: the
  GENTOW-2(ii)/(iv) displays at the exact geography GENTOW-BOX-1
  conditions (layer 1's graded-frame consumption at μ₂ ≥ 3), and
  they held to the digit.
* NOT RUN (disclosed): non-prime q (f₁ ≥ 2 / d = 2 ambient — rnf
  cost, the PE1 disclosure standing); gauge-LIVE f₂ ≥ 2 rows
  (covered at F1/X + hetowr1, re-run bit-identical this pass).

## GRADE LINE

passPE2 verdict: **CLEAN (0C / 0G / 1m)** — the acceptance counter
moves **0/2 → 1/2** on the tower stack's most-consumed note. The r1
round repaired exactly what PE1 charged and nothing it didn't: the
gauge annex's pins are mathematically substantive at the value-live
site, the sealed artifacts are byte-frozen, and the note's budget,
pin-boundary, and refine displays survived their first η ≠ 1 × e₂ ≥
2 and first μ₂ = 3 machine contacts at hand-derived precision. The
m-1 coverage-enumeration nit is repairable by a one-line dated
correction (3 distinct η ≠ 1 frames, three instruments) and does
not gate acceptance. Next: PE3 by a fresh verifier; candidates it
should own: a gauge-LIVE (f₂ ≥ 2) budget frame at e₂ ≥ 2, non-prime
q, and the GENTOW-5 band clauses at f₁f₂ ≥ 2 windows.

— GENTOW1 passPE2 hostile verifier, 2026-08-10
