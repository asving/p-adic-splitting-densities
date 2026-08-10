# GENTOW1 passPE3 — hostile verification report (THE ACCEPTANCE ATTEMPT)

**VERDICT: CLEAN — 0 CRITICAL / 0 GAP / 1 MINOR. The acceptance
counter moves 1/2 → 2/2: GENTOW1 is ACCEPTED.** The one MINOR is a
factual slip in the post-PE2 rider's seam-diversity sentence (frame W
sits at i(u₂) = 2, not 1 — the caveat UNDERSTATES machine coverage);
no mathematical content of the verified body is touched. The least-
visited surfaces (the ONTO cardinality argument, GENTOW-5(c)/(d), the
table-generation method) held under independent re-derivation; the
machine leg is bit-identical on four isolated re-runs; and a
two-frame fresh route — the program's FIRST non-prime-q frame (q = 4,
f₁ = 2 outer) and its FIRST gauge-live × μ₂ = 3 frame — came back
GREEN 85/0 on run 1 with every hand-derived pin exact.

Target: `GENTOW1_PROOF_2026-08-09.md` at HEAD = 0bb7610 (arc: seal
59d0350→5eca905 → PE1 NOT CLEAN, 1G+2m @ 606e85c → r1 gauge annex
0d75026+477b1b1 → PE2 CLEAN 1e99926, counter 0/2→1/2 → post-PE2
dated-correction rider 0bb7610). Protocol: quote-and-classify, fix
nothing. Verifier: fresh context, zero prior stake. PE1 and PE2
reports read first; their routes not re-walked (PE1: η≠1 entry +
e₁ = 3; PE2: η≠1 × e₂ = 2 + first μ₂ = 3 + the pin-straddle tooth).

## FINDINGS

### m-1 (MINOR): the rider's seam-diversity sentence misstates
### frame W's i(u₂) — the caveat's i(u₂)-axis leg is false in the
### conservative direction

QUOTE (rider, dated correction 2026-08-10): "the three enumerated
frames sit at i(u₂) = 1 with W(0) = 1, W(1) = 0 (X, Z, and W alike
per the pins above); a gauge-live frame at i(u₂) ≥ 2 or W(0) ≥ 2
remains uncovered machine-side."

THE SLIP. Per the rider's OWN pins (item 3: frame W has u₂ = 5,
e₁ = 3, h = 1) and per `hetowr1_supp.py` at source (`i(k) = k mod
e1`), frame W's i(u₂) = 5 mod 3 = **2**, not 1. Its W-pins are
nevertheless right: W(0) = ⌊2·2/3⌋ = 1, W(1) = ⌊1·2/3⌋ = 0 — the
sentence is internally inconsistent with the pins two lines above
it. Consequently "i(u₂) ≥ 2 remains uncovered machine-side" is
FALSE: frame W is a machine-covered gauge-live frame at i(u₂) = 2
(hetowr1_supp GREEN). The W(0) ≥ 2 leg of the caveat survives (X, Z,
W all have W(0) = 1). Provenance: the same error appears in PE2's
m-1 text ("note all three sit at i(u₂) = 1"); the rider transcribed
it into the note, which is where it now lives. FAILURE SCENARIO: a
downstream seam audit hunting an i(u₂) ≥ 2 confirmation re-runs a
frame already covered (wasted unit); or a consumer takes i(u₂) = 1
as a pin for frame W in wrap arithmetic and computes W(0) =
⌊2·1/3⌋ = 0 ≠ 1, propagating an inconsistent gauge datum. Direction:
conservative (coverage understated); body statements untouched.

## RIDER VERIFICATION (0bb7610) — everything else checks

* **Append-only + byte-freeze exact:** `git show 477b1b1:<note> |
  md5sum` = c2f4f3d148b1ab94c5f9f95aa01de139 at 38,204 bytes, and
  `head -c 38204` of HEAD gives the SAME md5 (prefix property);
  `git diff 477b1b1..0bb7610` on the file has 0 deletion lines
  (pure 39-line append); the rider commit touches only the note.
* **Frame identifications verified at source:** X = PE1's F1 =
  hetowr1_supp's first frame — genre data identical (p = 3,
  Φ′ = x²−6, e₁ = 2, η = 2 ord 2, (e₂,f₂) = (1,2), u₂ = 3,
  ψ₂ = Z²+Z+2, W = (1,0)); counted once, three instrument legs —
  correct, and it repairs PE2's m-1 as charged. Z and W pins (p = 5,
  x²−10 with ord(η) = 4; p = 5, x³−10 with e₁ = 3; ψ₂ = Z²+Z+1
  both; W = (1,0) both) all match `hetowr1_supp.py`'s docstring and
  Frame constructors — except the i(u₂) slip above (m-1).
* **Counter claim:** "PE2 CLEAN @ 1e99926, counter 0/2 → 1/2, HOLDS
  at 1/2" matches the PE2 report. Observation (not a finding): the
  header ARC line still ends at PE1/0/2 — stale in the conservative
  direction, governed by the append-only convention (the dated
  correction at the bottom carries the live counter).
* **Sealed artifacts byte-untouched:** all four artifact md5s at
  HEAD match the note's pinned figures (below).

## CLEAN CHARGES (attacked, held under independent verification)

1. **The ONTO direction of the digit bijections (owned surface 1) —
   the cardinality argument re-derived from scratch.** For
   GENTOW-1(b): the global coefficient map (monic deg-n f) ↔ (all
   digit tuples) is a bijection by iterated monic division (Φ₂-adic
   then Φ′-adic; existence + uniqueness over Ô), unipotent in the
   x-degree filtration; Steps 2+3 identify image(𝒯) = budget box, so
   onto is CONSTRUCTIVE there (Step 2 is the onto direction; no
   counting needed). For GENTOW-2(iii) layer 3 — where cardinality
   IS the argument: per window N (large enough that both loci are
   unions of mod-π^N fibers), the event slice at fixed s and the
   λ-floored node box have EQUAL finite cardinality — per coordinate
   j both force all digits at heights < (μ₂−j)λ to zero and the
   height-(μ₂−j)λ digit to one value (event: binom(μ₂,j)(−s̄)^{μ₂−j}
   ·wraps, zero at p | binom; box: zero), with identical free
   positions above (slot strings key-independent since Φ₂⁺ carries
   the same invariants by (i), GENHN-2′ applies verbatim). The map
   descends mod π^N (layer 2 = upward carries; GENTOW-5(e) at both
   keys), is injective there (restriction of the global f-bijection
   through (f mod π^N)), hence bijective per window; inverse limit
   gives onto exactly. Cross-check: (iv) independently exhibits the
   old-key read of every node-box member as the exact alpha event —
   two disjoint routes to onto agree.
2. **LEMMA GENTOW-5(c)/(d) (owned surface 2).** (c): consulted
   height m in class (a,b) satisfies m ≡ w(a,b) (mod e₁e₂) (class
   heights are e₁e₂v + w) and m < e₁e₂N (readable = below cap), so
   v ≤ N−1, i.e. m ≤ e₁e₂(N−1) + w(a,b) — exact; note the bound is
   not tight at large w (m ≤ e₁e₂(N−1) + w can exceed the cap; the
   binding constraint there is the cap itself) — harmless as an
   upper bound, and exactly the geography my MAXRAG row probes.
   (d): a layer-2 contribution landing at height d has raw weight
   ≤ d and every source factor has weight ≤ raw weight ≤ d, so new
   digits at height d are functions of old digits at heights ≤ d;
   below-cap heights are in-string in every class (by (c)'s
   congruence), so deep composed histories never consult the ragged
   band; induction over chain updates closes. Both re-derived
   independently and machine-touched fresh (H2-WIN/MAXRAG/UNDERCUT).
3. **The S1 table-GENERATION method (owned surface 3) — no
   systematic bias found.** The tables are the runner's
   `Fam.floor()` printout = the LEMMA GENTOW-1(a) formula (ceil via
   -((-num)//m), pin iff num % m == 0, num ≤ 0 → 0: the display
   implemented exactly, "≥ 0" proviso included) — so as evidence
   they are formula-echo, and the honest force is the PINCER around
   them: NEC members are built from LEVEL-1 recipes with hardcoded
   per-family scales (decorrelated constants) and then checked
   AGAINST the floors — a too-HIGH floor anywhere reached would
   flag; REAL members are built at floor+{0,0,1,2} and pushed
   through the LEVEL-1 GATE (actual Φ′-adic development) + PARI — a
   too-LOW floor would flag. Necessity AT the boundary (floor−1
   rejected) is machine-tested at slot (0,0,0) (T-MUTFLOOR ×5,
   T-BELOWNODE) and PE2's pin-straddle; my fresh route adds the
   first OFF-LATTICE below-floor rejection at a non-(0,0,0) slot
   (H2, slot (j=0,(1,0)): v = 8 < floor 9 fails the gate at the
   hand-derived dv(A₀) = 17). I re-derived all 30 floor-table
   entries, all 5 node-floor pairs/triples, and the read-off claims
   (i)–(iv) by hand from (E₂, w, e₁e₂) — every entry exact; the
   f₁f₂-pins-per-height law confirmed at both f₂ = 2 families.
4. **Free hunt (owned surface 4) — arithmetic displays.** Step 0
   x-carry (e₁g + ch ≥ D′h tail pricing) and Φ′-carry (n(m) weight
   e₂m, lift terms exact at E₂); S3's a₀ ≥ 0 display E₂ ≥
   (e₁−1)e₂h + (e₂−1)u₂ + 1 (via u₂ > e₂D′h); Step 2's outer
   grammar μ₂E₂ + 1 − (μ₁−1)(u₂−e₂D′h) = u₂ + (μ₁−1)e₂D′h + 1 >
   ne₂h; Step 4's two-step CRT (b mod e₂ by gcd(u₂,e₂) = 1, then a
   mod e₁ by gcd(h,e₁) = 1); COR 1.1's E₂ + 1/μ₂ minimum and
   E₂ > D₂e₂h; the S5 tally sum (= 1,128); B-R2's two-monomial lift
   16 + 4xΦ′ re-derived and matched against the runner's
   REFINE_ROWS entry. All check. The DRAIN-member subtlety in
   GENTOW-1(c)'s equality construction (j ≥ 1 single-slot members
   have Φ₂ | f) is consistent with 𝒯's polygon+residual definition
   and S5's disclosed DRAIN skip — no violation.

## MACHINE LEG (integrity verified)

* Pins at HEAD: `gentow1_checks.py` 6df4b213..., output
  25667bf6... (= S5's figures); `gentow1_r1_p1_output.txt`
  93a2cd6f...; `gentow1_pe1_fresh.py` a655800b... / output
  225c6212... — all match the note's and the PE-reports' pinned
  values.
* Isolated re-runs (fresh /tmp copies, this pass, all FOUR
  instruments): BIT-IDENTICAL outputs — gentow1_checks GREEN
  1,128/0 with 5/5 teeth and the S5 tally; gentow1_r1_p1 GREEN
  20/0; gentow1_pe1_fresh GREEN 373/0 (GAUGE-NODE ×20, GAUGE-SIGMA
  ×2, REFWRONG ×2); gentow1_pe2_fresh GREEN 181/0 (PIN-STRADDLE,
  BN3, REFWRONG ×2).
* Tautology audit: NEGATIVE, with the floor-generation audit of
  clean charge 3 as this pass's contribution (formula-echo tables
  pincered by decorrelated NEC/REAL+gate legs; teeth enter real
  objects; PARI is consulted on members, never on the formula).
  Standing caveat re-confirmed: the level-1 gate checks the polygon
  clause of 𝒯 only (residual clause by construction + σ-oracle
  indirectly) — unchanged from PE1/PE2, disclosed.

## FRESH ROUTE (disjoint frames; sealed 4ccc8c5 pre-run; GREEN 85/0
## on RUN 1, no instrument repair; runner md5 c122c5b1..., output
## 56bc1d39...)

**H1 = the program's FIRST non-prime-q contact** (q = Q^{f₁} = 4,
K = F₄ — breaches GENTOW-BOX-2's "q ∈ {2,3}" AND "f₁ = 1 outer keys
only" at once; the PE1+PE2 "non-prime q NOT RUN (rnf cost)"
disclosure discharged rnf-free via the unramified outer): genre
(2; e₁=1, f₁=2, μ₁=2; h=1), Φ′ = x²+2x+4 (ψ = Z²+Z+1, roots 2ζ₃),
u₂ = 3, ψ₂ = Z − ω with ω ∈ F₄\F₂ (a genuinely non-prime-q letter
in the residual AND the refine normalizer), μ₂ = 2, n = 4, E₂ = 3,
m = 1 (every slot pinned, f₁f₂ = 2 pins per height). Key Φ₂ =
Φ′ − lift(ω;3) = x²−2x+4, σ {(1,2)} both routes. Results: 8 box
members (2 deep v = 40 perts) through gate + hand floors + node
oracle (val(x) = pr.e, val(Φ′) = 3pr.e, val(Φ₂) > 3pr.e STRICT);
NODE-EQ anchor p₀ = 7 = μ₂E₂+1 exact, σ {(2,2)} both routes; the
q = 4 REFINE row: f = Φ₂² + 128x + 256, old pins (8, None) (q = 2:
the 2s = 0 pin gone), refined key x²−10x+4 σ {(1,2)}, new pins
EXACTLY the hand-derived (9, 5) — kills above the λ-node — σ
{(2,2)} both routes; REFWRONG ×2 (wrong-height Φ₂−16x, wrong-flavor
Φ₂−16): pin ALIVE at 8 both; mutant-floor tooth Φ₂²+2⁵ REJECTED at
the hand-derived dv(A₀) = 5.

**H2 = the FIRST gauge-live × μ₂ = 3 frame** (the two hard axes
together: η = 2 ≠ 1 with f₂ = 2, W(0) = 1 — corrected ≠ naive key —
AND μ₂ = 3 = p; PE2's G2 was μ₂ = 3 but gauge-dead f₂ = 1, PE1's F1
gauge-live but μ₂ = 2): genre (3; e₁=2, f₁=1, μ₁=6; h=1), frame-X
key Φ₂ = Φ′²+3xΦ′+108 at μ₂ = 3, n = 12, E₂ = 6, node floors
[19,13,7]. Results: 6 box members through gate/floors/node oracle
(2val(Φ₂) > 6pr.e strict every row); anchor p₀ = 19 exact σ {(6,2)}
both routes; below-floor tooth at the OFF-LATTICE slot: Φ₂³+3⁸x
rejected at dv(A₀) = 17 exact; THE COMBINED REFINE (λ = 7,
s = η₂, lift(η₂;7) = 9Φ′): fE = (Φ₂−9Φ′)³ + 3¹³ — OLD-key pins
EXACTLY the hand-derived **(21, 15, 9)**: p₀ = 3λ (event carried by
p₀ alone, both middle binomials ≡ 0 mod 3 at a GAUGE-LIVE frame —
GENTOW-2(iv)'s char-sensitive display), p₁ = 2λ+1 (layer 2's bound
TIGHT — the same 2λ+1 carry PE2 measured at gauge-dead G2, now
gauge-live), p₂ = λ+2; NEW-key kills (26, None, None); σ {(6,2)}
both routes; REFWRONG ×2 (wrong-height 27Φ′, wrong-flavor 27x): pin
ALIVE at 21 both. Hand cross-check recorded: the raw height-21
residue 2(η₂+1) times the cocycle unit η^{−1} equals −η₂³ = −s̄³
exactly — the coherent (T−s̄)³ event datum; scored machine-side by
p₀ = 21 EXACT (a cancellation would raise it) + σ, keeping every
scored row height-level or PARI-level (the PE2 run-1 wrap lesson
applied). **WINDOW at MAXIMAL RAGGED OFFSET** (w = 4 class, N = 12,
cap 24): 6 ambient π^N-lifts leave all below-cap reads identical;
the last in-string digit of the max-offset class (v = 11 = N−1,
height 26 > cap — the ragged-band geography where (c)'s string
bound exceeds the cap) changes NO below-cap read; UNDERCUT tooth:
the above-cap p₀ = 26 read moves to 24 under a v = N digit — fired.

NOT RUN (disclosed): d = 2 ambients (q = 4 reached via f₁ = 2
outer instead — the first breach of the disclosure either way);
gauge-live at i(u₂) ≥ 2 with W(0) ≥ 2 (see m-1: the honest residual
axis is W(0) ≥ 2 only).

## GRADE LINE

passPE3 verdict: **CLEAN (0C / 0G / 1m)** — nothing GAP-or-worse
survived this pass. The acceptance counter moves **1/2 → 2/2:
GENTOW1 (box items (1), (5), (6β): LEMMA GENTOW-1 + COR 1.1, LEMMA
GENTOW-2 at its stated μ₂ = 2/graded-frame conditionality, LEMMA
GENTOW-5) is ACCEPTED** — with its own honest conditionality stack
standing as written: T(b)′ at the corrected key (erratum 59c1966
pinned), the [r1] node floor, S4 coherent normalizers, the
GENTOW-BOX-1 graded-frame consumption at μ₂ ≥ 3 (read through
GENTOW5 S1.5's 0/2-conditioned retirement), and GENTOW-BOX-2's
machine-coverage box (now narrowed: non-prime q and f₁ = 2 outer
and gauge-live × μ₂ = 3 each have a first GREEN contact; the m-1
correction owed: frame W is an i(u₂) = 2 datum, and the uncovered
seam axis is W(0) ≥ 2). The m-1 rider slip is repairable by a
one-line dated correction and does not gate acceptance.

— GENTOW1 passPE3 hostile verifier, 2026-08-10
