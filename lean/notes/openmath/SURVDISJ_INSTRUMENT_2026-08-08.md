# (SURV-DISJ) INSTRUMENT — the protection-identity census: which identity protects the surviving slot in each kill regime

Unit: the (SURV-DISJ) INSTRUMENT of the W-MULT-DCX arc (2026-08-08
campaign, wallclock 2026-08-04).  Target: the S7 box of
`SURV_PROOF_2026-08-08.md` at 51a8ac9 —

    (SURV-DISJ):  on live rows (TRACK, (H1)-(H3), c_{m-1} >= k) the
    netted BOTTOM stratum survives OR the CASCADE slot survives.
    Record entering this unit: 486 committed + 545 fresh rows, six
    unique total-bottom-kill rows, 0 counterexamples; on every kill the
    survivor was the cascade slot AT the cascade line.

The two kill regimes on record (SURV_PROOF S8.b):

    (K1)  residue-characteristic-2 mod-p multiplicity pair-kills at
          g0 = 1 (path-multiplicity-2 collisions netting 2*(unit) == 0
          mod 2; six rows incl. one mixed-characteristic Zp p = 2; the
          CASCADE slot survived every one);
    (K2)  characteristic-BLIND opposite-sign equal-residue pair-kills
          at g0 = 2 (37 bottom-line groups on EQ3G2B, p = 3) plus the
          52 committed cascade-slot kills at g0 >= 2 — the BOTTOM
          survived every one.

The composer's question this unit instruments: **WHAT IDENTITY protects
the surviving slot in each regime?**

## D1. Design (sealed BEFORE the battery)

Runner `verification/openmath/survdisj_instrument.py`, committed engines
consumed read-only, md5-pinned (the five SURV_PROOF pins PLUS
`surv_derive_checks.py` 2365289e… and `surv_pe1_ext.py` 937317c7…, whose
selection logic / PX roster are replicated verbatim).  Deterministic,
exact arithmetic; results written incrementally after every tower
(salvage-safe).

**Union roster** (live rows only):
* SEALED — WS.ROSTER through the committed sealed selection loop (copied
  byte-faithfully from `surv_derive_checks.run_sealed_tower`);
* EQ — ED.FRESH_ROSTER at PE1's raised caps 12/6 (superset of the
  committed 6/3 selection);
* PX — the PE1 PX roster verbatim, caps 12/6;
* SD — **NEW adversarial roster**: eight g0 >= 2 towers at RESIDUE
  CHARACTERISTIC 2 (Fpt p=2 and Zp p=2, incl. d0 = 2 and one m = 4 and
  the (3,2,2) deep-pool cross of the W3DEEPF kill shape with g0 = 2) —
  both kill regimes reachable ON THE SAME ROWS, a cross no committed
  battery ever probed.  Engine-unsupported shapes disclosed-skipped.

**Residue-decomposition layer.**  For every same-slot equal-line group:
group subsum at its line, killed iff zero-or-raised.  For every KILLED
group and every SURVIVOR slot (netted slots attaining w_m(Q^1)): per-cell
sign / w0 / normalized K-residue / corrections / junk / path type, the
K0-RESIDUE-PRODUCT factorization of every junk-free coefficient
(res(b) = res(b0) * prod_{correction edges} res(c_d) * res(c_D-seed),
w0 additive, sign = (-1)^{#corrections} — the L-NORM(a) chain of the
ACCEPTED RMENGINE, checked cellwise: family SDI-RESFACT), and the
residue-class multiplicity structure mod p (classes by keq, signed
counts).  Kill genres: SIGN-PAIR[-MULTI] (every class signed count 0,
char-blind) / MODP[-MULTI] (some class signed count != 0 but == 0 mod p)
/ CROSS (neither — cancellation across distinct residue classes, a genre
the S7 box does NOT carry; loud flag).

**Candidate protection identities** (law-keyed: g0-class | residue-char |
thresh/above/direct stratum; each with a mutation control WITH TEETH):

* **P-A** [combinatorial, g0 = 1]: the cascade slot is a SINGLE cell (no
  same-slot companion of ANY valuation) on every g0 = 1 live row — the
  (NEP)-strong form.  M-A1: the same predicate must FAIL on some g0 >= 2
  row.  M-A2: "every bottom-line slot at g0 = 1 is a singleton" must
  FAIL somewhere (the 13 committed collisions).
* **P-B** [g0 >= 2 bottom structure], measured per g0 >= 2 row over
  bottom-line slot groups: PB-single-some (some singleton group),
  PB-odd-some (some odd group), PB-odd-all-surv (every surviving netted
  bottom slot has odd group count), PB-mult1-some (some group carries a
  residue class of |signed count| = 1); each also sub-keyed to rows with
  a bottom-line kill (`@kill`).  M-B1: killed groups with ODD cell count
  (0 => parity separates kills from survivals; > 0 => parity is NOT the
  protection).  M-B2: some g0 >= 2 row must carry an EVEN bottom-line
  group (else no partnered bottom was censused — coverage failure).
* **P-C** [valuation separation]: on rows with >= 1 killed group, every
  killed group's line > beta_min ("kills never reach the bottom").
* **P-D** [survivor sum-free]: every minimal surviving netted slot is a
  single cell at its minimal line with netline = that line (residue = a
  single L-NORM(a) product, never a sum).  P-D-all / P-D-some over all
  rows; P-D-all@kill over rows with >= 1 killed group (the load-bearing
  case).  M-D1: some row must show a minimal survivor with >= 2 cells at
  its line netting NONZERO (else the predicate is structurally vacuous);
  every such row's net-residue identity is recorded (PDFAIL witnesses).

**Verdict families** (each backs a PROVED lemma or the conjecture):
SDI-PIN, SDI-CONS (stage sums = E1IH / Q^1), SDI-DIGIT (S-L0(c)),
SDI-LINE (W-D5), SDI-EQV (same slot+line => same w0; S-L4(i) shadow),
SDI-RESFACT (the L-NORM(a) chain), SDI-SEP (w_m(Q^1) vs beta_min and the
netted minimum), SDI-SURV ((SURV-DISJ) itself — a violation IS a
counterexample), HARNESS.

## D2. Preregistered predictions and falsifiers (sealed)

* **PRED-1**: 0 violations in SDI-PIN / SDI-CONS / SDI-DIGIT / SDI-LINE /
  SDI-EQV / SDI-RESFACT / SDI-SEP / HARNESS on every traced row.
  Falsifier: any violation — an engine-or-lemma instance breach.
* **PRED-2**: 0 SDI-SURV violations, INCLUDING the new SD regime-crossing
  rows.  Falsifier: a row with bottom dead AND cascade slot dead — a
  (SURV-DISJ) counterexample (headline event, everything else moot).
* **PRED-3 (P-A)**: 0 failures on the g0 = 1 denominator; M-A1 and M-A2
  both fire.  Falsifier: a partnered g0 = 1 cascade slot — kills the
  combinatorial-protection reading of regime (K1).
* **PRED-4 (P-C)**: REFUTED — killed groups AT beta_min exist in BOTH
  regimes (the 44 + 6 record).  The law-keyed failure pattern is the
  datum; if P-C unexpectedly HOLDS on some sub-key, that sub-key's
  protection is valuational and the box should say so.
* **PRED-5 (P-D@kill)**: on EVERY row with a kill, the minimal survivor
  is sum-free — its residue is a single K0-product.  Falsifier: a kill
  row carried by a netted SUM — then the protection identity needs the
  carry algebra even at the survivor, and its recorded decomposition is
  the design input.
* **PRED-6 (P-B)**: NO preregistered direction — the measurement IS the
  product (which of the four P-B measures, if any, is exceptionless
  keys the g0 >= 2 protection).  Teeth requirement: M-B2 fires, and the
  killed-vs-surviving parity populations separate or the P-B family is
  declared toothless.
* **PRED-7 (genres)**: every killed group classifies SIGN-PAIR* or
  MODP*; genre CROSS never occurs.  Falsifier: a CROSS kill — a NEW kill
  genre, and the S7 box's design constraint list is incomplete.

## D3. RESULTS (commit 2; verdict from the artifacts — single
deterministic run, 26.3s, **979 live rows** = 286 sealed + 330 EQ +
212 PX + 151 SD; **0 violations in all nine verdict families**)

**PRED-1 CONFIRMED.**  SDI-PIN/CONS/DIGIT/LINE/EQV/RESFACT/SEP/HARNESS
all 0.  In particular SDI-RESFACT: **3,218 junk-free two-exit cells,
every coefficient's normalized residue EXACTLY the K0-product
res(b0)·prod res(c_d)·res(c_D), w0 additive, sign = (−1)^{#corr}** —
the L-NORM(a) chain holds cellwise across the whole union roster.

**PRED-2 CONFIRMED.**  SDI-SURV 0: **(SURV-DISJ) stands on 979 rows, 0
counterexamples — now INCLUDING the g0 ≥ 2 × residue-char-2 cross**
(151 SD rows; 30 fresh bottom-line sign-kills there; 4 rows carried
BOTH a MODP kill and a SIGN kill simultaneously — the regimes stack
without producing a counterexample).  Total-bottom-dead rows: exactly
the six known K1 rows; survivor = the cascade slot at the cascade line
on all six (re-confirmed).

**PRED-3 CONFIRMED — the (K1) protection identity is COMBINATORIAL
SINGLETON-NESS.**  P-A: **693/693 g0 = 1 rows ok, 0 fail** (all strata,
both residue characteristics, both ring kinds): the cascade slot NEVER
has a same-slot companion of ANY valuation at g0 = 1.  Teeth: M-A1
fired 77 (the singleton predicate fails on partnered g0 ≥ 2 cascades),
M-A2 fired 18 (g0 = 1 bottom collisions exist — other slots DO get
partnered).  With S-L1 the slot content is the single field product
b̄₀·c̄_D ≠ 0 — nothing to cancel against, characteristic-free.

**PRED-4 CONFIRMED (P-C REFUTED as designed).**  103/200 kill rows have
a killed group AT beta_min (97 g0 ≥ 2 bottom-line sign-kill rows + the
6 K1 rows); valuation separation protects nothing.

**PRED-5 FALSIFIED — productively.**  P-D-all@kill = 180/200: on **20
kill rows (all g0 ≥ 2)** the minimal survivor is a netted 3-cell SUM
(signs ±1, ∓1, ∓1), not a single product.  What saved every one of
them is the sharper law below.  (Class-wide P-D-all = 937/979; M-D1
fired 42 — the predicate has teeth.)

**PRED-6 RESOLVED — the (K2) protection identity is the
SIGNED-MULTIPLICITY-ONE law.**  P-B measures on 286 g0 ≥ 2 rows:
PB-odd-some **286/286**, PB-mult1-some **286/286** (exceptionless);
PB-single-some 268/286 (17 fails on kill rows — singleton is NOT the
protection); PB-odd-all-surv 274/286 (12 off-kill fails: the d0 = 2
family's surviving bottom PAIR — even count, two DISTINCT residue
classes, net = difference of distinct field elements ≠ 0).  M-B1:
**39 killed groups have ODD count** (the MODP p = 3 n ∈ {3,6} kills +
CROSS) — **parity is NOT the protection**; M-B2 fired 109.

**THE UNIFIED SURVIVOR LAW (P-M1, post-hoc census on the artifacts —
the headline).**  On ALL 200 kill rows, EVERY minimal survivor slot's
minimal-line group has residue-class signed-count vector in
**{(+1)×85, (−1)×115, (−1,0)×5, (0,+1)×4, (−1,+1)×2}** — every class
count in {−1, 0, +1}, at most TWO nonzero classes, so the net is a
single K-residue or a DIFFERENCE OF TWO DISTINCT K-residues: **nonzero
by field distinctness alone, characteristic-free — no carry algebra is
consumed at the survivor.**  Complementarity, exceptionless: **no
non-CROSS killed group EVER carries a ±1 class** (0 instances) — a ±1
class is immune to sign-pairing (needs count 0) and to mod-p
multiplicity (needs p | count); only a CROSS field relation could
reach it, and **CROSS never occurred at a bottom line or a survivor
line in 979 rows** (all 9 CROSS kills off-bottom).  Scope caveat: P-M1
is @kill-scoped — off kill rows 12 survivors have vector (−2) (the
p = 3 same-sign collision pairs netting −2·unit ≠ 0 mod 3), so the
class-wide survivor statement is "some class with count ≢ 0 mod p and
no cross relation"; P-M1 is its exceptionless form exactly where kills
fire.  (Post-hoc classes use string equality of the canonical residue
reps; the in-run kill classification used keq, and survivor
nonzero-ness is engine-verified independently of any class reading.)

**PRED-7 FALSIFIED — a NEW kill genre exists, but off-bottom.**  9
CROSS kills (cancellation ACROSS distinct residue classes): 8 at
p = 3, g0 = 1, junk-FREE, n = 3, signed counts (−2, +1) with the field
relation 2·res_a = res_b in F₃ (correction-count-heterogeneous paths:
ncorr 1 vs 2); 1 at residue char 2, g0 = 2, the MIXED-JUNK group
EQ3G2A/SDG2AF[2321,2321] (junks {1,2}, n = 5) with res_a + res_b =
res_c in the char-2 field.  ALL 9 off-bottom, 0 at survivor lines.
The S7 box's genre list must add CROSS for off-bottom slots.  ALSO
NEW: **31 MODP kills at p = 3** (n = 3/6, same-sign, junk-free, g0 = 1,
all OFF-bottom) — mod-p multiplicity kills are NOT
residue-char-2-specific as a class fact; only the BOTTOM-reaching ones
are (at the bottom the multiplicities stay ≤ 2 at g0 = 1, so only
p = 2 can divide them).  Bottom-line kill census, complete: SIGN-PAIR
97 (66 at p = 3 Zp g0 = 2, 30 at residue-char-2 SD, 1 at p = 5 —
char-blindness confirmed through p = 5) + MODP 6 (the K1 rows).  No
CROSS, no MODP at p > 2, no MODP at g0 ≥ 2 at any bottom line.

**The answer to the composer's question.**  The protection identity,
per regime:

* **(K1), g0 = 1: a PATH-COUNT identity.**  The cascade slot is a
  ONE-PATH slot (P-A, 693/693, any valuation) — prove NEP-strong by
  path combinatorics (S-L4(iii)'s uniqueness half is the m = 2 case)
  and the slot survives as the single L-NORM(a) product b̄₀c̄_D ≠ 0.
  No residue arithmetic beyond "a field product of nonzero elements is
  nonzero".
* **(K2), g0 ≥ 2: a SIGNED-PATH-COUNT identity.**  Some bottom-line
  (slot, residue-class) has signed path-multiplicity EXACTLY ±1
  (PB-mult1-some 286/286; realized at the survivor on 200/200 kill
  rows with ≤ 2 nonzero classes) — prove by a sign-reversing pairing
  on the t-family paths that pairs off all but one path; the leftover
  class nets ±(one residue) or ±(difference of two distinct residues),
  nonzero characteristic-free.
* **The one residue-algebraic fence both regimes need:** no CROSS
  relation at the minimal line — instance-clean 979/979, and on kill
  rows vacuously strong (the survivor's net never mixes ≥ 3 classes).
  This, not the full carry algebra F[u]/(u^e − z̄), is the DEV-at-depth
  content (SURV-DISJ) actually consumes at the survivor.

Disclosures: coverage m ∈ {3, 4} as before; SDW3G2F/SDW4G2F run with
the principal d-cell ABSENT (theta_0 = 0; disclosed by the engine
census line) — the cascade may not exist there and the bottom carried
every such row; engine-unsupported shapes: none skipped (all 8 SD
towers traced).  All counts are measured INSTANCE evidence — never
proof steps; the two falsified preregistrations (PRED-5, PRED-7) are
retained above as falsified, not repaired away.

## Files

* runner: `verification/openmath/survdisj_instrument.py`
* output: `verification/openmath/survdisj_instrument_output.txt`
* results: `verification/openmath/survdisj_instrument_results.json`
  (written incrementally during the run; `final: true` on the sealed
  copy)
