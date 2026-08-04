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

## D3. RESULTS — PENDING (this section sealed empty; the battery has not
run at commit 1.  Commit 2 folds the verdict from the artifacts.)

## Files

* runner: `verification/openmath/survdisj_instrument.py`
* output: `verification/openmath/survdisj_instrument_output.txt` (commit 2)
* results: `verification/openmath/survdisj_instrument_results.json`
  (commit 2; incremental during the run)
