# GENH4 passPE5 report — hostile verification of GENH4_PROOF_2026-08-08.md (THE ACCEPTANCE ATTEMPT)

**VERDICT: PENDING (skeleton; legs running).**

**Verifier:** fresh-context hostile pass PE5 (quote-and-classify; fixes
nothing; the acceptance attempt — counter at 1/2 after PE4 CLEAN).
**Target:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` at HEAD
(note body = r3, 4b0d946). **Arc:** seal 121d9ab → RED 3eb1667 → GREEN
4b5c085 → PE1 263a36f → r1 dff23f8 → PE2 2618e9b → r2 fd35416/5279a11 →
PE3 a011533/3b88321 → r3 4b0d946 → PE4 CLEAN e15308d (1/2) → **PE5 =
this**. **Charges:** (1) the E-side (GENH4-CAP(E) + the odd/even slot
ladder) — never owned end-to-end by any pass; (2) the S9.3 level-0
assembly re-walked on TWO branches PE4 did not do; (3) the
[GENIND-H(4)] discharge supply argument itself (does GENH4.C produce
the labelling W-12.D consumes, both characteristics); (4) the
conditionality display at verdict-time git state; (5) free hunt over
the full [r1]+[r2]+[r3] tag set. Machine leg (11 md5 pins verified;
isolated re-run launched; supp leg re-run GREEN 3.0 s) and a fresh
route disjoint from all six prior routes (q = 9 = 3², the first
odd-non-prime-q cells ever, E-side raw walkers) below.

## Machine-leg status at skeleton commit

* **Pins 11/11 verified at worktree = HEAD:** runner `ee8024b7…`,
  output `9e6ca9b3…`, results `cbcff562…`, supp `7d0445c5…`/
  `8ce5faa8…`/`c966d311…`, qscout22 `cb885663…`/`6c2441a1…`, w10
  `a9c34244…`, w12 `7dc040d9…`, engine `7240a916…`. Runner
  byte-identical at 4b5c085 = fd35416 = 5279a11 = 4b0d946 = e15308d =
  HEAD; seal 121d9ab = `e5e435c3…` (the one disclosed repaired line).
* **Isolated full re-run** launched detached in /tmp/pe5/run (fresh
  copy; committed artifacts never written). **Supp leg re-run: GREEN,
  3.0 s, 0 violations** (leaf-diff pending below).

## Charge 1 (E-side, first result): OWN evaluator GREEN at ALL TEN committed consE rows

Own genre-E law evaluator written from S2.3 slot strings + S6.1
closed forms + my own re-derivation of GENH4-CAP(E) (no runner code;
`/tmp/pe5/e_side_checker.py`): full history recursion, band pricing
q^{(h−1)/2}, SPLTAIL/UND split at w < N vs w ≥ N as CAP(E) forces.
**Every consE row in BOTH artifact JSONs reproduces key-for-key: 10
rows, 301 keys, 0 mismatches, mass = (q−1)q^{4N−5h−3} exact on all** —
including the 114-key (Zp,2,7,h1) cell (deep histories to t = 2), the
deep-band cells (Zp,2,7,h3) and (Zp,2,11,h5) (h > 1: the ragged band
live, (h−1)/2 odd slots per string), and the equal-char fresh rows.
Teeth on MY OWN evaluator both fired: T1 (RAM allowed at odd band
values u ≥ 2N, i.e. CAP(E) violated) → mismatches; T2 (SPLTAIL
boundary at w < 2N instead of w < N, i.e. the undercut floor ignored)
→ 62 mismatches. Details + the CAP(E) re-derivation in the final
section below.

(Sections to be appended: findings, charges 2–5, fresh route, machine
verdict, grade line.)
