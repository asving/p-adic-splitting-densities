# W12 passPE6 report — hostile verification pass 6 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD = post-r5
(**be4a1dc** + markup fix **ee17210**). Read first: all five prior reports
(PE1 2b47711, PE2 1be15d2, PE3 c9c5c0e, PE4 26689da, PE5 c3e2f8e), the full
r5 diff (both commits), the delivered annex draft
`HMENU3_annex_draft_r5.md` and its application at HMENU3 (19c0285), and the
consumer notes at their pins (GENH4.C @ 4b0d946, GENIND Step 5 @ HEAD, HE7's
chain claim, GENHN's [GENHN-HE] box). This pass fixes nothing; it quotes and
classifies. Charged attack order: (1) the r5 text, never before attacked —
every changed passage walked against the files it cites; (2) the (A1)
σ-LABELING clause AS CONSUMED by its three consumers; (3) W-12.D's Step 4
(both bounds, post-r4/r5 warrants) and the Step 1–3 telescoping, re-derived
from scratch; (4) the (A0)/(A2) clauses; (5) free hunt. Fresh route:
three legs disjoint from all five prior routes (§4).

**VERDICT: (to be filled from findings)**

## 1. FINDINGS

(section pending)

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

(section pending)

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  **7dc040d94fbbb1e8d20ac817b665d418** == `git show f669cb0:…` — byte-identical
  at HEAD; committed artifacts carry §S10's md5s (05776c9e… / 0557b15f…).
* **Fresh isolated re-run (single run, this pass, detached with pidfile):**
  exit 0, **3,232,506 checks / 0 violations**, teeth **W12-T-SHAPE 23 /
  T-DRAIN 23 / T-CENSUS4 8 / T-SIGMA 1273**, 323.8 s, verdict GREEN — the
  SIXTH green run of the arc, at identical counts to §S10.
* **Artifacts:** fresh JSON content-identical to committed after stripping
  timing keys (programmatic compare == True); output diff = 1 line (elapsed
  323.8s vs 323.0s). Committed bytes RESTORED, md5s re-verified.
* **Tautology audit (spot):** the σ-witness leg's predictions are built from
  the note's constructions (runner L1043–1065) and scored against PARI
  `factorpadic` (L951) — an independent engine; the DBL/SHAPE legs compare
  reader-measured counts against note formulas, not formula-vs-formula.
  Witness-builder code re-read at HEAD: byte-consistent with the [r5] CITE
  VERIFICATION's description (`B = b2`; `B == 0` branch builds the SEALED
  pair with `predA = ((1,1),(2,1))`, `predB = ((3,1),)`); the 15-of-85
  arithmetic re-derived from the loop (b₂ = p·tdig = 0 iff tdig = 0, q pairs
  per row over rows (2,3),(2,4),(3,2),(3,3),(5,2): 2+2+3+3+5 = 15 of
  8+16+9+27+25 = 85).

## 4. FRESH ROUTE

(section pending)

## 5. ARC / COUNTER

(section pending)

— passPE6 verifier, fresh context, 2026-08-09.
