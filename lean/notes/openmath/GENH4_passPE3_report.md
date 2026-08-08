# GENH4 passPE3 report — hostile verification of GENH4_PROOF_2026-08-08.md

**Verifier:** fresh-context hostile pass PE3 (quote-and-classify; fixes
nothing). **Target:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` at HEAD
(dd83bc5; note body frozen at r2 fd35416+5279a11). **Arc:** seal 121d9ab →
RED 3eb1667 → GREEN 4b5c085 → PE1 263a36f → r1 dff23f8 → PE2 2618e9b → r2.
**Charges:** (1) the r2 census-display correction and its propagation
(S1/S6.1/S6.3/P-3 concordance + silent Q−1 consumers); (2) the corrected
dv0 = N trichotomy vs committed counter-keys + a fresh cell of my own;
(3) the re-pinned W-12.D firing at r5 (clause + fired-clause row);
(4) the new supp leg `genh4r2_supp.py` audited for tautology; (5) the eleven
R_τ by a route different from all prior passes; (6) free hunt over every
[r1]/[r2] tag. Machine leg: md5 pins at worktree/HEAD/seal + isolated /tmp
re-run of runner AND supp leg.

## VERDICT: PENDING (skeleton commit; machine leg + fresh route running)

### Machine-leg pins (verified)

* Runner `genh4_checks.py` md5 `ee8024b7a500220a6408dab373d7432f` IDENTICAL
  at worktree, HEAD, 5279a11, fd35416, 2618e9b, dff23f8, 4b5c085, 3eb1667;
  seal-time 121d9ab = `e5e435c3…` (the one disclosed repaired line).
* Supp `genh4r2_supp.py` md5 `7d0445c57d93816c7997d6738bd7b15a` first appears
  at 5279a11 (r2 commit 2), identical at HEAD/worktree.
* Committed artifacts at HEAD: output `9e6ca9b3…`, results `cbcff562…`,
  supp output `8ce5faa8…`, supp results `c966d311…`, qscout22 runner
  `cb885663…`, qscout22 results `6c2441a1…`, engine `7240a916…` — all match
  the note's pins.
* r2 diff audit: fd35416 note-only (+98/−8); 5279a11 = note (+37/−3) + the
  three supp files. Sealed runner + artifacts byte-untouched through r2. The
  smoke artifacts (`*_smoke.*`) were committed at the wave-fold 0089f9b
  (housekeeping; the smoke was disclosed at seal).
* Isolated re-run in /tmp sandbox: LAUNCHED (committed artifacts untouched);
  supp leg re-run: GREEN, 0 violations, 1.9 s in sandbox.

### Charge 3 (W-12.D re-pin) — VERIFIED, see final report
### Charge 4 (supp tautology) — audit complete, see final report

(Findings, clean-charges, fresh route, and grade line follow at the final
commit.)
