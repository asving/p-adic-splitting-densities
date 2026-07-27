# CASE-MN3 V2 SEALED GATE — the THRESHOLD re-seal of the p=3 realizability clause

*(2026-07-27, sealed BEFORE case_mn3_v2_gate.py existed. Precedent: Case-K v2. The v1
gate (CASE_MN3_SEALED_PREDICTIONS.md) PASSED all content families at both primes but
FAILED the p=3 realizability clause AS SEALED — a prediction-DERIVATION error: the
sealed list drew exclusions from field size alone and ignored the decidability level.
The repaired SP.6 THRESHOLD clause (MOVES_2026-07-24.md §M-SPECIES rev 2) says:
realized iff field-size-admissible AND N >= N*(letter). This file derives the FULL
per-letter N* table (v2's fresh content), seals per-level realized sets for N = 1..7,
a sharpness layer (absence at N*-1), and 5 exact first-appearance counts. Census runs
AFTER this file is committed; predictions are never adjusted post-census.)*

## S0 — SCOPE, ENGINE, FEASIBILITY

- ENGINE: identical to v1 (case_mn3_gate.py machinery; conventions FC1-FC11 of the v1
  seal UNCHANGED — window reader, completions {N..4N-3} u {5N}, canonical lifts,
  branch-weighted hits). Only the LEVEL SCOPE changes: p = 3 at every N in {1,...,7},
  full enumeration of all 3^(3N) boxes (c2,c1,c0) mod 3^N.
- FEASIBILITY (declared design, no essential-box argument needed): N <= 5 trivial
  (v1 did 3^15 in 2.3 s); N = 6 is 3^18 ~ 387M (v1 diagnostic did it); N = 7 is
  3^21 ~ 10.46G = ~730x the N=5 volume: the same vectorized driver (outer loop over
  c2 mod 3^7 = 2187 iterations, inner 3^14-pair arrays ~ 4.8M int64, ~40 MB) is a
  ~30-60 min single-process job. Full enumeration is chosen OVER an essential-box
  shortcut so the stray/menu checks stay unconditional at N = 7.
- p = 2 is NOT re-run: the v1 p=2 N=8 clause passed exact (42/42) and is on record.

## S0.1 — CONTAMINATION LEDGER (what v1 already observed vs what is fresh)

OBSERVED by v1 (NOT fresh; consistency duties only):
- The p=3 N=5 realized set (45 letters, per-letter hit counts in
  results/case_mn3_results.json) and the six absentees.
- The p=3 N=6 realized set (the post-census diagnostic: 3^18 exhaustive, 0 strays,
  0 faults, five of the six diagnosed letters appear, hits 5832-8748).
- The six DIAGNOSED letters' thresholds (6,6,6,6,6,7) — derived in the v1
  adjudication and confirmed by that diagnostic + constructed N=7 witnesses
  (f = g(x-1), g = x^3+3x^2+27x+729u). These six N* values are marked DIAGNOSED
  in S1, not fresh.
- CAVEAT: v1's driver cross-validation ran a p=3 N=3 full enumeration (letter-for-
  letter vectorized-vs-scalar compare). Its realized set/counts were computed by the
  machinery though never evaluated or reported; I have not looked at them. N=3-level
  predictions below are derived from the arithmetic alone, but are flagged
  machinery-touched rather than fully fresh.
FRESH in v2 (never censused, never derived on record):
- The exact N* value of each of the 47 non-diagnosed letters (v1 only bounds them:
  <= 5 if realized at N=5). In particular every sub-5 threshold (N* in {1,2,3,4})
  and the realized sets at N in {1,2,4} (N=3 with the caveat above).
- The FULL N=7 census: realized set = 51, 0 strays, 0 off-menu, 0 faults (v1 only
  constructed 2 witness boxes at N=7; no census).
- SHARPNESS: each fresh letter is ABSENT at N*(letter) - 1 (>= 3 explicit falsifier
  rows named in S2).
- FIVE exact first-appearance counts (S2), all at levels N in {1,2} that no v1 run
  ever touched.

## S1 — THE PER-LETTER N* TABLE AT p = 3 (the v2 seal; DIAG = v1-diagnosed, not fresh)

N*(letter) = least N such that some depth-<=2 chain realizes the letter with every
retained field decided at cap N. Derivations display the cheapest realizing height
vector; "cap" = coefficient identically 0 mod 3^N (pseudo-side, FC5), stable iff its
completion slopes stay strictly above the read slope for ALL completions >= N.
KEY FACT (v2 correction to the v1-era intuition): the root slope-0 side is a read
(FC2, the mod-3 factorization); it makes the a>0/l>=2 root rows cheap. POST-REC
windows entered from a slope-0 recentering have key slope hn = 0, so (I-aug) forces
child slopes > 0 only (this is what the v1 adjudication's s1 > s2 >= 1 used).

GROUP R (root, W = 3; heights = (v(c0), v(c1), v(c2)), slot 3 = 0):
  R1 fl()|(2)    N* = 2  [(1,0,any): side [0,1] drop 1, flat [1,3]]
  R1 fl()|(1,1)  N* = 4  [(3,1,0): slopes 2>1>0; slot 0 is a read endpoint - no cap]
  R2 fl(1)|(1)   N* = 3  [(cap,1,0): [1,2] slope 1, [2,3] flat; cap stable iff N>=3
                          (at N=2 completion 2 makes [0,1] collinear with [1,2])]
  R3 fl(2)|()    N* = 2  [(1,1,0): left side [0,2] slope 1/2, read [2,3] flat]
  R3 fl(1,1)|()  N* = 3  [(cap,1,0): sides drops >=2 | 1 | 0; cap stable at N>=3]
  R4 (3 rows)    N* = 3  [(2,1|cap,0): read [0,2] slope 1, right flat; endpoint 2
                          exact needs N=3; all three lambda exist over F_3]
  R5 (3 rows)    N* = 1  [(cap,0,0): slope-0 read [1,3] (fbar = z * quadratic),
                          left pseudo-side; all heights on the read are 0]
  R6 (6 rows)    N* = 1  [(0,0,0): THE mod-3 factorization read, slope-0 side [0,3];
                          each realizable lambda exists with nonzero roots over F_3]
  R6 {(1,1)^3}   FIELD-SIZE EXCLUDED (needs 3 distinct nonzero roots; F_3 has 2)
  R7 s0'=0       N* = 2  [(1,>=1,0): side [0,2] slope 1/2, right flat]
  R7 s0'=1       N* = 2  [(cap,1,>=1): side [1,3] slope 1/2; cap stable at N>=2]
  R8             N* = 2  [(1,>=1,>=1): side [0,3] slope 1/3]

GROUP Q3 (POST-REC W = 3 via root sel-(1,3); cheapest entrance = slope-0 root
  fbar = (z-r)^3, hn = 0, child heights (v(B'0), v(B'1), v(B'2)), B'j = f^(j)(r)-
  type coefficients, vertex (3,0); (I-aug): child slopes > 0):
  Q3(R1) fl()|(2)    N* = 3   [child (2,1,>=1): [0,1] drop 1... slopes 1 > 1/2]
  Q3(R1) fl()|(1,1)  N* = 7 DIAG [child (6,3,1): slopes 3>2>1 forced; endpoint 6
                                  exact -> N = 7; the v1 R1-copy absentee]
  Q3(R2)             N* = 6 DIAG [child (cap,3,1): read [1,2] slope 2, cap needs
                                  completion slopes > 2 for all >= N: N = 6]
  Q3(R3) fl(2)|()    N* = 5   [child (4,>=3,1): left side [0,2] slope 3/2 > read
                               slope 1; endpoint 4 exact -> N = 5]
  Q3(R3) fl(1,1)|()  N* = 6 DIAG [child (cap,3,1): drops >=3 | 2 | 1; N = 6]
  Q3(R4) (3 rows)    N* = 6 DIAG [child (5,3|cap,1): v(B'0) = s2+2s1 = 1+2*2 = 5
                                  exact -> N = 6; the three v1 R4-copies]
  Q3(R5) (3 rows)    N* = 4   [child (cap,2,1|cap): read [1,3] slope 1; cap stable
                               iff completion slopes > 1 for all >= N: N = 4]
  Q3(R6) (6 rows)    N* = 4   [child (3,2|cap,1|cap): read [0,3] slope 1; {(1,1)^3}
                               row FIELD-SIZE EXCLUDED as at the root]
  Q3(R7) s0'=0       N* = 5   [child (4,>=3,1): side [0,2] slope 3/2, right drop 1]
  Q3(R7) s0'=1       N* = 2   [child (cap,1,>=1): side [1,3] slope 1/2, left cap]
  Q3(R8)             N* = 2   [child (1,>=1,>=1): side [0,3] slope 1/3]

GROUP Q2 (POST-REC W = 2 via root sel-(1,2): slope-0 R6 {(1,2),(1,1)} or slope-0
  R5 {(1,2)} roots; hn = 0, child heights (v(B'0), v(B'1)), vertex (2,0)):
  Q2.1 fl()|(1)  N* = 4  [child (3,1): slopes 2 > 1 forced integers; 3 exact]
  Q2.2 fl(1)|()  N* = 3  [child (cap,1): read [1,2] slope 1; cap stable at N>=3]
  Q2.3 (3 rows)  N* = 3  [child (2,1|cap): read [0,2] slope 1; endpoint 2 exact]
  Q2.4 e=2       N* = 2  [child (1,>=1): side [0,2] slope 1/2]
GROUP Q1 + GROUP I (all W = 1 verdict letters):
  Q1             N* = 2  [via slope-0 sel-(1,1) roots: child side [0,1] drop
                          v(B'0) = 1 exact; at N = 1 the endpoint is capped]
  I21, I22, I31, I33  N* = 2 each  [every increment landing needs one EXACT
                          remainder/component height >= 1, impossible at N = 1:
                          I22/I33 via slope-0 (2,1)/(3,1) roots, component v = 1;
                          I21 via R7 (root N*=2), component 2v(r1)+1 = 3 > wf_e=2;
                          I31 via R8, component 3v(b1)+1 = 4 > wf_e = 3]

## S2 — SEALED PREDICTIONS AND FALSIFIERS (p = 3, N = 1..7)

P1 REALIZED SETS (iff-form: realized iff field-size-pass AND N >= N*): cumulative
  realized counts by level N = 1,2,3,4,5,6,7:
    9, 22, 32, 43, 45, 50, 51
  N=1 (9): R5 x3, R6 x6.
  N=2 adds (13): R1fl(2), R3fl(2), R7 x2, R8, Q3(R7)s0'=1, Q3(R8), Q2.4, Q1, I x4.
  N=3 adds (10): R2, R3fl(1,1), R4 x3, Q3(R1)fl(2), Q2.2, Q2.3 x3.
  N=4 adds (11): R1fl(1,1), Q3(R5) x3, Q3(R6) x6, Q2.1.
  N=5 adds (2): Q3(R3)fl(2), Q3(R7)s0'=0.   [N<=5 set = v1's censused 45: CONSIST]
  N=6 adds (5): Q3(R2), Q3(R3)fl(1,1), Q3(R4) x3.   [DIAG]
  N=7 adds (1): Q3(R1)fl(1,1).   [DIAG]
  The 2 field-size letters (lambda = {(1,1)^3}) are absent at ALL levels.
P2 SHARPNESS (fresh-letter absence one level below threshold; explicit rows):
  R8 ABSENT at N=1; R7 s0'=0 ABSENT at N=1; Q2.4 ABSENT at N=1; R4 (all 3 rows)
  ABSENT at N=2; Q2.1 ABSENT at N=3; Q3(R5) x3 and Q3(R6) x6 ABSENT at N=3;
  Q3(R3)fl(2) ABSENT at N=4; Q3(R7)s0'=0 ABSENT at N=4 — and in full: P1's iff
  means EVERY letter is absent at every N < N*.
P3 FIRST-APPEARANCE COUNTS (branch-weighted hits, FC10, at the letter's own N*;
  all five at levels no v1 run touched; derivations = digit counts over the box):
  (a) R5 {(2,1)} at N=1 (box 27):        3    [c0=0 mod 3, (c1,c2) = one of the
      3 monic irreducible quadratics' coefficient pairs mod 3]
  (b) R8 at N=2 (box 729):              18    [v(c0)=1 (2 ways), v(c1)>=1 (3),
      v(c2)>=1 (3)]
  (c) R7 s0'=0 at N=2 (box 729):        36    [v(c0)=1 (2), v(c1)>=1 (3),
      v(c2)=0 (6)]
  (d) R1 fl()|(2) at N=2 (box 729):    108    [v(c0)=1 (2), v(c1)=0 (6), c2 (9)]
  (e) Q3(R8) at N=2 (box 729):          36    [f = (x-r)^3 mod 3: 27 boxes per r,
      v(f(r))=1 kills 1/3 of c0-lifts -> 18 per r, r in {1,2}]
  BONUS (machinery-touched level, see S0.1 caveat): R2 at N=3 (box 3^9): 108
      [c0 = 0 mod 27 (1), v(c1)=1 (6), v(c2)=0 (18)].
P4 CONTENT FAMILIES AT EVERY LEVEL: 0 strays, 0 off-menu transitions, 0 engine
  faults (BOX/VERTEX/I-aug/partition) at every N in {1..7}; realized loop-typed
  letters at level N = {Q2.3 sel(1,2) iff N>=3} u {Q3 sel(1,3) row iff N>=4},
  never anything else.
FALSIFIERS (any hit => the v2 gate FAILS; the seal is not touched):
  V1 any letter realized at some N < N*(letter);
  V2 any field-size-passing letter with N*(letter) <= N absent at N;
  V3 any of the five P3 counts wrong (exactness layer, judged separately);
  V4 any P4 violation (stray / off-menu / fault / loop-class mismatch).

## S3 — POST-CENSUS VERDICT (appended after the run; seal untouched)

*(2026-07-27, census = case_mn3_v2_gate.py, run after S0-S2 were committed. All seven
levels exhaustive: N = 1..7, boxes 3^3 .. 3^21 = 10,460,353,203 (N=7: 266.5 s,
vectorized full enumeration — no essential-box shortcut needed). Full log:
/tmp/mn3v2_census.out; machine-readable: results/case_mn3_v2_results.json. Engine
integrity: the v2 N=5 per-letter hits are bit-identical to the v1 record (0/53
mismatches), so the engine is unchanged.)*

| sealed family | verdict over N = 1..7 |
|---|---|
| P1 realized sets (iff: FS-pass AND N >= N*) | realized = predicted EXACTLY at every level: 9, 22, 32, 43, 45, 50, 51 — PASS |
| V1 early (any letter below its N*) | 0 at every level — PASS (47 fresh thresholds all sharp from above) |
| V2 missing (predicted but absent) | 0 at every level — PASS |
| P2 sharpness (absence at N*-1) | implied by V1 = 0 everywhere; the named rows (R8@1, R7a@1, Q2.4@1, R4x3@2, Q2.1@3, Q3(R5)x3+Q3(R6)x6@3, Q3(R3)fl(2)@4, Q3(R7)a@4) all ABSENT as sealed — PASS |
| P3 first-appearance counts | all five EXACT: R5{(2,1)}@1 = 3; R8@2 = 18; R7a@2 = 36; R1fl(2)@2 = 108; Q3(R8)@2 = 36; bonus R2@3 = 108 — PASS |
| P4 strays / off-menu / faults | 0 / 0 / 0 at every level incl. the never-censused N=7 box — PASS |
| P4 loop classes (level-aware) | exactly {Q2.3 sel(1,2) iff N>=3} u {Q3 sel(1,3) iff N>=4} — PASS |
| field-size exclusions | the 2 lambda={(1,1)^3} letters absent at ALL seven levels (the only absentees at N=7) — PASS |

Diagnosed-letter confirmations (not fresh, consistency): the six v1 absentees enter
exactly at their DIAG thresholds — the five N*=6 letters first appear at N=6 with the
v1-diagnostic hit counts (5832-8748), the Q3(R1)fl(1,1) copy first appears at N=7
(hits 104,976).

CONTAMINATION HONESTY (what this pass proves vs re-observes): the N=5 and N=6
realized SETS were v1-observed — here they are consistency checks, not evidence.
FRESH and never observed before this run: the 47 non-diagnosed letters' exact N*
values (tested from BOTH sides at N in {1,2,3,4} and by absence one level below);
the realized sets at N = 1, 2, 4 (N=3 machinery-touched per S0.1, predictions
derived blind); the five P3 counts (levels 1-2, untouched by v1); and the entire
N=7 census (v1 had only 2 constructed witness boxes there): 0 strays, 0 off-menu,
0 faults over 10.46G boxes, realized set exactly the sealed 51.

GATE VERDICT: **PASS — every family, every level.** The v2 THRESHOLD clause
(SP.6 rev 2: realized iff field-size-admissible AND N >= N*(letter)) is now
census-pinned at p = 3 across N = 1..7, replacing the failed v1 realizability
list; the Case-K-precedent re-seal is discharged. Perimeter unchanged: kernel
D4R.0-K remains OPEN (SP.6(c): gate verdicts are not kernel support), and the
n = 3 POST-INC limitation stands. One derivation lesson on record (S1 KEY FACT):
the v1-era intuition missed that slope-0 root reads make R5/R6 rows N* = 1 and
give POST-REC entrances hn = 0 — the v2 table built on that correction survived
all falsifiers.
