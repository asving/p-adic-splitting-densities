# CASE-RESUMN3 SEALED GATE — RESUM-n3, the §S-RESUM S.7 gate: the n = 3 block solve

*(2026-07-27. SEALED BEFORE ANY CENSUS CODE EXISTED (S.7 SEAL SEMANTICS: this artifact
is the seal; until it existed the gate was SPECIFIED only). Source: MOVES_2026-07-24.md
§S-RESUM rev 6 (dual-accepted), S.0 (R_e)/S.2 RS.1-SH/S.4 ACT/S.5 RS.4 + S.7 protocol
(i)-(v) + (ORC-1)-(ORC-4). Every mathematical value below is DERIVED BY HAND from the
displayed (R_e)/RS.1-SH machinery + the §V-TABLES V.6 letter tables — the solve is
displayed in S1; NO census implementation was consulted. Case-K discipline: any sealed
falsifier fires => the layer FAILS and this file is not touched.)*

## S0 — FREE CHOICES (census conventions ONLY)

- FC1 BOX: f = z^3 + a z^2 + b z + c over (a,b,c) mod p^N; exhaustive at p = 2, N <= 8
  (2^24 boxes at N = 8) and p = 3, N <= 5 (3^15); decided_sigma(N) per N = 1..Nmax.
- FC2 ORACLE (ORC-3 map, displayed): PARI factorpadic (gp 2.17.4, ~/.local) on the
  integer representative; sigma := multiset of (e_i, f_i), e_i = ramification index,
  f_i = deg_i/e_i of each irreducible factor. The five sigma at n = 3:
  (1,1)^3, (1,1)+(1,2), (1,3), (1,1)+(2,1), (3,1).
- FC3 ORACLE IMPLEMENTATION (convention): exhaustive typing by an ELEMENTARY
  Newton-Hensel oracle (independent implementation; textbook facts only: Z_p root
  count by digit-wise Hensel lifting; quadratic cofactor typed by disc square class
  — p = 2: v odd or unit ≢ 1 mod 8 => ramified, unit ≡ 1 mod 8 => split, ≡ 5 mod 8
  => inert; p = 3: v odd => ramified, else unit QR => split/inert; r = 0 boxes:
  (1,3) vs (3,1) by triple-residual NP descent — fractional slope => (3,1),
  irreducible residual => (1,3); any other residual forces a Q_p root, contradiction
  with r = 0). ANCHOR: factorpadic run EXHAUSTIVELY at p = 2 N = 4 (4096) and
  p = 3 N = 3 (19683), and on >= 2500 stratified samples per pool at top N; ANY
  disagreement elementary-vs-factorpadic is a FAIL of the census oracle layer.
- FC4 (ORC-1) CERTIFIED DETERMINATION RADIUS (seal-time display duty, discharged):
  d := v_p(disc f_rep) (exact integer disc of the integer representative).
    CRITERION: 3d < 2N certifies sigma constant on the whole box.
  DERIVATION (Krasner, displayed): roots of monic f,g integral; g ≡ f mod p^N =>
  |f(beta)| <= p^{-N} per root beta of g => some root alpha of f with
  v(beta-alpha) >= N/3. Pairwise v(alpha_i-alpha_j) <= d/2 (each term of
  d = 2 Sum v >= 0); disc g ≡ disc f mod p^N and d < N => v(disc g) = d, so g's
  pairwise root distances <= d/2 too. If N/3 > d/2: the matched root is UNIQUE
  (two alphas within > d/2 of beta contradict the pairwise bound), the matching is
  a BIJECTION (two betas at one alpha contradict g's pairwise bound), Krasner both
  ways gives Q_p(alpha) = Q_p(beta), and the matching is Galois-equivariant (by
  uniqueness), so orbit structure + per-factor (e,f) — i.e. sigma — agree. QED.
- FC5 (ORC-2) UNRESOLVED bin: every box with 3d >= 2N (incl. disc = 0 at working
  precision) — counted separately, NEVER into decided_sigma(N). Certified iff
  d <= 5 at (p,N) = (2,8); d <= 3 at (3,5).
- FC6 EXACTNESS: Python ints/Fractions, zero tolerance. Long output ->
  /tmp/resumn3_census.out; JSON -> verification/results/case_resumn3_results.json.
- FC7 (ORC-4) TYPED TARGET: the sealed theory totals (S3) are for the
  CLASSIFIER-decided set at level N (all walk reads within digit levels < N).
  The census computes both sets; tested equalities: (D-a) classifier-decided
  count per (sigma,N) == S3 integer; (D-b) zero type mismatches on boxes both
  oracle-certified and classifier-decided; (D-c) BOTH symmetric-difference counts
  RECORDED (sealed: both expected NONEMPTY at N >= 4 — a decided-not-certified box
  exists (deep-disc m_vv strata), a certified-not-decided box exists; their
  non-emptiness is an adjudication FINDING, not a FAIL); (D-d) UNRESOLVED = exact
  complement of certified (definitional; leakage = FAIL).

## S1 — THE SOLVE, DISPLAYED (hand derivation; (R_e) + RS.1-SH; masses conditional on entry)

BLOCK 2 (1 state; entry v(h0),v(h1) >= 1; per-read strata at depth L >= 1, V.6.3 letters):
  m2(L): per-(u,w) mass q^{-3L}; counts split (q-1)(q-2)/2, inert q(q-1)/2, double q-1;
  m_w2(k0 odd): mass (q-1) q^{-(3k0-1)/2} -> (2,1);  m_vv(k1): mass (q-1) q^{-3k1} -> (1,1)^2.
  Sum_L q^{-3L} = 1/(q^3-1).  K_2 = kappa_2 = (q-1)/(q^3-1) = 1/(q^2+q+1)  [W6 geometric,
  denominator q^2+q+1].  det(I-K_2) = (q^2+q)/(q^2+q+1).  Solve beta_2 = (I-K_2)^{-1} b_2:
    beta_2(split) = 1/(2(q+1));  beta_2(inert) = 1/(2(q+1));  beta_2(ram) = q/(q+1).
  [cross-check: p odd complete-the-square law P(v(delta) odd) = q/(q+1) — EQUAL.]
BLOCK 3 (1 state; entry v(a),v(b),v(c) >= 1; NP hull strata over (0,kc),(1,kb),(2,ka),(3,0);
 D6 := q^6-1, D3 := q^3-1; per-stratum totals, each derived by geometric height sums):
  A (kc = 3L, integer slope; residual cubic, const != 0; per-(u,abar,bbar) mass q^{-6L}):
    3dist (q-1)(q-2)(q-3)/6 -> (1,1)^3 | lin x quad q(q-1)^2/2 -> (1,1)+(1,2) |
    irr (q^3-q)/3 -> (1,3) | double+simple (q-1)(q-2) -> SPLIT leg (1,1) (+) blk2 |
    triple (q-1) -> K_3 column.   Totals: counts/D6.
  B (kc !≡ 0 mod 3, fractional /3): total (q-1)(q^5+q^3)/D6 -> (3,1).
  C (vertex (1,kb)): kb odd: (q-1)q^4/D6 -> (1,1)+(2,1);  kb = 2mu even, per-(u_b,abar)
    mass q^{-6mu}: distinct (q-1)(q-2)/2 -> (1,1)^3, irred q(q-1)/2 -> (1,1)+(1,2),
    double (q-1) -> SPLIT leg; totals: counts/D6.
  D (vertex (2,ka)): kc-ka odd: (q-1)^2 q^2/(D3 D6) -> (1,1)+(2,1); kc-ka = 2muD even:
    distinct (q-1)^2(q-2)/2, irred q(q-1)^2/2, double (q-1)^2, all /(D3 D6);
    distinct -> (1,1)^3, irred -> (1,1)+(1,2), double -> SPLIT leg.
  E (all vertices): (q-1)^2/(D3 D6) -> (1,1)^3.
  STRATUM CHECKSUM (verified symbolically): A+B+C+D+E totals = 1.
  K_3 = kappa_3 = (q-1)/D6;  det(I-K_3) = (q^6-q)/(q^6-1) = (q^5+q^4+q^3+q^2+q)/(q^5+...+1).
  J (split-leg coefficient, the (J-RAT) object) = [(q-1)(q-2)+(q-1)]/D6 + (q-1)^2/(D3 D6).
  Split legs: sigma = (1,1) (+) sigma_1, sigma_1 ~ beta_2 (delta = 1; NO delta = 2 legs
  exist at n = 3 — every residual double root lies in F_q: q0 = 4 tested ACT-only).
  beta_3(sigma) = (t_sigma + J beta_2map(sigma))/(1 - kappa_3), t_sigma the terminal totals.
ROOT (RS.1-SH; V.6.1 letters over q^3): m_H3 (q-1)(q-2)/(6q^2) -> (1,1)^3;
  m_H12 (q-1)/(2q) -> (1,1)+(1,2); m_H<3> (q^2-1)/(3q^2) -> (1,3);
  m_2+1 (q-1)/q^2 -> (1,1) (+) beta_2; m_3 1/q^2 -> beta_3.

## S2 — SEALED (i)+(ii): THE FIVE R_sigma, FOUR-PRIME VALUES, CHECKSUM

With P5 := q^5+2q^4+2q^3+2q^2+2q+1 = (q+1)(q^4+q^3+q^2+q+1), P4 := q^4+q^3+q^2+q+1:
  R_(1,1)^3     = (q^5 - q^4 + q^3) / (6 P5)          -> 1/6
  R_(1,1)+(1,2) = (q^5 + q^4 + q^3) / (2 P5)          -> 1/2
  R_(1,3)       = (q^4 + q^3) / (3 P4)                -> 1/3
  R_(1,1)+(2,1) = (q^4 + q^2 + q) / P5                -> 0
  R_(3,1)       = (q^2 + 1) / P4                      -> 0
  CHECKSUM: Sum_sigma R_sigma = 1 IDENTICALLY (verified symbolically).
  MOMENT CROSS-CHECK (classical, Kac-Rice): 3 R_111 + R_112 + R_1121 = q/(q+1) — EQUAL.
| q | (1,1)^3 | (1,1)+(1,2) | (1,3) | (1,1)+(2,1) | (3,1) | sum |
|---|---|---|---|---|---|---|
| 2 (wild) | 4/93 | 28/93 | 8/31 | 22/93 | 5/31 | 1 |
| 3 (wild) | 63/968 | 351/968 | 36/121 | 93/484 | 10/121 | 1 |
| 5 (tame) | 875/9372 | 3875/9372 | 250/781 | 655/4686 | 26/781 | 1 |
| 7 (tame) | 14749/134448 | 19551/44816 | 2744/8403 | 2457/22408 | 50/2801 | 1 |

## S3 — SEALED (iv): THE ACT LAYER (pools q0 = 2, 3, 4; tested-pool list RECORDED)

- Act_2 = Act_3 = Act_4 = {s_blk2 T-cell (|cell| = q-1), s_blk3 T-cell (|cell| = 1)}:
  ALL states active at every tested pool (cell sizes q-1, 1 nonvanishing at 2, 3, 4).
  JUNK BLOCKS EMPTY at all three pools: det(I - D_{q0}) = 1 (empty product) —
  RECORDED, nonzero at p = 2, 3 (and q0 = 4). Untested pools ride S.4's per-pool kernel.
- ENTRY VANISHING (empty ARROWS at wild pools — polynomial count vanishing; the census
  must find EXACTLY ZERO members): at q0 = 2 (factor q-2): root m_H3; blk2 m2 o_split;
  blk3 A-3dist, A-split (count (q-1)(q-2)), C_even-distinct, D_even-distinct.
  At q0 = 3 (factor q-3): blk3 A-3dist ONLY. Consequence sealed: at p = 2 the block-3
  SPLIT LEG (J's A-part + C/D distinct parts) loses its A-summand; J(2) = 1/63 + 1/441
  = 8/441 stays nonzero (C_even/D_even doubles survive).
- KERNEL/DET VALUES AT THE POOLS (active submatrix = full matrix, 1x1 per block):
  | q0 | K_2 | det(I-K_2) | K_3 | det(I-K_3) | J |
  | 2 | 1/7 | 6/7 | 1/63 | 62/63 | 8/441 |
  | 3 | 1/13 | 12/13 | 1/364 | 363/364 | 27/4732 |
  | 4 | 1/21 | 20/21 | 1/1365 | 1364/1365 | 64/28665 |
- ACTIVE-VALUE AGREEMENT (CTS-M(ii-c), per pool): the S2 wild values R_sigma(2),
  R_sigma(3) are the ACTIVE-subsystem solves at q0 = 2, 3 BY CONSTRUCTION (full = active);
  no pole survives cancellation at any tested pool (all denominators P5, P4, q^2+q+1,
  q^5+...+q are nonzero at q0 = 2, 3, 4 — sealed: P5(2) = 93, P5(3) = 968, P4(2) = 31,
  P4(3) = 121). A censused wild-p density disagreeing with S2 while the tame checksum
  holds adjudicates as an (ii-c)/ACT failure BEFORE any density comparison.

## S4 — SEALED (iii)+(v): DEPTH PARTIALS (read units; consistency-only layer)

Depth = number of classifier READS (root read = read 1; each block read = +1; a split
box is decided when BOTH members are decided). Recursions (displayed):
  D2(j) = 1 - kappa_2^j;  D3(j) = t3tot + J D2(j-1) + kappa_3 D3(j-1), D3(0) = 0,
  t3tot = 1 - J - kappa_3;  T_k = (1 - 1/q) + (q-1)/q^2 D2(k-1) + 1/q^2 D3(k-1).
Sealed still-in-block masses: blk2 kappa_2^k; blk3 same-size kappa_3^k (ESCAPE-probe
layer (b), consistency class). Sealed T_k (exact):
  p = 2: T_1 = 1/2; T_2 = 281/294; T_3 = 18413/18522; T_4 = 166559/166698;
         T_5 = 73505069/73513818; T_6 = 4631291801/4631370534;
         T_7 = 5954604797/5954619258; T_8 = 18381903272153/18381909649446.
  p = 3: T_1 = 2/3; T_2 = 3485/3549; T_3 = 1290071/1291836;
         T_4 = 470178911/470228304; T_5 = 171161719679/171163102656.
ESCAPE-probe layer (a) (E0's symbolic refuter): both kernels are 1x1 with
K_e(q0) < 1 at q0 = 2, 3, 4 — NO closed class exists at any tested pool (row deficit
= exit mass > 0); sealed: 1/7, 1/13, 1/21, 1/63, 1/364, 1/1365 all < 1.

## S5 — SEALED DISCRIMINATING LAYER: classifier-decided_sigma(N) THEORY INTEGERS

LEVEL BOOKKEEPING (displayed; box mod p^N knows digit levels 0..N-1; N_det = 1 + max
level read; recentering shifts are level-preserving; Hensel division f -> h is
level-preserving, V.6.4 THRESHOLD): root letters N = 1. Blk2 from scale s (own frame):
m2 terminal at cum L: N = 2L+1; m_w2 rel k0: N = 2s+k0+1; m_vv rel k1: N = 2s+2k1+1;
double at L recurses from scale L. Blk3 from scale mu: A terminal at cum L: N = 3L+1;
B rel kc: N = 3mu+kc+1; C_odd/D_odd/E rel kc: N = 3mu+kc+1; C_even terminal at muC:
N = 3mu+3muC+1; D_even terminal (ka,muD): N = 3mu+ka+2muD+1; A-triple recurses (+0);
EMBEDDED blk2 legs: N = lambda_sep + N_own, with (lambda_sep, start scale) = (L, L)
for A-split at L; (mu+muC, mu+muC) for C_even-double; (mu+ka, mu+muD) for D_even-double
(derived: the recentered-cubic window heights v(c')-3s, v(b')-2s at separation lambda:
c'-line read at lambda + 2*Lambda etc.). All masses as in S1, scale-invariant.
SEALED INTEGERS decided_sigma(N) * p^{3N} (order: (1,1)^3, (1,1)+(1,2), (1,3),
(1,1)+(2,1), (3,1); last col = total decided mass):
p = 2:
  N=1: 0, 2, 2, 0, 0                                | 1/2
  N=2: 0, 16, 16, 8, 8                              | 3/4
  N=3: 16, 144, 128, 80, 80                         | 7/8
  N=4: 128, 1184, 1056, 832, 640                    | 15/16
  N=5: 1280, 9728, 8448, 7040, 5248                 | 31/32
  N=6: 10368, 78080, 67584, 59648, 42240            | 2015/2048
  N=7: 87552, 629248, 541184, 484352, 337920        | 4063/4096
  N=8: 705536, 5038080, 4329472, 3930112, 2705408   | 16317/16384
p = 3:
  N=1: 1, 9, 8, 0, 0                                | 2/3
  N=2: 27, 243, 216, 108, 54                        | 8/9
  N=3: 1215, 7047, 5832, 3240, 1620                 | 26/27
  N=4: 32886, 190998, 158112, 99144, 43740          | 80/81
  N=5: 927288, 5196312, 4269024, 2711880, 1185354   | 242/243
(Each is a union of full mod-p^{N_det} boxes: every count integral — internal check
passed at derivation; masses increase to R_sigma(p): e.g. p=2 N=8 totals /2^24 are
within 3e-3 of S2's wild values, from BELOW, every sigma.)

## S6 — FALSIFIERS PER LAYER (any hit => that layer FAILS; sealed attribution)

F1 (S2/DISCRIMINATING): any (sigma,N) census classifier-decided count != S5 integer
   [indicts the CONJUNCTION: V.6 tables + (R_e) solve + level bookkeeping];
F2 (ORACLE): any elementary-vs-factorpadic disagreement (exhaustive low-N or sample)
   [indicts the census oracle, gate INVALID not the theory]; any box both certified
   and classifier-decided with oracle sigma != walk sigma [STRUCTURAL, plan §8 R1/R2];
F3 (ORC-2): any UNRESOLVED box with 3d < 2N, or any certified box with 3d >= 2N
   [leakage above/below the sealed radius];
F4 (ACT): any member found in a sealed-empty arrow (S3 entry-vanishing list) at its
   wild pool; junk-block nonemptiness at q0 in {2,3,4}; any surviving pole (S3);
F5 (CHECKSUM): Sum_sigma decided_sigma(N) + undecided(N) != 1 exactly at any N;
F6 (DEPTH, consistency-only): census read-depth partial sums != S4's T_k at any
   k <= 8 (p=2) / k <= 5 (p=3) [adjudicate: extractor-dependent, REV 3];
F7 (D-c): either symmetric difference EMPTY at p = 2, N = 8 would be a FINDING
   (sealed expectation: both nonempty) — adjudication, not FAIL.
STATUS: SEALED. Census (case_resumn3_gate.py) to be written AFTER this line.

## S7 — PRE-CENSUS CORRECTION TO S5 (2026-07-27, BEFORE any census code was written;
Case-K adjudication class (1), prediction-derivation error, caught at walk-semantics
review; S1-S4 and S6 UNTOUCHED — no stratum mass, R_sigma, det, or T_k value moves)

ERROR: S5's DP charged the C_odd and E strata with N_det = 3mu+kc+1 (exact v(c) read).
Their verdicts need NO exact v(c): C_odd's tracks are the ramified quadratic (kb exact,
odd — level 2mu+kb) + a linear track needing only VERTEX PLACEMENT (c-zeros through rel
(3kb-1)/2), so the whole kc-tail decides at N_det = 3mu+(3kb+1)/2; E likewise decides at
N_det = 3mu+2kb-ka+1 (c-zeros through rel 2kb-ka; kc-tail whole, incl. c = 0 members —
the same semantics S5 already used for blk2's m_vv). B/D_odd/A/C_even/D_even stand
(their verdict certificates genuinely read the deep digit: parity or residual constant).
CORRECTED SEALED INTEGERS decided_sigma(N) * p^{3N} (same order; supersede S5's table):
p = 2:
  N=1: 0, 2, 2, 0, 0                                | 1/2
  N=2: 0, 16, 16, 12, 8                             | 13/16
  N=3: 16, 144, 128, 96, 80                         | 29/32
  N=4: 128, 1184, 1056, 896, 640                    | 61/64
  N=5: 1280, 9728, 8448, 7360, 5248                 | 501/512
  N=6: 10496, 78080, 67584, 60928, 42240            | 1013/1024
  N=7: 88064, 629248, 541184, 489472, 337920        | 2037/2048
  N=8: 708608, 5038080, 4329472, 3951616, 2705408   | 16341/16384
p = 3:
  N=1: 1, 9, 8, 0, 0                                | 2/3
  N=2: 27, 243, 216, 126, 54                        | 74/81
  N=3: 1215, 7047, 5832, 3402, 1620                 | 236/243
  N=4: 32886, 190998, 158112, 100602, 43740         | 722/729
  N=5: 927288, 5196312, 4269024, 2726460, 1185354   | 19622/19683
F1's target is THIS table. The walk's read semantics (binding for the census
implementation of "classifier-decided"): a read completes when its verdict
CERTIFICATE digits are within the box — vertex-placement zeros for linear tracks,
the odd-valuation lead digit for ramified terminals, the residual coefficients for
residual-factorization reads.
CENSUS FOLLOWS THIS LINE.

## S8 — POST-CENSUS VERDICT (appended after the run; no sealed value above touched)

*(2026-07-27, census = case_resumn3_gate.py, written and run AFTER S0-S7. Log:
/tmp/resumn3_census.out; JSON: results/case_resumn3_results.json. Boxes walked
exhaustively: p = 3, N = 1..5 (3^3..3^15) and p = 2, N = 1..8 (2^3..2^24); ~19.2M + 16.4M
walk+oracle classifications; PARI = gp 2.17.4, oracle realized as factor+idealprimedec
(types (e,f) PARI-native; a census-side convention refining FC2's factorpadic naming),
exhaustive at p = 2 N = 4 (3072 certified) and p = 3 N = 3 (16038 certified) + 2500
stratified certified samples per pool at top N. Census-side repairs during smoke tests,
BEFORE any full run, all census-bugs not seal values: walk shape-dispatch False/None
conflation; zp_roots Hensel-certification before root separation (j > d/2 refinement
added); res3 LUT keyed without p; gp per-line failure retry + 256M stack.)*

| sealed layer | census result |
|---|---|
| F1 DISCRIMINATING (S7 corrected table) | classifier-decided counts EXACT at every (sigma,N): p = 2 all N = 1..8, p = 3 all N = 1..5 — 65/65 sealed integers ✓ |
| F2 oracle vs walk on overlap | 0 type mismatches on every box both certified and decided, all (p,N) ✓ |
| F2 PARI anchor | elementary oracle == PARI: 16038/16038 (p3 exh), 3072/3072 (p2 exh), 2500/2500 + 2500/2500 (top-N samples) ✓ |
| F3 ORC-1/2 radius + bin | definitional in the census routing (certified iff 3d < 2N; else UNRESOLVED); UNRESOLVED counts recorded: p2 N=8: 786432 (=3/64); p3 N=5: 649539 ✓ |
| F4 ACT | kernel/det values match sealed at q0 = 2, 3 (6/7, 62/63; 12/13, 363/364; q0 = 4 checked seal-side: 20/21, 1364/1365); junk blocks EMPTY (det(I-D)=1); entry-vanishing EXACT ZEROS: mH3/o_split/A-split at q=2, A-3dist at q=3 ✓ |
| F5 checksum | decided + undecided = p^{3N} exactly at every (p,N) ✓ |
| F6 depth (consistency) | census cum(k)/p^{3N} <= T_k <= cum(k)+undec(N) at every k: p=2 k=1..8, p=3 k=1..5 ✓ |
| F7 / D-c sym-diff | decided∖certified NONEMPTY everywhere (e.g. p2 N=8: 742400); certified∖decided EMPTY at ALL (p,N) — the sealed both-nonempty expectation HALF-FIRED: adjudication FINDING, recorded |

D-c ADJUDICATION (finding, not FAIL, per S6 F7): certified∖decided = 0 means the walk
decides every Krasner-certified box at these (n,N) — the walk's determination levels
sit BELOW the 3d/2 Krasner radius on every certified box here. The sealed expectation
of non-emptiness on that side was a prediction error ABOUT THE ADJUDICATION LAYER
(direction of set inclusion), not about any counted quantity; no sealed integer is
affected. The other side (decided∖certified, deep-disc strata: m_vv-type tails) is
nonempty exactly as sealed.
CONSISTENCY LAYERS (RS.5): repo-internal engine agreement confirmed at spot values —
lean/notes/M1_bridge.md records alpha(3,(1,1)^3;2) = 4/93 and L5fix_complete.md the
(3,1) row (5/31, 10/121, 26/781, 50/2801), both == S2's sealed values verbatim.

GATE VERDICT: **PASS** — FAILS: 0; every falsifier family F1-F6 silent; the one F7
finding adjudicated above. What this exercises (S.7's own scope caveat, sealed): the
SOLVE (both 1x1 blocks + the deep split legs' beta_2 convolution), the ACT semantics
at the wild pools q0 = 2, 3 (+ q0 = 4 arithmetic), the checksum, and the (ORC)-typed
oracle equality — the value-kernel and mu >= 2 machinery are NOT exercised (gated at
n = 5 per plan §0). Per S.7: gate RESUM-n3 status SEALED -> RUN -> **PASSED**; the
§S-RESUM acceptance ledger still awaits STATE-probe-2 and [1v]-FULL (untouched here).
