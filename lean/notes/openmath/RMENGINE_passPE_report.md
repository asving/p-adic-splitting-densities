# RMENGINE-PE — Fable round-1 hostile pass (execution + content) on RMENGINE_2026-08-08.md @ bf18bfe: NOT-CLEAN, 1C(display-local)/2G/3n — every proved clause CONFIRMED by blind reimplementation (incl. the first (RM-4) data ever); PC-C1 adjudicated TEXT-GAP; ONE NEW critical display (the S4.2 fence-box mechanism is FALSE at d0 = 1 — the flat corners at d0 = 1 are coverable by the note's own L-MU family)

## VERDICT BLOCK

**VERDICT: NOT-CLEAN.**  Findings: **1 CRITICAL (display-local, off the
theorem chain)** + **2 justification gaps** + 3 nits.  Simultaneously: the
note's entire PROVED perimeter survived a from-note-alone hostile
reimplementation at fresh instances with ZERO violations — all four box
clauses at m = 2, 3 AND m = 4 (the first level-4 engine data ever measured),
tree == canonical division, strict mu-descent on T-scope, exact line quanta,
the zh-kernel end-to-end, LAW-DCX-(m+1) 0 mismatches on 2,208 fresh pairs
including the FIRST LAW-DCX-5 census, 7/7 mutation controls visible.  The
committed diagnostic re-ran byte-exact.  The critical is confined to the
S4.2 FENCE box (asserted content consumed by nothing on the proof chain):
its obstruction mechanism is arithmetically false at d0 = 1, and the note's
own (A_i)/(B_i) construction in fact COVERS the d0 = 1 flat corners
(machine witnesses below) — the fence over-fences; openness is overstated
(conservative direction; no proved clause is touched).  Also: the PE leg
ADJUDICATES RMENGINE-PC's C1 as a TEXT GAP (mechanism sound; the
pi-normalization step must be displayed), and dissolves most of PC-G5's
bite (the (D3) off-grid-at-own-line case is provably EMPTY; census 0).

* **F1 [CRITICAL, display-local — NEW]** S4.2 fence box: "(A_i)/(B_i) are
  jointly unsatisfiable" is FALSE at d0 = 1; witness weights + strict
  descent measured on actual flat trees.  Off the theorem chain (nothing
  consumes the fence box); cure = erratum re-scoping the fence to d0 >= 2
  + the cheap strengthening (T-TERM, and plausibly RM-GEN, extends to the
  d0 = 1 flat corners by the note's own proofs).
* **F2 [GAP]** = PC-C1, here adjudicated: DIGIT-SPLIT as displayed needs
  the pi-normalization step (factor pi^{w0(b)+w0(c_d)}, split the unit
  parts, restore).  TEXT gap, not mechanism gap: my from-note
  implementation was FORCED to insert it, and with it every displayed law
  holds (97 engine calls, 0 violations); the committed diag's own
  digit_split_norm does the same.
* **F3 [GAP]** S0.2 scope remark (ii)'s v = 0 case appears UNREALIZABLE on
  the legal class (deg f < deg Phi_m caps the read at <= g_{l-1} slots per
  level, so the read value is a z_l-polynomial of sub-minimal degree with
  not-all-zero coefficients at every level: v != 0 always).  Measured
  0/97.  Harmless as stated ("v = 0 is legal") but the clause is dead
  weight and the (D3)/RM-GEN off-grid branches it feeds are likewise
  vacuous (see F5).
* **n4** claims-table key C2 spans a line-wrap in S0.3 (grep-stable only
  whitespace-normalized) — the table's "machine-censusable" charter needs
  a normalization caveat.  Census result: 14/14 keys otherwise present.
* **n5** S7.1 (COR-A) carries no inline at-acceptance qualifier (it lives
  in the genre header + S11 + the 0/2 counter) — same surface as PC-G4;
  agreed, presentational.
* **n6** garbled intermediate displays: L-LINE(ii)/(iii) and the S4.1
  base-case sentence contain unparseable fragments ("/e_i*...",
  "e_{i-1} >= 1 <= P_{i-1}*(w_{i-1}/w_{i-1})..."), and the fence box uses
  an undefined symbol W_{i-1}.  The END results are right (re-derived and
  machine-confirmed); the displays need cleanup.

## F1 IN FULL (quote, arithmetic, machine witnesses)

Quoted (S4.2 fence box): "at a flat level i >= 2 (e_i = 1) the conditions
(A_i)/(B_i) are jointly unsatisfiable (the promotion interval collapses:
w_{i-1}P_{i-1}*1 > W_{i-1} + w_{i-1}P_{i-1} is impossible)" and "a
level-(i+1) correction can genuinely RAISE any linear mu"; the box then
declares TERMINATION OPEN on {exists i: e_i = 1} minus the single L-LEX
case.

The arithmetic error: the displayed impossibility uses rho_{i-1} =
P_{i-1}, but the note's own S4.1 display defines rho_l := P_l - 1 for
l >= 1.  With the correct rho, joint satisfiability of (A_i)/(B_i) at a
flat level i is equivalent to w_{i-1} > sum_{l<i-1} w_l rho_l, which
cascades down (each step needs w_l near its (A_l) ceiling) and bottoms
out at rho_0 < P_0, i.e. exactly d0 = 1.  So: at d0 >= 2 the fence's
conclusion holds (my probe confirms: F2-e1flat-d2, F3-e2flat-d2 both
INFEASIBLE); at d0 = 1 it is FALSE.

Machine witnesses (rmengine_pe_reimpl.py, exact Fractions, strict
inequalities):
  * shape (d0=1, e=(2,2,1), g=(1,1,1)) — the box's own case, flat level
    i = 2: weights (1, 5/4, 19/8) satisfy ALL (A_i)/(B_i) strictly
    ((A_2): 19/8 < 5/2; (B_2): 19/8 > 1 + 5/4 = 9/4).  The M3C tower
    (Zp3, that shape + top read (2,1,1)) ran the ACTUAL S2.2 tree under
    those weights: 88 nodes, 30 promotions, 16 exits, 16 level-3
    corrections (the alleged mu-raisers) — 0 non-descending mu edges.
  * m = 2, e1 = 1, d0 = 1 (the L-LEX case): interval (P0-1, P0) nonempty;
    witness (1, 3/2); M2C actual tree: 0 non-descending edges — even the
    scoped L-LEX supplement is unnecessary (plain L-MU-family strictness).
  * also feasible at d0 = 1: flat i = 1 mid (witness (1, 3/2, 1)), DOUBLE
    flat (1, 3/2, 5/4), flat e=1 g=2 (1, 3/2, 17/8), m = 4 top-1 flat
    (1, 5/4, 149/64, 591/128).  (The S4.1 midpoint rule itself fails on
    the last one — nonemptiness at flat levels needs near-ceiling
    choices, which is why the note's e_i >= 2 existence proof does not
    see this region.)

Consequences: (i) both quoted mechanism sentences are false at d0 = 1;
(ii) the fence's OPEN set is overstated — the note's own L-MU descent
arithmetic (every edge inequality is exactly (A)/(B)) terminates ALL
d0 = 1 flat shapes, so T-TERM extends there by the note's own proof; and
since no other clause of S2/S3/S5 consumes e_i >= 2 (the reads just
degenerate: s = 0, eps = 1), DEV-(m)/RM-GEN plausibly extend verbatim —
the four clauses measured instance-true on both flat towers here (census,
0 exceptions), consistent with RM2E.  (iii) The S4.2 PRICE display
("non-linear/filtration measure ... one dedicated unit") applies only to
the d0 >= 2 corners.  S8 rows 5/6 inherit the erratum.  No impact on
RM-GEN's stated T-scope claims: the error is one-sided (under-claiming).

## PC-C1 ADJUDICATION (the dispatcher's question to this leg)

TEXT GAP, not mechanism gap.  Building the tree from the note alone, the
displayed DIGIT-SPLIT (q the reduction hom) annihilates any coefficient
product with w0 > 0 (q(alpha) = 0), which would break L-LINE(ii)'s
Delta-line = 0 (the L-child would be absent and the pi-child would carry
the whole mass at Delta-line = 0, contradicting L-LINE(iii)'s "junk
strictly raises").  The forced cure is exactly PC's: factor
pi^{w0(b)+w0(c_d)}, DIGIT-SPLIT the unit parts, restore the factor.  With
that one insertion the ENTIRE displayed calculus holds with 0 violations
at 97 fresh engine calls (m = 2/3/4, incl. d0 = 2 junk-alive and g0 = 2
multi-k level-0 corrections); the committed diag's digit_split_norm makes
the same normalization ("DIGIT-SPLIT on the unit part").  Repair = display
the normalization step in S2.1/S2.2 and thread w0-additivity (w0 is a
valuation — already the note's own phrase in L-LINE(ii)) through
L-LINE(iii).

## PC-G5 (off-grid lambda-chain): the case is EMPTY — census + two-line proof

Measured: 0 equal-line off-grid cells anywhere (every cell with
line(C) = beta* was on-grid at beta*; counter C-GRID never fired).
Reason (re-derived): for ANY cell at beta* = line(C), the lambda-chain
values are exactly the sub-cell lines (integral by linearity of the line),
and s_l(lambda_l) == j_{l-1} mod e_{l-1} since lambda_l = e_{l-1}
lambda_{l-1} + j_{l-1} gamma_l, gamma_l == h_{l-1}, and l_{l-1}h_{l-1} == 1
(mod e_{l-1}).  Hence DEV-(m)(D3)'s second case (line(G) = beta*, G
off-grid) and RM-GEN's "off-grid x-cells" branch are VACUOUS: off-grid
occurs only at foreign targets, where the above-line case already governs.
PC-G5's missing partial-chain definition is real as a definitional nit,
but it is only ever consulted on this empty case; the cure is the
first-failure convention plus this vacuity lemma (which also SIMPLIFIES
the note: (D3) case 2 and the L-ZMULT converse-integrality appeal can be
replaced by the two-line argument above).

## CONTENT RE-DERIVATIONS (charge items; all against the note text alone)

* **L-ZMULT / self-curing carries: SOUND.**  Lambda-chains add by
  affine-linearity; L1 gives s_l(lam+lam') = s_l+s_l' - delta_l e_{l-1},
  delta_l in {0,1}; t-leg contributes z_l^{+delta_l}, EXP-KIT(b)'s eps-leg
  z_l^{-delta_l} at every l <= m-1; level m has a t-leg and no eps-leg, so
  exactly z_m^{eps-tilde} survives with eps-tilde = floor((s_m(beta)+
  s_m(beta'))/e_{m-1}).  The top-level no-eps-leg convention matches the
  harness read composition (machine-tied: R4 leg, per-leaf res*zh ==
  harness single-cell read at every sampled leaf, 3 rings).  Measured: 133
  product pairs exact, 6 with internal carries genuinely firing (M3B);
  mutants "top carry dropped" (MU1, 35 trips) and "internal carries
  survive" (MU2, 13 trips) both visible.
* **T-tele(i+1) via psi_i(z_{i+1}) = 0: SOUND.**  Re-derived in full: the
  correction-(k,d) child's chain shifts are exact (t_{i+1} += k - g_i;
  lambda_i += beta_k = (g_i-k)gamma_{i+1} by linearity); B-READ on
  C_k^{(i)} may be taken inside the k-sum (the d-cells are on-line
  on-grid by the realize structure, and res(b-bar) factors since the
  L-child residue is the product); EXP-KIT(b) + eps_i(beta_k)tau_k =
  psi_{i,k} collapse the sum to z^{t_{i+1}-g_i}(psi_i(z_{i+1}) -
  z^{g_i}) = z^{t_{i+1}} with the (ID-(i+1)) minus sign; sign discipline
  checks (promotion/exit +, corrections -).  Machine: end-to-end via the
  R1/R4 triple (leaf zh-sum == R-read == z_m^{eps'}v tau_m) at m = 2/3/4.
* **(C-EPS)** is L1 restated: checked, and machine-checked with eps' in
  {0,1} at every call.
* **(C-W_Q) via the exit-cofactor structural remark: SOUND** — E1-priority
  makes the sub-cell reduced at level m-1, the cofactor a single
  Phi_{m-1}-digit at ANY top exponent, so w_m == line exactly; machine:
  every exit cofactor (capped 200/tower, 471 total) had w_m == line ==
  parent - w_m(Phi_m).
* **L-CAP: PROVED as displayed** (pool_1 <= 3e_0 - 3, inductively
  pool_l <= 3e_{l-1} - 1; trivial e = 1 branch fine); machine max carry
  observed 2 (M3B), bound never exceeded.
* **m = 1 reproduction vs [IL3]:** T-scope(1) = (e0 >= 2 or d0 = 1) =
  (e0 >= 2) union (e0 = 1 and d0 = 1) — exactly the RM-1 scope of record;
  the claim DAG's "DEV-1 NOT consumed / DIGIT-SPLIT IS consumed" split is
  coherent (DIGIT-SPLIT is a distinct engine-free lemma).
* **T-scope honesty: CLEAN.**  All 31 T-scope/T-class sites checked; every
  consumption of termination carries the pin (S4.2, S5.1 statement+proof,
  S5.2, S7.1, S8 rows 4/7/8, S9, S10); S2/S3 legs are honestly scope-free;
  T-class(n) re-derived as the exact union of the per-call pins for
  n >= 3 (PC-G4's n = 1, 2 literal-emptiness slip agreed, minor).
* **LAW-DCX consumed sealed-not-proved: CLEAN.**  All 10 v2/UNIFORM-CARRY
  sites + 13 LAW-DCX sites carry the conjecture/sealed grade; S8 row 10
  rests on "--"; DAG routes it to COND-B only; S6.1's m = 1/m = 2
  specialization audit re-checked exact (u_1 = (gamma_3 -
  s_2(gamma_3)gamma_2)/e_1 = the DCX3 u_0).  On PC-G2 (floor-form row 11
  over-graded): agreed in direction — S6.2's own prose fences what it
  does not derive, but row 11's bare "PROVED, generic" compresses away
  the heuristic half; wording repair.
* **Head pastes:** all three dagger blocks compared against
  BRIDGE_ADJUDICATIONS_2026-07-30.md (lines 6643/7902/8518): content-token
  identical (the [IL3] paste's bracketed S1-notation gloss is declared).
* **W-WIN:** consumed by nothing (C5/C14 verified; my reimpl never needed
  it); my m = 2/3/4 censuses saw 0 over-window cells, bound tight at
  2P_l - 1 (matches the diag).

## EXECUTION LEG 1 — the committed diagnostic, byte-exact

`rmengine_diag.py` (md5 985795090987caa495f99d068026e797 == the note's S9
pin) re-run on this machine: exit 0, 0.66 s; stdout byte-identical to the
committed `rmengine_diag_output.txt` (874557bba69e5726bf884626e4f055f9);
`rmengine_diag_results.json` reproduced identically modulo the volatile
`elapsed` float (committed bytes restored, 7e9177d15a2f04dfe5a1b6dd396a3b18).
All six committed verdict lines reproduced verbatim (D1-D4/D6 GREEN 0, D5
mism=0/896).  Post-reimpl inspection of the runner: law-keyed to the note's
displays as claimed (its D5 pool/carry chain is S6.1 verbatim; its measured
DCX uses the [ILN] S4.7 d-plus clause, equivalent to TRACK at e >= 2; its
digit_split_norm confirms F2's normalization).

## EXECUTION LEG 2 — the from-note reimplementation (written BEFORE opening the diag)

`verification/openmath/rmengine_pe_reimpl.py` (md5
103c1a9c99e2b4a3e8b63c93cbf87e25) + `rmengine_pe_reimpl_output.txt`
(4fd8eeb1f8663b6aa6fb8fdcfe5a2509) + `rmengine_pe_reimpl_results.json`
(d02297a6d4bea64ace6426beb55b6f39); note @ md5
bc4b9cdf964bffcadf12572fca36fc45.  Sealed harness consumed read-only
(grb/strata3/iterlaw4/iterlawn towers, md5s in the JSON provenance block);
everything the note NEWLY displays — cells/lines/tree/DIGIT-SPLIT children,
the lambda/t-chain + zh + L-ZMULT, the L-MU interval family, LAW-DCX-(m+1)
pools — implemented from the note text; the m = 4 layer (realize4 /
build_Phi5, Chat_4 = Phi_5 - Phi_4^2) is a fresh one-level-up mirror.
Deterministic, exact arithmetic, no RNG; exit 0; 2.2 s.

FRESH roster (disjoint from RME3A/B/C and the RM2/DCX3 rosters):
  M2A Zp5 d0=1 (2,1,1)^3 [all-e=2 T-boundary]      M2B Zp3 d0=2
  (3,1,2)(2,1,1)(2,3,1) [g0=2, e0=3, junk-alive]   M2F F2[[t]] d0=1
  (2,1,1)^3 [cross-ring]                            M3A Zp5 d0=1 (2,1,1)^4
  M3B Zp3 d0=2 (2,1,2)(3,2,1)(2,1,1)^2              M4A Zp3 d0=1 (2,1,1)^5
  [the m=4 SMOKE]  + FLAT fence towers M2C (e1=1) and M3C (e2=1), both
  correctly REJECTED by the T-scope predicate (fence fired; theorem legs
  not run there; exploratory censuses only).

ACTUALS (verdict lines, all predicted-0 GREEN):
  R0 harness-eps tie + scope predicate            GREEN [0]
  R1 four box clauses m=2/3/4                     GREEN [0]   (97 engine calls:
     12+16+12 at m=2, 16+16 at m=3, 12 at m=4 — THE FIRST (RM-4) DATA EVER:
     canonical division of f*Chat_4 by Phi_4, (C-W_R)/(C-W_Q)/(C-READ) with
     z_4^{eps'} v tau_4 pinned, (C-EPS), all exact)
  R2 tree==division + strict mu + intervals + IDs GREEN [0]   (97/97 CONS;
     strict descent on ALL in-tree edges, e.g. M3B: 17,772 nodes, 3,973
     promotions, 8,656 corr-L, 5,098 junk children, 0 flat/ascending;
     interval-rule weights e.g. (1,5/4,29/16) m=3, (1,5/4,29/16,181/64) m=4)
  R3 line calculus exact quanta                   GREEN [0]   (promotion ==
     h_{i+1}*prod e; corr-L == 0; junk >= Em / >= Gam_0; exit == -w_mPhi_m;
     leaf w_m == line, incl. every checked exit cofactor)
  R4 zh kernel                                    GREEN [0]   (B-READ(f) == v
     and B-READ(Chat) == tau on every call; leaf zh-sum == R-read ==
     z_m^{eps'} v tau_m; 133 L-ZMULT pairs, 6 internal-carry pairs; equal-line
     off-grid census 0)
  R6 LAW structure (u-chain in Z>=0, L-CAP <= 2)  GREEN [0]
  R5 CENSUS LAW-DCX-(m+1): mismatches = 0 / 2,208 fresh pairs —
     m=2 (LAW-DCX-3 = v2): 272 pairs, 5 live; m=3 (LAW-DCX-4): 896 pairs
     (incl. flat M3C), 37 live; m=4 (LAW-DCX-5, FIRST DATA EVER): 1,024
     pairs, 120 track, 28 live, 28/28 chain-fed (c_3 > 0), 0 mismatches,
     max carry 1, deficits all 0.  Every live row at every m was chain-fed;
     M3B realized max carry 2 and one deficit-1 row.
  R7 mutants 7/7 visible: MU1 top-carry drop 35 / MU2 internal-carry
     survival 13 / MU3 promotion-quantum+1 4,243 / MU4 eps'+1 49 / MU5
     LAW threshold-1 166 / MU6 LAW c_{m-1} drop 70 / MU7 (B_{m-1})-violating
     weights 1,566 non-descending edges.
  Observation: v = 0 never realized (0/97) — see F3.

FLAT fence actuals: M2C predicate fired, probe witness (1, 3/2), 15-node
exploratory tree 0 non-descending edges, LAW census 0 live/0 mism; M3C
predicate fired, witness (1, 5/4, 19/8), 88-node tree with 16 level-3
corrections, 0 non-descending, LAW-DCX-4 3 live 0 mism.  Shape-level
feasibility table (13 shapes) as in F1: every d0 = 1 flat shape feasible,
every probed d0 >= 2 flat shape infeasible.

## CLAIMS-TABLE MACHINE CENSUS

All 14 grep keys located in the committed text; 13/14 line-grep-stable, C2
requires whitespace normalization (n4).  Spot-verification: C1/C4/C5/C6/C7/
C10/C11/C13/C14 accurate against the displayed proofs (C5/C14 additionally
machine-supported: nothing in my reimpl consumes W-WIN; C10 supported
vacuously via F3 — the weight clauses were never fed a v = 0 input because
none exists).  On PC-G3 (missing rows): agreed as charter shortfall; the
three quoted absentee claims are real "only/never" sites.

## PROVENANCE APPENDIX

Verifier: Fable (claude-fable-5), fresh context, note read at bf18bfe;
concurrent Codex leg = RMENGINE_passPC_report.md (read only AFTER my
reimplementation and diag re-run were complete and frozen).
Files + md5:
  rmengine_diag.py            985795090987caa495f99d068026e797  (committed, re-run)
  rmengine_diag_output.txt    874557bba69e5726bf884626e4f055f9  (byte-exact rerun)
  rmengine_diag_results.json  7e9177d15a2f04dfe5a1b6dd396a3b18  (== committed;
                              rerun differed only in the volatile `elapsed`)
  rmengine_pe_reimpl.py       103c1a9c99e2b4a3e8b63c93cbf87e25  (NEW, this pass)
  rmengine_pe_reimpl_output.txt  4fd8eeb1f8663b6aa6fb8fdcfe5a2509  (exit 0)
  rmengine_pe_reimpl_results.json d02297a6d4bea64ace6426beb55b6f39
  note RMENGINE_2026-08-08.md bc4b9cdf964bffcadf12572fca36fc45
  harness (read-only): grb dab62713... strata3 40ecf8c0... iterlaw4
  80b4c265... iterlawn cd7581b7...
Output tails eyeballed: diag rerun ends "D6 VERDICT ... GREEN [0
violations]" + "ALL LEGS GREEN"-equivalent six-line block == committed;
reimpl output ends "R7 VERDICT ... GREEN {...}" / "TOTAL: ALL GREEN;
census notes: 0; elapsed 2.2s".

## DISPOSITION HANDED TO THE ORCHESTRATOR

The repair unit (already owed per PC) should fold: (1) the F1 erratum —
re-scope the S4.2 fence to d0 >= 2, correct the mechanism display (rho =
P - 1, the W symbol), delete or re-scope the "any linear mu" sentence, and
either extend T-TERM to the d0 = 1 flat corners (the note's own arithmetic
does it) or display them as coverable-pending-DEV-(m)-rerun; L-LEX may be
retired or kept as a remark; (2) PC-C1 as a TEXT insertion (the
normalization step), grade unchanged; (3) the PC-G5 cure via the vacuity
lemma (which SIMPLIFIES (D3) and RM-GEN); (4) the smaller displays (F3
remark, row 11 wording, table rows, C2 wrap, S7.1 qualifier, n6 cleanup).
Nothing in this pass moves LAW-DCX-(m+1)'s conjecture grade; the fresh
2,208-pair census (first m = 4 data) is instance evidence only.

— RMENGINE-PE, Fable round-1 hostile pass, wallclock 2026-08-04.
