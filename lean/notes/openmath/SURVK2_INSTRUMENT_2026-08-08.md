# (SURV-K2) INSTRUMENT — the pairing-structure census: measuring the sign-reversing pairing behind the signed-multiplicity-one law at g0 >= 2

Unit: the (SURV-K2) INSTRUMENT of the W-MULT-DCX arc (2026-08-08
campaign, wallclock 2026-08-04).  Target: the (SURV-K2) box of
`SURVDISJ_PROOF_2026-08-08.md` S6 (at 553895d) —

    (SURV-K2):  on TRACK, (H1)-(H3), g0 >= 2, c_{m-1} >= k: some slot
    group AT THE BOTTOM LINE beta_min carries a PROTECTED residue-class
    vector (SD-L7 sense: one class of signed count +-1, or a +1/-1 pair
    of distinct classes).

The proved reduction on record (SD-L6/SD-L7): protected => survives,
characteristic-free — so the EXISTENCE half alone closes (SURV-DISJ)'s
bottom leg at g0 >= 2.  The proof target the box displays: a
SIGN-REVERSING PAIRING on the bottom-line path family — pair
correction-riders by a local toggle (correction <-> t-seed shift, the
two routes to the same slot mass), residue-preserving and
sign-flipping, leaving exactly one unpaired path (or one +1/-1 pair of
distinct classes).  The instrument constraint census the box carries:
survivor vectors {(+1)x85, (-1)x115, (-1,0)x5, (0,+1)x4, (-1,+1)x2} on
all 200 kill rows; CROSS confinement (cross-class field relations kill
only OFF-bottom, 9/9); M-B1 = 39 killed groups with ODD count (parity
is NOT the mechanism); P-C refuted (kills reach beta_min on 103/200
kill rows).  THIS unit MEASURES the pairing structure itself.

## D0. Consumption and design derivations (input, not proof steps)

Committed engines read-only, md5-pinned (the survdisj_instrument PINS
plus survdisj_instrument.py itself, 3df33c7406913510ed7ebaa60d480b57,
whose union-roster selection loops are replicated verbatim).  Design
derivations displayed here as DESIGN INPUT (they shape the candidate
relations; the battery tests them; nothing here is a proof step):

* W-D2(iv) (WMULTDCX†, attempt grade): at g0 >= 2 under (H3) every
  d-cell seed D_t has j0(D_t) = s1(u1) + t*e0, 0 <= t < g0, all higher
  exponents principal, and w0(b_{D_t}) = u0 - t*h0.  So the seed
  t-parameter is read off any cell as t = (j0(D) - s1(u1))/e0.
* [RMG] S2.2 / the corr_table construction (ACCEPTED): the level-0
  correction children are C_k = lift(psi0_k) * pi^{(g0-k)h0} for the
  k < g0 with psi0_k != 0 — consumption P0 - e0*k = e0*(g0-k) at level
  0, NO dump vector, w0(C_k) = (g0-k)*h0 exactly.  Interior levels
  (g_i = 1 pinned) have k = 0 only, consumption e_i, dump vector avec.
* THE TOGGLE ARITHMETIC (LED_0 = W-D3 at level 0, pi_0 = 0): two
  terminal cells at the SAME slot whose correction multisets differ by
  exactly one level-0 edge (0, k) must have seed parameters differing
  by t_rider - t_other = g0 - k (the rider = the side WITH the edge),
  and then their w0 agree automatically (w0(C_k) = (g0-k)*h0 cancels
  the seed shift (u0 - t*h0) exactly).  Residues agree iff
  res(C_k) * res(c_{D_{t+g0-k}}) = res(c_{D_t}) in K0 — a SEED-LEVEL
  identity between the correction digits and the d-cell coefficients
  (Q-A0 below measures its truth table directly).
* Sign bookkeeping: sgn = (-1)^{#correction edges} identically (walk
  construction; checked cellwise as SK2-SGN).  Hence any opposite-sign
  same-class pair has correction counts of opposite parity, and a
  single-edge toggle always flips sign.

## D1. Design (sealed BEFORE the battery)

Runner `verification/openmath/survk2_instrument.py`.  Deterministic,
exact arithmetic, no sampling; results written incrementally after
every tower (salvage safety).  Engineering disclosure: one smoke run
(tower XM3B alone, direct driver call, no artifacts written) preceded
the seal for crash/cost validation; only its row count (16), elapsed
(0.2 s) and violation count (0) were read — no candidate verdict, law
table, census or record was inspected.  Rows: the union-roster selection of the
committed (SURV-DISJ) instrument replicated verbatim (sealed loop + EQ
caps 12/6 + PX + SD), RESTRICTED to g0 >= 2 towers (the committed 286
live g0 >= 2 rows), PLUS the NEW adversarial K2 roster: twelve towers
at g0 in {2,3,4} — the FIRST g0 >= 3 probes in any battery — deep m
(two m = 4), both residue characteristics (2, 3, 5), d0 = 2, deep
pools, threshold and above strata; caps 12/6.  Engine-unsupported
shapes and tree-cap overflows disclosed-skipped (a tree-cap event is a
disclosed skip, NOT a violation).

Per g0 >= 2 live row: both walk stages replicated; every terminal cell
gets (sgn, slot j, line, w0, K-residue, seed t, correction-edge list
ce, junk, y2).  Bottom-line groups = per-slot cell sets at line ==
beta_min; the MINIMAL group := the bottom-line group of the surviving
netted slot at beta_min with lexicographically least slot (bottom
death at g0 >= 2 would be a SK2-BOT event, see PRED-2).  Residue
classes by keq within each group; signed count per class.

**Pair-relation taxonomy** (for every same-class OPPOSITE-SIGN cell
pair inside a bottom-line group; rider := the side with more
correction edges):
    T0  correction multisets differ by EXACTLY one level-0 edge
        (0, k, no dump, no Y), and t_rider - t_other == g0 - k
        (the derived quantum);
    TG  differ by exactly one level-0 edge but the quantum FAILS
        (wrong seed shift, or dump/Y anomaly) — measured separately;
    TI  differ by exactly one INTERIOR edge (i >= 1); descriptor
        (i, avec, delta-t, delta-pc) censused — no quantum imposed;
    TM  anything else (multi-edge difference).
A pure seed shift with EQUAL correction multisets cannot be an
opposite-sign pair (sign parity) — excluded by arithmetic, so the
charge's "t -> t' involution" candidate lives inside T0/TI (the
seed shift rides WITH the correction toggle).

**Candidate measurements** (law-keyed: g0-value g2/g3/g4+ |
residue-char rc2/rcODD | thresh/above/direct stratum):

* **Q-A0** [the seed-level residue law, per tower]: the full truth
  table of  res(C_k) * res(c_{D_t'}) == res(c_{D_t})  over all defined
  triples (t, t', k) with t' - t = g0 - k.  All-true on a tower =>
  every T0 toggle there is residue-preserving for free.
* **Q-A** [the pairing]: per group and residue class, maximum
  bipartite matching of positive against negative cells using ONLY
  T0 u TI pairs; verdict per row (minimal group: QA-match) and per
  group (QA-match-all): matching is PERFECT (size = min(npos, nneg)).
  Teeth: M-QA-TX counts opposite-sign same-class pairs that are NOT
  single-toggle (TM > 0 somewhere => the relation genuinely
  restricts); M-QA-WRONGQ replaces the T0 quantum by g0 - k + 1 and
  must strictly shrink some matching (the quantum bites).
* **Q-B** [the remainder law]: for every class with signed count +-1
  (perfect-matching classes only): the set of majority-side cells
  that SOME maximum T0uTI matching leaves unpaired (cell x removable
  iff matching without x still saturates the minority side).
  CANONICAL remainder := that set is a singleton.  Classify the
  remainder's seed: t == 0 (principal side) vs t == class max vs
  t == g0 - 1 vs interior; and its (ncorr, junk, corr-free) profile.
  QB-canon / QB-rem-t0 / QB-rem-tmax / QB-rem-interior counters.
  Mutation M-QB-T1 ("remainder always at t == 1") must fail somewhere.
* **Q-C** [closed form]: per minimal group, the per-seed signed counts
  S_t := sum of sgn over cells with seed t, the vector (S_0..S_{g0-1}),
  the total S := sum S_t, and the per-class signed vector.  Candidate
  laws tested: QC-seedbound (|S_t| <= 1 for every t); QC-cf (S ==
  signed count of the correction-free junk-free cells alone — riders
  cancel in toto).  No preregistered direction on either; their
  law-keyed failure patterns are the product, and the (S_t) census is
  the input to any Catalan/binomial fit (post-hoc, labeled as such).
  Teeth: M-QC-2 counts bottom classes with |signed| >= 2 (the bound
  predicates are non-vacuous only if it fires).
* **Q-D** [taxonomy strata]: per row, the minimal group's residue-class
  signed-count vector (classes in first-occurrence walk order — the
  committed P-M1 convention) as a pattern string, keyed against the
  pool-arithmetic frame (g0, e0, h0, d0, kdef, ctop, stratum,
  #d-cells, principal present, t and presence of the group's
  correction-free cell, kill-on-row).  Verdict = the contingency
  census; the box's five patterns should reappear on kill rows and
  every NEW pattern is a loud event.  Teeth: M-QD-DIV requires >= 2
  distinct patterns observed.

**Verdict families** (predicted 0): SK2-PIN (8 md5 pins), SK2-CONS
(stage sums = E1IH / Q1), SK2-SEED (the W-D2(iv) t-decomposition:
integrality, 0 <= t < g0, w0(c_D) = u0 - t*h0 via the d-cell table),
SK2-W0K (w0(C_k) = (g0-k)*h0), SK2-SGN (sgn = (-1)^{#ce} cellwise),
SK2-EQV (same slot+line => same w0), SK2-MULT1 (some bottom-line group
carries a +-1 class — PB-mult1-some re-measured; a violation IS a
(SURV-K2)-form counterexample), SK2-BOT (netted bottom survives at
g0 >= 2), HARNESS.

## D2. Preregistered predictions and falsifiers (sealed)

* **PRED-1**: 0 violations in SK2-PIN / SK2-CONS / SK2-SEED / SK2-W0K /
  SK2-SGN / SK2-EQV / HARNESS.  Falsifier: any — engine-or-lemma
  instance breach (SK2-SEED breach = W-D2(iv) instance failure).
* **PRED-2**: 0 violations in SK2-MULT1 and SK2-BOT, INCLUDING the
  fresh g0 in {3,4} rows — the first test of the box's law beyond
  g0 = 2.  Falsifier: a g0 >= 2 live row with no +-1 bottom class
  (kills the box's protected-vector form as stated), or a bottom-dead
  g0 >= 2 row (reshapes (SURV-DISJ)'s g0 >= 2 leg entirely).
* **PRED-3 (Q-A)**: QA-match fail = 0 on minimal groups — every
  minimal-group class pairs off completely under T0 u TI; and the
  teeth fire (M-QA-TX > 0 across the roster, M-QA-WRONGQ > 0).
  Falsifier: a class needing a TM pair (the pairing is NOT local
  single-toggle — the box's proof target needs a different mechanism);
  toothless controls (disclose, downgrade the count's evidential value).
* **PRED-4 (Q-A0)**: NO preregistered direction — the truth table is
  the product.  All-true would make T0 residue-preservation a
  seed-level identity (the pairing proof reduces to the seed digits);
  a mixed table keys WHERE pairing can kill.
* **PRED-5 (Q-B)**: NO direction between t = 0 / t = max — measuring
  WHICH extreme is the charge.  Falsifiers of the extremal law: a
  canonical remainder at interior t (with g0 >= 3 now probed, interior
  t exists for the first time — the g0 = 2 record could never see
  this); a non-canonical remainder (>= 2 removable cells) is itself a
  datum (the pairing is not forced, only the count is).
* **PRED-6 (Q-C)**: QC-seedbound expected to hold (|S_t| <= 1 — the
  per-seed signed-multiplicity-one refinement); QC-cf carries NO
  direction (its failure pattern is the (-1)-survivor mechanism).
  Falsifier for seedbound: any |S_t| >= 2 — then the pairing is not
  seed-local and the census records the offending profile.
* **PRED-7 (Q-D)**: on kill rows the pattern census stays inside the
  committed five vectors {(+1), (-1), (-1,0), (0,+1), (-1,+1)}; NEW
  patterns (if any) appear only at g0 >= 3 / off-kill and are loud.
  Falsifier: a kill-row pattern outside the five — the box's
  constraint census is incomplete.

    [AMENDMENT rev 2, 2026-08-08 campaign (wallclock 2026-08-04), AFTER
    the seal 10ec9f3 and BEFORE any verdict was read.  The sealed run's
    union phase replicated the committed selection EXACTLY (286/286
    g0 >= 2 live rows, tower-by-tower counts matching) in 22 s; PHASE
    K2's first tower (K2G3AF, Fpt g0 = 3) then exceeded 45 MINUTES
    inside ENGINE PREP (the w_m(Chat) Phi-adic development;
    stack-pinned in strata3_probe.w3 -> dev -> pdivmod) without
    completing.  Throwaway engineering probes (/tmp copies, no
    artifacts): Fpt g0=3 m=3 prep > 250 s; Zp g0=3 m=3 prep > 240 s;
    even m=2 g0=3 prep > 240 s; while g0=2 shapes at the SAME level-0
    polygon width P0 = 6 (e.g. reads (3,2,2)) prep in under a second —
    the wall is the g0 >= 3 residual-degree K-tower arithmetic in the
    committed engines (read-only, not repairable here), not polygon
    size.  Amendment, runner rev 2 (md5 389b1db9fc0266a12db74e021d7d51c9):
    (i) per-row ATOMIC buffering — global records/counters commit only
    at the end of a fully traced row; (ii) a 300 s per-tower wall-clock
    budget in PHASE K2, timeout = disclosed skip (counter
    tower_budget_timeout), so every sealed K2 tower still gets a
    bounded attempt in the deterministic run.  ROSTER AND ALL D2
    PREDICTIONS UNCHANGED.  Consequence declared up front: the g0 >= 3
    towers are expected to time out, in which case the g0 in {3,4}
    clause of PRED-2 is UNTESTED — a disclosed COVERAGE FAILURE, kept
    on record, not repaired away — and g0 >= 3 remains machine-dark
    program-wide, now with a measured reason (the engine cost wall).
    The wall-clock budget makes the K2 row set timing-dependent in
    principle; every row actually traced is listed in the artifacts
    and all verdicts are law-keyed over those rows.]

## D3. RESULTS (commit 2; verdict from the artifacts — single
deterministic rev-2 run, 3022.5 s wall (2748 s of it the ten g0 >= 3
budget timeouts), **332 live g0 >= 2 rows** = 286 union (replication
EXACT, tower-by-tower counts matching the committed instrument) + 46
fresh K2 (K2G2P5B 39, K2W4G2Z 7); **0 violations in all nine verdict
families**; 102 bottom-kill rows = the 97 committed + 5 fresh)

**PRED-1 CONFIRMED.**  SK2-PIN (8 md5 pins) / SK2-CONS / SK2-SEED /
SK2-W0K / SK2-SGN / SK2-EQV / HARNESS all 0.  In particular SK2-SEED:
every terminal cell on all 332 rows decomposes per W-D2(iv)
(j0(D) = s1(u1) + t*e0, w0(c_D) = u0 - t*h0) and SK2-W0K:
w0(C_k) = (g0-k)*h0 on every level-0 correction digit — the two
w0-legs of the toggle arithmetic hold cellwise.

**PRED-2 CONFIRMED WHERE TESTED; g0 >= 3 UNTESTED (disclosed).**
SK2-MULT1 332/332 (every g0 >= 2 live row has a bottom-line group
with a +-1 class — the box's law, now including 46 fresh rows with
fresh kills); SK2-BOT 0 (the netted bottom survived every row).  The
g0 in {3,4} clause is UNTESTED: all ten g0 >= 3 towers hit the 300 s
budget inside ENGINE PREP (surfaced via the setup except-path as
"ENGINE UNSUPPORTED (TimeoutError)" — same disclosed-skip semantics,
counter tower_skipped = 10; the amendment bracket above carries the
measured cost-wall evidence).  g0 >= 3 remains machine-dark
program-wide; the first-probe attempt is on record.

**PRED-3 (Q-A) PRODUCTIVELY FALSIFIED — the single-toggle T0 u TI
matching is NOT the whole pairing; the measured completion is
displayed below.**  QA-match on minimal groups: 323/332 ok, 9 fail
(ALL rc2, the SDG2BF/SDG2BZ single-seed towers); QA-match-all over
all 531 bottom groups: 487 ok / 44 fail (36 rc2 direct + 4 rc2 above
+ 4 rcODD direct = the fresh K2G2P5B).  Pair-relation census over
all same-class opposite-sign bottom pairs: **T0 = 76, TM = 58,
TI = 0, TG = 0** — no interior single-edge toggle and no
wrong-quantum level-0 single edge EVER appears; every non-T0 pair is
a MULTI-edge exchange, and their anatomy (read from the group
records) is exactly two further realizations of the same level-0
mass exchange (see the headline below).  Teeth: M-QA-WRONGQ 76
(every T0-carried matching strictly shrinks under the quantum+1
mutation — the g0 - k quantum is load-bearing in all 76 pairs);
TM > 0 (the T0 predicate genuinely restricts).

**PRED-4 (Q-A0) — the seed-level residue table, the pairing's
residue input, MIXED as measured: 5 towers TRUE, 4 FALSE, 7 empty
(single-seed).**  res(C_k)*res(cD_{t+g0-k}) == res(cD_t) holds on
{W3G2A, W3G2B, W3G2P5, XM3B, EQ3G2B} and FAILS on {EQ3G2A, SDG2AF,
SDG2AZ, K2W4G2Z}.  The law-keyed correlation: ALL 67 seed-shift
(cross-t) 2-cell bottom kills live on A0-TRUE towers (EQ3G2B 37,
W3G2A 15, W3G2B 10, XM3B 4, W3G2P5 1) — where the identity holds,
the T0 toggle is residue-preserving and kills; the three A0-FALSE
d0 = 2 towers have ZERO bottom kills; the fourth A0-FALSE tower
(K2W4G2Z, d0 = 1, m = 4, fresh) produced the single loud NEW event
below via a DIFFERENT (ratio-law) identity.

**PRED-5 (Q-B) — canonical remainder CONFIRMED; the extremal-t
question stays open.**  QB-canon 435/435: every +-1 class with a
perfect T0 u TI matching has a UNIQUE removable cell.  Every one of
the 435 is SINGLE-SEED (all its cells share one t) — +-1 survivor
classes never mix seeds; the cross-seed T0 pairs live only in KILLED
classes.  Minimal-group remainder census (ncorr, sign, t):
correction-free (+1) 183 (t=0 x122, t=1 x61); 1-corr (-1) 89 (t=1
x78, t=0 x11); 2-corr (+1) 47; 3-corr (-1) 5 — the remainder is a
RIDER (not the correction-free path) on 141 of the 324
minimal-group remainder records, and
its sign is exactly its correction parity.  t = 0 vs t = 1 both
common and tower-keyed; at g0 = 2 both seeds are extremal, and the
g0 >= 3 interior-t probe timed out — the t0-vs-tmax law is
UNDECIDED, disclosed.  M-QB-T1-fail 203 (teeth).

**PRED-6 (Q-C) — the per-seed bound CONFIRMED; the single-seed
survivor law measured; ONE |signed| >= 2 bottom class exists (in a
killed group).**  QC-seedbound 332/332: every per-seed signed count
S_t of the minimal group lies in {-1, 0, +1}.  Sharper, measured:
the stvec (S_0, S_1) census is (1,0) x164, (0,1) x73, (0,-1) x74,
(-1,0) x20, (1,-1) x1 — EXACTLY ONE nonzero seed entry on 331/332
rows (the minimal survivor nets to one seed's one class at +-1); the
single (1,-1) exception is the two-class (-1,+1) protected survivor
on the CROSS-kill row below (both entries still +-1).  QC-cf (total
= correction-free signed count) 184 ok / 148 fail — the failure set
is EXACTLY the n_cf = 0 rows (minimal group carries no
correction-free path; the survivor is a rider class), matching the
pattern table below.  M-QC-2 fired 1: the (+2) class inside the
killed CROSS group below — the only class beyond +-1 ever seen at a
bottom line (332 rows; and it sits in a KILLED group, not a
survivor).

**PRED-7 (Q-D) CONFIRMED — no new survivor pattern; the strata key
found.**  Kill-row minimal-survivor patterns: (+1) x44, (-1) x48,
(0,-1) x5, (0,+1) x4, (-1,+1) x1 — all inside the committed five
vectors (class-order convention: this unit's (0,-1) = the committed
(-1,0) content), with (-1,+1) now realized at-kill on the fresh
roster.  Pattern x pool-arithmetic separation (all 332 rows):
pattern (+1) with n_cf = 1 x183 (the correction-free path's class
survives; t_cf in {0 x122, 1 x61}); (+1) with n_cf = 0 x50 (2-corr
rider remainder); (-1)/(0,-1)/(0,+1)/(-1,+1) x99 all have n_cf = 0
(NO correction-free path in the minimal group — the survivor is a
rider class, sign = its parity).  So the taxonomy is keyed by
(n_cf, remainder correction parity) — a pool/path-count function,
no residue arithmetic.

**THE PAIRING STRUCTURE (the headline, measured).**  Every observed
same-slot bottom-line cancellation and every +-1 remainder is
generated by ONE mechanism — **level-0 mass exchange at fixed slot**:
two paths pair iff their level-0 books (seed t*e0 + dumps - level-0
correction consumptions) balance, i.e. their correction multisets
and seeds differ by an exchange of total level-0 mass
Sigma e0*(g0-k) against a seed shift (or a dump-cell swap); the sign
flips iff the correction-count parity differs, w0 matches
automatically (SK2-W0K + W-D2(iv) — the two sides of
(g0-k)h0 = h0-per-e0-unit), and residue preservation is a
DIGIT-LEVEL identity specific to the realization.  Three
realizations carried ALL 102 bottom kills:
  (i)  T0 seed-shift toggle: remove C_k, shift t -> t - (g0-k);
       residue law = the Q-A0 identity; carried the 67 cross-t pair
       kills, all on A0-TRUE towers (display witness: EQ3G2B
       [1479,1485] slot (5,0,0) — rider (+, t=1, ce {(0,k=1),
       (1,0,dump(1,))}) vs (-, t=0, ce {(1,0,dump(1,))}); dt = 1 =
       g0 - k; same w0 54; equal residue; killed).
  (ii) dump-swap at fixed seed: interior-correction dump cell
       a_0 -> a_0 + e0(g0-k) against C_k; carried the 30 same-t
       char-2 pair kills (SDG2BF/SDG2BZ/SDW3G2F; witness SDG2BF
       [1479,1485]: dump (4,) + C_1 vs dump (1,), e0(g0-k) = 3).
  (iii) correction-multiset exchange at fixed seed: C_1 + C_1 <->
       C_0 (mass 2*e0(g0-1) = e0*g0 at g0 = 2); carried the 4 FRESH
       p = 5 same-t pair kills (K2G2P5B) — the first same-t kills at
       ODD characteristic: realization (ii)/(iii) is CHAR-BLIND, not
       a char-2 artifact.
And the row-level remainder law: after the exchanges cancel, the
minimal group nets to ONE seed x ONE residue class x signed count
+-1 (the stvec law), canonically (QB-canon 435/435).  This is the
measured shape of the box's conjectured sign-reversing pairing: the
involution is level-0-mass exchange, the "+-1 remainder" is the
single unpaired path (or the protected (-1,+1) pair of single-seed
classes), and the only residue input is the per-realization digit
identity — never the full carry algebra.

**LOUD NEW EVENT (constraint census update for the S6 box).**  The
fresh tower K2W4G2Z (m = 4, Zp p = 3, g0 = 2, d0 = 1 — an A0-FALSE
shape) produced, at row [2635,2635] slot (4,0,0,0), the FIRST
bottom-line killed group of ODD size and the FIRST bottom-line
CROSS-type kill: n = 3, cells (-, t=1, 3-corr, res 2), (+, t=1,
2-corr, res 1), (+, t=0, 2-corr, res 1); classes signed (-1, +2);
net -2 + 2*1 = 0 in F_3 — cancellation ACROSS distinct classes,
signed counts not all 0 and not all == 0 mod p.  The (+2) class is
the M-QC-2 event: its two same-sign cells sit at DIFFERENT seeds
with equal residue via the k-exchange transport C_0 at t+1 <-> C_1
at t, whose residue law is the RATIO identity
res(C_0)*res(cD_{t+1}) = res(C_1)*res(cD_t) (which holds here even
though the Q-A0 identity fails on this tower).  Consequences, stated
honestly: (a) the committed CROSS confinement ("cross-class field
relations kill only OFF-bottom, 979/979") is now instance-BROKEN at
the bottom line — 1 bottom CROSS kill in 332 g0 >= 2 rows; the
(SURV-K2) box's weaker-form fence "no cross relation at beta_min"
can no longer be cited as exceptionless and must be restated scoped
(no cross relation at the SURVIVOR's class set — which held: the
row's minimal survivor was the protected (-1,+1) two-class group,
qa-perfect, and the row passed SK2-MULT1 and SK2-BOT); (b) bottom
kills are NOT always pair kills (M-B1-at-bottom now fires: one odd
killed group); (c) the boxed LAW ITSELF is untouched — protected
bottom classes existed on all 332 rows.

**Disclosures.**  (i) The ten g0 >= 3 towers: budget timeouts inside
setup/prep, reported through the ENGINE UNSUPPORTED message path
with TimeoutError displayed (same disclosed-skip semantics; wording
quirk of the rev-2 alarm meeting setup's broad except — no
functional difference).  (ii) Wall-clock budget makes the K2 phase
row set timing-dependent in principle; the rows actually traced are
fully listed in the artifacts and every verdict is law-keyed over
those rows.  (iii) Coverage: g0 = 2 only in the traced set; m in
{3,4}; d0 = 2 probed only at g0 = 2 on the A0-FALSE shape; interior
g >= 2 never probed (program-wide).  (iv) TI = 0 and TG = 0 are
measured absences on this roster, not impossibilities.  (v) All
counts are measured instance evidence, never proof steps; the
committed P-M1/CROSS censuses are quoted as constraints and the
update in the LOUD EVENT paragraph is instance evidence against ONE
of the box's secondary constraint displays, not against its law.

## Files

* runner: `verification/openmath/survk2_instrument.py`
  (rev 2, md5 389b1db9fc0266a12db74e021d7d51c9; seal 10ec9f3,
  amendment dbe0cb9)
* output: `verification/openmath/survk2_instrument_output.txt`
  (md5 0db6f784cf37e747057cc45b9a3f3acb)
* results: `verification/openmath/survk2_instrument_results.json`
  (md5 1ac516df8292ac5d57a88e430de3d1e4; written incrementally during
  the run; `final: true`)
