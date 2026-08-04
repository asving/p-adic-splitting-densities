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

## D3. RESULTS

PENDING — this section is written at commit 2, from the artifacts of
the single deterministic run, after the seal commit.  Nothing below
this line exists at seal time.

## Files

* runner: `verification/openmath/survk2_instrument.py`
* output: `verification/openmath/survk2_instrument_output.txt` (commit 2)
* results: `verification/openmath/survk2_instrument_results.json`
  (written incrementally during the run; `final: true` on the sealed
  copy; commit 2)
