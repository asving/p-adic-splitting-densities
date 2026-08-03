#!/usr/bin/env python3
"""(ADM-REAL') attempt falsifier — the composed track-A argument's checkable claims.

UNIT: the (ADM-REAL') attempt (G-ADM-2 routing, lean/notes/openmath/GADM2_2026-08-08.md:
track A live as (ADM-REAL'); charter ADM_U7_TRACKA_ATTEMPT.md + HDISCHARGE_H3.md 1.3(c)).
Artifact under test: lean/notes/openmath/ADMREAL_2026-08-08.md (the composed argument:
W-CAP -> STEP -> NON-END -> LOC, boundary hypothesis (B-PIN) displayed).

ROLE: falsifier, never proof (finding 7 discipline).  R2 under beta_end >= 0 and R4
are THEOREM-GRADE falsifiers: a hit refutes Lemma STEP / Theorem NON-END themselves
(exit 2, stop-the-line), not just the note's transcription.

================================================================================
PREREGISTERED PREDICTIONS (sealed in this header BEFORE the first execution of
this file; derivations = the note's own proofs, written first).

  R1 (W-CAP, the exact identity): on the full abstract type grid
      r in {1,2,3}, e_i in {1,2,3}, h_i in {1..4} with gcd(h_i,e_i)=1,
      f_i in {1,2}, f0 in {1,2} (12,348 types), the brute-force max ledger
      weight equals V^ - w(phi_1) - sum_{i=2..r} E_i h_i, is attained at the
      top index (f0-1, e_i f_i - 1), and satisfies
      Wmax <= V^ - w(phi_1) <= V^ - 1.  Prediction: 0 failures on all three.
  R2 (STEP + NON-END, abstract data, seeded rng, 20,000 data):
      (a) within each face, consecutive on-line slots drop by EXACTLY
          e_S*V^ + h_S;  prediction: 0 failures.
      (b) beta strictly decreases along the ordered on-line slot list
          (multi-face concatenation included);  prediction: 0 failures.
      (c) THEOREM-GRADE: on every datum with beta_{k_s} >= 0, every on-line
          slot k != k_s has beta_k >= V^ + 1 AND beta_k > classmax(beta_k)
          (max ledger weight in beta_k's residue class mod e; vacuous if the
          class is empty).  Prediction: 0 failures.  A hit refutes NON-END.
      (d) every clearance failure at k != k_s in the beta_{k_s} < 0 pool has
          beta_{k_s} <= -2 (derived pre-run: failure at any non-end slot
          forces the k_s-adjacent slot's beta <= Wmax, so beta_{k_s} <=
          Wmax - (e_s V^ + h_s) <= (V^-1) - (V^+1) = -2).  Prediction: 0
          failures of the bound.
      (e) the beta_{k_s} < 0 pool DOES contain clearance failures (the
          hypothesis beta_{k_s} >= 0 is load-bearing, not decorative).
          Prediction: >= 1 such row.
  R3 ((CLASS-d) control, same grid as R1):
      (a) r = 1: every residue class mod e has exactly d ledger indices;
          prediction: 0 failures (O-9's proved r <= 1 instance).
      (b) r = 2: class-count failures EXIST on the coprime-only grid
          (F-ADM-2 reconfirmed: (CLASS-d) at r >= 2 is genuinely (GR-B)'s,
          hence a DISPLAYED hypothesis of the FULL conversion, never free).
          Prediction: > 0 failures.
  R4 (realized re-adjudication, decorrelated leg): re-read the sealed
      G-ADM-2 battery verification/logs/gadm2_attainment_20260802T232440Z.jsonl
      (198 rows) WITHOUT the harness: recompute full/partial from (n_att, q),
      check stored flags agree, then:
      (a) THEOREM-GRADE: zero partial rows off the right end (slot != mu);
      (b) every non-right-end row is FULL;
      (c) tallies = the sealed disposition: rows 198, full 113,
          partial@end 85, off-end 0, empty 0;
      (d) every right-end row has n_att = 1 (the rho-pin shape (FRESH)(c)).
      Prediction: all four hold.
  R5 (the k_s carve-out is NECESSARY): subprocess re-run of the machine
      falsifier lean/LeanUrat/Scaffold/HDischarge/H3/adm_u7_check.py ->
      exit 0 + "ALL ASSERTIONS PASS" (instances A/B/C: realized reads with
      beta_{k_s} < classmax at k_s — (ADM-REAL) as displayed stays refuted,
      so (ADM-REAL')'s right-end exclusion cannot be dropped).
      Prediction: pass.
================================================================================

Exit codes: 0 = all predictions hold; 2 = THEOREM-GRADE hit (R2c under
beta_end >= 0, or R4a off-end partial); 1 = any other drift.
Run:  python3 admreal_check.py        (~1-2 min, pure python, no deps)

================================================================================
POST-RUN ADDENDUM (2026-08-08 unit clock; run 1 verdict preserved verbatim in
the note's section 7 — R1/R2/R4/R5/R3(a) PASS, R3(b) FAIL, exit 1).

The sealed R3(b) prediction FAILED: the r = 2 grid has ZERO class-count
failures under THIS file's weights.  Diagnosis (the unit's central finding,
note sections 5-6): this file computes the O-9 section-4 ledger weights
w(phi_i) = E_i*(e_i*V_i + h_i)  (E_i = e_{i+1}...e_r; w = v_{r+1}, iterated
(P1)), while F-ADM-2's scan — the source of the sealed prediction —
transcribed the CARRIER's coded weights wphi_i = e_i*V_i + h_i (no E_i
rescale; CensusCore.lean `wphi`).  The two agree at r <= 1 (E_1 = 1) and
diverge at every r >= 2 type with a ramified stage above i.  O-9 section 4
pins the TOP convention (wt(j) := w(B_j), w a valuation of (P1)-scope; TRI's
proof rescales sub-radix weights by e_r).  Under the top convention
(CLASS-d) is a LATTICE THEOREM at every order — Lemma CLASS-LAT in the note,
proved by induction BEFORE leg R3'' below was run.  F-ADM-2's finding
survives as a statement about the coded carrier lattice (= finding F-ADM-3:
carrier weight variance; design input for the carrier re-key, sign-off
gated).

  ADDENDUM LEGS (predictions sealed before their first run):
  R3'  (diagnosis reproduction): under the CARRIER's coded weights
       (wphi_i = e_i V_i + h_i), the r = 2 grid DOES have class-count
       failures, and F-ADM-2's quoted smallest type (e1,h1,e2,h2,f*) =
       (2,1,2,1,all 1) reproduces weights {0,1,5,6} mod 4 with an empty
       class; the SAME type under top weights gives {0,2,5,7} mod 4 =
       uniform.  Prediction: both hold.
  R3'' (CLASS-LAT at r = 3): the full r = 3 grid (11,664 types) under top
       weights has ZERO class-count failures.  Prediction: 0 (per the
       CLASS-LAT induction, written first).

  ADDENDUM exit contract (supersedes the sealed one, transparently): exit 0
  iff R1, R2, R3(a), R4, R5, R3', R3'' ALL pass — the sealed R3(b)
  prediction is RETIRED AS REFUTED (its failure is the finding); it is
  still printed, marked SEALED-PREDICTION-REFUTED.  Exit 2 unchanged
  (theorem-grade).
================================================================================
REVISION 1 ADDENDUM (2026-08-03 real clock; pass-1 report
lean/notes/openmath/ADMREAL_pass1_report.md, verdict CRITICAL 1C/9G; this
block sealed BEFORE the revised file's first execution — the pre-run
immutable artifact is the preregistration commit that carries exactly this
file, referenced from the note's REVISION 1 block).

CONTRACT REPAIRS (pass-1 gaps 6-9):
  R2(a) — shared-vertex coverage fix (gap 6): slots now carry face-membership
      SETS (a shared vertex belongs to both adjacent faces); EVERY consecutive
      pair is checked against the (unique) shared face's exact step law
      b1 - b2 == e_F*V^ + h_F; a coverage counter asserts checked pairs ==
      len(slots) - 1 on every datum.  Prediction: 0 step-law failures,
      0 coverage misses, 0 non-singleton shared sets (20,000 data).
  R2(d)/(e) — failure predicate corrected (gap 7): clearance is
      b > classmax, so failure is b <= classmax (equality failures were
      omitted by the old `b < cm`).  The pre-run derived bound covers
      equality (failure at k != k_s forces b <= Wmax), so the predictions
      are UNCHANGED under the corrected predicate: (d) every neg-pool
      clearance failure has beta_end <= -2, 0 bound violations; (e) the pool
      contains >= 1 failure.
  R3' — exact-count contract (gap 8): coded_fail == 88 exactly (was > 0);
      a drift to 1 or 89 now FAILS the leg.
  R3(b)-STATE — refutation-state enforcement (gap 9): r2_fail == 0 under top
      weights joins the LIVE exit contract (a reappearance of top-weight
      r = 2 class failures => exit 1, not a silent PASS print).
  R2 pool — stationary-interleaved 2-stage types join the datum pool
      ([(1,h,1), s] and [s, (1,h,1)] for live s); prediction: R2(c) stays 0.

NEW LEG R6 (the stationary-level leg; falsifier of the pass-1 CRITICAL
repair).  Repair taken (note section 3 REVISION 1): option (b)-strong —
W-LAD's vanishing omega_j(phi_i) = 0 is GMN's own Lemma 2.14 (arXiv-v2
numbering; label `omji`), printed for ANY type of GMN's section-2 scope and
proved WITHOUT degree comparison (slope minus-infinity point + the
Lemma 2.2(1) omega-chain), so W-LAD holds at ALL levels, stationary
included; secondary degree route covers exactly the ledger-live levels.
  R6(a) closed-form tie: on the full r <= 3 grid (12,348 types, stationary
      stages included) AND the r = 4 stationary spot grid, the note's ladder
      w_i = E_i(e_i V_i + h_i) equals GMN Prop 2.15(1)'s closed form
      sum_{j<=i} (e_{j+1}..e_r) (e_j f_j .. e_{i-1} f_{i-1}) h_j, every i.
      Prediction: 0 failures.
  R6(b) stationary W-CAP + CLASS-LAT: on the sub-grid with >= 1 stationary
      stage (e_i f_i = 1) — count displayed, must be > 0 (leg non-vacuous) —
      and the r = 4 spot grid: W-CAP identity + top-index attainment + cap,
      and every residue class mod e has exactly d ledger indices.
      Prediction: 0 failures.
  R6(c) strictness-premise control (the pass-1 critical was REAL): on the
      stationary sub-grid, m_i < m_j (i < j <= r; m_1 = f0,
      m_{i+1} = e_i f_i m_i) FAILS for >= 1 pair — the retired degree
      argument's premise is genuinely false there — and EVERY failing pair
      has level i STATIONARY (live-level failures == 0: the secondary
      route's exact coverage).  Predictions: >= 1 stationary-pair failure;
      0 live-pair failures.

  REVISION 1 exit contract (supersedes the addendum contract,
  transparently): exit 0 iff R1, R2 (with the repaired (a)/(d)/(e)),
  R3(a), R3(b)-STATE, R4, R5, R3' (== 88), R3'', R6 ALL pass.  Exit 2
  unchanged (theorem-grade: R2(c) hit or R4 off-end partial).
================================================================================
"""
import itertools
import json
import os
import random
import subprocess
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

# ---------------------------------------------------------------- type grid
STAGE = [(e, h, f) for e in (1, 2, 3) for h in (1, 2, 3, 4)
         if gcd(e, h) == 1 for f in (1, 2)]          # 18 stage choices


def type_data(f0, stages):
    """(P3) V-recursion + ledger weight generators for a type.
    stages = [(e_i, h_i, f_i)] i=1..r.  Returns dict with V^, e, d, w_i list,
    E_i list, and the full ledger weight multiset."""
    r = len(stages)
    V = 0
    Vs = [None]  # V_1..V_{r+1}; Vs[i] = V_i (1-indexed)
    Vs.append(0)
    for (e, h, f) in stages:
        V = e * f * (e * V + h)
        Vs.append(V)
    Vhat = Vs[r + 1]
    E = [None] * (r + 2)                 # E_i = e_{i+1}...e_r, E_r = 1
    E[r] = 1
    for i in range(r - 1, 0, -1):
        E[i] = E[i + 1] * stages[i][0]   # stages[i] is stage i+1 (0-based)
    w = [None] * (r + 1)                 # w[i] = w(phi_i) = E_i(e_i V_i + h_i)
    for i in range(1, r + 1):
        e, h, _f = stages[i - 1]
        w[i] = E[i] * (e * Vs[i] + h)
    etot = 1
    d = f0
    for (e, _h, f) in stages:
        etot *= e
        d *= f
    ranges = [range(f0)] + [range(e * f) for (e, _h, f) in stages]
    wts = []
    for j in itertools.product(*ranges):
        wts.append(sum(j[i] * w[i] for i in range(1, r + 1)))
    return dict(r=r, Vhat=Vhat, e=etot, d=d, w=w, E=E, wts=wts,
                stages=stages, f0=f0)


def all_types(rmax=3):
    for r in range(1, rmax + 1):
        for f0 in (1, 2):
            for stages in itertools.product(STAGE, repeat=r):
                yield type_data(f0, list(stages))


# ------------------------------------------------------------ R1: W-CAP
def run_R1():
    fails = [0, 0, 0]
    n = 0
    for T in all_types():
        n += 1
        r, Vhat, w, E = T['r'], T['Vhat'], T['w'], T['E']
        brute = max(T['wts'])
        closed = Vhat - w[1] - sum(E[i] * T['stages'][i - 1][1]
                                   for i in range(2, r + 1))
        top = sum((T['stages'][i - 1][0] * T['stages'][i - 1][2] - 1) * w[i]
                  for i in range(1, r + 1))
        if brute != closed:
            fails[0] += 1
        if brute != top:
            fails[1] += 1
        if not (brute <= Vhat - w[1] <= Vhat - 1):
            fails[2] += 1
    print('R1 W-CAP: types=%d  identity-fails=%d top-index-fails=%d '
          'cap-fails=%d' % (n, *fails))
    return dict(types=n, fails=fails, ok=fails == [0, 0, 0])


# ---------------------------------------------------- R2: STEP + NON-END
def classmax(beta, wts, e):
    cl = [w for w in wts if w % e == beta % e]
    return max(cl) if cl else None


def random_datum(rng, pool):
    T = rng.choice(pool)
    Vhat = T['Vhat']
    s = rng.randint(1, 3)
    # strictly decreasing positive slopes h_S/e_S (so -h/e strictly increasing)
    while True:
        faces = []
        for _ in range(s):
            e = rng.randint(1, 3)
            h = rng.randint(1, 5)
            g = gcd(e, h)
            faces.append((e // g, h // g))
        keys = [h / e for (e, h) in faces]
        keys_sorted = sorted(set(keys), reverse=True)
        if len(keys_sorted) == len(faces):
            faces.sort(key=lambda eh: -eh[1] / eh[0])
            break
    lens = [rng.randint(1, 3) for _ in range(s)]         # lattice lengths
    k0 = rng.randint(0, 2)
    beta_end = rng.randint(-4, 8)
    # vertices right-to-left in beta coordinates: at the shared vertex both
    # faces' lines meet, so beta at vertex S-1 = beta at vertex S + dS*hS
    #   + (k_S - k_{S-1})*Vhat  (since beta_k = L_k - k*Vhat and the line
    #   rises dS*hS over dS*eS columns leftward).
    # Build the ordered on-line slot list left-to-right with per-face steps.
    slots = []          # (k, beta, face_index)
    # compute vertex betas from the right
    vbeta = [None] * (s + 1)
    vk = [None] * (s + 1)
    vk[0] = k0
    for S in range(1, s + 1):
        vk[S] = vk[S - 1] + lens[S - 1] * faces[S - 1][0]
    vbeta[s] = beta_end
    for S in range(s, 0, -1):
        eS, hS = faces[S - 1]
        vbeta[S - 1] = vbeta[S] + lens[S - 1] * (hS + eS * Vhat)
    # REVISION 1 (gap 6): slots carry face-membership SETS — a shared vertex
    # belongs to BOTH adjacent faces, so every consecutive pair has a face in
    # common and the per-face step law can be checked with NO skipped pairs.
    smap = {}                     # k -> [beta, set(faces)]
    for S in range(1, s + 1):
        eS, hS = faces[S - 1]
        for j in range(0, lens[S - 1] + 1):
            k = vk[S - 1] + j * eS
            beta = vbeta[S - 1] - j * (hS + eS * Vhat)
            if k in smap:
                assert smap[k][0] == beta, 'vertex mismatch'
                smap[k][1].add(S)
            else:
                smap[k] = [beta, {S}]
    slots = [(k, b, fs) for k, (b, fs) in sorted(smap.items())]
    return T, faces, slots, beta_end


def run_R2(trials=20000, seed=20260803):
    rng = random.Random(seed)
    pool = [type_data(f0, [st]) for f0 in (1, 2) for st in STAGE]
    pool += [type_data(f0, [s1, s2]) for f0 in (1, 2)
             for s1 in STAGE[::3] for s2 in STAGE[::4]]
    # REVISION 1: stationary-interleaved 2-stage types join the pool
    SS = [(1, h, 1) for h in (1, 2, 3, 4)]
    LIVE = [st for st in STAGE if st[0] * st[2] >= 2]
    pool += [type_data(f0, [st, li]) for f0 in (1, 2)
             for st in SS for li in LIVE[::3]]
    pool += [type_data(f0, [li, st]) for f0 in (1, 2)
             for st in SS for li in LIVE[::3]]
    fa = fb = fc = fd = 0
    cov_fail = shared_bad = 0
    neg_failures = 0
    for _ in range(trials):
        T, faces, slots, beta_end = random_datum(rng, pool)
        Vhat, e, wts = T['Vhat'], T['e'], T['wts']
        Wmax = max(wts)
        # (a) REVISION 1: exact step law on EVERY consecutive pair, via the
        # unique shared face (gap-6 repair; coverage counter enforced)
        checked = 0
        for (k1, b1, F1), (k2, b2, F2) in zip(slots, slots[1:]):
            shared = F1 & F2
            if len(shared) != 1:
                shared_bad += 1
                continue
            S = next(iter(shared))
            eS, hS = faces[S - 1]
            if b1 - b2 != eS * Vhat + hS:
                fa += 1
            checked += 1
        if checked != len(slots) - 1:
            cov_fail += 1
        # (b) strict decrease across the whole ordered list
        for (k1, b1, _), (k2, b2, _) in zip(slots, slots[1:]):
            if not b1 > b2:
                fb += 1
        for (k, b, _F) in slots[:-1]:
            cm = classmax(b, wts, e)
            fail = (b < Vhat + 1) or (cm is not None and not b > cm)
            if beta_end >= 0:
                if fail:
                    fc += 1
            else:
                # REVISION 1 (gap 7): clearance FAILURE is b <= classmax
                # (equality included; clearance itself is b > classmax)
                if cm is not None and b <= cm:
                    neg_failures += 1
                    if beta_end > -2:
                        fd += 1
    print('R2 STEP/NON-END: trials=%d  (a)step-fails=%d cov-fails=%d '
          'shared-bad=%d (b)monotone-fails=%d '
          '(c)THEOREM-GRADE clearance fails@beta_end>=0=%d '
          '(d)bound-fails=%d (e)neg-pool failures(b<=cm)=%d'
          % (trials, fa, cov_fail, shared_bad, fb, fc, fd, neg_failures))
    return dict(fa=fa, fb=fb, fc=fc, fd=fd, neg=neg_failures,
                ok=(fa == 0 and cov_fail == 0 and shared_bad == 0
                    and fb == 0 and fc == 0 and fd == 0
                    and neg_failures >= 1))


# ------------------------------------------------------- R3: CLASS-d control
def run_R3():
    r1_fail = 0
    r1_n = 0
    for f0 in (1, 2):
        for st in STAGE:
            T = type_data(f0, [st])
            r1_n += 1
            for c in range(T['e']):
                if sum(1 for w in T['wts'] if w % T['e'] == c) != T['d']:
                    r1_fail += 1
    r2_fail = 0
    r2_n = 0
    for f0 in (1, 2):
        for s1 in STAGE:
            for s2 in STAGE:
                T = type_data(f0, [s1, s2])
                r2_n += 1
                if any(sum(1 for w in T['wts'] if w % T['e'] == c) != T['d']
                       for c in range(T['e'])):
                    r2_fail += 1
    print('R3 CLASS-d: r1 types=%d fails=%d | r2 types=%d class-count '
          'failing types=%d (SEALED prediction was > 0)'
          % (r1_n, r1_fail, r2_n, r2_fail))
    return dict(r1_fail=r1_fail, r2_fail=r2_fail,
                ok=(r1_fail == 0 and r2_fail > 0))


# ------------------------------- ADDENDUM legs: R3' (diagnosis) + R3'' (r=3)
def coded_type_data(f0, stages):
    """The CARRIER's coded lattice (CensusCore.lean wphi/Vrec transcription):
    wphi_i = e_i*V_i + h_i, NO E_i rescale.  Same (P3) Vrec."""
    r = len(stages)
    V = 0
    Vs = [None, 0]
    for (e, h, f) in stages:
        V = e * f * (e * V + h)
        Vs.append(V)
    w = [None] * (r + 1)
    for i in range(1, r + 1):
        e, h, _f = stages[i - 1]
        w[i] = e * Vs[i] + h
    etot = 1
    d = f0
    for (e, _h, f) in stages:
        etot *= e
        d *= f
    ranges = [range(f0)] + [range(e * f) for (e, _h, f) in stages]
    wts = [sum(j[i] * w[i] for i in range(1, r + 1))
           for j in itertools.product(*ranges)]
    return dict(e=etot, d=d, wts=wts)


def run_R3prime():
    coded_fail = 0
    for f0 in (1, 2):
        for s1 in STAGE:
            for s2 in STAGE:
                T = coded_type_data(f0, [s1, s2])
                if any(sum(1 for w in T['wts'] if w % T['e'] == c) != T['d']
                       for c in range(T['e'])):
                    coded_fail += 1
    # F-ADM-2's quoted smallest type: (e1,h1,f1)=(2,1,1), (e2,h2,f2)=(2,1,1),
    # f0 = 1 — coded weights {0,1,5,6} (empty class mod 4); top weights
    # {0,2,5,7} (uniform mod 4).
    Tc = coded_type_data(1, [(2, 1, 1), (2, 1, 1)])
    Tt = type_data(1, [(2, 1, 1), (2, 1, 1)])
    coded_ok = (sorted(Tc['wts']) == [0, 1, 5, 6]
                and any(sum(1 for w in Tc['wts'] if w % 4 == c) == 0
                        for c in range(4)))
    top_ok = (sorted(Tt['wts']) == [0, 2, 5, 7]
              and all(sum(1 for w in Tt['wts'] if w % 4 == c) == 1
                      for c in range(4)))
    print("R3' diagnosis: coded-weight r2 failing types=%d (REVISION 1 "
          "contract: == 88 exactly) | F-ADM-2 type coded wts=%s (empty "
          "class: %s) top wts=%s (uniform: %s)"
          % (coded_fail, sorted(Tc['wts']), coded_ok,
             sorted(Tt['wts']), top_ok))
    # REVISION 1 (gap 8): the exact F-ADM-2 count is the contract
    return dict(ok=(coded_fail == 88 and coded_ok and top_ok))


def run_R3doubleprime():
    r3_fail = 0
    n = 0
    for T in all_types(rmax=3):
        if T['r'] != 3:
            continue
        n += 1
        if any(sum(1 for w in T['wts'] if w % T['e'] == c) != T['d']
               for c in range(T['e'])):
            r3_fail += 1
    print("R3'' CLASS-LAT at r=3: types=%d class-count failing types=%d "
          "(prediction 0)" % (n, r3_fail))
    return dict(ok=(r3_fail == 0))


# ------------------- R6 (REVISION 1): the stationary-level leg (pass-1 crit)
def prop215_closed(T, i):
    """GMN Prop 2.15(1) closed form (arXiv-v2; paper-r := r+1, our indexing):
    sum_{j=1..i} (e_{j+1}..e_r) * (e_j f_j .. e_{i-1} f_{i-1}) * h_j."""
    stages = T['stages']
    r = T['r']
    total = 0
    for j in range(1, i + 1):
        Ej = 1
        for l in range(j + 1, r + 1):
            Ej *= stages[l - 1][0]
        mid = 1
        for l in range(j, i):
            mid *= stages[l - 1][0] * stages[l - 1][2]
        total += Ej * mid * stages[j - 1][1]
    return total


def r4_spot_grid():
    """r = 4 spot grid: stationary stages (1,h,1) interleaved among live."""
    SS = [(1, h, 1) for h in (1, 2, 3, 4)]
    LIVE = [st for st in STAGE if st[0] * st[2] >= 2]
    for f0 in (1, 2):
        for st in SS:
            for li in LIVE:
                for st2 in SS:
                    for li2 in LIVE:
                        yield type_data(f0, [st, li, st2, li2])
                        yield type_data(f0, [li, st, li2, st2])
                        yield type_data(f0, [li, st, st2, li2])


def check_wcap_classlat(T):
    """W-CAP identity + top attainment + cap, and class counts == d."""
    r, Vhat, w, E = T['r'], T['Vhat'], T['w'], T['E']
    brute = max(T['wts'])
    closed = Vhat - w[1] - sum(E[i] * T['stages'][i - 1][1]
                               for i in range(2, r + 1))
    top = sum((T['stages'][i - 1][0] * T['stages'][i - 1][2] - 1) * w[i]
              for i in range(1, r + 1))
    if brute != closed or brute != top:
        return False
    if not (brute <= Vhat - w[1] <= Vhat - 1):
        return False
    return all(sum(1 for x in T['wts'] if x % T['e'] == c) == T['d']
               for c in range(T['e']))


def run_R6():
    a_fail = b_fail = 0
    n_all = n_stat = n_spot = 0
    stat_pair_fail = live_pair_fail = 0
    for T in list(all_types(rmax=3)) + list(r4_spot_grid()):
        r = T['r']
        spot = (r == 4)
        n_all += 1
        if spot:
            n_spot += 1
        # (a) closed-form tie on EVERY type (stationary included)
        for i in range(1, r + 1):
            if T['w'][i] != prop215_closed(T, i):
                a_fail += 1
        stationary = any(st[0] * st[2] == 1 for st in T['stages'])
        if not (stationary or spot):
            continue
        if stationary:
            n_stat += 1
        # (b) W-CAP + CLASS-LAT on the stationary sub-grid + the spot grid
        if not check_wcap_classlat(T):
            b_fail += 1
        # (c) strictness-premise control: m_i < m_j pairs
        if stationary:
            m = [None, T['f0']]
            for st in T['stages']:
                m.append(m[-1] * st[0] * st[2])
            for i in range(1, r + 1):
                live_i = T['stages'][i - 1][0] * T['stages'][i - 1][2] >= 2
                for j in range(i + 1, r + 1):
                    if not m[i] < m[j]:
                        if live_i:
                            live_pair_fail += 1
                        else:
                            stat_pair_fail += 1
    print('R6 stationary leg: types=%d (stationary=%d spot-r4=%d)  '
          '(a)closed-form fails=%d  (b)W-CAP/CLASS-LAT fails=%d  '
          '(c)premise-control: stationary-pair m_i<m_j failures=%d '
          '(pred >= 1), live-pair failures=%d (pred 0)'
          % (n_all, n_stat, n_spot, a_fail, b_fail,
             stat_pair_fail, live_pair_fail))
    return dict(ok=(a_fail == 0 and b_fail == 0 and n_stat > 0
                    and stat_pair_fail >= 1 and live_pair_fail == 0))


# --------------------------------------------- R4: realized re-adjudication
def run_R4():
    path = os.path.join(REPO, 'verification', 'logs',
                        'gadm2_attainment_20260802T232440Z.jsonl')
    rows = [json.loads(x) for x in open(path)]
    bad_flags = offend = nonend_notfull = empty = 0
    n_full = n_pend = 0
    pin_bad = 0
    for r in rows:
        full = (r['n_att'] == r['q'] - 1)
        partial = (0 < r['n_att'] < r['q'] - 1)
        if full != r['full'] or partial != r['partial']:
            bad_flags += 1
        right = (r['slot'] == r['mu'])
        if right != r['is_right_end']:
            bad_flags += 1
        if partial and not right:
            offend += 1
        if not right and not full:
            nonend_notfull += 1
        if r['n_att'] == 0:
            empty += 1
        if full:
            n_full += 1
        if partial and right:
            n_pend += 1
        if right and r['n_att'] != 1:
            pin_bad += 1
    tallies_ok = (len(rows) == 198 and n_full == 113 and n_pend == 85
                  and offend == 0 and empty == 0)
    print('R4 realized: rows=%d full=%d partial@end=%d OFF-END=%d empty=%d '
          'flag-mismatch=%d pin(n_att!=1 @end)=%d tallies-ok=%s'
          % (len(rows), n_full, n_pend, offend, empty, bad_flags, pin_bad,
             tallies_ok))
    return dict(offend=offend, nonend_notfull=nonend_notfull,
                bad_flags=bad_flags, pin_bad=pin_bad,
                ok=(offend == 0 and nonend_notfull == 0 and bad_flags == 0
                    and pin_bad == 0 and tallies_ok))


# ------------------------------------------------ R5: carve-out necessity
def run_R5():
    script = os.path.join(REPO, 'lean', 'LeanUrat', 'Scaffold', 'HDischarge',
                          'H3', 'adm_u7_check.py')
    res = subprocess.run([sys.executable, script], capture_output=True,
                         text=True)
    ok = (res.returncode == 0 and 'ALL ASSERTIONS PASS' in res.stdout)
    print('R5 carve-out necessity (adm_u7_check.py rerun): exit=%d pass=%s'
          % (res.returncode, ok))
    return dict(ok=ok)


def main():
    r1, r2 = run_R1(), run_R2()
    r3, r4, r5 = run_R3(), run_R4(), run_R5()
    r3p, r3pp = run_R3prime(), run_R3doubleprime()
    r6 = run_R6()
    preds = {
        'R1 (W-CAP identity/top-index/cap)': r1['ok'],
        'R2 (STEP+NON-END abstract; (c) theorem-grade; REV-1 (a)/(d)/(e))':
            r2['ok'],
        'R3(a) (CLASS-d r1 clean)': r3['r1_fail'] == 0,
        'R3(b)-STATE REV-1 (top-weight r2 grid stays clean; refutation '
        'state enforced)': r3['r2_fail'] == 0,
        'R4 (realized: no off-end partial; pin shape)': r4['ok'],
        'R5 (k_s carve-out necessary; A/B/C stand)': r5['ok'],
        "R3' ADDENDUM (coded twin == 88 exactly; REV-1 contract)": r3p['ok'],
        "R3'' ADDENDUM (CLASS-LAT clean on full r=3 grid)": r3pp['ok'],
        'R6 REVISION-1 (stationary leg: closed form + W-CAP/CLASS-LAT + '
        'premise control)': r6['ok'],
    }
    print('\n== PREDICTIONS (sealed header + sealed addenda incl. REV-1) ==')
    for k, v in preds.items():
        print('  [%s] %s' % ('PASS' if v else 'FAIL', k))
    print('  [%s] %s' % ('SEALED-PREDICTION-REFUTED' if r3['r2_fail'] == 0
                         else 'REAPPEARED-SEE-R3b-STATE',
                         'R3(b) (r2 fails exist under top weights) — '
                         'RETIRED: its failure IS finding F-ADM-3'))
    theorem_hit = (r2['fc'] > 0) or (r4['offend'] > 0)
    if theorem_hit:
        print('\nTHEOREM-GRADE HIT: NON-END/STEP refuted — stop the line.')
        return 2
    print('\nVERDICT:', 'ALL LIVE PREDICTIONS PASS (REVISION 1 contract)'
          if all(preds.values()) else 'DRIFT (see FAIL rows)')
    return 0 if all(preds.values()) else 1


if __name__ == '__main__':
    sys.exit(main())
