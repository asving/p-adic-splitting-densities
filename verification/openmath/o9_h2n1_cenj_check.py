#!/usr/bin/env python3
"""H2-N1: the CEN-J free-end VALUE gate (blueprint HDISCHARGE_H2 sec. 7,
unit H2-N1; spec source O9_phaseB_verifybrief_rev5 sec. 2 / 5.4 / 6.4).

Companion module of o9_order2_census_check.py -- it IMPORTS that harness's
own readers and keying (parent_data, child_data, delta_ceils, M_type) and
runs the same box enumeration, so every stratum key below is byte-identical
to the recorded K1-K4 harness's.  (Kept as a companion file rather than an
in-place edit because the H2-N2 unit is extending the same target file
concurrently; the two units share the enumeration semantics through the
import, not through a merged loop.)

THE CHECK (CJ).  Theorem CEN-J (O-9 rev 5 sec. 2), conditioned on a parent
realization rho and specialized to the fibered form (its step-1 lift
absorbs the level-N0 parent count into the level-N fiber size), predicts,
for every order-2 stratum datum D over rho:

    #(rho-fiber in D) * q^X  ==  #(rho-fiber) * prod_S M_{lambda_S}(q^d)

with the displayed (E'') exponent in relative form

    X = sum_{k in K_D} max(0, s(beta_k) - s(g_k)) + d * L',
    L' = L - [k_s in K_D]    (the FREE-END subtraction under test:
                              the chain's right-end read is rho-pinned --
                              (FRESH)(c) -- charged to the parent, never
                              a free unit),

where, per O-9 sec. 2 over the monic-top box (eg | n, K_D = {0..ell-1}):
  * beta_k = the datum's per-slot thresholds in w_1-coordinates:
      - k < kleft: the capped class w_1 >= e*M (the harness keys strata by
        the principal part of the level-M-determined polygon, so a slot
        left of kleft is a slot whose point is lift-unstably deep; any
        stable point there would extend the principal part = other key);
      - kleft <= k <= k_s on a face: the face value at on-line LATTICE
        slots (these are the L read slots), floor(line)+1 = ceil(line) at
        the strictly-above non-lattice slots (within faces the line is
        non-integral exactly off the lattice);
      - k_s < k <= ell-1: the right tail u_k >= u_min (non-strict; a lower
        point would move the polygon's minimum = other key);
  * s(beta) = sum_j max(0, ceil((beta - wt_j)/e)) over the m = e*g ledger
    weights wt_j = j*h (LED(ii); f_0 = 1 root-key-X slice, d = g);
  * g_k = the per-slot minimal attained w_1(C_k) over the rho-fiber --
    the floors are measured EMPIRICALLY, because the (FRESH)(a')
    transported-floor formula is exactly the open kernel; shape-only-ness
    of the floors is H2-N2's charge, not certified here;
  * prod M over the child faces' residual types at q^d, d = g.

FREE-END cells: extending the harness's tabulation from mu >= 2 to
mu >= 1 makes the windows with k_s = mu < ell appear -- exactly the
free-end shape (k_s in K_D) that NO prior run discriminated (O-9 sec. 10
coverage note: every prior cell had k_s = ell, where epsilon = 0 is forced
by monicity).  At the g = 2 design configs this includes the K7 class
(r = 1, d = 2): a (FRESH)(c) pin failure of the free-unit shape would
inflate the fibered count by a (q^d - 1)-flavored factor here.

HONEST POWER (verbatim charge, blueprint sec. 7 / review finding 18): CJ
gates the CEN-J COMPOUND -- (a') AND (b) AND (c) AND (ADM)-FULL AND the
harness/(DET) leg.  A mismatch REFUTES THE COMPOUND and owes a diagnosis;
it is NOT automatically a clause-(c) countermodel.  An exact match is
supporting evidence sensitive to the free-unit failure MODE of (c) only:
fiber-varying pins or cross-slot-correlated failures can evade aggregate
counts.  MISMATCH = STOP-THE-LINE.

FENCES (skipped and tallied, per the theorem's displayed scope):
  * (ADM)-FULL failures at an on-line lattice slot (dim G_beta < d by the
    LED(iii) count) -- CEN-J is asserted under (ADM) only (K7 semantics);
  * interior on-line slots with g_k > beta_k -- O-9's scope clause says
    the displayed formula "does not apply" there (the digit is forced 0);
  * eg nmid n coset tops (LED-top s' sub-ledger, out of this unit's scope);
  * k_s != mu cells (capped-slot intrusion; the T2/Lemma-2.17(2) guard).
A vertex slot with g_k > beta_k on a REALIZED cell is impossible (the
fiber minimum is attained), so it is graded an ANOMALY = violation.

Coverage honesty: the d >= 2 free-end cells reachable at feasible box
sizes have mu = 1 (k_s = 1), single-face, trivial child type, p in {2,3};
mu >= 2 free ends at d >= 2 need n >= 6 windows (infeasible for full
enumeration at determinacy-compatible M) and REMAIN QUEUED; the mu >= 2,
d = 1 free ends (n = 3 configs) and the right-tail slots (n = 4, g = 1,
mu <= 2) are exercised.  Floors here are per-rho empirical minima, so a
rho-DEPENDENT floor set would surface as a per-rho VALUE mismatch only if
it breaks the product count -- H2-N2's N2i is the direct floor gate.

Run: python3 o9_h2n1_cenj_check.py         (default = the 10 recorded
                                            harness configs, ~10-40 min)
     python3 o9_h2n1_cenj_check.py fast    (same filter as the harness)
     python3 o9_h2n1_cenj_check.py dev     (p = 2 configs only, quick)
Exit nonzero on any violation OR if a coverage class is empty (a free-end
gate that never sees a free-end d >= 2 cell would be vacuous).
"""
import math
import os
import sys
from collections import Counter
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o9_order2_census_check import (parent_data, child_data, delta_ceils,
                                    M_type)
from o1thr_rev2_checks import development
from o1thr_rev3_depth2_check import V_sloped


# ---------------- ledger layer (LED(ii)/(iii); K6/K7 conventions) --------
def s_led(beta, weights, e):
    """s(beta) = sum_j max(0, ceil((beta - wt_j)/e))  (LED(ii))."""
    return sum(max(0, (beta - wt + e - 1) // e) for wt in weights)


def dim_full(beta, weights, e):
    """LED(iii): dim G_beta = #{j : wt_j = beta mod e AND wt_j <= beta}."""
    return sum(1 for wt in weights if (beta - wt) % e == 0 and wt <= beta)


def dev_slots(a, p, n, e, h, psi):
    """Phi_1-development slots of the box a (same construction as the
    harness's child_data; recomputed here to keep its signature frozen)."""
    g = len(psi) - 1
    f = list(a) + [1]
    Phi1 = [0] * (e * g + 1)
    for k in range(g + 1):
        Phi1[e * k] = psi[k] * p ** ((g - k) * h)
    return development(f, Phi1)


def wclasses(C, p, e, h, M):
    """Per-slot lift-stable w_1 class: the value if <= e*M - 1, else the
    capped-class sentinel e*M (covers C_k = 0)."""
    cap = e * M
    out = []
    for c in C:
        b = V_sloped(c, p, e, h) if any(c) else None
        out.append(cap if (b is None or b > cap - 1) else b)
    return out


# ---------------- tabulation (the harness enumeration, mu >= 1) ----------
def run_config(p, n, M, mins=None):
    """Same boxes, parent keying and superset guard as the harness's
    run_config; tabulates, for EVERY mark (s_idx, psi, mu >= 1):
      countRho[(pkey, rho)]              rho-fiber size at level M,
      countJ[(pkey, (rho,s,psi), ckey)]  per-realization child census,
      minwJ[(pkey, rho, s_idx, psi)]     per-slot empirical floor classes.
    rho = the concrete residual factorizations of all sides (the parent
    realization, up to the leading-unit pooling of non-final sides --
    pooling averages equal fibers under CEN-J, so a pooled mismatch still
    refutes the compound)."""
    mins = mins or [1] * n
    ranges = [range(p ** (M - m)) for m in mins]
    stats = dict(boxes=0, open_poly=0, inst=0, undet=0, t2bad=0)
    countRho, countJ, minwJ = {}, {}, {}
    for tup in product(*ranges):
        a = tuple(t * p ** m for t, m in zip(tup, mins))
        stats['boxes'] += 1
        pd = parent_data(a, p, n, M)
        if pd is None:
            stats['open_poly'] += 1
            continue
        delta, sides = pd
        ptypes = tuple(tuple(sorted((len(q2) - 1, m2) for q2, m2 in
                                    fac.items()))
                       for (_, _, _, fac) in sides)
        pkey = (delta, ptypes)
        if mins != [1] * n:
            _, minv = delta_ceils(delta, n)
            if any(mv < m for mv, m in zip(minv, mins)):
                continue          # stratum not fully inside the superset
        rho = tuple(tuple(sorted(fac.items())) for (_, _, _, fac) in sides)
        countRho[(pkey, rho)] = countRho.get((pkey, rho), 0) + 1
        for s_idx, (e, h, pat, fac) in enumerate(sides):
            for psi, mu in fac.items():
                g = len(psi) - 1
                C = dev_slots(a, p, n, e, h, psi)
                wv = wclasses(C, p, e, h, M)
                mkey = (pkey, rho, s_idx, psi)
                cur = minwJ.get(mkey)
                if cur is None:
                    minwJ[mkey] = list(wv)
                else:
                    for i, b in enumerate(wv):
                        if b < cur[i]:
                            cur[i] = b
                cd = child_data(a, p, n, M, e, h, psi, mu)
                if cd is None:
                    continue
                if cd == 'UNDET':
                    stats['undet'] += 1
                    continue
                kleft, uleft, faces, types, t2ok = cd
                if t2ok is False:
                    stats['t2bad'] += 1
                stats['inst'] += 1
                key = (pkey, (rho, s_idx, psi),
                       (s_idx, g, mu, kleft, uleft, faces, types))
                countJ[key] = countJ.get(key, 0) + 1
    return stats, (countRho, countJ, minwJ)


# ---------------- the CEN-J cell evaluation -------------------------------
def cenj_cell(p, n, M, pkey, s_idx, ckey, cj, P, gk):
    """Evaluate one (rho, D) cell.  Returns (status, detail): status in
    {'ok', 'VIOLATION', 'VERTEX_OOB_ANOMALY'} or a fence tag in
    {'coset_top', 'ks_ne_mu', 'adm_not_full', 'interior_oob'}."""
    delta, _ = pkey
    (j0, v0), (j1, v1) = delta[s_idx], delta[s_idx + 1]
    g0 = math.gcd(v0 - v1, j1 - j0)
    e, h = (j1 - j0) // g0, (v0 - v1) // g0
    _, g, mu, kleft, uleft, faces, types = ckey
    d = g
    mw = e * g                            # deg Phi_1 = m = e*d (f0 = 1)
    ell, rem = divmod(n, mw)
    if rem:
        return 'coset_top', None
    ghat0 = mw * h                        # Vhat in w_1-normalization
    verts = [(kleft, uleft)]
    for dk, du in faces:
        verts.append((verts[-1][0] + dk, verts[-1][1] - du))
    k_s, u_min = verts[-1]
    if k_s != mu:                         # capped intrusion (T2 guard)
        return 'ks_ne_mu', None
    assert 0 <= k_s <= ell, (pkey, ckey)
    weights = [t * h for t in range(mw)]
    vset = {v[0] for v in verts}
    X, L = 0, 0
    for k in range(ell):                  # K_D = {0..ell-1}, monic top
        onl = False
        if k < kleft:
            bw = e * M                    # capped class (see docstring)
        elif k <= k_s:
            bu = None
            for (x0, y0), (x1, y1) in zip(verts, verts[1:]):
                if x0 <= k <= x1:
                    gS = math.gcd(x1 - x0, y0 - y1)
                    eS = (x1 - x0) // gS
                    num = y0 * (x1 - x0) - (k - x0) * (y0 - y1)
                    den = x1 - x0
                    if (k - x0) % eS == 0:
                        onl = True
                        assert num % den == 0, (pkey, ckey, k)
                        bu = num // den   # on-line lattice: exact value
                    else:
                        bu = num // den + 1   # strictly above: floor+1
                    break
            assert bu is not None, (pkey, ckey, k)
            bw = bu - k * ghat0
        else:
            bw = u_min - k * ghat0        # right tail: u_k >= u_min
        if onl:
            L += 1
            if dim_full(bw, weights, e) != d:
                return 'adm_not_full', (k, bw)
            if gk[k] > bw:
                if k in vset:
                    return 'VERTEX_OOB_ANOMALY', (k, bw, gk[k])
                return 'interior_oob', (k, bw, gk[k])
        X += max(0, s_led(bw, weights, e) - s_led(gk[k], weights, e))
    Lp = L - (1 if k_s < ell else 0)      # the free-end subtraction
    X += d * Lp
    mm = 1
    for t in types:
        mm *= M_type(t, p ** g)
    ok = (cj * p ** X == P * mm)
    free = k_s < ell
    return ('ok' if ok else 'VIOLATION'), (free, d, X, L, Lp, cj, P, mm)


def check_cenj(p, n, M, tables):
    countRho, countJ, minwJ = tables
    fences = Counter()
    cls = {}                              # (free, d>=2) -> [cells, viol]
    bad = []
    for (pkey, rkey, ckey), cj in sorted(countJ.items()):
        rho, s_idx, psi = rkey
        P = countRho[(pkey, rho)]
        gk = minwJ[(pkey, rho, s_idx, psi)]
        status, det = cenj_cell(p, n, M, pkey, s_idx, ckey, cj, P, gk)
        if status in ('coset_top', 'ks_ne_mu', 'adm_not_full',
                      'interior_oob'):
            fences[status] += 1
            continue
        if status == 'VERTEX_OOB_ANOMALY':
            fences['VIOLATION'] += 1
            if len(bad) < 5:
                bad.append((status, pkey, rkey, ckey, det))
            continue
        free, d = det[0], det[1]
        c = cls.setdefault((free, d >= 2), [0, 0])
        c[0] += 1
        if status != 'ok':
            c[1] += 1
            fences['VIOLATION'] += 1
            if len(bad) < 5:
                bad.append((status, pkey, rkey, ckey, det))
    return cls, fences, bad


CLS_NAMES = {(True, True): 'FREE-END d>=2 (THE GATE CLASS)',
             (True, False): 'free-end d=1',
             (False, True): "monic-end d>=2 (E'' predictor regression)",
             (False, False): "monic-end d=1 (E'' predictor regression)"}


def main():
    fast = 'fast' in sys.argv[1:]
    dev = 'dev' in sys.argv[1:]
    cfgs = [(2, 3, 5, None), (3, 3, 5, None),
            (2, 4, 4, None), (3, 4, 4, None),
            (2, 4, 3, None), (3, 4, 3, None), (5, 4, 3, None),
            (5, 3, 5, (3, 2, 1)),
            (2, 4, 6, (4, 3, 2, 1)), (3, 4, 6, (4, 3, 2, 1))]
    if fast:
        cfgs = [c for c in cfgs
                if c[0] ** (c[2] * c[1] - sum(c[3] or [1] * c[1])) < 10 ** 6]
    if dev:
        cfgs = [c for c in cfgs if c[0] == 2]
    nviol = 0
    total_cls = {}
    total_fence = Counter()
    for p, n, M, mins in cfgs:
        stats, tables = run_config(p, n, M, list(mins) if mins else None)
        cls, fences, bad = check_cenj(p, n, M, tables)
        mode = 'restr' + str(list(mins)) if mins else 'full'
        print(f"p={p} n={n} M={M} {mode}: boxes={stats['boxes']} "
              f"open={stats['open_poly']} inst={stats['inst']} "
              f"undet={stats['undet']} t2bad={stats['t2bad']} "
              f"rho-fibers={len(tables[0])} cells={sum(c[0] for c in cls.values())}")
        for ck in sorted(cls):
            c = cls[ck]
            print(f"   {CLS_NAMES[ck]}: cells={c[0]} violations={c[1]}")
            t = total_cls.setdefault(ck, [0, 0])
            t[0] += c[0]
            t[1] += c[1]
        fviol = fences.pop('VIOLATION', 0)
        if fences:
            print(f"   fenced (formula not asserted): {dict(fences)}")
        total_fence.update(fences)
        nviol += fviol + sum(c[1] for c in cls.values())
        for b in bad:
            print("   FIRST VIOLATIONS:", b)
        sys.stdout.flush()
    print("\n==== CJ SUMMARY (all configs) ====")
    for ck in sorted(total_cls):
        t = total_cls[ck]
        print(f"  {CLS_NAMES[ck]}: cells={t[0]} violations={t[1]}")
    if total_fence:
        print(f"  fenced totals: {dict(total_fence)}")
    # coverage: an empty gate class would make the run vacuous
    gate_cells = total_cls.get((True, True), [0, 0])[0]
    free1_cells = total_cls.get((True, False), [0, 0])[0]
    monic_cells = (total_cls.get((False, True), [0, 0])[0]
                   + total_cls.get((False, False), [0, 0])[0])
    cover_ok = gate_cells > 0 and free1_cells > 0 and monic_cells > 0
    if not cover_ok:
        print("COVERAGE FAILURE: gate class empty "
              f"(free d>=2: {gate_cells}, free d=1: {free1_cells}, "
              f"monic: {monic_cells})")
    print("OVERALL:", "CJ GATE SURVIVES (0 violations)"
          if nviol == 0 and cover_ok
          else f"CJ GATE FIRES ({nviol} violations, coverage_ok={cover_ok})"
          " -- STOP-THE-LINE, diagnosis owed (compound, not (c)-attribution)")
    return 1 if (nviol or not cover_ok) else 0


if __name__ == '__main__':
    sys.exit(main())
