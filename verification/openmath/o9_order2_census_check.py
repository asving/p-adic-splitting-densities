#!/usr/bin/env python3
"""O-9 falsifier: ORDER-2 STRATUM CENSUS checks (OL-A/OL-B/OL-C at the first
tower step r: 1 -> 2), extending the depth-3 harness's order-2 reads to
census COUNTS -- the M08 proposed test T6, executed.

Setup: boxes = monic f = X^n + a_{n-1}X^{n-1} + ... + a_0 over Z/p^M with all
a_i = 0 mod p (root key X, the standing degree-1 slice).  Level-1 stratum =
(Newton polygon Delta, per-side residual factorization TYPE); the level-1
census is M08 Theorem 2's q^E * prod_S M_lambda(q) -- re-verified here as a
regression (check K1).  For each repeated residual factor (psi, mu >= 2) the
ORDER-2 stratum datum is read through the PINNED coherent anchored-march
convention of o1thr_depth3_check (the (GR-B)(2') shape): order-2 polygon of
the Phi_1-development + per-face order-2 residual types over K_1 = F_{p^g},
g = deg psi.  Working-level determinacy is enforced by a KEY-LEVEL guard
(slot coefficient valuations w_1(C_k) <= e*M - 1; deeper slots enter the key
only as a capped class -- the finite-level reading of the slope-minus-
infinity corner).

Checks (a violation FIRES the gate; any single hit refutes the named claim):
  K1 (regression, M08 Thm 2): level-1 census = p^E * prod M_lambda(p).
  K2 (OL-B shadow, representative independence): for a fixed discrete
     (parent, child) stratum, the refined census is the SAME for every
     concrete parent realization (same polygon+types, different residues /
     different marked psi) -- the count depends on discrete data only.
  K3 (OL-C product law, per p): for fixed parent + child polygon, the child
     census divided by prod_faces M_lambda'(p^g) is the same for every
     child type vector -- the census factors through the type-count
     polynomials over the ORDER-2 residue field F_{p^g}.
  K4 (OL-C cross-p): the normalized per-realization census
     s(p) := c(p) / prod M_lambda'(p^g) equals p^a * (p^g-1)^b * (p-1)^d
     with ONE exponent vector (a,b,d) for all primes run at the same (n,M)
     -- any congruence dependence (the M08 sec 2.5 character phenomenon,
     q mod 3/4/8) kills this first.
  T2 (pinned Lemma 2.17(2) shadow): where no capped slot intrudes, the
     principal part of the order-2 polygon has length exactly mu.

Modes: full enumeration (all a_i = 0 mod p), and a restricted mode (per-
coefficient minimum valuations) reaching the g = 2 design Delta = (0,4)->
(4,0), slope -1, marked type (2,2): order-2 residuals over F_{p^2}.

Run: python3 o9_order2_census_check.py           (default configs, ~2-4 min)
     python3 o9_order2_census_check.py fast      (drops the p=5 full runs)
Exit nonzero on any violation.
"""
import math
import os
import sys
from collections import Counter
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import o1thr_persite_check as base
from o1thr_rev2_checks import development, v_int
from o1thr_rev3_depth2_check import V_sloped, hull_faces, principal, \
    strictly_above
from o1thr_depth3_check import fq_mul, fq_ypow, fq_factor, t0_of, res1

# ---------------- M_lambda: the type-count polynomial (M08 Lemma B) ------
def _moebius(k):
    out, d = 1, 2
    while d * d <= k:
        if k % d == 0:
            k //= d
            if k % d == 0:
                return 0
            out = -out
        d += 1
    return -out if k > 1 else out


def n_irred(d, q):
    """Number of monic irreducibles of degree d over F_q (Gauss)."""
    s = sum(_moebius(k) * q ** (d // k) for k in range(1, d + 1) if d % k == 0)
    assert s % d == 0
    return s // d


def M_type(lam, q):
    """#{monic R over F_q : R(0) != 0, factorization type lam}; lam a sorted
    tuple of (deg, mult) pairs; exact integer (M08 Lemma B)."""
    by_d = {}
    for d, m in lam:
        by_d.setdefault(d, []).append(m)
    out = 1
    for d, ms in by_d.items():
        pool = n_irred(d, q) - (1 if d == 1 else 0)   # exclude y itself
        num = 1
        for i in range(len(ms)):
            num *= pool - i
        den = 1
        for c in Counter(ms).values():
            den *= math.factorial(c)
        assert num % den == 0, (lam, q)
        out *= num // den
    return out


# ---------------- memoized factorizations --------------------------------
_PF_MEMO, _FQ_MEMO = {}, {}


def polfactor_memo(pat, p):
    key = (pat, p)
    if key not in _PF_MEMO:
        _PF_MEMO[key] = base.polfactor(list(pat), p)
    return _PF_MEMO[key]


def fq_factor_memo(patC, psit, p):
    key = (patC, psit, p)
    if key not in _FQ_MEMO:
        _FQ_MEMO[key] = fq_factor(list(patC), psit, p)
    return _FQ_MEMO[key]


# ---------------- level-1 classification ---------------------------------
def parent_data(a, p, n, M):
    """(delta, sides) of the box, or None if the polygon is not closed below
    M.  delta = hull vertex tuple; sides = [(e, h, pat, fac)] per face."""
    vs = [v_int(x, p) if x else M for x in a]
    if vs[0] >= M:
        return None
    pts = [(j, vs[j]) for j in range(n) if vs[j] < M] + [(n, 0)]
    hull = base.lower_hull(sorted(pts))
    sides = []
    for (j0, v0), (j1, v1) in zip(hull, hull[1:]):
        assert v0 > v1, (a, hull)     # block condition => strict descent
        g0 = math.gcd(v0 - v1, j1 - j0)
        e, h = (j1 - j0) // g0, (v0 - v1) // g0
        pat = []
        for k in range(g0 + 1):
            j = j0 + e * k
            aj = 1 if j == n else a[j]
            pat.append((aj // p ** (v0 - k * h)) % p)
        assert pat[0] and pat[-1], (a, hull)
        sides.append((e, h, tuple(pat), polfactor_memo(tuple(pat), p)))
    return tuple(hull), sides


def delta_ceils(delta, n):
    """c_i of M08 Thm 2 (Delta(i)+1 at lattice slots, ceil(Delta(i)) else)
    and the per-i minimal stratum valuation (Delta(i) at slots)."""
    ceils, minv = [], []
    for (j0, v0), (j1, v1) in zip(delta, delta[1:]):
        g0 = math.gcd(v0 - v1, j1 - j0)
        e, h = (j1 - j0) // g0, (v0 - v1) // g0
        for i in range(j0, j1):
            k, r = divmod(i - j0, e)
            if r == 0:
                ceils.append(v0 - k * h + 1)
                minv.append(v0 - k * h)
            else:
                d = Fraction(v0) - Fraction((i - j0) * h, e)
                ceils.append(math.ceil(d))
                minv.append(math.ceil(d))
    assert len(ceils) == n
    return ceils, minv


# ---------------- order-2 read (coherent anchored march) -----------------
def child_data(a, p, n, M, e, h, psi, mu):
    """Order-2 stratum datum at the marked (psi, mu).  Returns
    (kleft, uleft, faces, types, capped_below, t2ok) -- all p-free except
    through the residue-type vocabulary."""
    g = len(psi) - 1
    f = list(a) + [1]
    Phi1 = [0] * (e * g + 1)
    for k in range(g + 1):
        Phi1[e * k] = psi[k] * p ** ((g - k) * h)
    ghat0 = e * g * h
    C = development(f, Phi1)
    # level-determinacy cap: a lift of the same box changes C_k by terms of
    # w_1 >= e*M, so beta = w_1(C_k) is lift-stable iff beta <= e*M - 1, and
    # every on-line digit read then has depth <= beta/e < M.  Slots beyond
    # the cap enter the key only as the capped class (they stay strictly
    # above every counted face at every lift: face beta-heights <= e*M - 1).
    bcap = e * M - 1
    pts, capped = [], []
    for k in range(len(C)):
        beta = V_sloped(C[k], p, e, h) if any(C[k]) else None
        if beta is None or beta > bcap:
            capped.append(k)
        else:
            pts.append((k, beta + k * ghat0))
    if not pts:
        return None
    pfaces = principal(hull_faces(pts))
    if not pfaces:
        return 'UNDET'
    # LEVEL-DETERMINACY CRITERION (key-level, box-free): at every dev
    # abscissa k the extended face lines must sit strictly below the cap
    # height e*M + k*ghat0.  Then (i) every on-line digit read has depth
    # < M, and (ii) every capped slot (beta >= e*M, for EVERY lift of the
    # box) is automatically strictly above every face line -- so the
    # visible faces are the true low part of N_2^- for every lift, the
    # first-min abscissa is exact, and the census key is a genuine
    # level-M-determined stratum.  Strata failing this are not decidable
    # at working level M and are dropped WHOLE (never box-by-box).
    ell = n // (e * g)
    for k in range(ell + 1):
        for (x1, y1), (x2, y2) in pfaces:
            lineval = Fraction(y1) + Fraction((k - x1) * (y2 - y1), x2 - x1)
            if lineval - k * ghat0 >= e * M:
                return 'UNDET'
    umin = min(u for _, u in pts)
    kright = min(k for k, u in pts if u == umin)
    t2ok = (kright == mu)
    psit = tuple(x % p for x in psi)
    ud = dict(pts)
    faces, types = [], []
    for (k0, u0), (k1, u1) in pfaces:
        g1 = math.gcd(u0 - u1, k1 - k0)
        e1, h1 = (k1 - k0) // g1, (u0 - u1) // g1
        d1 = (k1 - k0) // e1
        gamma1 = e1 * u0 + k0 * h1
        gamma2 = e1 * ghat0 + h1
        astep = t0_of(gamma2, e, h)
        zero = tuple([0] * g)
        patC, t0left = [], None
        for kap in range(d1 + 1):
            j = k0 + e1 * kap
            if not (j in ud and e1 * ud[j] + j * h1 == gamma1):
                patC.append(zero)
                continue
            r, t0j, _ = res1(C[j], p, e, h, g)
            if t0left is None:
                t0left = t0j
            mk, rem = divmod(t0j - t0left + kap * astep, e)
            assert rem == 0
            patC.append(fq_mul(r, fq_ypow(mk, psit, p), psit, p))
        assert any(patC[0]) and any(patC[-1]), (a, patC)
        fac2 = fq_factor_memo(tuple(patC), psit, p)
        faces.append((k1 - k0, u0 - u1))
        types.append(tuple(sorted((len(q2) - 1, m) for q2, m in fac2.items())))
    kleft, uleft = pfaces[0][0]
    return kleft, uleft, tuple(faces), tuple(types), t2ok


# ---------------- one configuration run ----------------------------------
def run_config(p, n, M, mins=None):
    """Enumerate boxes with v(a_i) >= mins[i] (default all-1) mod p^M and
    tabulate level-1 and order-2 censuses.  Returns (stats, tables)."""
    mins = mins or [1] * n
    ranges = [range(p ** (M - m)) for m in mins]
    stats = dict(boxes=0, open_poly=0, inst=0, t2bad=0, t2skip=0, undet=0)
    countP, countC, countR = {}, {}, {}
    roster = {}
    for tup in product(*ranges):
        a = tuple(t * p ** m for t, m in zip(tup, mins))
        stats['boxes'] += 1
        pd = parent_data(a, p, n, M)
        if pd is None:
            stats['open_poly'] += 1
            continue
        delta, sides = pd
        ptypes = tuple(tuple(sorted((len(q2) - 1, m) for q2, m in fac.items()))
                       for (_, _, _, fac) in sides)
        pkey = (delta, ptypes)
        countP[pkey] = countP.get(pkey, 0) + 1
        if mins != [1] * n:
            # restricted mode: tabulate children only for strata that lie
            # FULLY inside the enumerated superset (else censuses corrupt)
            _, minv = delta_ceils(delta, n)
            if any(mv < m for mv, m in zip(minv, mins)):
                continue
        for s_idx, (e, h, pat, fac) in enumerate(sides):
            for psi, mu in fac.items():
                if mu < 2:
                    continue
                cd = child_data(a, p, n, M, e, h, psi, mu)
                if cd is None:
                    continue
                if cd == 'UNDET':
                    stats['undet'] += 1
                    continue
                kleft, uleft, faces, types, t2ok = cd
                if t2ok is False:
                    stats['t2bad'] += 1
                g = len(psi) - 1
                ckey = (s_idx, g, mu, kleft, uleft, faces, types)
                rkey = (tuple(tuple(sorted(f2.items()))
                              for (_, _, _, f2) in sides), s_idx, psi)
                stats['inst'] += 1
                countC[(pkey, ckey)] = countC.get((pkey, ckey), 0) + 1
                countR[(pkey, rkey, ckey)] = \
                    countR.get((pkey, rkey, ckey), 0) + 1
                roster.setdefault((pkey, s_idx, g, mu), set()).add(rkey)
    return stats, (countP, countC, countR, roster)


def check_config(p, n, M, mins, stats, tables):
    """Per-p checks K1/K2/K3; returns (violations dict, K4 export)."""
    countP, countC, countR, roster = tables
    viol = dict(K1=0, K2=0, K3=0)
    ex = {}
    # K1: level-1 census regression against M08 Theorem 2
    k1n = 0
    for (delta, ptypes), cnt in countP.items():
        ceils, minv = delta_ceils(delta, n)
        if mins and any(mv < m for mv, m in zip(minv, mins)):
            continue                     # stratum not inside the superset
        k1n += 1
        E = sum(M - c for c in ceils)
        pred = p ** E
        for t in ptypes:
            pred *= M_type(t, p)
        if cnt != pred:
            viol['K1'] += 1
            ex.setdefault('K1', (delta, ptypes, cnt, pred))
    # K2: representative independence of the refined census
    percell = {}                          # (pkey, ckey) -> c (if K2 holds)
    for (pkey, ckey), cnt in countC.items():
        s_idx, g, mu = ckey[0], ckey[1], ckey[2]
        rs = roster[(pkey, s_idx, g, mu)]
        rs = {r for r in rs if len(r[2]) - 1 == g
              and dict(r[0][s_idx]).get(r[2]) == mu}
        vals = {countR.get((pkey, r, ckey), 0) for r in rs}
        if len(vals) != 1:
            viol['K2'] += 1
            ex.setdefault('K2', (pkey, ckey, sorted(vals)))
        else:
            percell[(pkey, ckey)] = vals.pop()
    # K3: per-(parent, child polygon) the census / prod M is type-free
    groups = {}
    for (pkey, ckey), cnt in countC.items():
        s_idx, g, mu, kleft, uleft, faces, types = ckey
        mm = 1
        for t in types:
            mm *= M_type(t, p ** g)
        gk = (pkey, s_idx, g, mu, kleft, uleft, faces)
        groups.setdefault(gk, set()).add(Fraction(cnt, mm))
    for gk, ratios in groups.items():
        if len(ratios) != 1:
            viol['K3'] += 1
            ex.setdefault('K3', (gk, sorted(ratios)))
    # K4 export: normalized per-realization census
    k4 = {}
    for (pkey, ckey), c in percell.items():
        g, types = ckey[1], ckey[6]
        mm = 1
        for t in types:
            mm *= M_type(t, p ** g)
        k4[(pkey, ckey)] = Fraction(c, mm)
    return viol, ex, k4, k1n


def k4_fit(svals, gs):
    """One exponent vector (a,b,d) with s(p) = p^a (p^g-1)^b (p-1)^d for all
    primes?  svals: {p: Fraction}; gs: g (child residue-field degree)."""
    for aa in range(0, 61):
        for bb in range(0, 5):
            for dd in range(0, 5):
                if all(s == Fraction(p ** aa * (p ** gs - 1) ** bb
                                     * (p - 1) ** dd)
                       for p, s in svals.items()):
                    return aa, bb, dd
    return None


def main():
    fast = 'fast' in sys.argv[1:]
    slow = 'slow' in sys.argv[1:]
    # (p, n, M, mins): mins=None is full enumeration (all v(a_i) >= 1).
    # Design notes: the determinacy criterion forces M >= 1 + (max extended
    # face-line height at k=0)/e, so order-2 census strata need M ~ 2x the
    # parent heights.  Coverage: n=3 M=5 = the mu=2 (and capped-tail mu=3)
    # slope -1 designs; n=4 M=4 = quadratic CHILD types on the e=2 slope
    # -1/2 parent (the M08 sec 2.5 character territory, march active);
    # n=4 M=3 = trivial-type children at three primes; the restricted runs
    # reach p=5 (poolable: a stratum inside the superset has the same
    # census in any mode) and the g=2 design (order-2 residuals over
    # F_{p^2}, restricted (4,3,2,1) at M=6).
    cfgs = [(2, 3, 5, None), (3, 3, 5, None),
            (2, 4, 4, None), (3, 4, 4, None),
            (2, 4, 3, None), (3, 4, 3, None), (5, 4, 3, None),
            (5, 3, 5, (3, 2, 1)),
            (2, 4, 6, (4, 3, 2, 1)), (3, 4, 6, (4, 3, 2, 1))]
    if fast:
        cfgs = [c for c in cfgs if c[0] ** (c[2] * c[1] - sum(c[3] or [1] * c[1])) < 10 ** 6]
    if slow:
        cfgs.append((5, 4, 4, (2, 2, 1, 1)))
    allviol = 0
    k4_pool = {}                          # (n, M, pkey, ckey) -> {p: s}
    for cfg in cfgs:
        p, n, M, mins = cfg
        stats, tables = run_config(p, n, M, list(mins) if mins else None)
        viol, ex, k4, k1n = check_config(p, n, M, mins, stats, tables)
        mode = 'restr' + str(mins) if mins else 'full'
        print(f"p={p} n={n} M={M} {mode}: boxes={stats['boxes']} "
              f"open={stats['open_poly']} K1-strata={k1n} "
              f"order2-inst={stats['inst']} undet={stats['undet']} "
              f"cells={len(k4)} T2skip={stats['t2skip']}")
        print(f"   violations K1:{viol['K1']} K2:{viol['K2']} "
              f"K3:{viol['K3']} T2:{stats['t2bad']}")
        for k in ('K1', 'K2', 'K3'):
            if viol[k]:
                print(f"   first {k}:", ex[k])
        allviol += sum(viol.values()) + stats['t2bad']
        for (pkey, ckey), s in k4.items():
            k4_pool.setdefault((n, M, pkey, ckey), {})[p] = s
    # K4: cross-p exponent-vector fit
    k4bad = k4singles = k4n = 0
    exponents = Counter()
    first_bad = None
    for key, svals in k4_pool.items():
        if len(svals) < 2:
            k4singles += 1
            continue
        k4n += 1
        g = key[3][1]
        fit = k4_fit(svals, g)
        if fit is None:
            k4bad += 1
            first_bad = first_bad or (key, svals)
        else:
            exponents[(g, fit)] += 1
    print(f"K4: cross-p cells={k4n} (singles skipped={k4singles}) "
          f"violations={k4bad}")
    print("   fitted (g,(a,b,d)) spectrum:", dict(exponents))
    if first_bad:
        print("   first K4 violation:", first_bad)
    allviol += k4bad
    print("OVERALL:", "GATE SURVIVES (0 violations)" if allviol == 0
          else f"GATE FIRES ({allviol} violations)")
    return 1 if allviol else 0


if __name__ == '__main__':
    sys.exit(main())
