#!/usr/bin/env python3
"""O4T_transfer_check.py -- O-4 DRAINAGE TRANSFER falsifier (unit O4T, 2026-07-31).

CHARGE (DELTA-2 path step 6 / tree O-4): the VERIFIED semantic drainage core (M05
Lemmas A-D + Theorem E, V2 items 5-8; Dfloor SEM-DRAIN, V22 SOUND) must transfer to
the OM/GD tree classifier through the OL1-ii agreement seam.  This harness tests the
TRANSFER numerically at n <= 3, where the canonical OM run stays at ORDER <= 1 with
refinements only (side length e*d >= 4 is impossible at n <= 3), i.e. exactly the
GD23-verified perimeter (V26: order-<=1 algebra + DEVID upheld).

WHAT IS IMPLEMENTED
-------------------
An executable CANONICAL ORDER-<=1 CLASSIFIER with an explicit READ LEDGER:
  * step 0: residual factorization of f mod p (reads digit level 0);
  * per repeated residual root: recentered cluster walk -- LEVEL-SYNCHRONOUS LAZY
    scan k = lam_prev+1, lam_prev+2, ... of the digits of the shifted coefficients
    g_i of g = f(x+c); at each k the lower Newton hull of the RESOLVED points
    (v(g_i) < k) is built and the step certifies iff
      (C1) every unresolved i in (x0, n) sits STRICTLY above the resolved hull
           (k > hull(i)), so the hull is the true hull in every completion;
      (C2) left edge: x0 = 0 (nothing left of the hull), or x0 = 1 with the
           vertex certificate k > y(1) + slope_right(1) AND k > y(1) + lam_prev
           (then EVERY completion, including g_0 = 0, has a length-1 leftmost side
           => one Galois-stable root => a certified (1,1) factor); x0 >= 2 never
           certifies (keep scanning).
  * certified sides with slope s = h/e > lam_prev (Fractions):  d := len/e;
    d = 1 => certified irreducible factor (e, 1);  d >= 2 (forces e = 1 at n <= 3)
    => residual polynomial read off the on-line digits (all < k), factored over
    F_p: simple factors => certified (1, deg); a repeated root z0 (mult m') =>
    RECENTER c <- c + lift(z0) p^h and recurse with lam_prev = h.
  * L(f) := max certify-level k over all steps (levels consumed; step 0 charges 1).
    Budget C: any scan reaching k > C aborts => UNDECIDED at every N <= C.
The classifier "decide the level-N class iff L <= N, with the walk's verdict" is
stable (deterministic digit reads) and its verdict is a class function of level L.

PREREGISTERED PREDICTIONS (written BEFORE the production run; falsifier-first)
------------------------------------------------------------------------------
  P1 SOUND : walker verdict == exact oracle type of the integer representative,
             for every decided rep (any mismatch REFUTES the surrogate).
  P2 FLOOR : semantic-decided level <= L pointwise (n=2 exact law; n=3: no level-N
             class with a certified lift-type disagreement may have L <= N).
             Refutation = an unsound decision (VPSound broken).
  P3 CEIL  : L(f) <= v_p(disc f) + 1 for every separable rep with v + 1 <= C
             (THE O4T ceiling theorem; a violation refutes the attempt's
             Theorem N3 before it is consumed).
  P4 KRA   : hence L <= 2v+1 for v >= 1 and L = 1 at v = 0: the OM walker is
             never slower than the Krasner/discriminant decider =>
             undec_OM(N) <= undec_K(N) at every level (shift <= 0).
  P5 ENV   : undec_OM(N) <= (n-1) * p^(-max(0, ceil((N - n*v_p(n))/(n-1))))
             (the transferred M05-Lemma-C envelope via P3), and undec_OM
             nonincreasing in N.
  P6 LEAN2 : at n = 2, undec_OM(N) <= (floor(N/2)+1) * p^(-(N-1)) (the K-12
             machine-checked hExhaustP envelope shape; consistency anchor).

CONFIGS (exhaustive, exact integer arithmetic; wild cells included):
  n=2: (p=2, C=10) (p=3, C=6) (p=5, C=4);  n=3: (p=2, C=5) (p=3, C=4).

HONESTY FLAGS
-------------
  F1. This is the CANONICAL MATHEMATICAL run (M05 section 5's N(f)), not the as-built
      Lean OM-tree engine (which has no executable extraction -- same flag as
      N1-exhaust F1).  The engine-conformance seam (GD-4/GD-6, CU-2/CU-4) is NOT
      tested here and is priced in the O4T brief.
  F2. The level-synchronous scan is a PINNED read policy; other lazy policies give
      L' <= L + O(1).  The ceiling theorem is stated for THIS policy.
  F3. n=3 semantic undecidedness is only BRACKETED (certified-disagreement lower
      bound <= U_sem <= Krasner upper bound); n=2 is exact (N1's validated law).
"""
import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
from padic_types import quad_type, cubic_type_monic, vp as vp_int  # noqa: E402

QUAD_MAP = {"split": ((1, 1), (1, 1)), "inert": ((1, 2),), "ram": ((2, 1),)}
CUBIC_MAP = {"111": ((1, 1), (1, 1), (1, 1)), "12": ((1, 1), (1, 2)),
             "3": ((1, 3),), "1r1": ((1, 1), (2, 1)), "1c": ((3, 1),)}


def vp_cap(x, p, cap):
    """v_p(x) if < cap else None (None also for x == 0)."""
    if x == 0:
        return None
    v = 0
    while x % p == 0:
        x //= p
        v += 1
        if v >= cap:
            return None
    return v


def shift_poly(n, a, c):
    """Coefficients g_0..g_{n-1} of f(x+c), f = x^n + sum a_i x^i (monic)."""
    co = list(a) + [1]                      # ascending, degree n
    for _ in range(n):                      # repeated synthetic 'division' by (x-(-c))
        # Taylor shift via Horner: g(x) = f(x+c)
        pass
    # direct Taylor shift (n <= 3 so cost is trivial): g_k = sum_j>=k C(j,k) co[j] c^(j-k)
    from math import comb
    g = [sum(comb(j, k) * co[j] * c ** (j - k) for j in range(k, n + 1))
         for k in range(n)]
    return g


def roots_mults_fp(coeffs_asc, p):
    """Roots+multiplicities over F_p of poly sum coeffs_asc[i] x^i (lead nonzero)."""
    cur0 = [c % p for c in coeffs_asc]
    while cur0 and cur0[-1] == 0:
        cur0.pop()
    out = {}
    for r in range(p):
        cur = list(cur0)
        mult = 0
        while len(cur) > 1:
            # synthetic division by (x - r): ascending coeffs
            dsc = list(reversed(cur))
            q = [dsc[0]]
            for cc in dsc[1:]:
                q.append((q[-1] * r + cc) % p)
            rem = q.pop()
            if rem != 0:
                break
            mult += 1
            cur = list(reversed(q))
        if mult:
            out[r] = mult
    deg = len(cur0) - 1
    return out, deg


def lower_hull(pts):
    """Lower convex hull of dict x->y (ints); returns vertex list [(x,y)] x asc."""
    xs = sorted(pts)
    hull = []
    for x in xs:
        y = pts[x]
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep hull lower-convex: slope(h[-2],h[-1]) must be < slope(h[-1],new) is
            # WRONG orientation; we need y as function of x convex from below:
            if (y2 - y1) * (x - x2) >= (y - y2) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append((x, y))
    return hull


def hull_val(hull, x):
    """Hull height at x (Fraction); None if x < first vertex."""
    if x < hull[0][0]:
        return None
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        if x1 <= x <= x2:
            return Fraction(y1) + Fraction(y2 - y1, x2 - x1) * (x - x1)
    return Fraction(hull[-1][1])


class Undecided(Exception):
    pass


def om_walk(n, a, p, C):
    """Canonical order-<=1 lazy walk. Returns (verdict tuple or None, L)."""
    Lmax = [1]                              # step-0 residual read: level 0 consumed
    factors = []

    def cluster(c, m, lam_prev):
        g = shift_poly(n, a, c)
        vs = [vp_cap(g[i], p, C) for i in range(n)]   # None = (>= C or 0)
        start = int(lam_prev) + 1
        for k in range(max(1, start), C + 1):
            resolved = {i: vs[i] for i in range(n)
                        if vs[i] is not None and vs[i] < k}
            resolved[n] = 0
            x0 = min(resolved)
            hull = lower_hull(resolved)
            # (C1) interspersed unresolved strictly above hull
            ok = True
            for i in range(x0 + 1, n):
                if i not in resolved:
                    hv = hull_val(hull, i)
                    if not (Fraction(k) > hv):
                        ok = False
                        break
            if not ok:
                continue
            left11 = False
            if x0 >= 2:
                continue
            if x0 == 1:
                y1 = resolved[1]
                if len(hull) >= 2 and hull[0][0] == 1:
                    sr = Fraction(hull[0][1] - hull[1][1], hull[1][0] - hull[0][0])
                elif hull[0][0] > 1:        # (1,y1) not even a hull vertex yet
                    continue
                else:
                    sr = Fraction(0)
                if Fraction(k) > y1 + sr and Fraction(k) > y1 + lam_prev:
                    left11 = True
                else:
                    continue
            # hull certified: harvest sides with slope > lam_prev
            got = []
            subclusters = []
            feasible = True
            for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
                s = Fraction(y1 - y2, x2 - x1)
                if not (s > lam_prev):
                    continue
                e, h = s.denominator, s.numerator
                ell = x2 - x1
                if ell % e != 0:
                    feasible = False        # cannot happen for a true hull; rescan
                    break
                d = ell // e
                if d == 1:
                    got.append((e, 1))
                    continue
                assert e == 1, "e>=2 with d>=2 impossible at n<=3"
                res = []
                for j in range(d + 1):
                    xi = x1 + j
                    yline = y1 - j * h
                    if xi == n:
                        gval, vi = 1, 0
                    else:
                        gval, vi = g[xi], vs[xi]
                    onl = (vi == yline) if vi is not None else False
                    res.append((gval // p ** yline) % p if onl else 0)
                rts, dg = roots_mults_fp(res, p)
                simple_lin = sum(1 for mu in rts.values() if mu == 1)
                rep_deg = sum(mu for mu in rts.values() if mu >= 2)
                leftover = dg - simple_lin - rep_deg
                got.extend([(1, 1)] * simple_lin)
                if leftover == 2:
                    got.append((1, 2))
                elif leftover == 3:
                    got.append((1, 3))
                elif leftover not in (0,):
                    feasible = False
                    break
                for z0, mu in rts.items():
                    if mu >= 2:
                        subclusters.append((c + z0 * p ** h, mu, h))
            if not feasible:
                continue
            Lmax[0] = max(Lmax[0], k)
            if left11:
                got.append((1, 1))
            factors.extend(got)
            for (c2, mu, h) in subclusters:
                cluster(c2, mu, h)
            return
        raise Undecided

    fbar_roots, _ = roots_mults_fp(list(a) + [1], p)
    lin = sum(fbar_roots.values())
    leftover = n - lin
    if leftover == 2:
        factors.append((1, 2))
    elif leftover == 3:
        factors.append((1, 3))
    try:
        for r, mu in fbar_roots.items():
            if mu == 1:
                factors.append((1, 1))
            else:
                cluster(r, mu, 0)
    except Undecided:
        return None, C + 1
    assert sum(e * f for (e, f) in factors) == n, (a, p, factors)
    return tuple(sorted(factors)), Lmax[0]


# ----------------------------------------------------------------------------
# exact oracles / semantic side
# ----------------------------------------------------------------------------

def disc_of(n, a):
    if n == 2:
        return a[1] * a[1] - 4 * a[0]
    c0, c1, c2 = a
    return (18 * c2 * c1 * c0 - 4 * c2 ** 3 * c0 + c2 ** 2 * c1 ** 2
            - 4 * c1 ** 3 - 27 * c0 ** 2)


def oracle_type(n, a, p):
    if n == 2:
        if a[1] * a[1] - 4 * a[0] == 0:
            return None                     # inseparable exact rep
        t = quad_type(a[1], a[0], p)
        return QUAD_MAP.get(t)
    if disc_of(3, a) == 0:
        return None
    t = cubic_type_monic(a[2], a[1], a[0], p)
    return CUBIC_MAP.get(t)


def quad_sem_first(a1, a0, p, C):
    """First level N <= C at which the level-N class is semantically decided
    (N1-exhaust's validated exact law); C+1 if none."""
    from importlib import util as _u
    return _QSEM(a1, a0, p, C)


def _load_n1_qsem():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "n1x", os.path.join(HERE, "N1-exhaust_run.py"))
    mod = importlib.util.module_from_spec(spec)
    # N1's main() only runs under __main__; import is side-effect-light
    spec.loader.exec_module(mod)
    def first(a1, a0, p, C):
        for N in range(1, C + 1):
            if mod.quad_sem_decided(a1 % p ** N, a0 % p ** N, N, p):
                return N
        return C + 1
    return first


# ----------------------------------------------------------------------------
# per-config exhaustive scan
# ----------------------------------------------------------------------------

def run_config(n, p, C, log):
    t0 = time.time()
    total = p ** (n * C)
    log(f"== config n={n} p={p} C={C}  ({total} classes)")
    w = n * (1 if n % p == 0 else 0) * (vp_int(n, p) or 0) if n % p == 0 else 0
    w = n * (vp_int(n, p) or 0) if n % p == 0 else 0     # w = n*v_p(n)
    undec_om = [0] * (C + 1)          # index N=0..C ; count classes at depth C
    undec_k = [0] * (C + 1)
    undec_sem = [0] * (C + 1)         # n=2 exact; n=3 filled from groups below
    fails = {"P1": [], "P2": [], "P3": [], "P4": []}
    max_shift = None                  # max L - (v+1) over v+1 <= C reps
    shift_hist = {}
    skipped_deep_v = 0
    n3_groups = [dict() for _ in range(C + 1)] if n == 3 else None
    inseparable = 0

    def coeff_iter():
        pc = p ** C
        idx = [0] * n
        while True:
            yield tuple(idx)
            i = 0
            while i < n:
                idx[i] += 1
                if idx[i] < pc:
                    break
                idx[i] = 0
                i += 1
            if i == n:
                return

    cnt = 0
    for a in coeff_iter():
        cnt += 1
        verdict, L = om_walk(n, a, p, C)
        D = disc_of(n, a)
        v = vp_int(abs(D), p) if D != 0 else None
        if D == 0:
            inseparable += 1
        # oracle + P1
        ot = oracle_type(n, a, p)
        if verdict is not None and ot is not None and verdict != ot:
            fails["P1"].append((a, verdict, ot))
        # P3 / P4 ceiling+Krasner shifts
        if v is not None and v + 1 <= C:
            s = L - (v + 1)
            shift_hist[s] = shift_hist.get(s, 0) + 1
            max_shift = s if max_shift is None else max(max_shift, s)
            if s > 0:
                fails["P3"].append((a, L, v))
            if L > max(1, 2 * v + 1):
                fails["P4"].append((a, L, v))
        elif v is None and D != 0:
            skipped_deep_v += 1
        elif D == 0:
            pass
        # aggregate undecided counts (class of depth-C rep at level N: L > N)
        for N in range(0, C + 1):
            if L > N:
                undec_om[N] += 1
            if D == 0 or v is None or 2 * v + 1 > N:
                undec_k[N] += 1
        # semantic side
        if n == 2:
            NS = _QSEM(a[1], a[0], p, C)
            for N in range(0, C + 1):
                if NS > N:
                    undec_sem[N] += 1
            if NS > L:                # P2 pointwise floor: OM decided => sem decided
                fails["P2"].append((a, L, NS))
        else:
            for N in range(0, C + 1):
                key = tuple(ai % p ** N for ai in a)
                gr = n3_groups[N].setdefault(key, [set(), C + 2])
                if ot is not None:
                    gr[0].add(ot)
                gr[1] = min(gr[1], L)
        if cnt % 200000 == 0:
            log(f"   ... {cnt}/{total}  ({time.time()-t0:.0f}s)")
    # n=3 semantic lower bound + pointwise floor
    if n == 3:
        for N in range(0, C + 1):
            bad = 0
            for key, (types, Lmin) in n3_groups[N].items():
                if len(types) >= 2:
                    bad += 1
                    if Lmin <= N:
                        fails["P2"].append((key, N, Lmin))
            # scale group count to depth-C member count for common normalization
            undec_sem[N] = bad * p ** (n * (C - N))
    # tables (fractions of Haar mass, exact rationals -> floats)
    tab = {}
    envfail = []
    monofail = []
    import math
    for N in range(0, C + 1):
        u_om = undec_om[N] / total
        u_k = undec_k[N] / total
        u_s = undec_sem[N] / total
        env = (n - 1) * p ** (-max(0, math.ceil((N - w) / (n - 1)))) if N > 0 else 1.0
        lean2 = (N // 2 + 1) * p ** (-(N - 1)) if (n == 2 and N >= 1) else None
        tab[N] = {"undec_OM": u_om, "undec_K": u_k,
                  ("undec_sem_exact" if n == 2 else "undec_sem_lower"): u_s,
                  "env_transfer": env, **({"env_lean_n2": lean2} if lean2 else {})}
        if N >= 1 and u_om > env + 1e-15:
            envfail.append(N)
        if N >= 1 and undec_om[N] > undec_om[N - 1]:
            monofail.append(N)
        if n == 2 and lean2 is not None and u_om > lean2 + 1e-15:
            envfail.append(("lean2", N))
    res = {
        "n": n, "p": p, "C": C, "classes": total, "w": w,
        "inseparable_reps": inseparable, "v_unresolved_reps": skipped_deep_v,
        "max_shift_L_minus_v_minus_1": max_shift,
        "shift_hist": {str(k): v for k, v in sorted(shift_hist.items())},
        "tables": tab,
        "P1_sound_fails": len(fails["P1"]), "P2_floor_fails": len(fails["P2"]),
        "P3_ceiling_fails": len(fails["P3"]), "P4_krasner_fails": len(fails["P4"]),
        "P5_env_fails": [str(x) for x in envfail], "P5_mono_fails": monofail,
        "fail_examples": {k: v[:5] for k, v in fails.items() if v},
        "seconds": round(time.time() - t0, 1),
    }
    ok = (not fails["P1"] and not fails["P2"] and not fails["P3"]
          and not fails["P4"] and not envfail and not monofail)
    res["verdict"] = "PASS" if ok else "FAIL"
    log(f"   verdict={res['verdict']}  max_shift={max_shift} "
        f"P1/P2/P3/P4 fails={len(fails['P1'])}/{len(fails['P2'])}/"
        f"{len(fails['P3'])}/{len(fails['P4'])}  env/mono fails="
        f"{len(envfail)}/{len(monofail)}  [{res['seconds']}s]")
    return res


def selftest(log):
    """Anchors with hand-computed L and types (wild included)."""
    cases = [
        # (n, coeffs(asc), p, C, expected_type, expected_L_max)
        (2, (1, 1), 2, 12, ((1, 2),), 1),           # x^2+x+1 irred mod 2
        (2, (2, 0), 2, 12, ((2, 1),), 3),           # x^2+2: v(disc)=3? L<=v+1
        (2, (-9, 0), 2, 12, ((1, 1), (1, 1)), 3),   # a=9=1+8: splits, L<=3
        (2, (0, -1), 3, 12, ((1, 1), (1, 1)), 1),   # x(x-1)
        (2, (-3, 0), 3, 12, ((2, 1),), 2),          # x^2-3 ram
        (3, (-3, 0, 0), 3, 12, ((3, 1),), 2),       # x^3-3 wild Eisenstein
        (3, (2, 0, 0), 2, 12, ((3, 1),), 2),        # x^3+2
        (3, (-1, 0, 0), 2, 12, ((1, 1), (1, 2)), 1),  # x^3-1 mod 2 =(x+1)(x^2+x+1)
    ]
    bad = 0
    for (n, a, p, C, et, eL) in cases:
        vv, L = om_walk(n, a, p, C)
        okv = (vv == et) and (L <= eL)
        if not okv:
            bad += 1
            log(f"   SELFTEST FAIL: n={n} a={a} p={p}: got {vv} L={L}, "
                f"want {et} L<={eL}")
    # ceiling anchors L <= v+1 on the worked families
    for m in range(1, 8):
        a = (0, -(3 ** m))                           # x^2 - 3^m x: v=2m
        vv, L = om_walk(2, a, 3, 20)
        if not (vv == ((1, 1), (1, 1)) and L <= 2 * m + 1):
            bad += 1
            log(f"   SELFTEST FAIL: split family m={m}: {vv} L={L}")
    log(f"   selftest: {'PASS' if bad == 0 else f'{bad} FAILURES'}")
    return bad == 0


def main():
    logpath = os.path.join(HERE, "logs",
                           f"O4T_transfer_{time.strftime('%Y%m%d_%H%M%S')}.log")
    os.makedirs(os.path.dirname(logpath), exist_ok=True)
    lf = open(logpath, "w")

    def log(msg):
        print(msg, flush=True)
        lf.write(msg + "\n")
        lf.flush()

    global _QSEM
    _QSEM = _load_n1_qsem()
    log("O4T drainage-transfer falsifier (preregistered P1-P6; see docstring)")
    if not selftest(log):
        log("SELFTEST FAILED -- aborting before production run")
        sys.exit(2)
    quick = "--quick" in sys.argv
    configs = ([(2, 2, 7), (2, 3, 4), (3, 2, 4)] if quick else
               [(2, 2, 10), (2, 3, 6), (2, 5, 4), (3, 2, 5), (3, 3, 4)])
    out = {"preregistered": "P1 sound / P2 floor / P3 ceiling L<=v+1 / "
                            "P4 Krasner shift<=0 / P5 envelope+monotone / P6 lean-n2",
           "configs": []}
    allpass = True
    for (n, p, C) in configs:
        r = run_config(n, p, C, log)
        out["configs"].append(r)
        allpass = allpass and (r["verdict"] == "PASS")
    out["overall"] = "ALL PASS" if allpass else "FAILURES PRESENT"
    rp = os.path.join(HERE, "results", "O4T_transfer_results.json")
    os.makedirs(os.path.dirname(rp), exist_ok=True)
    with open(rp, "w") as fh:
        json.dump(out, fh, indent=1)
    log(f"OVERALL: {out['overall']}  -> {rp}")
    sys.exit(0 if allpass else 1)


if __name__ == "__main__":
    main()
