#!/usr/bin/env python3
"""n3_family_check.py -- numeric cross-check of the n = 3 (monic cubic) certificate families.

SETTING.  O is a complete DVR with residue field of size q (think Z_p, q = p).  For a monic
cubic  f(X) = X^3 + a2 X^2 + a1 X + a0  over O, its SPLITTING TYPE sigma is the multiset of
pairs (e,f) = (ramification index, residue degree) of the monic irreducible factors of f
over O.  For cubics there are exactly five types:

    S   = {(1,1),(1,1),(1,1)}   three linear factors                 ("split")
    LI  = {(1,1),(1,2)}         linear x inert quadratic
    I   = {(1,3)}               irreducible, unramified              ("cubic inert")
    LR  = {(1,1),(2,1)}         linear x ramified quadratic
    R   = {(3,1)}               totally ramified

Predicted densities (Phi := q^4+q^3+q^2+q+1), from the project's informal corpus:

    R_S  = q^3(q^2-q+1) / (6(q+1)Phi)      R_LI = q^3(q^2+q+1) / (2(q+1)Phi)
    R_I  = q^3(q+1) / (3Phi)               R_LR = q(q^3+q+1) / ((q+1)Phi)
    R_R  = (q^2+1) / Phi                   (these sum to exactly 1; asserted below)

A level-N COEFFICIENT CLASS is (a0,a1,a2) mod p^N.  A class is sigma-DECIDED if EVERY lift of
it to O has splitting type sigma.  decided(sigma,N)/q^(3N) increases to the density as N -> oo,
so any set of certified-decided classes gives a LOWER bound for its density and, via
1 - (sum of the other four lower bounds), an UPPER bound.

v(x) denotes the p-adic valuation, with v(0) = N inside Z/p^N (i.e. "v >= N, exact value
unknown").  Bars denote reduction mod p.

--------------------------------------------------------------------------------------------
PART 1 -- the five Lean certificate families, brute-forced against their closed forms.

  F_I   ("residually irreducible cubic", level 1, type I):
        the residue cubic X^3 + a2b X^2 + a1b X + a0b has NO root in F_p.
        closed form: (p^3 - p)/3 classes at level 1, hence (p^3-p)/3 * p^(3(N-1)) at level N.

  F_LI  ("linear x residually irreducible quadratic", level 1, type LI):
        the residue cubic factors as (X - rho)(X^2 - b1 X + b0) with X^2 - b1 X + b0 having
        no root in F_p.   closed form: p^2(p-1)/2 at level 1, times p^(3(N-1)).

  F_LR  ("linear x Eisenstein quadratic", level 2, type LR):
        v(a2) = 0, v(a1) >= 1, v(a0) = 1 exactly.
        closed form at level 2: p^2(p-1)^2;  at level N >= 2: p^2(p-1)^2 * p^(3(N-2)).

  F_R   ("Eisenstein cubic", level 2, type R):
        v(a2) >= 1, v(a1) >= 1, v(a0) = 1 exactly.
        closed form at level 2: p^2(p-1);   at level N >= 2: p^2(p-1) * p^(3(N-2)).

  F_S3  ("three distinct residue roots", level 1, type S):
        the residue cubic has three distinct roots in F_p.
        closed form: C(p,3) at level 1, times p^(3(N-1)).  Empty at p = 2.

  F_Sdeep ("deep split", level 3, type S):
        the single class (a0,a1,a2) = (0, p, -(1+p)) mod p^3, i.e. the class of X(X-1)(X-p).
        closed form: 1 class at level 3, p^(3(N-3)) at level N >= 3.

  The five types' lower bounds use L_S = (#F_S3 + #F_Sdeep)/p^(3N); the six families are
  pairwise disjoint (asserted by the brute force).

--------------------------------------------------------------------------------------------
PART 2 -- a genuine n = 3 decider (Newton polygon / Ore, with recentring refinement).

  certify(f mod p^N) returns a splitting type or None ("undecided").  It is SOUND by
  construction: it only returns a type when the finite-precision data forces that type for
  every lift.  The rules, in order:

    (1) residue squarefree  ->  Hensel: each irreducible residue factor of degree d gives an
        unramified factor (1,d).
    (2) residue = (X-rho)^2 (X-tau), rho != tau  ->  Newton-lift the simple root tau, divide
        it out ((1,1) factor), recurse on the quadratic cofactor (known to the same precision).
    (3) residue = (X-rho)^n  ->  recentre X -> X + rho, then read the Newton polygon.
        Coefficients are only known mod p^P_i, so v(c_i) is EXACT iff v(c_i) < P_i.  The hull
        is built from the exact points plus (n,0); every inexact point must lie STRICTLY above
        it, otherwise the class is declared undecided.  If the leftmost exact point is at
        x = 1, the (unknown) leftmost segment has length 1 and therefore contributes a (1,1)
        factor regardless -- allowed provided the convexity margin P_0 > v_1 + |slope_1| holds.
        Each hull segment of slope -h/e (lowest terms) and horizontal length l gives residual
        degree d = l/e; d = 1 gives a factor (e,1); d > 1 (which for degree <= 3 forces e = 1)
        gives the residual polynomial R(y) over F_p:
          - R squarefree: each irreducible factor of degree s gives a factor (e,s)  [Ore];
          - R not squarefree: it has a unique repeated root r (r != 0, since the segment's
            left endpoint is a vertex); REFINE by translating the whole polynomial by
            t = p^h * r and recursing (the splitting type is translation invariant).

  Counting uses the translation action f(X) -> f(X+c): the splitting type, and hence
  decidedness, is invariant, so it suffices to enumerate orbit representatives.  For p != 3,
  3 is a unit so a2 normalises to 0 (orbit size p^N, p^(2N) reps).  For p = 3 one normalises
  a2 into {0,1,2} (3^(2N+1) reps, each with 3^(N-1) distinct translates).  The orbit count is
  cross-checked against full enumeration for the small (p,N).

  The corpus predicts an undecided count U(q,N) = q * u(q,N) with u(q,1) = 1, u(q,2) = q^2,
  u(q,3) = q^4, u(q,4) = q^6 + (q-1)^2 q^3, and u(2,7) = 5664.  We report the comparison
  WITHOUT tuning the decider to fit.

Pure standard library (no sympy needed), exact integer / Fraction arithmetic, deterministic.
"""

import sys
from fractions import Fraction
from math import comb, gcd

# --------------------------------------------------------------------------------------
# predicted densities
# --------------------------------------------------------------------------------------

def predicted(q):
    Phi = q**4 + q**3 + q**2 + q + 1
    return {
        'S':  Fraction(q**3 * (q*q - q + 1), 6 * (q + 1) * Phi),
        'LI': Fraction(q**3 * (q*q + q + 1), 2 * (q + 1) * Phi),
        'I':  Fraction(q**3 * (q + 1), 3 * Phi),
        'LR': Fraction(q * (q**3 + q + 1), (q + 1) * Phi),
        'R':  Fraction(q*q + 1, Phi),
    }

TYPES = ['S', 'LI', 'I', 'LR', 'R']

# --------------------------------------------------------------------------------------
# small F_p polynomial helpers (coefficient lists are low -> high, monic)
# --------------------------------------------------------------------------------------

def fp_eval(coeffs, x, p):
    r = 0
    for c in reversed(coeffs):
        r = (r * x + c) % p
    return r

def fp_div_root(coeffs, r, p):
    """Divide the monic poly `coeffs` (low->high) by (X - r); r must be a root."""
    hi = list(reversed(coeffs))
    b = [hi[0] % p]
    for k in range(1, len(hi)):
        b.append((hi[k] + r * b[-1]) % p)
    assert b[-1] == 0, "fp_div_root: not a root"
    return list(reversed(b[:-1]))

def fp_factor_shape(coeffs, p):
    """Monic poly of degree <= 3 over F_p -> list of (degree, multiplicity).

    Valid for degree <= 3: after stripping linear factors the remainder has no root in F_p,
    hence is irreducible (degree 2 or 3) and can only occur with multiplicity 1.
    """
    work = [c % p for c in coeffs]
    assert work[-1] == 1, "fp_factor_shape wants a monic polynomial"
    out = []
    for r in range(p):
        m = 0
        while len(work) > 1 and fp_eval(work, r, p) == 0:
            work = fp_div_root(work, r, p)
            m += 1
        if m:
            out.append((1, m, r))
    d = len(work) - 1
    if d > 0:
        assert d >= 2, "degree-1 leftover must have a root"
        out.append((d, 1, None))
    return out

# --------------------------------------------------------------------------------------
# p-adic helpers with finite precision
# --------------------------------------------------------------------------------------

def vp(x, p):
    """Exact valuation of a nonzero integer."""
    assert x != 0
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def val_cap(x, p, prec):
    """(v, exact) for a coefficient known mod p^prec.  v = prec, exact = False means v >= prec."""
    assert 0 <= prec <= 64
    x %= p ** prec
    if x == 0:
        return prec, False
    return vp(x, p), True

def translate(c, P, p, t):
    """Substitute X -> X + t in X^n + sum c_i X^i.  Returns (new c, new P).

    c_i is known mod p^(P_i); the leading coefficient 1 is exact.  A product c_j * m is known
    mod p^(P_j + v(m)), so the new precision is the min over the contributing terms.
    """
    n = len(c)
    fc = list(c) + [1]
    fP = list(P) + [None]                 # None = exact
    nc, nP = [0] * n, [None] * n
    for i in range(n):
        s, pr = 0, None
        for j in range(i, n + 1):
            m = comb(j, i) * (t ** (j - i))
            if m == 0:
                continue
            s += fc[j] * m
            if fP[j] is not None:
                cand = fP[j] + vp(m, p)
                pr = cand if pr is None else min(pr, cand)
        nc[i], nP[i] = s, pr
    for i in range(n):
        if nP[i] is not None:
            nc[i] %= p ** nP[i]
    return nc, nP

def lower_hull(pts):
    """Lower convex hull of points with distinct x, sorted by x; collinear points dropped."""
    hull = []
    for pt in sorted(pts):
        while len(hull) >= 2:
            (x0, y0), (x1, y1) = hull[-2], hull[-1]
            cross = (x1 - x0) * (pt[1] - y0) - (y1 - y0) * (pt[0] - x0)
            if cross <= 0:
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull

def hull_height(hull, x):
    """Fraction height of the hull chain at abscissa x (x within the hull's span)."""
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        if x1 <= x <= x2:
            return Fraction(y1) + Fraction((y2 - y1) * (x - x1), x2 - x1)
    raise ValueError("x outside hull span")

# --------------------------------------------------------------------------------------
# the decider
# --------------------------------------------------------------------------------------

TYPE_NAME = {
    ((1, 1), (1, 1), (1, 1)): 'S',
    ((1, 1), (1, 2)): 'LI',
    ((1, 3),): 'I',
    ((1, 1), (2, 1)): 'LR',
    ((3, 1),): 'R',
}

def certify(c, P, p, depth=0, maxdepth=24):
    """Sound certifier.  Returns a sorted tuple of (e,f) pairs, or None if undecided."""
    n = len(c)
    if n == 0:
        return ()
    if n == 1:
        return ((1, 1),)
    if depth > maxdepth:
        return None
    if any(pp is None or pp < 1 for pp in P):
        return None

    fb = [ci % p for ci in c] + [1]
    facs = fp_factor_shape(fb, p)

    if all(m == 1 for (_, m, _) in facs):                       # (1) residue squarefree
        return tuple(sorted((1, d) for (d, _, _) in facs))

    rep = [(d, m, r) for (d, m, r) in facs if m >= 2]
    assert len(rep) == 1 and rep[0][0] == 1, "degree <= 3: a unique repeated LINEAR factor"
    rho = rep[0][2]
    simple = [(d, m, r) for (d, m, r) in facs if m == 1]

    if simple:                                                  # (2) split off the simple root
        assert n == 3 and len(simple) == 1 and simple[0][0] == 1
        M = min(P)
        mod = p ** M
        tau = simple[0][2]
        for _ in range(M + 2):                                  # Newton iteration (simple root)
            h = (tau**3 + c[2] * tau * tau + c[1] * tau + c[0]) % mod
            hp = (3 * tau * tau + 2 * c[2] * tau + c[1]) % mod
            assert hp % p != 0
            tau = (tau - h * pow(hp, -1, mod)) % mod
        assert (tau**3 + c[2] * tau * tau + c[1] * tau + c[0]) % mod == 0
        b = (c[2] + tau) % mod
        cc = (c[1] + tau * b) % mod
        assert (-tau * cc) % mod == c[0] % mod, "Hensel division consistency"
        sub = certify([cc, b], [M, M], p, depth + 1, maxdepth)
        return None if sub is None else tuple(sorted(((1, 1),) + sub))

    # (3) residue = (X - rho)^n : recentre and read the Newton polygon
    c2, P2 = translate(c, P, p, rho)
    vs = [val_cap(c2[i], p, P2[i]) for i in range(n)]
    assert all(v >= 1 for (v, _) in vs), "recentred: all coefficients divisible by p"

    exact_pts = [(i, vs[i][0]) for i in range(n) if vs[i][1]] + [(n, 0)]
    x0 = min(x for x, _ in exact_pts)
    hull = lower_hull(exact_pts)

    for i in range(n):
        if not vs[i][1] and i > x0:
            if not Fraction(vs[i][0]) > hull_height(hull, i):
                return None

    extra = ()
    if x0 == 1:
        (x1, y1), (x2, y2) = hull[0], hull[1]
        slope_mag = Fraction(y1 - y2, x2 - x1)
        if not Fraction(vs[0][0]) > Fraction(y1) + slope_mag:
            return None
        extra = ((1, 1),)
    elif x0 >= 2:
        return None

    factors = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        ell, delta = x2 - x1, y1 - y2
        assert delta > 0, "recentred polygon has strictly negative slopes"
        d = gcd(delta, ell)
        e, h = ell // d, delta // d
        if d == 1:
            factors.append((e, 1))
            continue
        assert e == 1, "degree <= 3: residual degree > 1 forces e = 1"
        res = []
        for k in range(d + 1):
            x = x1 + k * e
            hgt = y1 - k * h
            if x == n:
                res.append(1 % p)
            elif vs[x][1] and vs[x][0] == hgt:
                res.append((c2[x] // p**hgt) % p)
            else:
                res.append(0)
        assert res[0] % p != 0 and res[-1] % p != 0, "segment endpoints are vertices"
        inv = pow(res[-1], -1, p)
        R = [(r * inv) % p for r in res]
        rfacs = fp_factor_shape(R, p)
        if all(m == 1 for (_, m, _) in rfacs):
            for (dd, _, _) in rfacs:
                factors.append((e, dd))
        else:
            reps = [(dd, m, r) for (dd, m, r) in rfacs if m >= 2]
            assert len(reps) == 1 and reps[0][0] == 1, "deg <= 3 residual: one repeated root"
            r = reps[0][2]
            assert r % p != 0, "repeated residual root cannot be 0"
            c3, P3 = translate(c2, P2, p, p**h * r)
            return certify(c3, P3, p, depth + 1, maxdepth)

    out = tuple(sorted(extra + tuple(factors)))
    assert sum(e * f for e, f in out) == n, "degrees must add up"
    return out

def certify_type(a0, a1, a2, p, N):
    t = certify([a0, a1, a2], [N, N, N], p)
    return None if t is None else TYPE_NAME[t]

# --------------------------------------------------------------------------------------
# PART 1
# --------------------------------------------------------------------------------------

def level1_label(r0, r1, r2, p):
    """Label of the residue cubic X^3 + r2 X^2 + r1 X + r0: 'I', 'LI', 'S3' or None."""
    facs = fp_factor_shape([r0, r1, r2, 1], p)
    shape = sorted((d, m) for (d, m, _) in facs)
    if shape == [(3, 1)]:
        return 'I'
    if shape == [(1, 1), (2, 1)]:
        return 'LI'
    if shape == [(1, 1), (1, 1), (1, 1)]:
        return 'S3'
    return None

def part1(p, N, fails):
    mod = p ** N
    box = mod ** 3
    valtab = [N] * mod
    for x in range(1, mod):
        valtab[x] = vp(x, p)
    lab = {}
    for r2 in range(p):
        for r1 in range(p):
            for r0 in range(p):
                lab[(r0, r1, r2)] = level1_label(r0, r1, r2, p)

    cnt = {k: 0 for k in ['I', 'LI', 'S3', 'LR', 'R', 'Sdeep']}
    deep = (0, p % mod, (-(1 + p)) % mod) if N >= 3 else None
    m3 = p ** 3 if N >= 3 else None
    overlap = 0

    for a2 in range(mod):
        r2, v2 = a2 % p, valtab[a2]
        for a1 in range(mod):
            r1, v1 = a1 % p, valtab[a1]
            labs = [lab[(r0, r1, r2)] for r0 in range(p)]
            # F_LR / F_R are level-2 families: "v(a0) = 1 exactly" is not expressible at N = 1
            isLR = (N >= 2 and v2 == 0 and v1 >= 1)
            isR = (N >= 2 and v2 >= 1 and v1 >= 1)
            deep21 = (N >= 3 and a1 % m3 == p % m3 and a2 % m3 == (-(1 + p)) % m3)
            for a0 in range(mod):
                hits = 0
                L = labs[a0 % p]
                if L is not None:
                    cnt[L] += 1
                    hits += 1
                if (isLR or isR) and valtab[a0] == 1:
                    cnt['LR' if isLR else 'R'] += 1
                    hits += 1
                if deep21 and a0 % m3 == 0:
                    cnt['Sdeep'] += 1
                    hits += 1
                if hits > 1:
                    overlap += 1

    if overlap:
        fails.append(f"p={p} N={N}: {overlap} classes lie in two families (should be disjoint)")

    closed = {
        'I':     (p**3 - p) // 3 * p**(3 * (N - 1)),
        'LI':    p*p * (p - 1) // 2 * p**(3 * (N - 1)),
        'S3':    comb(p, 3) * p**(3 * (N - 1)),
        'LR':    p*p * (p - 1)**2 * p**(3 * (N - 2)) if N >= 2 else None,
        'R':     p*p * (p - 1) * p**(3 * (N - 2)) if N >= 2 else None,
        'Sdeep': p**(3 * (N - 3)) if N >= 3 else None,
    }
    rows = []
    for fam in ['I', 'LI', 'S3', 'LR', 'R', 'Sdeep']:
        want = closed[fam]
        got = cnt[fam]
        if want is None:
            rows.append((fam, got, None, 'n/a (family needs a deeper level)'))
            if got:
                fails.append(f"p={p} N={N} {fam}: {got} hits below the family's own level")
            continue
        ok = (got == want)
        if not ok:
            fails.append(f"p={p} N={N} {fam}: brute {got} != closed {want}")
        rows.append((fam, got, want, 'OK' if ok else 'MISMATCH'))

    lower = {
        'I':  Fraction(cnt['I'], box),
        'LI': Fraction(cnt['LI'], box),
        'LR': Fraction(cnt['LR'], box),
        'R':  Fraction(cnt['R'], box),
        'S':  Fraction(cnt['S3'] + cnt['Sdeep'], box),
    }
    return rows, lower, box

def run_part1(fails):
    print("=" * 94)
    print("PART 1 -- the five Lean certificate families: brute force vs closed form")
    print("=" * 94)
    print(f"{'p':>2} {'N':>2}  {'family':<7} {'brute force':>12} {'closed form':>12}  {'verdict':<34}")
    print("-" * 94)
    lowers = {}
    for p in (2, 3, 5):
        for N in (1, 2, 3):
            box = p ** (3 * N)
            if box > 2 * 10**6:
                print(f"{p:>2} {N:>2}  (skipped: p^(3N) = {box} > 2e6; closed forms only)")
                continue
            rows, lower, _ = part1(p, N, fails)
            for fam, got, want, verdict in rows:
                w = '-' if want is None else str(want)
                print(f"{p:>2} {N:>2}  {'F_' + fam:<7} {got:>12} {w:>12}  {verdict:<34}")
            lowers[(p, N)] = lower
            print("-" * 94)
    return lowers

def run_brackets(lowers, fails):
    print()
    print("=" * 94)
    print("PART 1(b) -- density brackets from the level-3 certified families")
    print("=" * 94)
    for p in (2, 3, 5):
        if (p, 3) not in lowers:
            continue
        low = lowers[(p, 3)]
        pred = predicted(p)
        assert sum(pred.values()) == 1, "predicted densities must sum to 1"
        tot = sum(low.values())
        print(f"\n  q = p = {p}   (level N = 3, box = p^9 = {p**9})")
        print(f"  {'type':<5} {'lower':>10} {'upper':>10} {'predicted':>12}   "
              f"{'lower(dec)':>11} {'upper(dec)':>11} {'pred(dec)':>11}  verdict")
        for s in TYPES:
            lo = low[s]
            hi = 1 - (tot - lo)
            inside = lo <= pred[s] <= hi
            if not inside:
                fails.append(f"p={p} type {s}: predicted {pred[s]} outside [{lo}, {hi}]  <<< CONTAINMENT FAILURE")
            print(f"  {s:<5} {str(lo):>10} {str(hi):>10} {str(pred[s]):>12}   "
                  f"{float(lo):>11.6f} {float(hi):>11.6f} {float(pred[s]):>11.6f}  "
                  f"{'inside' if inside else 'OUTSIDE <<<'}")
        print(f"  sum of lower bounds = {tot} = {float(tot):.6f}   "
              f"{'OK (<= 1)' if tot <= 1 else 'IMPOSSIBLE (> 1) <<<'}")
        if tot > 1:
            fails.append(f"p={p}: certified lower bounds sum to {tot} > 1")

# --------------------------------------------------------------------------------------
# PART 2
# --------------------------------------------------------------------------------------

def residue_branch(a0, a1, a2, p):
    """'sqfree' | 'dbl' ((X-r)^2(X-s)) | 'trpl' ((X-r)^3)."""
    facs = fp_factor_shape([a0 % p, a1 % p, a2 % p, 1], p)
    mm = max(m for (_, m, _) in facs)
    return 'sqfree' if mm == 1 else ('trpl' if mm == 3 else 'dbl')

def orbit_reps(p, N):
    """(representatives, orbit size).  Translation X -> X + c acts; a2 -> a2 + 3c."""
    mod = p ** N
    if p != 3:
        reps = [(a0, a1, 0) for a1 in range(mod) for a0 in range(mod)]
        return reps, mod
    reps = [(a0, a1, a2) for a2 in range(3) for a1 in range(mod) for a0 in range(mod)]
    return reps, 3 ** (N - 1)

def part2_counts(p, N, use_orbits=True):
    counts = {t: 0 for t in TYPES}
    undec = 0
    undec_branch = {'sqfree': 0, 'dbl': 0, 'trpl': 0}
    if use_orbits:
        reps, w = orbit_reps(p, N)
    else:
        mod = p ** N
        reps = [(a0, a1, a2) for a2 in range(mod) for a1 in range(mod) for a0 in range(mod)]
        w = 1
    for (a0, a1, a2) in reps:
        t = certify_type(a0, a1, a2, p, N)
        if t is None:
            undec += w
            undec_branch[residue_branch(a0, a1, a2, p)] += w
        else:
            counts[t] += w
    return counts, undec, undec_branch

def u_small(q, N):
    """Corpus u(q,N), where quoted."""
    u = {1: 1, 2: q**2, 3: q**4, 4: q**6 + (q - 1)**2 * q**3}
    if N in u:
        return u[N]
    if q == 2 and N == 7:
        return 5664
    return None

def u_corpus(q, N):
    """Corpus prediction U(q,N) = q * u(q,N) for the total undecided count, where known."""
    u = u_small(q, N)
    return None if u is None else q * u

def run_part2(fails, plan):
    print()
    print("=" * 94)
    print("PART 2 -- Newton-polygon / Ore decider: certified counts by type")
    print("=" * 94)
    prev = {}
    for p, Ns in plan:
        pred = predicted(p)
        print(f"\n  p = q = {p}")
        print(f"  {'N':>2} {'box':>10} " + " ".join(f"{t:>8}" for t in TYPES) +
              f" {'undec':>8} {'undec%':>8}   corpus U(q,N)")
        for N in Ns:
            counts, undec, ub = part2_counts(p, N)
            box = p ** (3 * N)
            assert sum(counts.values()) + undec == box, "counts must tile the box"
            U = u_corpus(p, N)
            if U is None:
                ustr = "(not given)"
            elif U == undec:
                ustr = f"{U}  MATCH"
            else:
                ustr = f"{U}  differs by {undec - U:+d}"
            print(f"  {N:>2} {box:>10} " + " ".join(f"{counts[t]:>8}" for t in TYPES) +
                  f" {undec:>8} {100.0*undec/box:>7.3f}%   {ustr}")
            us = u_small(p, N)
            note = "" if us is None else (
                f"  [corpus u(q,N) = {us}: {'MATCHES trpl' if us == ub['trpl'] else 'differs from trpl by %+d' % (ub['trpl'] - us)}]")
            print(f"     undecided by residue branch: (X-r)^2(X-s): {ub['dbl']}   "
                  f"(X-r)^3: {ub['trpl']}   squarefree: {ub['sqfree']}{note}")
            # monotonicity of certified counts (as fractions) and level consistency
            for t in TYPES:
                f_now = Fraction(counts[t], box)
                if (p, t) in prev and f_now < prev[(p, t)]:
                    fails.append(f"p={p} N={N} type {t}: certified fraction decreased")
                if f_now > pred[t]:
                    fails.append(f"p={p} N={N} type {t}: certified fraction {f_now} exceeds "
                                 f"predicted density {pred[t]}  <<<")
                prev[(p, t)] = f_now
            if ub['sqfree']:
                fails.append(f"p={p} N={N}: {ub['sqfree']} squarefree-residue classes undecided "
                             f"(Hensel should decide all of them)")
        print(f"  {'--':>2} {'target':>10} " + " ".join(f"{float(pred[t]):>8.4f}" for t in TYPES)
              + "      <- predicted densities R_sigma(q) (as fractions of the box)")
    print("""
  NOTE on the corpus prediction U(q,N) = q*u(q,N).  This decider's TOTAL undecided count does
  not equal U(q,N); the two are counting different things (at p=2, N=7 the corpus value 11328
  even EXCEEDS this decider's 11264, and since certification implies decidedness the true
  undecided count is <= 11264, so U cannot be "number of undecided level-N classes" in the
  sense used here).  What does line up is the TRIPLE-ROOT branch alone: the count of undecided
  classes whose residue cubic is (X-rho)^3 equals u(q,N) exactly at N = 2 and N = 3 for both
  q = 2 and q = 3 (4, 16 and 9, 81).  It departs at N = 1 (q rather than 1) and at N = 4, where
  the corpus's extra term (q-1)^2 q^3 (8 at q=2, 108 at q=3) is absent here -- i.e. this
  decider certifies those classes.  Reported as found; the decider was not tuned to fit.""")

def run_part2_validation(fails):
    """Cross-checks on the decider: orbit counting, level-to-level consistency, Part-1 families."""
    print()
    print("=" * 94)
    print("PART 2(b) -- validation of the decider")
    print("=" * 94)

    # (i) orbit counting vs full enumeration
    for p, N in [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3)]:
        a = part2_counts(p, N, use_orbits=True)
        b = part2_counts(p, N, use_orbits=False)
        ok = (a[0] == b[0] and a[1] == b[1] and a[2] == b[2])
        if not ok:
            fails.append(f"p={p} N={N}: orbit counting != full enumeration")
        print(f"  orbit-vs-full   p={p} N={N}: {'OK' if ok else 'MISMATCH'}")

    # (ii) refinement consistency: a class certified sigma at level N must have every level-N+1
    #      subclass certified sigma or undecided (never a different type)
    bad = 0
    for p, N in [(2, 2), (2, 3), (3, 2)]:
        mod = p ** N
        for a2 in range(mod):
            for a1 in range(mod):
                for a0 in range(mod):
                    t = certify_type(a0, a1, a2, p, N)
                    if t is None:
                        continue
                    for d2 in range(p):
                        for d1 in range(p):
                            for d0 in range(p):
                                s = certify_type(a0 + d0 * mod, a1 + d1 * mod,
                                                 a2 + d2 * mod, p, N + 1)
                                if s is not None and s != t:
                                    bad += 1
        print(f"  level-consistency p={p} N={N}->{N+1}: "
              f"{'OK' if bad == 0 else str(bad) + ' CONTRADICTIONS'}")
    if bad:
        fails.append(f"decider is UNSOUND: {bad} level-to-level type contradictions")

    # (iii) the Part-1 families must be certified with their claimed types
    fam_type = {'I': 'I', 'LI': 'LI', 'S3': 'S', 'LR': 'LR', 'R': 'R', 'Sdeep': 'S'}
    for p in (2, 3):
        N = 3
        mod = p ** N
        m3 = p ** 3
        bad_fam = {}
        for a2 in range(mod):
            for a1 in range(mod):
                for a0 in range(mod):
                    fams = []
                    L = level1_label(a0 % p, a1 % p, a2 % p, p)
                    if L:
                        fams.append(L)
                    v0 = vp(a0, p) if a0 != 0 else N
                    if v0 == 1 and a1 % p == 0:
                        fams.append('LR' if a2 % p else 'R')
                    if a0 % m3 == 0 and a1 % m3 == p % m3 and a2 % m3 == (-(1 + p)) % m3:
                        fams.append('Sdeep')
                    if not fams:
                        continue
                    t = certify_type(a0, a1, a2, p, N)
                    for f in fams:
                        if t != fam_type[f]:
                            bad_fam[f] = bad_fam.get(f, 0) + 1
        if bad_fam:
            fails.append(f"p={p}: Part-1 families not certified as claimed: {bad_fam}")
        print(f"  part1-families    p={p} N=3: "
              f"{'OK (all six families certified with the claimed type)' if not bad_fam else bad_fam}")


# --------------------------------------------------------------------------------------
# PART 3 -- the n = 3 STRUCTURE THEOREM (unit N3B), brute-forced over prime residue fields
#
# THEOREM (cubic_trichotomy, Lean: UniformityCheck.cubic_trichotomy).  Over ANY field K a monic
# cubic satisfies exactly one of
#     (T1) it has a SIMPLE root (F(rho) = 0 and F'(rho) != 0);
#     (T2) it has NO root in K;
#     (T3) it is (X - gamma)^3 for a unique gamma.
# This is the enumeration that gates the whole drainage argument: it says the only residual
# shapes WITHOUT a simple root are "irreducible" (already decided at level 1) and the perfect
# cube.  Checked here at the wild primes 2 and 3 and beyond.
# --------------------------------------------------------------------------------------

def cube_coeff(g, p):
    """Coefficient vector (c0,c1,c2) of (X - g)^3 over F_p."""
    return ((-g ** 3) % p, (3 * g ** 2) % p, (-3 * g) % p)

def run_part3(fails):
    print()
    print("=" * 94)
    print("PART 3 -- the structure theorem: simple root | no root | perfect cube")
    print("=" * 94)
    for p in (2, 3, 5, 7, 11, 13):
        bad = []
        n_t1 = n_t2 = n_t3 = 0
        for c2 in range(p):
            for c1 in range(p):
                for c0 in range(p):
                    coe = [c0, c1, c2, 1]
                    roots = [x for x in range(p) if fp_eval(coe, x, p) == 0]
                    simple = [x for x in roots
                              if (3 * x * x + 2 * c2 * x + c1) % p != 0]
                    cubes = [g for g in range(p) if cube_coeff(g, p) == (c0, c1, c2)]
                    t1, t2, t3 = bool(simple), not roots, bool(cubes)
                    if sum((t1, t2, t3)) != 1:
                        bad.append(((c0, c1, c2), t1, t2, t3))
                    n_t1 += t1; n_t2 += t2; n_t3 += t3
                    if len(cubes) > 1:
                        bad.append(("cubeCoeff not injective", (c0, c1, c2), cubes))
        # the shape breakdown predicted by the theorem
        n_irred = (p ** 3 - p) // 3
        ok = (not bad) and n_t2 == n_irred and n_t3 == p and n_t1 == p ** 3 - n_irred - p
        print(f"  trichotomy        p={p:2d}: T1(simple root)={n_t1:5d}  T2(no root)={n_t2:4d}"
              f"  T3(perfect cube)={n_t3:3d}   sum={n_t1+n_t2+n_t3:5d} = p^3={p**3:5d}   "
              f"{'OK' if ok else 'FAIL ' + str(bad[:3])}")
        if not ok:
            fails.append(f"part3-trichotomy p={p}")

    # the reducible lift that makes the level-1 {(1,3)} certificate EXHAUSTIVE
    # (Lean: UniformityCheck.inert3_decided_iff).  For every residue cubic WITH a root rho,
    # the vector  linQuadCoeff = (-rho*B0, B0 - rho*B1, B1 - rho)  with
    # (B0,B1) = (c1 + c2*rho + rho^2, c2 + rho)  reduces to the SAME class and is reducible.
    for p in (2, 3, 5, 7, 11):
        bad = 0
        n = 0
        for c2 in range(p):
            for c1 in range(p):
                for c0 in range(p):
                    coe = [c0, c1, c2, 1]
                    for rho in range(p):
                        if fp_eval(coe, rho, p) != 0:
                            continue
                        n += 1
                        B0 = (c1 + c2 * rho + rho * rho) % p
                        B1 = (c2 + rho) % p
                        got = ((-rho * B0) % p, (B0 - rho * B1) % p, (B1 - rho) % p)
                        if got != (c0, c1, c2):
                            bad += 1
        print(f"  reducible-lift    p={p:2d}: {n:5d} (class, root) pairs, "
              f"{'OK (the peeled lift reduces to the same class)' if not bad else f'FAIL {bad}'}")
        if bad:
            fails.append(f"part3-reducible-lift p={p}")

    # the triple-root stratum has exactly p^(3N-2) classes at level N
    for p in (2, 3, 5):
        for N in (1, 2, 3):
            mod = p ** N
            cnt = 0
            for a2 in range(mod):
                for a1 in range(mod):
                    for a0 in range(mod):
                        if any(cube_coeff(g, p) == (a0 % p, a1 % p, a2 % p) for g in range(p)):
                            cnt += 1
            pred = p ** (3 * N - 2)
            ok = cnt == pred
            print(f"  triple-stratum    p={p} N={N}: {cnt:7d} classes, predicted p^(3N-2)"
                  f"={pred:7d}  {'OK' if ok else 'FAIL'}")
            if not ok:
                fails.append(f"part3-triple-stratum p={p} N={N}")

# --------------------------------------------------------------------------------------
# PART 4 -- unit N3C: the four-case split, the recursion, and the exact inert value
#
# This is the numeric leg for N3_CHECK_2026-08-13.md sections 13.1-13.5.  Setting: O = Z_p,
# q = p, Phi = q^4+q^3+q^2+q+1.  B = (B0,B1,B2) is the RECENTRED coefficient vector of
# X^3 + B2 X^2 + B1 X + B0 with every Bi = 0 mod p (i.e. B = shiftVec a gamma lands in m^3,
# which by 13.1 is exactly the triple-root stratum).  Valuations are capped at the working
# precision (val_cap), so "v = K" means "v >= K, exact value unknown".
#
# Section 13.1's CORRECTED four-case split of the triple-root stratum, with its verdicts:
#
#     E : v(B0) = 1                    -> R  = {(3,1)}          Eisenstein
#     L : v(B0) >= 2, v(B1) = 1        -> LR = {(1,1),(2,1)}    strong Hensel at x0 = pi t
#     R : v(B0) = 2,  v(B1) >= 2       -> R  = {(3,1)}          no root + coprime norms
#     S : v(B0) >= 3, v(B1) >= 2       -> recurse on X = pi Y   typeOf_scale
#
# The correction to section 9.4 is the v(B1) refinement inside v(B0) = 2: at v(B1) = 1 the type
# is LR, NOT R (witness X^3 + pX + p^2, which has a root of valuation 1).  Checks 4b/4c test
# exactly that on real classes; 4d tests the level bookkeeping of the extraction (HYP.08);
# 4e sandwiches the claimed exact inert density q^3(q+1)/(3Phi) between certified-decided and
# decided+undecided; 4f tests the recursion (*) and its sharp form.
#
# All pass/fail decisions use exact Fraction arithmetic; floats are for display only.
# --------------------------------------------------------------------------------------

def R_inert(q):
    """The claimed exact inert density of section 13.5: q^3(q+1) / (3 Phi)."""
    Phi = q**4 + q**3 + q**2 + q + 1
    return Fraction(q**3 * (q + 1), 3 * Phi)

_PART2_MEMO = {}

def part2_counts_cached(p, N):
    """part2_counts(p, N) memoised (PARTS 2 and 4 ask for the same (p,N) several times)."""
    if (p, N) not in _PART2_MEMO:
        _PART2_MEMO[(p, N)] = part2_counts(p, N)
    return _PART2_MEMO[(p, N)]

def case_of(B0, B1, B2, p, K):
    """Section 13.1's four-case label of a recentred vector, from B mod p^K.  K >= 3.

    Returns (label, list of the four case booleans).  Every condition only has to separate
    v(B0) in {1, 2, >=3} and v(B1) in {1, >=2}, all of which are readable at cap K >= 3.
    """
    assert K >= 3, "the four-case split is a mod-p^3 condition; K >= 3 required"
    a = val_cap(B0, p, K)[0]
    b = val_cap(B1, p, K)[0]
    d = val_cap(B2, p, K)[0]
    assert a >= 1 and b >= 1 and d >= 1, "case_of wants a RECENTRED vector (all Bi in m)"
    flags = [a == 1, a >= 2 and b == 1, a == 2 and b >= 2, a >= 3 and b >= 2]
    labels = [lab for lab, f in zip('ELRS', flags) if f]
    return (labels[0] if len(labels) == 1 else None), flags

def check4a(fails):
    """4a -- section 13.5's fixed point: ((q^3-q)/(3q^3)) / (1 - q^-5) = q^3(q+1)/(3 Phi)."""
    print()
    print("=" * 94)
    print("PART 4 -- unit N3C: the four-case split, the recursion, and the exact inert value")
    print("=" * 94)
    print("\n  CHECK 4a -- the geometric fixed point I = (q^3-q)/(3q^3) + q^-5 I  (section 13.5)")
    print(f"  {'q':>3} {'LHS = level-1 mass / (1 - q^-5)':>34} {'RHS = q^3(q+1)/(3Phi)':>24} "
          f"{'decimal':>10}  verdict")
    for q in (2, 3, 5, 7, 11, 13):
        lhs = Fraction(q**3 - q, 3 * q**3) / (1 - Fraction(1, q**5))
        rhs = R_inert(q)
        ok = (lhs == rhs)
        if not ok:
            fails.append(f"4a q={q}: fixed point {lhs} != closed form {rhs}  <<<")
        # the same value must be the corpus R_I already used by PARTS 1-2
        corpus = predicted(q)['I']
        ok2 = (rhs == corpus)
        if not ok2:
            fails.append(f"4a q={q}: closed form {rhs} != corpus predicted()['I'] {corpus}  <<<")
        print(f"  {q:>3} {str(lhs):>34} {str(rhs):>24} {float(rhs):>10.6f}  "
              f"{'OK' if ok and ok2 else 'MISMATCH <<<'}"
              + ("" if ok2 else f"  corpus R_I = {corpus}"))
    for q, want in ((2, Fraction(8, 31)), (3, Fraction(36, 121))):
        got = R_inert(q)
        ok = (got == want and got == predicted(q)['I'])
        if not ok:
            fails.append(f"4a q={q}: R_I = {got}, expected {want} (= corpus {predicted(q)['I']})")
        print(f"  q = {q}: R_I = {got} = {float(got):.6f}   HMENU3/corpus value {want}   "
              f"{'OK' if ok else 'MISMATCH <<<'}")

def part4_case_scan(p, K):
    """Enumerate every recentred B mod p^K (all Bi = 0 mod p) and test 13.1's split.

    Returns a dict with the four case counts, the exhaustive/disjoint violations, the type
    verdicts per case, and the 13.1 refinement data inside v(B0) = 2 (check 4c).
    """
    want = {'E': 'R', 'L': 'LR', 'R': 'R'}          # section 13.1's verdicts (S recurses)
    res = {
        'counts': {c: 0 for c in 'ELRS'},
        'notone': [],                                # vectors in 0 or >= 2 cases
        'wrong': {c: [] for c in 'ELR'},             # certified type != predicted type
        'undec': {c: [] for c in 'ELR'},             # certifier returned None (a FAILURE)
        'refine': {'b1': 0, 'b2': 0},                # inside v(B0)=2: v(B1)=1 / v(B1)>=2
        'refine_wrong': {'b1': [], 'b2': []},
        'refine_undec': {'b1': [], 'b2': []},
    }
    step = p
    pk = p ** K
    for B0 in range(0, pk, step):
        a = val_cap(B0, p, K)[0]
        for B1 in range(0, pk, step):
            b = val_cap(B1, p, K)[0]
            for B2 in range(0, pk, step):
                lab, flags = case_of(B0, B1, B2, p, K)
                if lab is None:
                    res['notone'].append(((B0, B1, B2), flags))
                    continue
                res['counts'][lab] += 1
                if lab == 'S':
                    continue
                t = certify_type(B0, B1, B2, p, K)
                if t is None:
                    res['undec'][lab].append((B0, B1, B2))
                elif t != want[lab]:
                    res['wrong'][lab].append(((B0, B1, B2), t, want[lab]))
                if a == 2:                            # section 13.1's corrected refinement
                    key = 'b1' if b == 1 else 'b2'
                    exp = 'LR' if key == 'b1' else 'R'
                    res['refine'][key] += 1
                    if t is None:
                        res['refine_undec'][key].append((B0, B1, B2))
                    elif t != exp:
                        res['refine_wrong'][key].append(((B0, B1, B2), t, exp))
    return res

def check4b4c(fails, plan):
    """4b -- the split is exhaustive + disjoint and E/L/R have the predicted types.
       4c -- the section-13.1 correction: inside v(B0) = 2, v(B1) decides LR vs R."""
    print("\n  CHECK 4b -- the four-case split of the recentred (triple-root) stratum")
    print("           enumerating ALL (B0,B1,B2) mod p^K with B0=B1=B2=0 mod p")
    print(f"  {'p':>2} {'K':>2} {'vectors':>9} {'E':>8} {'L':>8} {'R':>8} {'S':>8}   "
          f"exactly-one-case   E,L,R types (R,LR,R)")
    scans = {}
    for p, K in plan:
        res = part4_case_scan(p, K)
        scans[(p, K)] = res
        tot = sum(res['counts'].values()) + len(res['notone'])
        box = (p ** (K - 1)) ** 3
        if tot != box or res['notone']:
            fails.append(f"4b p={p} K={K}: split not exhaustive/disjoint; "
                         f"{len(res['notone'])} bad vectors, e.g. {res['notone'][:3]}")
        nwrong = sum(len(v) for v in res['wrong'].values())
        nundec = sum(len(v) for v in res['undec'].values())
        for c in 'ELR':
            if res['wrong'][c]:
                fails.append(f"4b p={p} K={K} case {c}: {len(res['wrong'][c])} vectors have the "
                             f"WRONG certified type, e.g. {res['wrong'][c][:3]}  <<<")
            if res['undec'][c]:
                fails.append(f"4b p={p} K={K} case {c}: {len(res['undec'][c])} vectors UNDECIDED "
                             f"by the sound certifier although the Lean certificate decides them, "
                             f"e.g. {res['undec'][c][:3]}  <<< HUMAN LOOK")
            if res['counts'][c] == 0:
                fails.append(f"4b p={p} K={K}: case {c} is EMPTY (nothing was tested)")
        print(f"  {p:>2} {K:>2} {box:>9} " +
              " ".join(f"{res['counts'][c]:>8}" for c in 'ELRS') +
              f"   {'OK' if not res['notone'] and tot == box else 'VIOLATIONS <<<':<18}"
              f" {'all OK' if nwrong == 0 and nundec == 0 else f'{nwrong} wrong, {nundec} undecided <<<'}")
        if nundec:
            print(f"      *** {nundec} case-E/L/R vectors were left UNDECIDED by the sound "
                  f"certifier at p={p}, K={K}.")
            print(f"      *** Section 13.1 says E, L, R are level-3 DECIDEDNESS certificates, so "
                  f"this needs a human.")

    print("\n  CHECK 4c -- section 13.1's correction to section 9.4: inside v(B0) = 2, split on v(B1)")
    print("           9.4 read the whole v(B0)=2 stratum as R = {(3,1)}; 13.1 says v(B1) = 1 gives "
          "LR = {(1,1),(2,1)}")
    print(f"  {'p':>2} {'K':>2} {'v(B0)=2,v(B1)=1':>16} {'-> all LR?':>11} "
          f"{'v(B0)=2,v(B1)>=2':>17} {'-> all R?':>10}   both non-empty")
    for p, K in plan:
        res = scans[(p, K)]
        n1, n2 = res['refine']['b1'], res['refine']['b2']
        bad1 = res['refine_wrong']['b1'] + res['refine_undec']['b1']
        bad2 = res['refine_wrong']['b2'] + res['refine_undec']['b2']
        if bad1:
            fails.append(f"4c p={p} K={K}: v(B0)=2, v(B1)=1 is not uniformly LR: "
                         f"{len(bad1)} offenders, e.g. {bad1[:3]}  <<<")
        if bad2:
            fails.append(f"4c p={p} K={K}: v(B0)=2, v(B1)>=2 is not uniformly R: "
                         f"{len(bad2)} offenders, e.g. {bad2[:3]}  <<<")
        if n1 == 0 or n2 == 0:
            fails.append(f"4c p={p} K={K}: a sub-stratum of v(B0)=2 is EMPTY (n1={n1}, n2={n2})")
        print(f"  {p:>2} {K:>2} {n1:>16} {'yes' if not bad1 else 'NO <<<':>11} "
              f"{n2:>17} {'yes' if not bad2 else 'NO <<<':>10}   "
              f"{'yes' if n1 and n2 else 'NO <<<'}")

    # the explicit section-13.1 witness X^3 + pX + p^2, i.e. B = (p^2, p, 0)
    Kw = 6
    print(f"\n  CHECK 4c(ii) -- the witness F = X^3 + pX + p^2  (B = (p^2, p, 0)), at K = {Kw}")
    print(f"  {'p':>2} {'certified type':>15} {'13.1 claim':>11} {'roots x with p|x, F(x)=0 mod p^K':>36} "
          f"{'v(x)':>5} {'v(F(x))':>8} {'v(F1(x))':>9}  verdict")
    for p, _K in plan:
        B = (p * p, p, 0)
        t = certify_type(B[0], B[1], B[2], p, Kw)
        mod = p ** Kw
        roots = [x for x in range(0, mod, p)
                 if (x**3 + p * x + p * p) % mod == 0]
        # independent leg: a root of valuation EXACTLY 1 mod p^Kw, with v(F') = 1, so
        # v(F(x)) >= Kw > 2 = 2 v(F'(x)) and strong Hensel lifts it to a genuine root of O.
        good = []
        for x in roots:
            vx = val_cap(x, p, Kw)[0]
            vF = val_cap((x**3 + p * x + p * p) % mod, p, Kw)[0]
            vF1 = val_cap((3 * x * x + p) % mod, p, Kw)[0]
            if vx == 1 and vF1 == 1 and vF > 2 * vF1:
                good.append((x, vx, vF, vF1))
        ok = (t == 'LR') and bool(good)
        if t != 'LR':
            fails.append(f"4c(ii) p={p}: witness X^3+pX+p^2 certified {t}, section 13.1 claims LR  <<<")
        if not good:
            fails.append(f"4c(ii) p={p}: witness X^3+pX+p^2 has NO Hensel-liftable root of "
                         f"valuation 1 mod p^{Kw} (roots found: {roots})  <<<")
        show = good[0] if good else (None, None, None, None)
        print(f"  {p:>2} {str(t):>15} {'LR':>11} {str(roots):>36} "
              f"{str(show[1]):>5} {str(show[2]):>8} {str(show[3]):>9}  {'OK' if ok else 'FAIL <<<'}")
        print(f"      all {len(roots)} root(s) have valuation exactly 1: "
              f"{all(val_cap(x, p, Kw)[0] == 1 for x in roots)}; "
              f"strong Hensel applies (v(F) >= {Kw} > 2 = 2 v(F')) -> a genuine root of valuation 1, "
              f"so the type contains (1,1) and cannot be {{(3,1)}}")

def check4d(fails, plan):
    """4d -- typeOf_scale + section 13.3: the extraction X = pi Y preserves the type, and the
    level bookkeeping is the WEAKEST of the three coordinate precisions, K-3."""
    print("\n  CHECK 4d -- case S: the extraction d = (B0/p^3, B1/p^2, B2/p) preserves the type")
    print("           d0 is known mod p^(K-3), d1 mod p^(K-2), d2 mod p^(K-1); section 13.3 uses "
          "the WEAKEST, K-3")
    print(f"  {'p':>2} {'K':>2} {'case-S vectors':>14} {'compared':>9} {'agreed':>7} "
          f"{'B undec':>8} {'d undec':>8} {'both undec':>11}  verdict")
    for p, K in plan:
        M = K - 3
        assert M >= 1
        pk, pm = p ** K, p ** M
        n = agreed = bundec = dundec = bothundec = compared = 0
        bad = []
        for B0 in range(0, pk, p**3):
            for B1 in range(0, pk, p**2):
                for B2 in range(0, pk, p):
                    n += 1
                    tB = certify_type(B0, B1, B2, p, K)
                    d = ((B0 // p**3) % pm, (B1 // p**2) % pm, (B2 // p) % pm)
                    td = certify_type(d[0], d[1], d[2], p, M)
                    if tB is None and td is None:
                        bothundec += 1
                    elif tB is None:
                        bundec += 1
                    elif td is None:
                        dundec += 1
                    else:
                        compared += 1
                        if tB == td:
                            agreed += 1
                        else:
                            bad.append(((B0, B1, B2), tB, d, td))
        if bad:
            fails.append(f"4d p={p} K={K}: {len(bad)} case-S vectors where typeOf(B) != "
                         f"typeOf(extraction) although BOTH are certified, e.g. {bad[:3]}  <<<")
        print(f"  {p:>2} {K:>2} {n:>14} {compared:>9} {agreed:>7} {bundec:>8} {dundec:>8} "
              f"{bothundec:>11}  {'OK' if not bad else str(len(bad)) + ' CONTRADICTIONS <<<'}")

def check4e(fails, plan):
    """4e -- the exact inert density of section 13.5, sandwiched by brute force."""
    print("\n  CHECK 4e -- the claimed exact inert density R_I = q^3(q+1)/(3Phi), sandwiched")
    print("           D = classes certified {(1,3)}; U = classes the sound certifier leaves "
          "undecided; box = p^(3N)")
    print("           soundness gives  D/box <= genuineDensity <= (D+U)/box  (a class decided "
          "as another type cannot be inert)")
    print(f"  {'p':>2} {'N':>2} {'box':>9} {'D':>9} {'U':>7} {'D/box':>9} {'R_I':>9} "
          f"{'(D+U)/box':>10} {'width':>9}  {'sandwich':<9} lower-end gain")
    lowprev = {}
    for p, N in plan:
        counts, undec, _ = part2_counts_cached(p, N)
        box = p ** (3 * N)
        D, U = counts['I'], undec
        lo, hi, RI = Fraction(D, box), Fraction(D + U, box), R_inert(p)
        inside = (lo <= RI <= hi)
        if not inside:
            fails.append(f"4e p={p} N={N}: R_I = {RI} OUTSIDE the certified sandwich "
                         f"[{lo}, {hi}]  <<< the section-13.5 value is refuted")
        gain = '-'
        if p in lowprev:
            prevN, prevlo = lowprev[p]
            if lo < prevlo:
                fails.append(f"4e p={p}: certified inert fraction DECREASED from N={prevN} "
                             f"({prevlo}) to N={N} ({lo}) -- decided sets must be nested  <<<")
            gain = ('+' + str(float(lo - prevlo)) if lo > prevlo
                    else 'flat (no new inert class certified)')
        lowprev[p] = (N, lo)
        print(f"  {p:>2} {N:>2} {box:>9} {D:>9} {U:>7} {float(lo):>9.6f} {float(RI):>9.6f} "
              f"{float(hi):>10.6f} {float(hi - lo):>9.6f}  "
              f"{'inside' if inside else 'OUTSIDE <<<':<9} {gain}")
    print("      NOTE the pass/fail test on the lower end is MONOTONICITY (non-decreasing), which "
          "is all the")
    print("      mathematics gives: decided sets are nested under refinement, so the certified "
          "fraction cannot")
    print("      fall, but it may be FLAT at a level that certifies no new inert class (p=2, "
          "N=4->5->6 is flat).")

def check4f(fails, plan):
    """4f -- the recursion (*) of section 13.4, and its sharp (section 13.5) form."""
    print("\n  CHECK 4f -- the recursion (*): tripleUndecidedSeq(N) <= q^-2 undecidedSeq(N-3)")
    print("           T = level-N classes left undecided whose residue cubic is a perfect cube "
          "(X-g)^3 mod p")
    print("           U3 = ALL undecided classes at level N-3.  (*) <=> T <= p^7 U3;  sharp "
          "(q^-5, section 13.5) <=> T <= p^4 U3")
    # tie T's definition to PART 3's cube_coeff: the 'trpl' residue branch IS the cubeCoeff image
    for p in (2, 3, 5, 7):
        bad = 0
        for c2 in range(p):
            for c1 in range(p):
                for c0 in range(p):
                    is_cube = any(cube_coeff(g, p) == (c0, c1, c2) for g in range(p))
                    if is_cube != (residue_branch(c0, c1, c2, p) == 'trpl'):
                        bad += 1
        if bad:
            fails.append(f"4f p={p}: residue_branch=='trpl' differs from the cube_coeff image on "
                         f"{bad} residue vectors (so T is counting the wrong stratum)")
        print(f"  cube_coeff cross-check p={p:2d}: residue_branch=='trpl' <=> residue is "
              f"(X-g)^3 for some g: {'OK' if not bad else 'MISMATCH <<<'}")
    print(f"  {'p':>2} {'N':>2} {'T':>8} {'U3 (N-3)':>9} {'p^7 U3':>10} {'(*)':>5} "
          f"{'p^4 U3':>9} {'sharp':>6}   {'T/p^(3N)':>11} {'p^-2 U3/p^(3N-9)':>17}  ratio T/(p^4 U3)")
    sharp_all = True
    for p, N in plan:
        if N < 4:
            continue
        _, _, ub = part2_counts_cached(p, N)
        _, U3, _ = part2_counts_cached(p, N - 3)
        T = ub['trpl']
        b7, b4 = p**7 * U3, p**4 * U3
        ok7, ok4 = (T <= b7), (T <= b4)
        if not ok7:
            fails.append(f"4f p={p} N={N}: T = {T} > p^7 U3 = {b7} -- the Lean lemma "
                         f"card_undecidedTriple_le is CONTRADICTED  <<<")
        sharp_all = sharp_all and ok4
        lhs = Fraction(T, p ** (3 * N))
        rhs = Fraction(U3, p**2 * p ** (3 * (N - 3)))
        # the density form of (*) and the count form must be the SAME statement
        if (lhs <= rhs) != ok7:
            fails.append(f"4f p={p} N={N}: density form of (*) ({lhs} <= {rhs}) disagrees with the "
                         f"count form (T <= p^7 U3)  <<< bookkeeping bug")
        ratio = '-' if b4 == 0 else str(Fraction(T, b4))
        print(f"  {p:>2} {N:>2} {T:>8} {U3:>9} {b7:>10} {'OK' if ok7 else 'FAIL':>5} "
              f"{b4:>9} {'OK' if ok4 else 'FAIL':>6}   {float(lhs):>11.8f} {float(rhs):>17.8f}  "
              f"{ratio}")
    print(f"      SHARP form T <= p^4 U3 (the q^-5 constant section 13.5 needs for the exact "
          f"value): {'HOLDS on all rows' if sharp_all else 'FAILS on some row'}")
    print("      (reported, not asserted: 13.4 lands only the weaker q^-2 = p^7 U3 form, which is "
          "what the fails list tests)")

def run_part4(fails):
    import time
    t0 = time.time()
    # parameters: 4b/4c scan all p^(3(K-1)) recentred vectors mod p^K, so p=5 K=4 is the
    # expensive row (5^9 = 1953125 vectors, ~35 s).  4d needs K-3 >= 1 with K as large as
    # affordable.  4e/4f reuse PART 2's counts (memoised, no recomputation).
    plan_bc = [(2, 4), (3, 4), (5, 4)]
    plan_d = [(2, 6), (3, 5)]
    plan_ef = [(2, 4), (2, 5), (2, 6), (3, 3), (3, 4)]
    check4a(fails)
    print(f"\n  PARAMETERS -- 4b/4c: (p,K) = {plan_bc};  4c(ii) witness at K = 6;  "
          f"4d: (p,K) = {plan_d};")
    print(f"                4e/4f: (p,N) = {plan_ef} (reusing PART 2's certified counts).")
    check4b4c(fails, plan_bc)
    check4d(fails, plan_d)
    check4e(fails, plan_ef)
    check4f(fails, plan_ef)
    print(f"\n  PART 4 elapsed: {time.time() - t0:.1f} s")

# --------------------------------------------------------------------------------------

def main():
    fails = []
    lowers = run_part1(fails)
    run_brackets(lowers, fails)
    plan = [(2, [1, 2, 3, 4, 5, 6, 7, 8]), (3, [1, 2, 3, 4, 5])]
    run_part2(fails, plan)
    run_part2_validation(fails)
    run_part3(fails)
    run_part4(fails)
    print()
    print("=" * 94)
    if fails:
        print("FAILURES PRESENT:")
        for f in fails:
            print("  - " + f)
    else:
        print("ALL CHECKS PASSED")
    print("=" * 94)
    return 0 if not fails else 1

if __name__ == "__main__":
    sys.exit(main())
