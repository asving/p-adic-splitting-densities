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

def main():
    fails = []
    lowers = run_part1(fails)
    run_brackets(lowers, fails)
    plan = [(2, [1, 2, 3, 4, 5, 6, 7, 8]), (3, [1, 2, 3, 4, 5])]
    run_part2(fails, plan)
    run_part2_validation(fails)
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
