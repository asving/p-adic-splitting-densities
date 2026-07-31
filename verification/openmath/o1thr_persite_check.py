#!/usr/bin/env python3
"""O1thr falsifier: per-site bounded read at depth 1, exhaustive.

Tests the O-1(thr)/D-14/D-15 package on the depth-1 slice where the OM read
machine is directly computable: boxes = monic f = X^n + a_{n-1}X^{n-1}+...+a_0
with all a_i = 0 mod p (reduction X^n: one fully-degenerate track, so the root
window is the whole Newton polygon of f w.r.t. the key X).

A SITE at depth 1 is a (principal-polygon face, irreducible residual factor)
pair with its recorded data (e,h,s0,wSide,pattern,psi,mu).  Its CEILING is
L = 1 + ceil(intercept of the side line at slot 0).

T-A (D-14/O-1thr): for every harvested site with L <= M, the set of boxes
     realizing it is an exact union of level-L coefficient cylinders.
T-B (sharpness):   count sites whose membership is NOT constant on level-(L-1)
     cylinders (expected >0: the ceiling cannot be lowered).
T-C (D-15 proxy):  for boxes whose polygon closes below M (v(a_0) < M), the
     full site roster is constant on the level-t cylinder, t = max site
     ceiling of the roster.
T-D (Eisenstein):  the M03 countermodel family sits OUTSIDE every guard:
     f = X^n + p^N has its unique site at ceiling N+1 > N, and the zero box
     (agreeing below N) does not realize it.
"""
import sys, math
from fractions import Fraction
from itertools import product

def vcap(a, p, M):
    if a == 0:
        return M
    v = 0
    while a % p == 0:
        a //= p; v += 1
    return min(v, M)

def lower_hull(pts):
    # pts sorted by j, one per j; returns hull vertex list
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # remove if hull[-1] not strictly below segment hull[-2]->pt
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull

def polfactor(coeffs, p):
    """Factor poly (list of coeffs mod p, low->high) into monic irreducibles.
    Returns dict {irr_tuple: multiplicity}. Degree <= 6 territory; brute force."""
    # normalize: strip leading zeros
    c = list(coeffs)
    while c and c[-1] % p == 0:
        c.pop()
    assert c, "zero residual polynomial"
    deg = len(c) - 1
    # make monic
    inv = pow(c[-1], p - 2, p) if p > 2 else c[-1]
    c = [(x * inv) % p for x in c]
    def polmod(a, b):
        a = list(a)
        while len(a) >= len(b):
            if a[-1] % p:
                q = a[-1]  # b monic
                off = len(a) - len(b)
                for i, bc in enumerate(b):
                    a[off + i] = (a[off + i] - q * bc) % p
            while a and a[-1] % p == 0 and len(a) >= len(b):
                a.pop()
            if a and a[-1] % p == 0:
                a.pop()
        while a and a[-1] % p == 0:
            a.pop()
        return a
    def poldiv(a, b):
        a = list(a); qout = [0] * (len(a) - len(b) + 1)
        while len(a) >= len(b):
            q = a[-1] % p
            off = len(a) - len(b)
            qout[off] = q
            for i, bc in enumerate(b):
                a[off + i] = (a[off + i] - q * bc) % p
            a.pop()
            while a and a[-1] % p == 0 and len(a) < len(b) + 1:
                break
            while a and a[-1] % p == 0:
                a.pop()
        return qout, a
    def irreducibles(maxdeg):
        out = []
        for d in range(1, maxdeg + 1):
            for tup in product(range(p), repeat=d):
                f = list(tup) + [1]
                # test irreducibility: no factor among lower-degree irreducibles
                if all(polmod(f, g) for g in out if len(g) - 1 <= d // 2):
                    out.append(f)
        return out
    irrs = irreducibles(deg)
    fac = {}
    rem = c
    for g in irrs:
        if len(rem) - 1 < len(g) - 1:
            continue
        while True:
            if len(rem) - 1 < len(g) - 1 or polmod(rem, g):
                break
            rem, r = poldiv(rem, g)
            assert not r
            fac[tuple(g)] = fac.get(tuple(g), 0) + 1
        if len(rem) == 1:
            break
    assert len(rem) == 1, (c, rem)
    return fac

def sites_of_box(a, p, n, M):
    """Harvest depth-1 sites of f = X^n + sum a_i X^i with ceiling <= M."""
    pts = [(j, vcap(a[j], p, M)) for j in range(n) if vcap(a[j], p, M) < M]
    pts.append((n, 0))
    pts.sort()
    hull = lower_hull(pts)
    out = []
    for (j0, v0), (j1, v1) in zip(hull, hull[1:]):
        if v0 <= v1:
            continue  # principal faces only (strictly decreasing)
        g = math.gcd(v0 - v1, j1 - j0)
        e, h = (j1 - j0) // g, (v0 - v1) // g
        intercept = Fraction(v0) + Fraction(j0 * h, e)
        L = 1 + math.ceil(intercept)
        if L > M:
            continue  # not fully determined at this working level
        d = (j1 - j0) // e
        pat = []
        for k in range(d + 1):
            j = j0 + e * k
            beta = v0 - k * h
            aj = 1 if j == n else a[j]
            pat.append((aj // p**beta) % p)
        assert pat[0] != 0 and pat[-1] != 0, (a, hull)
        for psi, mu in polfactor(pat, p).items():
            out.append((j0, j1, e, h, tuple(pat), psi, mu, L))
    return out

def run(p, n, M):
    boxes = [tuple(p * t for t in tup)
             for tup in product(range(p**(M - 1)), repeat=n)]
    site_members = {}
    roster = {}
    for a in boxes:
        ss = sites_of_box(a, p, n, M)
        roster[a] = frozenset(ss)
        for s in ss:
            site_members.setdefault(s, set()).add(a)
    # T-A: union of level-L cylinders
    bad_A, bad_B, sharp = 0, 0, 0
    for s, S in site_members.items():
        L = s[-1]
        groups = {}
        for a in boxes:
            groups.setdefault(tuple(x % p**L for x in a), [0, 0])[0] += 1
        for a in S:
            groups[tuple(x % p**L for x in a)][1] += 1
        if any(0 < inn < tot for tot, inn in groups.values()):
            bad_A += 1
        # T-B at L-1
        g2 = {}
        for a in boxes:
            g2.setdefault(tuple(x % p**(L - 1) for x in a), [0, 0])[0] += 1
        for a in S:
            g2[tuple(x % p**(L - 1) for x in a)][1] += 1
        if any(0 < inn < tot for tot, inn in g2.values()):
            sharp += 1
    # T-C: roster constant on level-t cylinders for closed boxes
    closed = [a for a in boxes if vcap(a[0], p, M) < M and roster[a]]
    bad_C = 0
    ros_groups = {}
    for a in closed:
        t = max(s[-1] for s in roster[a])
        ros_groups.setdefault((t, tuple(x % p**t for x in a)), set()).add(roster[a])
    bad_C = sum(1 for v in ros_groups.values() if len(v) > 1)
    # T-D: Eisenstein family
    eis_ok = True
    for N in range(1, M):
        a = tuple(p**N if i == 0 else 0 for i in range(n))
        zz = tuple(0 for _ in range(n))
        ss = [s for s in sites_of_box(a, p, n, M)]
        if not all(s[-1] == N + 1 for s in ss) or ss == []:
            eis_ok = False
        if any(s in roster.get(zz, frozenset()) for s in ss):
            eis_ok = False
    print(f"p={p} n={n} M={M}: boxes={len(boxes)} sites={len(site_members)} "
          f"| T-A cylinder-law violations: {bad_A} "
          f"| T-B sites sharp at L (not (L-1))-cylindrical: {sharp} "
          f"| T-C closed-box roster violations: {bad_C} (closed={len(closed)}) "
          f"| T-D Eisenstein outside-guard: {'PASS' if eis_ok else 'FAIL'}")
    return bad_A, bad_C, eis_ok

if __name__ == "__main__":
    ok = True
    for (p, n, M) in [(2, 2, 5), (2, 2, 6), (3, 2, 5), (2, 3, 4), (3, 3, 4)]:
        bad_A, bad_C, eis = run(p, n, M)
        ok = ok and bad_A == 0 and bad_C == 0 and eis
    print("OVERALL:", "ALL PASS" if ok else "FAILURES FOUND")
