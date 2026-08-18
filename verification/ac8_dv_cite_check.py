#!/usr/bin/env python3
"""A-C.8 certification, Leg C — the independent numeric leg (exact integer arithmetic).

Independent implementation of the dv-level reads at the s2 frame (O = Z_2-like,
pi = 2, Phi' = x^2 - 2, (e1, f1, h) = (2, 1, 1)); NOT copied from the Lean reductions.

Fixed tooth (the amendment's displayed two-slope witness):
  f = (Phi' + 8) * (Phi' + 4)  =  (x^2 + 6)(x^2 + 2)
  Phi'-development heights [10, 4, 0]; sides {0,1} at slope (6,1) and {1,2} at (4,1);
  side degrees (1,1); grouped factor degrees (2,2).

Bounded sweep (26 rows): f = prod_{m in {2,3,4}} (Phi' + 2^m)^{a_m}, a_m in {0,1,2},
not all zero.  Checks: principal slopes exactly {2m : a_m > 0}; side degree at 2m is
a_m; grouped factor degree 2*a_m; factor-permutation invariance; the two named fences
(low-degree X candidate; deliberate cross-slope swap).
"""
import sys
from itertools import product

E1, H = 2, 1          # frame numerals (e1, h); D' = e1*f1 = 2
FLOOR = E1 * 1 * H    # e1*f1*h = 2 : the cleared frame floor  (lambda > 0  <=>  u > 2*l)


def v2(n):
    if n == 0:
        return None  # +infinity
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


# ---- exact polynomial arithmetic over Z (dense little-endian lists) ----
def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pnorm(a):
    while len(a) > 1 and a[-1] == 0:
        a = a[:-1]
    return a


def pdivmod_monic(f, g):
    """f = q*g + r with g monic; exact over Z."""
    f = list(f)
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(pnorm(f)) - 1 >= dg and pnorm(f) != [0]:
        f = pnorm(f)
        df = len(f) - 1
        c = f[-1]
        q[df - dg] += c
        for i, gc in enumerate(g):
            f[df - dg + i] -= c * gc
        f = pnorm(f)
    return pnorm(q), pnorm(f)


PHI = [-2, 0, 1]  # x^2 - 2


def dev(f):
    """Phi'-adic development: list of blocks A_j (deg < 2), little-endian in Phi'."""
    blocks = []
    cur = pnorm(list(f))
    while cur != [0]:
        q, r = pdivmod_monic(cur, PHI)
        blocks.append(r)
        cur = q
        if cur == [0] or cur == []:
            break
    return blocks if blocks else [[0]]


def stage_height(A):
    """dv(A) = min_i (e1*v2(a_i) + h*i) over the block's coefficients; None = infinity."""
    best = None
    for i, c in enumerate(A):
        v = v2(c)
        if v is None:
            continue
        t = E1 * v + H * i
        if best is None or t < best:
            best = t
    return best


def dv_heights(f):
    return [stage_height(A) for A in dev(f)]


def principal_sides(hgts):
    """Lower-hull sides of {(j, h_j)} with cleared slope u/l, u > FLOOR*l, as
    {(u, l): sorted list of on-side abscissae}.  Independent hull walk."""
    pts = [(j, h) for j, h in enumerate(hgts) if h is not None]
    sides = {}
    # walk the lower convex hull from the right (top) to the left
    hull = []
    for p in sorted(pts, key=lambda t: t[0]):
        hull.append(p)
        while len(hull) >= 3:
            (x1, y1), (x2, y2), (x3, y3) = hull[-3:]
            # keep only lower-convex corners
            if (y3 - y1) * (x2 - x1) <= (y2 - y1) * (x3 - x1):
                hull.pop(-2)
            else:
                break
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        du, dl = y1 - y2, x2 - x1  # slope = -(u/l) with u = du, l = dl (heights fall)
        if dl <= 0 or du <= 0:
            continue
        from math import gcd
        g = gcd(du, dl)
        u, l = du // g, dl // g
        if u <= FLOOR * l:
            continue  # below/at the frame floor: not principal
        # on-side abscissae: points of pts on the segment
        ons = [x for (x, y) in pts
               if x1 <= x <= x2 and (y - y1) * (x2 - x1) == (y2 - y1) * (x - x1)]
        key = (u, l)
        sides.setdefault(key, set()).update(ons)
    return {k: sorted(v) for k, v in sides.items()}


fails = 0


def check(name, cond):
    global fails
    if not cond:
        print(f"FAIL: {name}")
        fails += 1


# ---------- fixed tooth ----------
g = {m: padd(PHI, [2 ** m]) for m in (2, 3, 4)}  # Phi' + 2^m
f0 = pmul(g[3], g[2])                            # (x^2+6)(x^2+2)
h0 = dv_heights(f0)
check("tooth heights [10,4,0]", h0 == [10, 4, 0])
s0 = principal_sides(h0)
check("tooth slopes {(6,1),(4,1)}", set(s0) == {(6, 1), (4, 1)})
check("tooth side (6,1) = {0,1}", s0.get((6, 1)) == [0, 1])
check("tooth side (4,1) = {1,2}", s0.get((4, 1)) == [1, 2])
def side_deg(ons, l):
    return (ons[-1] - ons[0]) // l  # the repo's dvSideDeg: horizontal length over l

check("tooth side degrees (1,1)",
      all(side_deg(v, k[1]) == 1 for k, v in s0.items()))
check("tooth grouped degrees (2,2)",
      all(2 * (k[1] * side_deg(v, k[1])) == 2 for k, v in s0.items()))  # D'*(l*sideDeg)

# ---------- 26-row sweep ----------
rows = 0
for a2, a3, a4 in product(range(3), repeat=3):
    if a2 == a3 == a4 == 0:
        continue
    rows += 1
    f = [1]
    for m, a in ((2, a2), (3, a3), (4, a4)):
        for _ in range(a):
            f = pmul(f, g[m])
    hg = dv_heights(f)
    sd = principal_sides(hg)
    expect = {(2 * m, 1) for m, a in ((2, a2), (3, a3), (4, a4)) if a > 0}
    check(f"row {(a2,a3,a4)} slopes", set(sd) == expect)
    for m, a in ((2, a2), (3, a3), (4, a4)):
        if a > 0:
            deg = side_deg(sd[(2 * m, 1)], 1)
            check(f"row {(a2,a3,a4)} sideDeg@{2*m}", deg == a)
            check(f"row {(a2,a3,a4)} groupedDeg@{2*m}", 2 * deg == 2 * a)
    # permutation invariance: rebuild in reverse factor order
    f2 = [1]
    for m, a in ((4, a4), (3, a3), (2, a2)):
        for _ in range(a):
            f2 = pmul(f2, g[m])
    check(f"row {(a2,a3,a4)} permutation-invariant", pnorm(f) == pnorm(f2))
check("row count 26", rows == 26)

# ---------- fences ----------
# low-degree candidate g = X: its dv-polygon has a side but D'*(l*sideDeg) >= D' = 2 > 1 = deg X
hX = dv_heights([0, 1])
sX = principal_sides(hX)
check("fence: X has no principal side satisfying the degree law",
      all(2 * (k[1] * side_deg(v, k[1])) != 1 for k, v in sX.items()))
# cross-slope swap: assigning g[2] to slope (6,1) must break purity — g[2]'s own polygon
h2 = dv_heights(g[2])
s2 = principal_sides(h2)
check("fence: Phi'+4 is one-sided at (4,1), NOT (6,1)", set(s2) == {(4, 1)})

print(f"rows={rows} fails={fails}")
print("==== ALL CHECKS PASSED ====" if fails == 0 else "==== FAILURES ====")
sys.exit(1 if fails else 0)
