"""M08-cl6-general sanity check: level-1 Newton-polygon stratum census formula.

Theorem 2 (attempt file): for the block f = x^e + a_{e-1}x^{e-1} + ... + a_0 over a
local field with residue field F_q, all v(a_i) >= 1 (block condition f-bar = x^e),
stratum D = (polygon Delta with lattice vertices from (0,y0) to (e,0), per-side
factorization types lambda_S of the residual polynomials), level N > max height:

  #\{(a_i) in (O/pi^N)^e : NP(f) = Delta, type(R_S) = lambda_S for all S\}
      = q^{ sum_i (N - c_i) } * prod_S M_{lambda_S}(q)

  c_i = Delta(i)+1 if i is a lattice point of Delta (incl. vertices), ceil(Delta(i)) else
  M_lambda(q) = #\{monic R in F_q[y], deg = ell_S, R(0) != 0, factorization type lambda\}
  computed by the necklace-multiset formula (a polynomial in q).

Brute force: enumerate all (a_0..a_{e-1}) in (Z/p^N)^e, classify, compare.
Pure python; p in {2,3,5,7}, e in {2,3}, N = 3.
"""
from itertools import product
from fractions import Fraction
from math import comb, factorial
from collections import Counter

def vpad(a, p, N):
    """valuation of a in Z/p^N, capped at N."""
    if a == 0:
        return N
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v

def lower_hull(pts):
    """lower convex hull of list of (x,y), x strictly increasing; returns vertices."""
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # remove hull[-1] if it is above or on segment hull[-2]--pt
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull

# ---------- factorization types over F_p (small degree, trial division) ----------
def polmulmod(f, g, p):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            r[i + j] = (r[i + j] + a * b) % p
    return r

def poldivmod(f, g, p):
    """f, g coefficient lists (low to high), g monic; returns (quot, rem)."""
    f = f[:]
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(f) - 1 >= dg and any(f):
        while f and f[-1] == 0:
            f.pop()
        if len(f) - 1 < dg:
            break
        c = f[-1]
        d = len(f) - 1 - dg
        q[d] = c
        for i, b in enumerate(g):
            f[d + i] = (f[d + i] - c * b) % p
    while f and f[-1] == 0:
        f.pop()
    return q, f

def irreducibles(p, maxdeg):
    """monic irreducibles over F_p of degree <= maxdeg, by sieve."""
    monics = {d: [list(t) + [1] for t in product(range(p), repeat=d)]
              for d in range(1, maxdeg + 1)}
    irr = {1: monics[1]}
    for d in range(2, maxdeg + 1):
        out = []
        for f in monics[d]:
            red = False
            for dd in range(1, d // 2 + 1):
                for g in irr.get(dd, []):
                    _, r = poldivmod(f, g, p)
                    if not r:
                        red = True
                        break
                if red:
                    break
            if not red:
                out.append(f)
        irr[d] = out
    return irr

def fact_type(f, p, irr):
    """factorization type of poly f (low-to-high coeffs, leading != 0) over F_p:
    frozenset-multiset of (deg, mult); ignores leading unit (type is scaling-inv)."""
    # normalize monic
    lead = f[-1]
    inv = pow(lead, p - 2, p) if p > 2 else lead  # p=2: lead=1
    f = [(c * inv) % p for c in f]
    typ = []
    d = 1
    while len(f) > 1:
        found = False
        for g in irr[d]:
            m = 0
            while True:
                q, r = poldivmod(f, g, p)
                if not r and len(q) >= 1:
                    f, m = q, m + 1
                else:
                    break
            if m:
                typ.append((d, m))
                found = True
            if len(f) == 1:
                break
        d += 1
        if d > 5:
            raise RuntimeError("degree overflow")
    return tuple(sorted(typ))

# ---------- the predicted polynomial M_lambda(q) ----------
def mobius(k):
    m, res = k, 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            res = -res
        d += 1
    if m > 1:
        res = -res
    return res

def divisors(k):
    return [d for d in range(1, k + 1) if k % d == 0]

def I_d(d, q):
    """number of monic irreducibles of degree d over F_q (exact rational -> int)."""
    return int(sum(Fraction(mobius(k) * q ** (d // k), d) for k in divisors(d)))

def M_lambda(typ, q):
    """# monic polys over F_q with factorization type typ=((d,m),...) and nonzero
    constant term: product over degrees d of (choose distinct irreducibles avoiding
    y when d=1) x (assign the multiplicity multiset)."""
    by_deg = {}
    for d, m in typ:
        by_deg.setdefault(d, []).append(m)
    total = 1
    for d, mults in by_deg.items():
        r = len(mults)
        avail = I_d(d, q) - (1 if d == 1 else 0)   # exclude y itself
        mult_counts = Counter(mults)
        assign = factorial(r)
        for c in mult_counts.values():
            assign //= factorial(c)
        total *= comb(avail, r) * assign
    return total

# ---------- classify one coefficient tuple ----------
def classify(a, e, p, N, irr):
    """a = (a_0..a_{e-1}) in Z/p^N; returns stratum key or None (undecided)."""
    vs = [vpad(x, p, N) for x in a]
    if vs[0] >= N:
        return None                    # left endpoint not visible at level N
    if min(vs[1:] + [N]) == 0 or vs[0] == 0:
        return None                    # not in the x^e block (v(a_i) >= 1 needed)
    pts = [(i, vs[i]) for i in range(e) if vs[i] < N] + [(e, 0)]
    hull = lower_hull(pts)
    if hull[0][0] != 0:
        return None
    # per-side residual types
    key_sides = []
    for s in range(len(hull) - 1):
        (x0, y0), (x1, y1) = hull[s], hull[s + 1]
        dx, dy = x1 - x0, y0 - y1
        from math import gcd
        g = gcd(dx, dy)
        eS, hS = dx // g, dy // g
        ell = g
        # lattice slots x0 + j*eS, j=0..ell ; heights y0 - j*hS
        coeffs = []
        for j in range(ell + 1):
            i = x0 + j * eS
            ht = y0 - j * hS
            if i == e:
                z = 1
            else:
                z = (a[i] // p ** ht) % p if vpad(a[i], p, N) >= ht else None
                # v(a_i) >= Delta(i) is guaranteed by hull membership
                z = (a[i] // p ** ht) % p
            coeffs.append(z)
        typ = fact_type(coeffs, p, irr)
        key_sides.append((tuple(hull[s:s + 2]), typ))
    return (tuple(hull), tuple(key_sides))

def predicted(key, e, p, N):
    hull, sides = key
    # c_i for i = 0..e-1
    Etot = 0
    hull_pts = list(hull)
    def delta_at(i):
        for s in range(len(hull_pts) - 1):
            (x0, y0), (x1, y1) = hull_pts[s], hull_pts[s + 1]
            if x0 <= i <= x1:
                return Fraction(y0 * (x1 - i) + y1 * (i - x0), x1 - x0)
        raise RuntimeError
    for i in range(e):
        d = delta_at(i)
        if d.denominator == 1:
            # lattice point of Delta?
            # integer height alone suffices only if (i, d) lies on the side's
            # arithmetic progression; integer height on the polygon IS lattice
            ci = int(d) + 1
        else:
            ci = int(-(-d.numerator // d.denominator))  # ceil
        Etot += N - ci
    pred = p ** Etot
    for (_seg, typ) in sides:
        pred *= M_lambda(typ, p)
    return pred

def run(e, N, primes):
    for p in primes:
        irr = irreducibles(p, e)
        census = Counter()
        for a in product(range(p ** N), repeat=e):
            k = classify(a, e, p, N, irr)
            if k is not None:
                census[k] += 1
        bad = 0
        for k, cnt in sorted(census.items()):
            pred = predicted(k, e, p, N)
            ok = (pred == cnt)
            if not ok:
                bad += 1
                print(f"  MISMATCH p={p} e={e}: {k}  brute={cnt} pred={pred}")
        print(f"p={p} e={e} N={N}: {len(census)} strata, mismatches={bad}")

if __name__ == "__main__":
    print("=== e=2, N=3 ===")
    run(2, 3, [2, 3, 5, 7])
    print("=== e=3, N=3 ===")
    run(3, 3, [2, 3, 5])

def chain_test(qs):
    """Direct test of the vertex-chain telescope (Lemma D): two sides sharing a
    vertex, each with residual degree 2 (one interior slot), rightmost vertex
    pinned to 1.  Joint census over (z0, z1 in Fq^*, w1, w2 in Fq) of
    type(R1)=l1, type(R2)=l2 with R1 = z0 + w1 y + z1 y^2, R2 = z1 + w2 y + y^2.
    Prediction: M_{l1}(q) * M_{l2}(q)."""
    for q in qs:
        irr = irreducibles(q, 2)
        joint = Counter()
        for z0 in range(1, q):
            for z1 in range(1, q):
                for w1 in range(q):
                    t1 = fact_type([z0, w1, z1], q, irr)
                    for w2 in range(q):
                        t2 = fact_type([z1, w2, 1], q, irr)
                        joint[(t1, t2)] += 1
        bad = 0
        for (t1, t2), cnt in sorted(joint.items()):
            pred = M_lambda(t1, q) * M_lambda(t2, q)
            if pred != cnt:
                bad += 1
                print(f"  CHAIN MISMATCH q={q} {t1}|{t2}: brute={cnt} pred={pred}")
        print(f"chain q={q}: {len(joint)} type pairs, mismatches={bad}")

def fiber_test(qs):
    """Lemma C examples: per-fiber counts with BOTH ends prescribed are NOT
    constant (audit necessity).  nu(t) = #{w : y^2 + w y + t irreducible} should
    be (q - chi(t))/2 for odd q — non-constant in t."""
    for q in qs:
        irr = irreducibles(q, 2)
        vals = {}
        for t in range(1, q):
            c = sum(1 for w in range(q)
                    if fact_type([t, w, 1], q, irr) == ((2, 1),))
            vals[t] = c
        distinct = sorted(set(vals.values()))
        tot = sum(vals.values())
        print(f"fiber q={q}: nu(t) values {distinct} (non-constant: "
              f"{len(distinct) > 1}), sum={tot}, I_2(q)={I_d(2, q)}")

print("=== chain telescope test ===")
chain_test([3, 5, 7, 11])
print("=== fiber non-constancy test ===")
fiber_test([3, 5, 7, 9] if False else [3, 5, 7, 11, 13])
print("=== e=2, N=4 (deeper polygons, incl. 2-vertex chains) ===")
run(2, 4, [2, 3, 5, 7])
print("=== e=3, N=4 ===")
run(3, 4, [2, 3])
