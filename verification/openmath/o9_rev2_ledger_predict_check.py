#!/usr/bin/env python3
"""O9 rev 2 falsifier K5: PREDICT censuses from the repaired E' ledger formula
(strict left-tail thresholds) and compare against brute-force enumeration.

Scope: r = 0 (f0 = 1, m = 1, d = 1, e = 1, Vhat = 0, w = v_pi), the one layer
where full brute force is feasible.  This is the check the O9 pass-1 verifier
recommended: the original harness (o9_order2_census_check.py) FITS censuses;
it never evaluates the E' closed form, which is how the rev-0 left-tail bug
(ceil = non-strict at integral extended-line abscissas) survived a clean run.

Per stratum datum D (vertex chain + left-tail cutoff + right tail + types),
per type assignment lambda:
  TRUTH   = #{(a_0..a_ell) in (Z/p^N)^{ell+1} (or monic-top box) satisfying
             the stratum conditions with STRICT left-tail semantics}
  NEW     = p^{E'_new} * (p-1)^eps * prod M_lambda   (repaired: left-tail
             threshold floor(line)+1; identical to ceil at non-integral)
  OLD     = same with rev-0 thresholds (ceil(line) at the left tail)
PASS iff NEW == TRUTH on every (D, lambda).  OLD is reported to reproduce the
refutation exactly where integral left-tail slots exist (e_1 | k0 - k).
"""
import itertools
from fractions import Fraction

# ---------------- F_p[y] factorization types ------------------------------
def polmulmod(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % p
    return tuple(r)

def poldivmod(a, b, p):
    # a, b tuples low->high, b monic; returns (q, r)
    a = list(a)
    db, da = len(b) - 1, len(a) - 1
    q = [0] * max(0, da - db + 1)
    for i in range(da - db, -1, -1):
        c = a[i + db] % p
        if c:
            q[i] = c
            for j, y in enumerate(b):
                a[i + j] = (a[i + j] - c * y) % p
    while len(a) > 1 and a[-1] % p == 0:
        a.pop()
    return tuple(q), tuple(x % p for x in a)

def irreducibles_upto(dmax, p):
    irr = []
    for d in range(1, dmax + 1):
        for tup in itertools.product(range(p), repeat=d):
            f = tuple(tup) + (1,)
            red = False
            for g in irr:
                if 2 * (len(g) - 1) > d + 1:
                    break
                if len(g) - 1 <= d // 2:
                    _, r = poldivmod(f, g, p)
                    if r == (0,):
                        red = True
                        break
            if not red:
                irr.append(f)
    return irr

_IRR = {}
def factor_type(f, p):
    """f tuple low->high, nonzero; returns sorted tuple of (deg, mult) per
    distinct irreducible factor (leading unit dropped) -- harness convention."""
    d = len(f) - 1
    if p not in _IRR or len(_IRR[p][-1]) - 1 < d:
        _IRR[p] = irreducibles_upto(max(d, 1), p)
    inv = pow(f[-1], p - 2, p)
    f = tuple(x * inv % p for x in f)
    typ = []
    for g in _IRR[p]:
        if len(g) > len(f):
            break
        m = 0
        while True:
            q, r = poldivmod(f, g, p)
            if r == (0,):
                f, m = q, m + 1
            else:
                break
        if m:
            typ.append((len(g) - 1, m))
    assert f == (1,), f
    return tuple(sorted(typ))

_M = {}
def M_type(typ, p, deg):
    """# monic degree-deg polys over F_p, nonzero constant term, given type."""
    key = (p, deg)
    if key not in _M:
        tally = {}
        for tup in itertools.product(range(p), repeat=deg):
            if tup[0] == 0:
                continue
            t = factor_type(tuple(tup) + (1,), p)
            tally[t] = tally.get(t, 0) + 1
        _M[key] = tally
    return _M[key].get(typ, 0)

# ---------------- datum: slots, thresholds, membership --------------------
def vcap(x, p, N):
    if x == 0:
        return N
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def slot_plan(verts, ell):
    """Per slot k=0..ell: ('lt', line Fraction) strict left tail /
    ('on', val int, is_vertex) / ('off', line Fraction) strict /
    ('rt', Us int) non-strict.  Also faces = [(k0,k1,e_S, [on-line ks])]."""
    k0, U0 = verts[0]
    ks, Us = verts[-1]
    plan, faces = {}, []
    for (a, ua), (b, ub) in zip(verts, verts[1:]):
        from math import gcd
        g = gcd(b - a, ua - ub)
        eS, hS = (b - a) // g, (ua - ub) // g
        ons = []
        for k in range(a, b + 1):
            val = Fraction(ua) - Fraction((k - a) * hS, eS)
            if (k - a) % eS == 0:
                plan[k] = ('on', int(val), k in (a, b) or None)
                ons.append(k)
            else:
                plan[k] = ('off', val)
        faces.append((a, b, eS, ons))
    h1e1 = Fraction(verts[0][1] - verts[1][1], verts[1][0] - verts[0][0])
    for k in range(0, k0):
        plan[k] = ('lt', Fraction(U0) + (k0 - k) * h1e1)
    for k in range(ks + 1, ell + 1):
        plan[k] = ('rt', Us)
    # vertices: mark all chain vertices
    vset = {v[0] for v in verts}
    for k in list(plan):
        if plan[k][0] == 'on':
            plan[k] = ('on', plan[k][1], k in vset)
    return plan, faces

def predict(verts, ell, p, N, types, monic_top):
    """(E_new, E_old, eps, pred_new, pred_old); types = tuple per face."""
    plan, faces = slot_plan(verts, ell)
    ks = verts[-1][0]
    E_new = E_old = 0
    for k in range(0, ell + (0 if monic_top else 1)):
        kind = plan[k]
        if kind[0] == 'lt':
            L = kind[1]
            bn = int(L) + 1 if L.denominator == 1 else -(-L.numerator // L.denominator)
            bo = -(-L.numerator // L.denominator)  # ceil
            E_new += N - bn
            E_old += N - bo
        elif kind[0] == 'off':
            b = -(-kind[1].numerator // kind[1].denominator)
            E_new += N - b
            E_old += N - b
        elif kind[0] == 'on':
            E_new += N - kind[1] - 1
            E_old += N - kind[1] - 1
        else:
            E_new += N - kind[1]
            E_old += N - kind[1]
    eps = 0 if monic_top else 1
    z = 1
    for (a, b, eS, ons), lam in zip(faces, types):
        z *= M_type(lam, p, (b - a) // eS)
    return E_new, E_old, eps, p ** E_new * (p - 1) ** eps * z, \
        p ** E_old * (p - 1) ** eps * z

def brute(verts, ell, p, N, monic_top):
    """Census dict: type-tuple -> count, over the box, STRICT semantics."""
    plan, faces = slot_plan(verts, ell)
    ncoord = ell if monic_top else ell + 1
    census = {}
    for tup in itertools.product(range(p ** N), repeat=ncoord):
        a = list(tup) + ([1] if monic_top else [])
        ok, digits = True, {}
        for k in range(ell + 1):
            kind = plan[k]
            if monic_top and k == ell:
                if kind[0] != 'on' or kind[1] != 0:
                    ok = False
                    break
                digits[k] = 1
                continue
            v = vcap(a[k], p, N)
            if kind[0] in ('lt', 'off'):
                if not Fraction(v) > kind[1]:
                    ok = False
                    break
            elif kind[0] == 'on':
                if v < kind[1]:
                    ok = False
                    break
                z = (a[k] // p ** kind[1]) % p
                if kind[2] and z == 0:   # vertex: exact valuation
                    ok = False
                    break
                digits[k] = z
            else:
                if v < kind[1]:
                    ok = False
                    break
        if not ok:
            continue
        tt = []
        for (x, y, eS, ons) in faces:
            R = tuple(digits[k] for k in ons)
            tt.append(factor_type(R, p))
        tt = tuple(tt)
        census[tt] = census.get(tt, 0) + 1
    return census

# ---------------- test matrix ---------------------------------------------
CASES = [
    # (name, p, N, ell, verts, monic_top)
    ("CM-verifier  (integral LT k=0,1)", 2, 4, 3, [(2, 1), (3, 0)], False),
    ("LT-e1-k1     (integral LT k=0)",   2, 4, 3, [(1, 2), (3, 0)], False),
    ("LT-mixed     (int k=0, frac k=1)", 2, 3, 4, [(2, 1), (4, 0)], False),
    ("RT+LT        (right tail + LT)",   2, 4, 3, [(1, 2), (2, 1)], False),
    ("MONIC-LT     (monic top + LT)",    2, 4, 3, [(1, 2), (3, 0)], True),
    ("M08-reg      (k0=0, no LT)",       2, 4, 3, [(0, 3), (3, 0)], True),
    ("p3-LT        (integral LT, p=3)",  3, 3, 2, [(1, 1), (2, 0)], False),
]

def m08_ceils(verts, ell):
    """M08 Thm 2 c_i for a k0=0 full polygon datum (monic top), i < ell."""
    plan, _ = slot_plan(verts, ell)
    cs = []
    for i in range(ell):
        kind = plan[i]
        if kind[0] == 'on':
            cs.append(kind[1] + 1)
        else:
            cs.append(-(-kind[1].numerator // kind[1].denominator))
    return cs

def main():
    nfail = 0
    for name, p, N, ell, verts, mt in CASES:
        census = brute(verts, ell, p, N, mt)
        seen = sorted(census)
        print(f"== {name}: p={p} N={N} ell={ell} verts={verts} "
              f"box={'monic-top' if mt else 'free'}")
        allt = set(seen)
        # all admissible type tuples (nonzero M) for completeness
        plan, faces = slot_plan(verts, ell)
        per_face = []
        for (a, b, eS, ons) in faces:
            d = (b - a) // eS
            key = (p, d)
            M_type((), p, d)      # populate
            per_face.append([t for t in _M[key]])
        for tt in itertools.product(*per_face):
            allt.add(tuple(tt))
        for tt in sorted(allt):
            En, Eo, eps, pn, po = predict(verts, ell, p, N, tt, mt)
            tr = census.get(tt, 0)
            tag = "PASS" if pn == tr else "FAIL"
            if pn != tr:
                nfail += 1
            old = "" if po == pn else f"  [rev-0 formula: {po} (REFUTED)]" \
                if po != tr else f"  [rev-0 formula: {po}]"
            print(f"   types={tt}: truth={tr}  new-formula={pn} "
                  f"(E'={En}, eps={eps})  {tag}{old}")
        if mt and verts[0][0] == 0:
            cs = m08_ceils(verts, ell)
            E = sum(N - c for c in cs)
            En = predict(verts, ell, p, N, tuple(() for _ in faces), mt)[0]
            print(f"   M08 regression: c_i={cs}, Sigma(N-c_i)={E}, "
                  f"E'_monic={En}  {'PASS' if E == En else 'FAIL'}")
            if E != En:
                nfail += 1
    print(f"\nRESULT: {'ALL PASS' if nfail == 0 else f'{nfail} FAILURES'}")
    return nfail

if __name__ == "__main__":
    raise SystemExit(main())
