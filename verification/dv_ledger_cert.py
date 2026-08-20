#!/usr/bin/env python3
"""dv_ledger_cert.py — numeric certification of the dv-graded engine's floor law.

Twin of docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md §5, protocol item (1).

Instance: the s2 depth-2 slice over Z_2 (the corpus's own witness values, C.97):
  Phi' = x^2 - 2,  (e1, f1, h) = (2, 1, 1), D' = 2
  (e2, f2, u2) = (2, 1, 5),  E2 = 10,  delta = u2 - e2*D'*h = 1,  D2 = 4
  Phi2 = Phi'^2 - 4x  (C.97's display, the corpus value)

CLAIM CERTIFIED (the engine's floor law, Corollary B summed by L1):
  for integral f = sum_m c_m x^m, every two-key digit slot of f satisfies
     e1e2*v2(coeff) + a*e2h + b*u2 + j*E2  >=  min_m ( e1e2*v2(c_m) + m*e2h )
  where the two-key digits are  dev_{Phi'} ( dev_{Phi2} f j ) b, slot coefficient at x^a.

ALSO CERTIFIED (the division ledger L4 in its consumable form):
  the same with f a BOX MONOMIAL c*x^a*Phi'^b*Phi2^j and the floor
     4*v2(c) + 2*a + 5*b + 10*j    (= wt of the monomial)
  — this is C.52's `dvAbove_boxMonomial` at the instance, exactly.

Exact integer arithmetic throughout (monic divisors keep everything in Z).
"""

import itertools, random, sys

# ---------- polynomial helpers over Z (dense coeff lists, index = degree) ----------

def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p

def padd(p, q):
    r = [0] * max(len(p), len(q))
    for i, c in enumerate(p): r[i] += c
    for i, c in enumerate(q): r[i] += c
    return trim(r)

def pscale(p, s):
    return trim([s * c for c in p])

def pmul(p, q):
    if not p or not q: return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)

def pdivmod_monic(f, g):
    """f = g*q + r with deg r < deg g; g MONIC. Integral."""
    f = list(f); q = []
    dg = len(g) - 1
    assert g[-1] == 1
    while len(f) - 1 >= dg and f:
        shift = len(f) - 1 - dg
        c = f[-1]
        q = padd(q, [0] * shift + [c])
        f = padd(f, pscale([0] * shift + g, -c))
    return trim(q), trim(f)

def dev(phi, f, j):
    """the j-th phi-adic digit of f (B.02's dev)."""
    for _ in range(j):
        f, _ = pdivmod_monic(f, phi)
    _, r = pdivmod_monic(f, phi)
    return r

def v2(n):
    if n == 0: return None  # +infinity
    v = 0
    while n % 2 == 0:
        n //= 2; v += 1
    return v

# ---------- the instance ----------

E1, F1, H = 2, 1, 1
E2q, F2, U2 = 2, 1, 5
DP = E1 * F1          # D' = 2
E2 = E2q * F2 * U2    # 10
D2 = DP * E2q * F2    # 4
DELTA = U2 - E2q * DP * H  # 1
E1E2 = E1 * E2q       # 4 = the pi-weight
PHI1 = [-2, 0, 1]                    # x^2 - 2
PHI2 = trim([4, -4, -4, 0, 1])       # Phi'^2 - 4x = x^4 - 4x^2 - 4x + 4
assert pmul(PHI1, PHI1) == [4, 0, -4, 0, 1]

def xweight(f):
    """the literal x-basis weight floor: min_m (4*v2(c_m) + 2m); None = +inf."""
    best = None
    for m, c in enumerate(f):
        if c == 0: continue
        w = E1E2 * v2(c) + m * (E2q * H)
        best = w if best is None else min(best, w)
    return best

def slot_weights(f, mu2):
    """all two-key digit slot weights of f: for j<mu2 (+top), b<e2f2, a<D'."""
    out = []
    for j in range(mu2 + 1):
        dj = dev(PHI2, f, j)
        for b in range(E2q * F2):
            digit = dev(PHI1, dj, b)
            for a in range(DP):
                c = digit[a] if a < len(digit) else 0
                if c == 0: continue
                out.append((E1E2 * v2(c) + a * (E2q * H) + b * U2 + j * E2, j, b, a, c))
    return out

def check(f, floor, tag, strict_report):
    for w, j, b, a, c in slot_weights(f, 3):
        if floor is not None and w < floor:
            print(f"FAIL [{tag}] slot (j={j},b={b},a={a}) coeff {c}: weight {w} < floor {floor}")
            print(f"     f = {f}")
            return False
    return True

fails = 0
tests = 0

# ---- exhaustive box monomials: c*x^a*Phi'^b*Phi2^j (Corollary B / dvAbove_boxMonomial) ----
for v in range(3):
    for a in range(2 * DP):        # deliberately INCLUDING overflowing a >= D'
        for b in range(2 * E2q * F2):
            for j in range(3):
                c = 3 * (2 ** v)   # unit 3 times 2^v
                mono = pscale([0] * a + [1], c)
                mono = pmul(mono, [1])
                pb = [1]
                for _ in range(b): pb = pmul(pb, PHI1)
                pj = [1]
                for _ in range(j): pj = pmul(pj, PHI2)
                f = pmul(pmul(mono, pb), pj)
                floor = E1E2 * v + a * (E2q * H) + b * U2 + j * E2
                tests += 1
                if not check(f, floor, f"box v={v},a={a},b={b},j={j}", True):
                    fails += 1

# ---- random integral f against the x-basis floor (the summed law) ----
rng = random.Random(20260820)
for trial in range(4000):
    deg = rng.randrange(0, 13)
    f = [rng.randrange(-64, 65) for _ in range(deg + 1)]
    f = trim(f)
    if not f: continue
    floor = xweight(f)
    tests += 1
    if not check(f, floor, f"rand#{trial}", False):
        fails += 1

# ---- the division ledger L4 sharpness probe: does the floor law ever bind with equality? ----
eq_hits = 0
for trial in range(400):
    deg = rng.randrange(0, 13)
    f = trim([rng.randrange(-8, 9) for _ in range(deg + 1)])
    if not f: continue
    fl = xweight(f)
    ws = [w for w, *_ in slot_weights(f, 3)]
    if ws and fl is not None and min(ws) == fl:
        eq_hits += 1

print(f"tests: {tests}, FAILS: {fails}, equality-attained probes: {eq_hits}/400")
sys.exit(1 if fails else 0)
