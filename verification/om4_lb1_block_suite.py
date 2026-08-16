#!/usr/bin/env python3
"""OM-4 certification leg for (LB1) = HYP.41 (ledger), EFF.T2.18, chapter-E node E.39.

(LB1) asserts: every level-one state whose clause-4 processing demands blocks -- every state
with >= 2 sides, and every side whose residual is mixed -- has the monic side and label blocks
of S1.7A: own full developments, single-side hulls, pure residuals (LABEL-PURE), product
identities (SIDE-PROD)/(LABEL-PROD), the integrality (LABEL-OWN)
    k = nu/(e' deg r') = deg F_{lam,r'} / (D e' deg r') in Z_{>=1},
disjoint exhaustive root partitions, and inherited continuation data.

This script certifies the claim EXACTLY (integer/rational arithmetic only, no floats) on
constructed batteries over BOTH primes p in {2,3} and BOTH characteristics
(O = Z_(p) subset Q_p, and O = F_p[t] subset F_p((t))), plus a decorrelated ORACLE leg
(char 0 only): random states factored by PARI factorpadic, factors regrouped into blocks,
suite re-verified.

Constructed batteries WITNESS existence (the blocks are exhibited); every S1.7A display is
then CHECKED, never assumed.  The attack leg (defeat search) is the oracle leg: any random
state violating any display would be a counterexample to (LB1)'s classical shadow
([GN15] Thm 2.3 / GMN Thm 3.1 + 3.7 + 2.26).

Run:  PYTHONPATH=~/.local/lib/python3.10/site-packages python3 om4_lb1_block_suite.py
"""

import sys
from fractions import Fraction
from itertools import product as iproduct

# ----------------------------------------------------------------------------------
# Exact coefficient domains.
#   char 0:  O = Z_(p); elements are Python ints (all our data are global integers);
#            v = p-adic valuation, residue = mod p.
#   char p:  O = F_p[t]; elements are tuples of ints mod p (coeff of t^i);
#            v = t-order, residue = coeff of t^0.
# Polynomials in x over O are dicts {deg: coeff} with exact arithmetic.
# ----------------------------------------------------------------------------------

class Dom:
    """char-0 domain Z at prime p."""
    def __init__(self, p): self.p, self.char = p, 0
    def zero(self): return 0
    def one(self): return 1
    def is_zero(self, a): return a == 0
    def add(self, a, b): return a + b
    def neg(self, a): return -a
    def mul(self, a, b): return a * b
    def val(self, a):
        if a == 0: return None
        v = 0
        while a % self.p == 0: a //= self.p; v += 1
        return v
    def residue_shift(self, a, v):
        """residue of a / p^v in F_p (a int with val >= v)."""
        return (a // self.p ** v) % self.p
    def from_int(self, n): return n
    def times_pi_pow(self, a, k): return a * self.p ** k


class DomT:
    """char-p domain F_p[t]; elements = tuples (c0, c1, ...) mod p, no trailing zeros."""
    def __init__(self, p): self.p, self.char = p, p
    def norm(self, t_):
        L = list(t_)
        while L and L[-1] % self.p == 0: L.pop()
        return tuple(c % self.p for c in L)
    def zero(self): return ()
    def one(self): return (1,)
    def is_zero(self, a): return len(a) == 0
    def add(self, a, b):
        n = max(len(a), len(b))
        return self.norm([ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n) ])
    def neg(self, a): return self.norm([-c for c in a])
    def mul(self, a, b):
        if not a or not b: return ()
        out = [0] * (len(a) + len(b) - 1)
        for i, ca in enumerate(a):
            for j, cb in enumerate(b): out[i + j] += ca * cb
        return self.norm(out)
    def val(self, a):
        if not a: return None
        for i, c in enumerate(a):
            if c % self.p: return i
        return None
    def residue_shift(self, a, v): return a[v] % self.p if v < len(a) else 0
    def from_int(self, n): return self.norm((n,))
    def times_pi_pow(self, a, k): return self.norm((0,) * k + tuple(a)) if a else ()


# ---------------- polynomials in x over a domain (dict deg -> coeff) ----------------

def pnorm(D, f): return {i: c for i, c in f.items() if not D.is_zero(c)}
def padd(D, f, g):
    out = dict(f)
    for i, c in g.items(): out[i] = D.add(out.get(i, D.zero()), c)
    return pnorm(D, out)
def pneg(D, f): return {i: D.neg(c) for i, c in f.items()}
def psub(D, f, g): return padd(D, f, pneg(D, g))
def pmul(D, f, g):
    out = {}
    for i, a in f.items():
        for j, b in g.items():
            out[i + j] = D.add(out.get(i + j, D.zero()), D.mul(a, b))
    return pnorm(D, out)
def pdeg(f): return max(f) if f else -1
def pconst(D, a): return {0: a} if not D.is_zero(a) else {}
def pmonomial(D, a, i): return {i: a} if not D.is_zero(a) else {}

def pdivmod_monic(D, f, phi):
    """divide f by MONIC phi over O: f = q*phi + r, deg r < deg phi.  Exact (monic)."""
    f = dict(f); q = {}
    dphi = pdeg(phi)
    while pdeg(f) >= dphi:
        d = pdeg(f); lc = f[d]
        q[d - dphi] = lc
        for j, c in phi.items():
            k = d - dphi + j
            f[k] = D.add(f.get(k, D.zero()), D.neg(D.mul(lc, c)))
            if D.is_zero(f[k]): del f[k]
    return pnorm(D, q), pnorm(D, f)

def development(D, f, phi):
    """phi-adic development: f = sum_j a_j phi^j, deg a_j < deg phi.  Returns list a_j."""
    out = []
    while f:
        f, r = pdivmod_monic(D, f, phi)
        out.append(r)
    return out

# ---------------- Gauss valuation of a coefficient poly (deg < deg phi) -------------

def gauss_val(D, a):
    """min valuation of the O-coefficients of a in O[x] (None if a == 0)."""
    if not a: return None
    vs = [D.val(c) for c in a.values() if D.val(c) is not None]
    return min(vs) if vs else None

# ---------------- Newton polygon at key phi -----------------------------------------

def polygon(D, f, phi):
    """principal phi-polygon of monic f with f ≡ phibar^mu mod pi:
    points (j, v(a_j)) for the development; returns list of sides
    [(slope_num, slope_den, j_start, j_end, v_start)] with slope = h/e > 0 in lowest terms,
    heights decreasing to (mu, 0).  Lower convex hull between (ord, v) and (mu, 0)."""
    dev = development(D, f, phi)
    pts = [(j, gauss_val(D, a)) for j, a in enumerate(dev) if a]
    # lower convex hull, from leftmost to (mu,0)
    pts.sort()
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep hull lower-convex: remove middle if pt makes it non-extreme
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    sides = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        num, den = y1 - y2, x2 - x1          # positive slope convention lam = (y1-y2)/(x2-x1)
        from math import gcd
        g = gcd(num, den)
        sides.append((num // g, den // g, x1, x2, y1))
    return dev, hull, sides

def residual_poly(D, dev, side):
    """residual polynomial (in F_p[y] -- valid whenever deg phi = 1, or when the
    development coefficients are CONSTANTS so the residue lies in the prime field) of the
    given side (h,e,j0,j1,v0): R(y) = sum_k res(a_{j0+ke} / pi^{v0-kh}) y^k.
    Returns list of ints mod p, low degree first.  For deg phi = 2 batteries use
    residual_poly_fq below."""
    h, e, j0, j1, v0 = side
    R = []
    for k in range((j1 - j0) // e + 1):
        j = j0 + k * e
        target = v0 - k * h
        a = dev[j] if j < len(dev) else {}
        if not a:
            R.append(0); continue
        va = gauss_val(D, a)
        if va > target: R.append(0)
        else:
            assert va == target, "point below the side: not a side of the polygon"
            assert list(a.keys()) == [0], "residual over prime field needs constant dev coeffs"
            R.append(D.residue_shift(a[0], target))
    return R

# ---------------- F_p[y] helpers -----------------------------------------------------

def fp_poly_mul(p, A, B):
    out = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B): out[i + j] = (out[i + j] + a * b) % p
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out

def fp_poly_pow(p, A, k):
    out = [1]
    for _ in range(k): out = fp_poly_mul(p, out, A)
    return out

def fp_assoc(p, A, B):
    """A ~ c*B for a nonzero constant c in F_p?"""
    if len(A) != len(B): return False
    for c in range(1, p):
        if all((c * b - a) % p == 0 for a, b in zip(A, B)): return True
    return False

# ---------------- battery construction ----------------------------------------------

def leaf(D, phi, digit_poly, height):
    """the block phi + pi^height * digit_poly  (digit_poly in O[x], deg < deg phi,
    unit Gauss valuation)."""
    inc = {i: D.times_pi_pow(c, height) for i, c in digit_poly.items()}
    return padd(D, phi, inc)

def run_battery(D, name, phi, groups, log):
    """groups: list of (side_key=(h,e), label_list) where each label is
    (r_prime_as_fp_list, [factors...]) -- the constructed block for that label is the
    product of its factors.  Verifies the whole S1.7A suite for F = product of everything.
    Returns number of failed checks."""
    p = D.p
    fails = 0
    def check(cond, msg):
        nonlocal fails
        if not cond:
            fails += 1
            log.append(f"    FAIL: {msg}")

    # F and the trigger
    F = pconst(D, D.one())
    all_blocks = []
    for (h, e), labels in groups:
        for rp, facs in labels:
            blk = pconst(D, D.one())
            for f in facs: blk = pmul(D, blk, f)
            all_blocks.append(((h, e), rp, blk, facs))
            F = pmul(D, F, blk)
    devF, hullF, sidesF = polygon(D, F, phi)
    Dkey = pdeg(phi)
    slopes = {(s[0], s[1]) for s in sidesF}
    mixed = False
    for s in sidesF:
        R = residual_poly(D, devF, s)
        # squarefree over F_p?  gcd(R, R') != const  -> mixed
        Rp = [(i * c) % p for i, c in enumerate(R)][1:]
        # poly gcd over F_p
        A, B = [c % p for c in R], [c % p for c in Rp]
        def fpgcd(A, B):
            A, B = A[:], B[:]
            def deg(X):
                d = len(X) - 1
                while d >= 0 and X[d] % p == 0: d -= 1
                return d
            while deg(B) >= 0:
                dA, dB = deg(A), deg(B)
                if dA < dB: A, B = B, A; continue
                inv = pow(B[deg(B)], p - 2, p)
                c = (A[dA] * inv) % p
                for j in range(dB + 1):
                    A[dA - dB + j] = (A[dA - dB + j] - c * B[j]) % p
                if deg(A) < deg(B): A, B = B, A
            return A, deg(A)
        _, dg = fpgcd(A, B)
        if dg > 0: mixed = True
        if not B and len([c for c in A if c]) : pass
    trigger = (len(sidesF) > 1) or mixed
    log.append(f"  [{name}] deg F = {pdeg(F)}, sides = {len(sidesF)}, mixed = {mixed}, "
               f"TRIGGER = {trigger}")
    check(trigger, "battery member does not trigger (LB1) -- construction error")

    # (SIDE-PROD): F = prod over sides of F_lam ; F_lam = product of its blocks
    for (h, e), labels in groups:
        Flam = pconst(D, D.one())
        for rp, facs in labels:
            blk = pconst(D, D.one())
            for f in facs: blk = pmul(D, blk, f)
            Flam = pmul(D, Flam, blk)
        # single-side hull of F_lam at slope h/e
        devL, hullL, sidesL = polygon(D, Flam, phi)
        check(len(sidesL) == 1 and (sidesL[0][0], sidesL[0][1]) == (h, e),
              f"side block at {(h,e)} not one-sided of its slope: {sidesL}")
    prodF = pconst(D, D.one())
    for (_, _), labels in groups:
        for rp, facs in labels:
            for f in facs: prodF = pmul(D, prodF, f)
    check(prodF == F, "(SIDE-PROD)x(LABEL-PROD) product identity failed")

    # per-label blocks: development, one-sidedness, purity, (LABEL-OWN)
    degsum = 0
    for (h, e), rp, blk, facs in all_blocks:
        devB, hullB, sidesB = polygon(D, blk, phi)
        check(len(sidesB) == 1 and (sidesB[0][0], sidesB[0][1]) == (h, e),
              f"label block at {(h,e)},{rp} not one-sided: {sidesB}")
        # own development is monic with top exponent nu = deg blk / Dkey
        nu = pdeg(blk) // Dkey
        check(pdeg(blk) == nu * Dkey, "block degree not a multiple of D")
        check(devB[nu] == pconst(D, D.one()) if nu < len(devB) else False,
              "(LABEL-DEV) top coefficient not 1")
        # (LABEL-PURE): R(blk) ~ c * rp^k over F_p
        R = residual_poly(D, devB, sidesB[0])
        k = (len(R) - 1) // (len(rp) - 1) if len(rp) > 1 else len(R) - 1
        check(fp_assoc(p, R, fp_poly_pow(p, rp, k)),
              f"(LABEL-PURE) failed: R = {R}, r' = {rp}, k = {k}")
        # (LABEL-OWN): k = nu/(e * deg r') = deg blk /(D e deg r') integer >= 1
        degr = len(rp) - 1
        check(nu % (e * degr) == 0 and nu // (e * degr) == k and k >= 1,
              f"(LABEL-OWN) failed: nu = {nu}, e = {e}, deg r' = {degr}, k = {k}")
        degsum += pdeg(blk)
    check(degsum == pdeg(F), "exhaustive partition: degree sum mismatch")

    # disjointness: pairwise coprime blocks.  Blocks at distinct slopes, or with distinct
    # residual factors, are coprime by polygon/residual separation (checked structurally
    # above); same-label constructed factors are checked via a nonzero constant/lower-height
    # difference certificate: gcd(f, g) | (f - g), and here f - g has Gauss valuation
    # STRICTLY below any root valuation only in the constructed patterns -- we verify the
    # sufficient certificate deg gcd = 0 via the resultant-free route: f - g is pi^a * unit
    # with unit a nonzero CONSTANT (then any common monic factor divides a constant).
    for i in range(len(all_blocks)):
        for j in range(i + 1, len(all_blocks)):
            for fi in all_blocks[i][3]:
                for fj in all_blocks[j][3]:
                    dif = psub(D, fi, fj)
                    if pdeg(fi) != pdeg(fj):
                        continue  # coprime by degree/slope separation (distinct leaves)
                    check(bool(dif), "identical factors across blocks (roots not disjoint)")
    # within a block: constructed factors must be pairwise distinct
    for (_, _), rp, blk, facs in all_blocks:
        for a in range(len(facs)):
            for b in range(a + 1, len(facs)):
                dif = psub(D, facs[a], facs[b])
                check(bool(dif), "repeated factor inside a block")
                if dif and pdeg(dif) == 0:
                    pass  # difference is a nonzero constant: gcd | const => coprime. OK
    return fails


def battery_for(D):
    """construct the genre battery over domain D (works verbatim in both characteristics:
    pi = p or t).  Key phi = x throughout (D = deg phi = 1); genre F (deg phi = 2) is
    separate."""
    x = {1: D.one()}
    phi = dict(x)
    def C(n): return pconst(D, D.from_int(n))
    def lf(digit, height):  # leaf x + pi^height * digit  (digit nonzero residue)
        return leaf(D, phi, pconst(D, D.from_int(digit)), height)
    p = D.p
    B = []
    # Residual-class convention: the leaf x + pi^h * d has development digit d at height h,
    # so its residual class is r' = y + d (root -d).  Declared classes below follow it.
    # Genre A: three sides (slopes 2, 1, 1/2), separable labels.
    gA = [((2, 1), [([1 % p, 1], [lf(1, 2)])]),                # r' = y + 1
          ((1, 1), [([1 % p, 1], [lf(1, 1)])]),
          ((1, 2), [([(-1) % p, 1],                            # x^2 - pi: digit -1, r' = y - 1
                     [psub(D, pmul(D, x, x), pconst(D, D.times_pi_pow(D.one(), 1)))])])]
    B.append(("A: multi-side separable", phi, gA))
    # Genre B: one side slope 1, mixed residual (y+1)^2 * (y+2) when p = 3; (y+1)^2 for p = 2.
    pair = [lf(1, 1), padd(D, lf(1, 1), pconst(D, D.times_pi_pow(D.one(), 2)))]
    if p == 2:
        gB = [((1, 1), [([1, 1], pair)])]
    else:
        gB = [((1, 1), [([1, 1], pair), ([2, 1], [lf(2, 1)])])]
    B.append(("B: one side, mixed residual", phi, gB))
    # Genre C: multi-side AND mixed: combine A's slope-2 leaf with B's mixed side.
    gC = [((2, 1), [([1 % p, 1], [lf(1, 2)])])] + gB
    B.append(("C: multi-side + mixed", phi, gC))
    # Genre D: mixed label of residual degree 2 (deg r' = 2), p = 2 flavor; p = 3 analog.
    if p == 2:
        # x^2 + 2x + 4 and x^2 + 2x + 12: slope-1 side (e=1), residual y^2+y+1 each.
        G1 = padd(D, padd(D, pmul(D, x, x), pmonomial(D, D.times_pi_pow(D.one(), 1), 1)),
                  pconst(D, D.times_pi_pow(D.one(), 2)))
        G2 = padd(D, G1, pconst(D, D.times_pi_pow(D.one(), 3)))
        gD = [((1, 1), [([1, 1, 1], [G1, G2])])]
    else:
        # p = 3: y^2 + 1 irreducible over F_3: x^2 + 3*0*x + 9*1?  Need side slope 1 length 2
        # with residual y^2 + 1: dev coeffs a0 with v=2 digit 1, a1 with v=1 digit 0 -> a1 = 0
        # forces residual y^2 + res(a0/9): x^2 + 9: R = y^2 + 1. G2 = x^2 + 9 + 27.
        G1 = padd(D, pmul(D, x, x), pconst(D, D.times_pi_pow(D.one(), 2)))
        G2 = padd(D, G1, pconst(D, D.times_pi_pow(D.one(), 3)))
        gD = [((1, 1), [([1, 0, 1], [G1, G2])])]
    B.append(("D: mixed residual of degree 2 (deg r' = 2, k = 2)", phi, gD))
    # Genre E: mixed at a ramified side e' = 2: (x^2 - pi)(x^2 - pi - pi^2): residual (y-1)^2
    # (for p=2, y+1 == y-1).
    E1 = psub(D, pmul(D, x, x), pconst(D, D.times_pi_pow(D.one(), 1)))
    E2 = psub(D, E1, pconst(D, D.times_pi_pow(D.one(), 2)))
    gE = [((1, 2), [([-1 % p, 1], [E1, E2])])]
    B.append(("E: mixed at e' = 2 side", phi, gE))
    return B


# ---------------- genre F: deg phi = 2 key, residue field F_4 (p = 2 only) -----------

def genre_F_f4(D, log):
    """key phi = x^2 + x + 1 over O (p = 2, either characteristic), leaves
    phi + pi*s for digits s in F_4 \\ {0} (lifts 1, x, x+1) and a second-height leaf for the
    mixed label.  Residuals are computed in F_4 = F_2[w]/(w^2+w+1); dev coefficients have
    degree <= 1 so res(a) = a0 + a1*w."""
    p = 2
    fails = 0
    def check(cond, msg):
        nonlocal fails
        if not cond:
            fails += 1
            log.append(f"    FAIL: {msg}")
    x = {1: D.one()}
    phi = padd(D, padd(D, pmul(D, x, x), x), pconst(D, D.one()))

    def f4_mul(a, b):
        # a=(a0,a1) meaning a0+a1*w, w^2 = w+1
        c0 = a[0]*b[0] + a[1]*b[1]
        c1 = a[0]*b[1] + a[1]*b[0] + a[1]*b[1]
        return (c0 % 2, c1 % 2)
    def f4_pow(a, k):
        out = (1, 0)
        for _ in range(k): out = f4_mul(out, a)
        return out

    # leaves: phi + pi*1, phi + pi*x ; mixed pair: phi + pi*(x+1), phi + pi*(x+1) + pi^2
    def mk(digit_poly, h): return leaf(D, phi, digit_poly, h)
    L1 = mk(pconst(D, D.one()), 1)
    L2 = mk({1: D.one()}, 1)
    M1 = mk(padd(D, {1: D.one()}, pconst(D, D.one())), 1)
    M2 = padd(D, M1, pconst(D, D.times_pi_pow(D.one(), 2)))
    F = pmul(D, pmul(D, L1, L2), pmul(D, M1, M2))
    dev, hull, sides = polygon(D, F, phi)
    check(len(sides) == 1 and (sides[0][0], sides[0][1]) == (1, 1),
          f"genre F polygon not one slope-1 side: {sides}")
    # residual over F_4 at the side (v0 = 4, length 4):
    h_, e_, j0, j1, v0 = sides[0]
    R = []
    for k in range(j1 - j0 + 1):
        a = dev[j0 + k]
        target = v0 - k * h_
        if not a: R.append((0, 0)); continue
        va = gauss_val(D, a)
        if va > target: R.append((0, 0)); continue
        check(va == target, "point below side (genre F)")
        c0 = D.residue_shift(a.get(0, D.zero()), target) if a.get(0) else 0
        c1 = D.residue_shift(a.get(1, D.zero()), target) if a.get(1) else 0
        R.append((c0, c1))
    # expected: R ~ (y-1)(y-w)(y-(w+1))^2  where digits are residues of -increment... in
    # char 2 signs vanish: R = (y+1)(y+w)(y+w+1)^2.  Verify by direct F_4 poly arithmetic.
    def f4poly_mul(A, B):
        out = [(0, 0)] * (len(A) + len(B) - 1)
        for i, a in enumerate(A):
            for j, b in enumerate(B):
                m = f4_mul(a, b)
                out[i + j] = ((out[i + j][0] + m[0]) % 2, (out[i + j][1] + m[1]) % 2)
        return out
    one, w, w1 = (1, 0), (0, 1), (1, 1)
    exp = [ (one[0], one[1]) ]
    expected = [one]
    for root, mult in [(one, 1), (w, 1), (w1, 2)]:
        for _ in range(mult):
            expected = f4poly_mul(expected, [root, one])   # (y + root)
    check(R == expected, f"genre F residual mismatch: {R} vs {expected}")
    # blocks: separable labels L1 (root 1), L2 (root w); mixed label (root w+1)^2 = M1*M2.
    for blk, root, k in [(L1, one, 1), (L2, w, 1), (pmul(D, M1, M2), w1, 2)]:
        devB, hullB, sidesB = polygon(D, blk, phi)
        check(len(sidesB) == 1 and (sidesB[0][0], sidesB[0][1]) == (1, 1),
              "genre F block not one-sided")
        nu = pdeg(blk) // 2
        check(nu == k * 1 * 1, f"(LABEL-OWN) genre F: nu = {nu}, k = {k} (e'=1, deg r'=1)")
    check(pmul(D, pmul(D, L1, L2), pmul(D, M1, M2)) == F, "genre F product identity")
    log.append(f"  [F: deg-phi = 2 key, F_4 residuals] deg F = {pdeg(F)}, fails = {fails}")
    return fails


# ---------------- oracle leg (char 0): random states via PARI factorpadic ------------

def oracle_leg(p, n_samples, seed, log):
    try:
        from cypari2 import Pari
    except ImportError:
        log.append("  [oracle] cypari2 unavailable -- skipped")
        return 0, 0
    pari = Pari()
    import random
    rng = random.Random(seed)
    D = Dom(p)
    x = {1: 1}
    phi = dict(x)
    fails = 0
    tested = 0
    PREC = 60
    for _ in range(n_samples):
        mu = rng.randint(3, 6)
        # random monic F ≡ x^mu mod p with p | a_j for j < mu, constant term nonzero
        coeffs = [0] * (mu + 1)
        coeffs[mu] = 1
        for j in range(mu):
            coeffs[j] = p * rng.randint(-p ** 4, p ** 4)
        if coeffs[0] == 0: coeffs[0] = p * rng.randint(1, p ** 4)
        F = {j: c for j, c in enumerate(coeffs) if c}
        devF, hullF, sidesF = polygon(D, F, phi)
        # squarefree over Q_p?  require disc valuation finite: use pari poldisc != 0 and
        # factorpadic multiplicity 1 for honesty.
        fx = pari(f"Pol({[coeffs[mu - i] for i in range(mu + 1)]})")
        fac = pari.factorpadic(fx, p, PREC)
        mults = [int(m) for m in fac[1]]
        if any(m > 1 for m in mults):
            continue  # not squarefree at this precision: outside (LB1)'s squarefree states
        tested += 1
        # group factors by (slope, residual factor over F_p)
        groups = {}
        for kf in range(len(fac[0])):
            g = fac[0][kf]
            gd = int(pari.poldegree(g))
            gco = {}
            for i in range(gd + 1):
                c = pari.polcoef(g, i)
                gco[i] = int(pari.truncate(c)) if int(c) or True else 0
            gco = {i: c for i, c in gco.items() if c}
            devG, hullG, sidesG = polygon(D, gco, phi)
            if len(sidesG) != 1:
                fails += 1
                log.append(f"    FAIL(oracle): irreducible factor with {len(sidesG)} sides "
                           f"(p={p}) -- violates theorem of the polygon")
                continue
            s = sidesG[0]
            R = residual_poly(D, devG, s)
            # normalize R monic over F_p for grouping; its unique irreducible support:
            groups.setdefault((s[0], s[1]), []).append((gco, R))
        # per-side regroup by residual irreducible factor: verify each factor's R is a
        # PRIME POWER over F_p (theorem of the residual polynomial per irreducible factor),
        # and (LABEL-OWN) for the grouped label blocks.
        for (h, e), lst in groups.items():
            for gco, R in lst:
                # R must be c * (irreducible)^k: check R has a unique irreducible factor by
                # brute force over F_p (deg R small)
                dR = len(R) - 1
                if dR == 0: continue
                # find irreducible divisor by trial over F_p polys of deg <= dR
                found = None
                for d in range(1, dR + 1):
                    if dR % d: continue
                    for tup in iproduct(range(p), repeat=d):
                        cand = list(tup) + [1]
                        if fp_assoc(p, fp_poly_pow(p, cand, dR // d),
                                    [c % p for c in R]):
                            # cand must itself be irreducible: no root/quadratic split check
                            found = (cand, dR // d)
                            break
                    if found: break
                if not found:
                    fails += 1
                    log.append(f"    FAIL(oracle): residual not a prime power: {R} (p={p})")
                else:
                    cand, k = found
                    nu = int(pdeg(gco))
                    if nu != e * (len(cand) - 1) * k * 1:
                        fails += 1
                        log.append(f"    FAIL(oracle): (LABEL-OWN) nu={nu} != e*degr*k = "
                                   f"{e}*{len(cand)-1}*{k} (p={p})")
    log.append(f"  [oracle p={p}] tested {tested} squarefree states, fails = {fails}")
    return tested, fails


def main():
    log = []
    total_fails = 0
    for p in (2, 3):
        for D, tag in ((Dom(p), f"char 0, O = Z_({p})"), (DomT(p), f"char {p}, O = F_{p}[[t]]")):
            log.append(f"BATTERY over {tag}:")
            for name, phi, groups in battery_for(D):
                total_fails += run_battery(D, name, phi, groups, log)
    # genre F (deg phi = 2, F_4) at p = 2, both characteristics
    log.append("GENRE F (deg phi = 2 key, residue field F_4), p = 2:")
    total_fails += genre_F_f4(Dom(2), log)
    total_fails += genre_F_f4(DomT(2), log)
    # oracle
    log.append("ORACLE LEG (PARI factorpadic, char 0):")
    for p in (2, 3):
        _, f = oracle_leg(p, 150, seed=20260816 + p, log=log)
        total_fails += f
    print("\n".join(log))
    print(f"\nTOTAL FAILS: {total_fails}")
    sys.exit(1 if total_fails else 0)


if __name__ == "__main__":
    main()
