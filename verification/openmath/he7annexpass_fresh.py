"""HE7 ANNEX-PASS fresh route (hostile verifier, 2026-08-09) — the
probe the annex legs DISCLOSE as missing: a K3 = F_{p^2} level-3
family (g2 = 2), making ANNEX-THEOREM R1-b's WITHIN-CLASS twist units
vartheta_t VISIBLE for the first time anywhere in the program; plus a
symbolic check of ANNEX-LEMMA R1-a's cocycle recursion (R1.1).

FRAME = the sealed battery's (2,1,1): Phi' = x^2 - p, varpi = x,
K = K2 = F_p, l = 2, d_r = 1, u = 5 (lam = 5/2), D'' = 4, T2 = 10.
Level-2 datum for the level-3 key: (lam2 = u2, l2 = 1, r2 QUADRATIC
irreducible over F_p) — the JUMP gate l2*deg r2 = 2 fires with
g2 = deg r2 = 2, so K3 = F_{p^2} and the level-3 slot read has TWO
slots per class at heights k, k - u2 with within-class twist
theta_1 = n2(k-u2) n2(u2) / n2(k) = Lam1^{a}, res = s^{a}; with u2
ODD, a = 1 at every EVEN height k — the unit is LIVE (s in {2,3}).

Level-3 objects (ANNEX-DEF HE7-2', i = 2, l2 = 1): n3 = n2 (s2 == 0),
w3 = dv2, T3 = 2*u2, D3 = 8; key Psi2 := Psi^2 + C1*Psi + C0 with
DEFINITION HE7-3's inverse-twisted residues (c_t exponents at u2 odd:
c0 = 0, c1 = 1, c_top = 1, so res(C0) = b0*s, res(C1) = b1 for
r2 = Z^2 + b1 Z + b0). Members f := Psi2^2 + B1*Psi2 + B0, deg 16,
mu = 8, mu2 = 4, mu3 = 2, sigma decided over K3 = F_{p^2}.

PREREGISTERED CHECKS (written before the first run of this file).
  Q0  (EXACT, symbolic) ANNEX-LEMMA R1-a: the cocycle recursion (R1.1)
      holds as an exponent-vector identity at level 3 in BOTH frames
      (l2 = 2 rannex frame; l2 = 1 this frame), with carry c in {0,1},
      for all a, b in [-60, 60]; and R1-b's theta_t telescoping
      identity, exact in exponents.
  Q1  the ladder read FORWARD from f: level-1 single side 5/2 with
      residual (Z-s)^4; level-2 single side u2 (INTEGER slope, l2=1)
      of length 4 with residual == r2^2 over F_p (assembled with the
      level-2 twist convention) — the first machine contact of a
      degree-2 repeated level-2 residual factor.
  Q2  sigma (level-3 read over F_{p^2}, WITHIN-CLASS vartheta carried
      per R1-b, lifts inverse-twisted per R1-c) == PARI, member by
      member, sum ef = 16.
  Q3  TOOTH (the vartheta tooth — R1-b's new letter): reading with
      vartheta_1 := 1 (all else identical) FLIPS at least one
      member's sigma. This is the within-class analogue of
      HE7-T-BADTWIST, at the exact hole both annex legs disclose.
  Q4  M2R members (residual forced (Z-c)^2 over F_{p^2}, c built by
      R1-c's INVERSE vartheta-twist, including c outside F_p) fire
      the level-3 alpha-refine; every chain terminates with the
      refined-at slope strictly above the floor; no level-4 node.
  Q5  every lift3 satisfies its contract (dv3 == k, res3 == target)
      — the R1-c/R1-b roundtrip at live vartheta.

Oracle: pari_sigma16 (the F-1 leg's deg-16 route, p-maximal hint) —
independent of the reader.  Members Z_p only (same disclosure as the
annex legs).  Grid: p in {5,7}, s in {2,3}, u2 in {11,13}, two
irreducible quadratics r2 per p; kinds M1/M2/M2/M2R/M2R/M3 per row.
"""
import sys
import os
import json
import time
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from he7_pe3_probe12 import (Fr12, padd, pneg, pmul, pdivmod,
                             development, gcdi, disc_nonzero, BIG)
from he7annex_supp import pari_sigma16

RES = {'rows': [], 'checks': {}, 'viol': [], 'secs': 0}


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


# ---------- Q0: symbolic cocycle recursion (R1.1), exact -------------

def q0_symbolic():
    """R1.1 at level 3 in exponent vectors, both frames; theta
    telescoping.  Returns number of (a,b) pairs checked."""
    u = 5  # level-1: n2(k) = x^m Phi'^sv, 2m + 5sv = k, sv = k%2

    def W2(k):                       # n2 exponents (x, Phi')
        sv = k % 2
        return ((k - u * sv) // 2, sv)

    checked = 0
    # frame A: l2 = 2, u2 odd (the rannex frame); n3(k) =
    # n2(m2(k)) Psi^{s2(k)}, 2*m2 + s2*u2 = k, s2 = k%2
    for u2 in (21, 23):
        def V3(k):
            s2 = k % 2
            m2 = (k - s2 * u2) // 2
            a, b = W2(m2)
            return (a, b, s2)

        def tau3(a, b):
            return tuple(x + y - z for x, y, z
                         in zip(V3(a), V3(b), V3(a + b)))

        # Lam2 = Psi^2 / n2(u2): exponents (-(u2-5)//2, -1, 2)
        L2 = (-(u2 - 5) // 2, -1, 2)
        for a in range(-60, 61):
            for b in range(-60, 61):
                s2a, s2b, s2ab = a % 2, b % 2, (a + b) % 2
                c = (s2a + s2b - s2ab) // 2
                if c not in (0, 1):
                    viol('Q0 carry not in {0,1}', {'a': a, 'b': b})
                    return checked
                m2a, m2b = (a - s2a * u2) // 2, (b - s2b * u2) // 2

                def t2(x, y):        # tau2 embedded in 3-vector
                    e = tuple(p + q - r for p, q, r
                              in zip(W2(x), W2(y), W2(x + y)))
                    return (e[0], e[1], 0)

                lhs = tau3(a, b)
                r1 = t2(m2a, m2b)
                r2v = t2(m2a + m2b, c * u2)
                rhs = tuple(c * l + x + y for l, x, y
                            in zip(L2, r1, r2v))
                if lhs != rhs:
                    viol('Q0 R1.1 fails', {'a': a, 'b': b,
                                           'lhs': lhs, 'rhs': rhs})
                    return checked
                checked += 1
    # frame B: l2 = 1 (this probe): n3 = n2 and tau3 = tau2 (R1.1
    # with s2 == 0, c == 0) — check tau2 = Lam1^{c1}, c1 in {0,1}
    L1 = (-u, 2)                     # Lam1 = Phi'^2 / x^5
    for a in range(-60, 61):
        for b in range(-60, 61):
            c1 = ((a % 2) + (b % 2) - ((a + b) % 2)) // 2
            if c1 not in (0, 1):
                viol('Q0 level-2 carry', {'a': a, 'b': b})
                return checked
            e = tuple(p + q - r for p, q, r
                      in zip(W2(a), W2(b), W2(a + b)))
            if e != (c1 * L1[0], c1 * L1[1]):
                viol('Q0 tau2 != Lam1^c', {'a': a, 'b': b, 'e': e})
                return checked
            checked += 1
    # theta_t telescoping (R1-b Step 3), n2-system, t < 5
    for m0 in range(-40, 41):
        for t in range(5):
            th = tuple(p + t * q - r for p, q, r
                       in zip(W2(m0 - t * u), W2(u), W2(m0)))
            acc = (0, 0)
            for j in range(t):
                stp = tuple(
                    p + q - r for p, q, r
                    in zip(W2(m0 - (j + 1) * u), W2(u),
                           W2(m0 - j * u)))
                acc = (acc[0] + stp[0], acc[1] + stp[1])
            if th != acc:
                viol('Q0 theta telescoping', {'m0': m0, 't': t})
                return checked
            checked += 1
    return checked


# ---------- F_{p^2} arithmetic mod r2 = Z^2 + b1 Z + b0 --------------

class Fq2:
    def __init__(self, p, b1, b0):
        self.p, self.b1, self.b0 = p, b1, b0

    def add(self, x, y):
        return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)

    def smul(self, c, x):
        return ((c * x[0]) % self.p, (c * x[1]) % self.p)

    def mul(self, x, y):
        p, b1, b0 = self.p, self.b1, self.b0
        # (x0 + x1 B)(y0 + y1 B), B^2 = -b1 B - b0
        hi = x[1] * y[1]
        return ((x[0] * y[0] - hi * b0) % p,
                (x[0] * y[1] + x[1] * y[0] - hi * b1) % p)

    def inv(self, x):
        for a0 in range(self.p):
            for a1 in range(self.p):
                if self.mul(x, (a0, a1)) == (1, 0):
                    return (a0, a1)
        raise ZeroDivisionError(x)

    def elements(self):
        return [(a, b) for a in range(self.p) for b in range(self.p)]


def q2_roots(fq, c1, c0):
    """roots of Z^2 + c1 Z + c0 over F_{p^2}, brute force."""
    out = []
    for z in fq.elements():
        v = fq.add(fq.add(fq.mul(z, z), fq.mul(c1, z)), c0)
        if v == (0, 0):
            out.append(z)
    return out


# ---------- the level-3 kit at g2 = 2 (K3 = F_{p^2}) -----------------

class Fr3Q:
    def __init__(self, fr, u2, b1, b0):
        assert u2 % 2 == 1 and u2 > fr.T2   # l2 = 1, integer slope
        self.fr, self.p, self.s = fr, fr.p, fr.s
        self.u2, self.b1, self.b0 = u2, b1, b0
        self.fq = Fq2(fr.p, b1, b0)
        self.T3 = 2 * u2
        self.Psi = list(fr.Psi0)
        # DEFINITION HE7-3 key: Psi^2 + C1 Psi + C0, inverse-twisted
        # residues (u2 odd: c0 = 0, c1 = 1, c_top = 1):
        # res(C0) = b0 * s^(1-0), res(C1) = b1 * s^(1-1)
        C0 = fr.lift2(2 * u2, (b0 * fr.s) % fr.p)
        C1 = fr.lift2(u2, b1 % fr.p) if b1 % fr.p else []
        self.key0 = padd(padd(pmul(self.Psi, self.Psi),
                              pmul(C1, self.Psi)), C0)

    def svec(self, k):               # level-2 s-function (u = 5 odd)
        return k % 2

    def vartheta_exp(self, k, t):
        """theta_t = n2(k - t u2) n2(u2)^t / n2(k): Lam1-exponent."""
        S = self.svec(k - t * self.u2) + t * self.svec(self.u2) \
            - self.svec(k)
        assert S % 2 == 0
        return S // 2

    def vartheta(self, k, t):
        return pow(self.s, self.vartheta_exp(k, t) % (self.p - 1),
                   self.p)

    def dv3(self, A):
        if not A:
            return BIG
        cs = development(A, self.Psi, 2)
        return min((self.fr.dv2(c) if c else BIG) + t * self.u2
                   for t, c in enumerate(cs))

    def res3(self, A, k, naive=False):
        """K3 residue of A at height k per R1-b (i = 2, g2 = 2):
        gamma_t * vartheta_t in basis {1, beta2}; naive drops the
        within-class unit (vartheta_t := 1) — the Q3 tooth column."""
        cs = development(A, self.Psi, 2)
        out = []
        for t in range(2):
            ht = k - t * self.u2
            c = cs[t]
            g = self.fr.res2(c, ht) \
                if (c and self.fr.dv2(c) == ht) else 0
            th = 1 if naive else self.vartheta(k, t)
            out.append((g * th) % self.p)
        return (out[0], out[1])

    def lift3(self, k, c):
        """R1-c at g2 = 2: c = (g0, g1) in K3; slot t lifts
        gamma_t = g_t * vartheta_t^{-1} at level-2 height k - t u2."""
        p = self.p
        parts = []
        for t, g in enumerate(c):
            if g % p == 0:
                continue
            th = self.vartheta(k, t)
            raw = (g * pow(th, p - 2, p)) % p
            piece = self.fr.lift2(k - t * self.u2, raw)
            parts.append(pmul(piece, self.Psi) if t else piece)
        out = []
        for piece in parts:
            out = padd(out, piece)
        return out

    def bracket(self, yj, t, u3, y0):
        """side-assembly cocycle n3(yj) n3(u3)^t / n3(y0) with
        n3 = n2: a Lam1-power (K2-scalar)."""
        S = self.svec(yj) + t * self.svec(u3) - self.svec(y0)
        assert S % 2 == 0
        return pow(self.s, (S // 2) % (self.p - 1), self.p)


def hull_of(pins):
    hull = [pins[0]]
    for pt in pins[1:]:
        while len(hull) >= 2 and \
            (hull[-1][1] - hull[-2][1]) * (pt[0] - hull[-1][0]) >= \
                (pt[1] - hull[-1][1]) * (hull[-1][0] - hull[-2][0]):
            hull.pop()
        hull.append(pt)
    return hull


# ---------- forward ladder reads (Q1) --------------------------------

def read_level1(fr, f):
    p = fr.p
    A = development(f, fr.Phi, 9)
    ys = [fr.dv1(a) if a else BIG for a in A[:8]] + [0]
    pins = [(j, ys[j]) for j in range(9) if ys[j] < BIG]
    h = hull_of(pins)
    if len(h) != 2 or h[0] != (0, 20) or h[1] != (8, 0):
        return False
    csr = []
    for t in range(5):
        y = 20 - 5 * t
        csr.append(fr.res1(A[2 * t], y) if ys[2 * t] == y else 0)
    binom = [1, 4, 6, 4, 1]
    want = [pow((-fr.s) % p, 4 - t, p) * binom[t] % p for t in range(5)]
    inv = pow(csr[-1], p - 2, p) if csr[-1] else 0
    return [x * inv % p for x in csr] == want


def read_level2(fr, f, u2, b1, b0):
    """f's Psi-polygon: single INTEGER slope u2 side, length 4,
    twisted residual == r2^2 = (Z^2 + b1 Z + b0)^2 over F_p."""
    p = fr.p
    A = development(f, fr.Psi0, 5)
    ys = [fr.dv2(a) if a else BIG for a in A[:4]] + [0]
    if ys[0] >= BIG:
        return 'peel'
    pins = [(j, ys[j]) for j in range(5) if ys[j] < BIG]
    h = hull_of(pins)
    if len(h) != 2 or h[0] != (0, 4 * u2) or h[1] != (4, 0):
        return 'shape'
    csr = []
    for j in range(5):
        y = (4 - j) * u2
        raw = fr.res2(A[j], y) if (j < 4 and ys[j] == y) else \
            (1 if j == 4 else 0)
        S = (y % 2) + j * (u2 % 2) - ((4 * u2) % 2)
        if S % 2:
            return 'parity'
        csr.append((raw * pow(fr.s, (S // 2) % (p - 1), p)) % p)
    inv = pow(csr[-1], p - 2, p)
    got = [x * inv % p for x in csr]
    r2sq = [(b0 * b0) % p, (2 * b0 * b1) % p,
            (b1 * b1 + 2 * b0) % p, (2 * b1) % p, 1]
    return 'ok' if got == r2sq else 'res'


# ---------- the level-3 read over K3 = F_{p^2} -----------------------

def read_level3(f3, f, naive=False, cap=12):
    p, fq = f3.p, f3.fq
    key = list(f3.key0)
    g = list(f)
    letters = []
    floor = f3.T3
    nref = 0
    while True:
        mu3 = (len(g) - 1) // 8
        A = development(g, key, mu3 + 1)
        ys = [f3.dv3(a) for a in A[:mu3]] + [0]
        if ys[0] >= BIG:                   # peel: key | g
            q, r = pdivmod(g, key)
            if r:
                return 'peelfail'
            letters.append((4, 2))         # e=4, f=2 (deg-8 key)
            note('peel3')
            g = q
            if len(g) == 1:
                return (letters, nref)
            continue
        pins = [(j, ys[j]) for j in range(mu3 + 1) if ys[j] < BIG]
        h = hull_of(pins)
        refine = None
        for i in range(len(h) - 1):
            (j0, y0), (j1, y1) = h[i], h[i + 1]
            L = j1 - j0
            num, den = y0 - y1, L
            gg = gcdi(num, den)
            u3, l3 = num // gg, den // gg
            if num <= f3.T3 * den:
                return 'badslope'
            cs = []
            for t in range(L // l3 + 1):
                j = j0 + l3 * t
                yj = y0 - t * u3
                if j < mu3 and ys[j] == yj:
                    r3 = f3.res3(A[j], yj, naive=naive)
                elif j >= mu3 and yj == 0:
                    r3 = (1, 0)
                else:
                    r3 = (0, 0)
                br = f3.bracket(yj, t, u3, y0)
                cs.append(f3.fq.smul(br, r3))
            if cs[0] == (0, 0) or cs[-1] == (0, 0):
                return 'endpoint0'
            # normalize monic over F_{p^2}
            top = fq.inv(cs[-1])
            cs = [fq.mul(top, c) for c in cs]
            if len(cs) == 2:                # deg-1 residual over K3
                letters.append((4 * l3, 2))
                note('decided-lin')
            elif len(cs) == 3:              # deg-2 residual over K3
                roots = q2_roots(fq, cs[1], cs[0])
                if not roots:
                    letters.append((4 * l3, 4))
                    note('decided-irr')
                elif len(roots) == 2:
                    letters.append((4 * l3, 2))
                    letters.append((4 * l3, 2))
                    note('decided-split')
                else:                       # double root: refine
                    if l3 != 1:
                        return 'L4'
                    if refine is not None:
                        return 'tworefines'
                    if u3 <= floor:
                        return 'floorfail'
                    refine = (u3, roots[0])
            else:
                return 'longside'
        if refine is None:
            return (letters, nref)
        nref += 1
        if nref > cap:
            return 'refcap'
        lam, root = refine
        w = f3.lift3(lam, root)
        if f3.dv3(w) != lam or f3.res3(w, lam) != root:
            viol('Q5 lift3 contract', {'lam': lam, 'root': root})
            return 'liftfail'
        note('Q5-lift3-contract')
        key = padd(key, pneg(w))
        floor = lam
        note('refine3')


# ---------- members --------------------------------------------------

def build_member(f3, kind, rng):
    p, u2 = f3.p, f3.u2
    rnz = lambda: (rng.randrange(1, p), rng.randrange(p))
    if kind == 'M1':                        # single side, l3 = 2
        u3 = 4 * u2 + rng.choice([1, 3])
        B0 = f3.lift3(u3, rnz())
        B1 = []
    elif kind == 'M2':                      # single side, l3 = 1
        lam = 2 * u2 + rng.choice([2, 4])
        c0 = (rng.randrange(1, p), rng.randrange(p))
        c1 = (rng.randrange(p), rng.randrange(p))
        B0 = f3.lift3(2 * lam, c0)
        B1 = f3.lift3(lam, c1) if c1 != (0, 0) else []
    elif kind == 'M2R':                     # forced (Z-c)^2 over K3
        lam = 2 * u2 + rng.choice([2, 4])
        c = (rng.randrange(p), rng.randrange(1, p))   # c outside F_p
        fq = f3.fq
        br = [f3.bracket(2 * lam - t * lam, t, lam, 2 * lam)
              for t in range(3)]
        ibr = [pow(b, p - 2, p) for b in br]
        # target residual (Z - c)^2: coeffs c^2, -2c over K3, each
        # pre-divided by its assembly bracket (bracket of top absorbed
        # by monic normalization: multiply targets by br[2])
        t0 = fq.smul((br[2] * ibr[0]) % p, fq.mul(c, c))
        t1 = fq.smul((br[2] * ibr[1]) % p, fq.smul(p - 2, c))
        B0 = f3.lift3(2 * lam, t0)
        B1 = f3.lift3(lam, t1)
    else:                                   # M3: two sides
        la = 2 * u2 + rng.choice([1, 2])
        lb = la + 1 + rng.randrange(3)
        B1 = f3.lift3(la, rnz())
        B0 = f3.lift3(la + lb, rnz())
    # noise strictly above the pins
    for _ in range(2):
        gg = (rng.randrange(p), rng.randrange(p))
        if gg != (0, 0):
            base = f3.dv3(B0) if B0 else 4 * u2 + 4
            B0 = padd(B0, f3.lift3(base + 1 + rng.randrange(3), gg))
    key = f3.key0
    return padd(padd(pmul(key, key), pmul(B1, key)), B0)


def irr_quads(p):
    out = []
    for b1 in range(p):
        for b0 in range(1, p):
            if all((z * z + b1 * z + b0) % p for z in range(p)):
                out.append((b1, b0))
    return out


def main():
    t0 = time.time()
    rng = random.Random(20260809)
    nq0 = q0_symbolic()
    print('Q0 symbolic cocycle checks: %d EXACT, violations so far %d'
          % (nq0, len(RES['viol'])))
    RES['checks']['Q0-exact'] = nq0
    members = agree = flips = refs = 0
    sigs = {}
    for p in (5, 7):
        quads = irr_quads(p)[:2]
        for s in (2, 3):
            fr = Fr12(p, 5, s)
            for u2 in (11, 13):
                for (b1, b0) in quads:
                    f3 = Fr3Q(fr, u2, b1, b0)
                    for kind in ('M1', 'M2', 'M2', 'M2R', 'M2R',
                                 'M3'):
                        f = build_member(f3, kind, rng)
                        if len(f) != 17:
                            viol('degree', {'deg': len(f) - 1})
                            continue
                        if not disc_nonzero(f):
                            note('disc0-discard')
                            continue
                        if not read_level1(fr, f):
                            viol('Q1 level-1', {'kind': kind})
                            continue
                        st2 = read_level2(fr, f, u2, b1, b0)
                        if st2 != 'ok':
                            viol('Q1 level-2 ' + st2, {'kind': kind})
                            continue
                        note('Q1-ladder')
                        out = read_level3(f3, f)
                        if isinstance(out, str):
                            viol('level-3 read ' + out,
                                 {'kind': kind})
                            continue
                        letters, nref = out
                        sig = tuple(sorted(letters))
                        if sum(e * ff for e, ff in sig) != 16:
                            viol('sum ef != 16', {'sig': sig})
                            continue
                        gs = pari_sigma16(f, p)
                        members += 1
                        refs += nref
                        if kind == 'M2R' and nref > 0:
                            note('Q4-refine-fired')
                        if gs == sig:
                            agree += 1
                            note('Q2-sigma-agree')
                        else:
                            viol('Q2 sigma mismatch',
                                 {'kind': kind, 'read': sig,
                                  'pari': gs, 'p': p, 's': s,
                                  'u2': u2, 'r2': (b1, b0)})
                        outn = read_level3(f3, f, naive=True)
                        sign = tuple(sorted(outn[0])) \
                            if not isinstance(outn, str) \
                            else ('ERR', outn)
                        if sign != sig:
                            flips += 1
                            note('Q3-vartheta-flip')
                        k = str(sig)
                        sigs[k] = sigs.get(k, 0) + 1
    RES['secs'] = round(time.time() - t0, 1)
    RES['summary'] = {'members': members, 'pari_agree': agree,
                      'vartheta_flips': flips, 'refines3': refs,
                      'sigmas': sigs, 'q0_exact': nq0,
                      'violations': len(RES['viol'])}
    print(json.dumps(RES['summary'], indent=1))
    verdict = 'GREEN' if (not RES['viol'] and agree == members
                          and members > 0 and flips >= 1
                          and RES['checks'].get('Q4-refine-fired', 0)
                          and nq0 > 0) else 'RED'
    print('VERDICT %s — %d members, PARI %d/%d, vartheta flips %d, '
          'level-3 refines %d, Q0 %d, %.1f s'
          % (verdict, members, agree, members, flips, refs, nq0,
             RES['secs']))
    RES['verdict'] = verdict
    with open(os.path.join(HERE, 'he7annexpass_fresh_results.json'),
              'w') as fh:
        json.dump(RES, fh, indent=1)
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
