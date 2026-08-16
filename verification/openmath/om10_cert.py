#!/usr/bin/env python3
"""OM-10 certification battery — the n >= 8 box family
(HYP.67-71, HYP.78-80, HYP.142, HYP.143, HYP.144-BOX-2).

Unit note: docs/openmath-campaign/OM-10_n8-boxes_2026-08-16.md (S1 outline).

LEGS (grouped by the outline's mechanism groups):
  A  (GROUP A, HYP.143)  branch (ii) of LEMMA HE3-4 — FIRST machine contact:
     mu = 4 decided-leaf members with an ell = 2 fractional side, all four cells
     {two linear labels} x {irreducible quadratic label} x {(e1,f1) = (2,1), (1,2)},
     mixed AND equal characteristic; class sizes |S_r| = D'*ell*deg r checked by
     elementary certificates (value-group forcing + residue forcing, exhaustive
     divisor arithmetic) + PARI decorrelation; the box's failure mode probed by a
     perturbation sweep; the higher-order test-polynomial separation (A-S3) and
     the count inversion (A-S5) measured by exact integer resultants.
  B  (GROUP B, HYP.79 + HYP.67 slice)  the p | binom(mu2,2) classification:
     single-slot geographies (X/P3) at fresh mu2 + the k-cascade geography (B/BP)
     at mu2 = 3..6, dual-route shadow instrument (fresh implementation).
  C  (GROUP C, HYP.67 f1>=2 face, HYP.80, HYP.70)  FIRST machine contact of the
     f1 >= 2 x mu2 >= 3 compound (frames F23/F22, eta != 1 axis included) + the
     new x-ful f1 = 2 row at mu2 = 2 (HYP.70).
  E  (GROUP E, HYP.71/69/78)  entry-driven witnesses at genres with the key
     self-power below D' in x (W1/W2, D' = 3, all key pairs in-grid); the
     obstruction pair reproduction; the E-S4 congruence-candidate attack.
  D  (GROUP D, HYP.68/144-BOX-2)  THEOREM GENTOW-6.6(c): first direct
     window-enumeration check of the ledger identity + fiber clause + c +- 1
     teeth; the c_J integer identity grid. (HYP.142's F9 leg is the separate
     script om10_f9_count.py — long-running.)

Exact arithmetic throughout (integers / F_q[t] own code); PARI via gp -q -f
(the pinned w12 GP_FUN convention, as in om7_cert.py).

Usage: python3 om10_cert.py [A|B|C|D|E|all]
"""
import sys
import subprocess
from fractions import Fraction

# ======================================================================
# Part 0 — shared exact primitives (own code)
# ======================================================================

def pstrip(f):
    while f and f[-1] == 0:
        f.pop()
    return f

def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])

def pneg(f):
    return [-c for c in f]

def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return pstrip(out)

def ppow(f, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, f)
    return out

def pdivmod(f, g):
    f = list(f)
    assert g and g[-1] == 1, 'divisor not monic'
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while pstrip(f) and len(f) - 1 >= dg:
        d = len(f) - 1 - dg
        c = f[-1]
        q[d] = c
        for k in range(len(g)):
            f[d + k] -= c * g[k]
        pstrip(f)
    return pstrip(q), pstrip(f)

def dev(C, PHI, nslots):
    """PHI-adic development of C into nslots coefficients."""
    out, r = [], list(C)
    for _ in range(nslots):
        r, rem = pdivmod(r, PHI)
        out.append(rem)
    assert not pstrip(r), 'dev overflow'
    return out

def vp(n, p):
    n = abs(n)
    assert n
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def resultant_int(f, g):
    """Sylvester resultant of integer polys (lists, ascending), exact.
    Fraction Gaussian elimination on the Sylvester matrix."""
    m, n = len(f) - 1, len(g) - 1
    assert m >= 0 and n >= 0
    if m == 0:
        return f[0] ** n
    if n == 0:
        return g[0] ** m
    N = m + n
    M = []
    fr = list(reversed(f))
    gr = list(reversed(g))
    for i in range(n):
        M.append([0] * i + fr + [0] * (n - 1 - i))
    for i in range(m):
        M.append([0] * i + gr + [0] * (m - 1 - i))
    M = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for col in range(N):
        piv = None
        for r in range(col, N):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = -det
        det *= M[col][col]
        inv = 1 / M[col][col]
        for r in range(col + 1, N):
            if M[r][col] != 0:
                fac = M[r][col] * inv
                for c in range(col, N):
                    M[r][c] -= fac * M[col][c]
    assert det.denominator == 1
    return int(det)

# ---- F_q arithmetic (q = p^k, small) ---------------------------------

class GF:
    """F_p[y]/(mod), elements = tuples of length k (ascending)."""
    def __init__(self, p, mod):
        self.p = p
        self.mod = mod            # list, monic, ascending, len k+1
        self.k = len(mod) - 1
        self.q = p ** self.k
        self.zero = (0,) * self.k
        self.one = tuple([1] + [0] * (self.k - 1))

    def els(self):
        out = []
        def rec(pref):
            if len(pref) == self.k:
                out.append(tuple(pref))
                return
            for c in range(self.p):
                rec(pref + [c])
        rec([])
        return out

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def neg(self, a):
        return tuple((-x) % self.p for x in a)

    def mul(self, a, b):
        prod = [0] * (2 * self.k - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] = (prod[i + j] + x * y) % self.p
        for d in range(len(prod) - 1, self.k - 1, -1):
            c = prod[d]
            if c:
                prod[d] = 0
                for j in range(self.k):
                    prod[d - self.k + j] = (prod[d - self.k + j]
                                            - c * self.mod[j]) % self.p
        return tuple(prod[:self.k])

    def pow(self, a, n):
        out = self.one
        while n:
            if n & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            n >>= 1
        return out

    def inv(self, a):
        assert a != self.zero
        return self.pow(a, self.q - 2)

    def is_square(self, a):
        if a == self.zero:
            return True
        return self.pow(a, (self.q - 1) // 2) == self.one

# ---- F_q[t] polynomials in x: coefficients are dicts {t-deg: GF elt} --

class EqChar:
    """Polynomials in x over F_q[t]; a poly = list (ascending in x) of
    dicts {j: GF element} meaning sum c_j t^j."""
    def __init__(self, K):
        self.K = K

    def czero(self):
        return {}

    def cstrip(self, c):
        return {j: v for j, v in c.items() if v != self.K.zero}

    def cadd(self, a, b):
        out = dict(a)
        for j, v in b.items():
            out[j] = self.K.add(out.get(j, self.K.zero), v)
        return self.cstrip(out)

    def cneg(self, a):
        return {j: self.K.neg(v) for j, v in a.items()}

    def cmul(self, a, b):
        out = {}
        for i, x in a.items():
            for j, y in b.items():
                k = i + j
                out[k] = self.K.add(out.get(k, self.K.zero),
                                    self.K.mul(x, y))
        return self.cstrip(out)

    def cval(self, c):
        c = self.cstrip(c)
        return min(c) if c else None

    def xstrip(self, f):
        while f and not self.cstrip(f[-1]):
            f.pop()
        return f

    def xadd(self, f, g):
        n = max(len(f), len(g))
        return self.xstrip([self.cadd(f[i] if i < len(f) else {},
                                      g[i] if i < len(g) else {})
                            for i in range(n)])

    def xneg(self, f):
        return [self.cneg(c) for c in f]

    def xmul(self, f, g):
        if not f or not g:
            return []
        out = [dict() for _ in range(len(f) + len(g) - 1)]
        for i, a in enumerate(f):
            for j, b in enumerate(g):
                out[i + j] = self.cadd(out[i + j], self.cmul(a, b))
        return self.xstrip(out)

    def xpow(self, f, k):
        out = [{0: self.K.one}]
        for _ in range(k):
            out = self.xmul(out, f)
        return out

    def is_monic(self, f):
        return f and f[-1] == {0: self.K.one}

    def xdivmod(self, f, g):
        f = [dict(c) for c in f]
        assert self.is_monic(g)
        dg = len(g) - 1
        q = [dict() for _ in range(max(1, len(f) - dg))]
        while self.xstrip(f) and len(f) - 1 >= dg:
            d = len(f) - 1 - dg
            c = f[-1]
            q[d] = self.cadd(q[d], c)
            for k in range(len(g)):
                f[d + k] = self.cadd(f[d + k],
                                     self.cneg(self.cmul(c, g[k])))
            self.xstrip(f)
        return self.xstrip(q), self.xstrip(f)

    def xdev(self, C, PHI, nslots):
        out, r = [], [dict(c) for c in C]
        for _ in range(nslots):
            r, rem = self.xdivmod(r, PHI)
            out.append(rem)
        assert not self.xstrip(r), 'xdev overflow'
        return out

# ---- harness ---------------------------------------------------------

NCHK = 0
NVIO = 0
TALLY = {}
KILLS = {}

def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    TALLY[tag] = TALLY.get(tag, 0) + 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

def tooth(name, killed, msg):
    KILLS[name] = KILLS.get(name, 0) + (1 if killed else 0)
    chk('TEETH', killed, 'tooth %s NOT killed: %s' % (name, msg))

# ---- PARI (the pinned w12 GP_FUN convention) -------------------------

GP_FUN = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sig(f, p) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
"""

def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) \
        or '0'

def gp_sig_batch(jobs):
    """jobs = [(coeff list ascending, p, tag)]; returns dict tag -> sig."""
    if not jobs:
        return {}
    lines = [GP_FUN]
    for i, (f, p, _) in enumerate(jobs):
        lines.append('print("R %d ", sig(%s, %d))' % (i, polystr(f), p))
    lines.append('quit')
    r = subprocess.run(['gp', '-q', '-f'],
                       input=('\n'.join(lines) + '\n').encode(),
                       capture_output=True, timeout=1200)
    out = r.stdout.decode()
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            nums = [int(x) for x in rest.replace('[', ' ')
                    .replace(']', ' ').replace(',', ' ').split()]
            got[int(idx)] = tuple(sorted(zip(nums[0::2], nums[1::2])))
    return {jobs[i][2]: got.get(i) for i in range(len(jobs))}

# ======================================================================
# LEG A — HYP.143: branch (ii) of LEMMA HE3-4, first machine contact
# ======================================================================
#
# Configurations (all at the decided-leaf shape: stage polygon of f at the
# key PHI' has ONE side of fractional dv-slope lambda = u/2, length 4,
# with separable residual of degree 2 — the box's exact geography, live
# first at mu = 4, n = D'*mu = 8):
#
#  A1 (e1,f1) = (2,1), O = Z_5, PHI' = x^2 - 5, h = 1, dv = 2v,
#     lambda = 5/2 (u = 5, letters c*25x at dv = 5, labels in F_5^x):
#     A1a  R_lambda = (Z-1)(Z-2): f = (PHI'^2-25x)(PHI'^2-50x), deg 8.
#          Elementary: each quartic has v(PHI'(rho)) = 5/4 => 4 | e =>
#          irreducible with (e,f) = (4,1). Predict sigma = {(4,1),(4,1)},
#          |S_{Z-1}| = |S_{Z-2}| = 4 = D'*ell*d = 2*2*1.
#     A1b  R_lambda = Z^2 - 2 (2 a non-square mod 5): f = PHI'^4 - 2*625x^2.
#          beta^2 = 2 => f >= 2, 4 | e, ef <= 8 => (e,f) = (4,2), deg 8
#          irreducible. |S_r| = D'*ell*d = 8.
#     A1c  the failure-mode sweep: perturbed leaf members (noise above the
#          residual grade at every slot); PARI sigma must stay the row's
#          sigma; label attribution by resultant jump must stay 4/4 (A1a).
#  A2 (e1,f1) = (1,2), O = Z_3, PHI' = x^2 - 18 (root 3*sqrt2, K = F_9,
#     eta = sqrt2 != 1), h = 1, dv = v, lambda = 5/2 (u = 5, letter 3^4*x):
#     A2a  labels 1, -1 (in F_3 subset F_9): f = (PHI'^2-3^5)(PHI'^2+3^5).
#          Each quartic: v(PHI') = 5/2 => e even; label read beta = +-1;
#          stage (e_s,f_s) = (2,1) => (e,f) = (2,2). sigma = {(2,2),(2,2)}.
#     A2b  label omega in F_9 non-square (residual Z^2 - omega irreducible
#          over F_9): f = PHI'^4 - W^2-lift, predict (e,f) = (2,4), deg 8
#          irreducible. |S_r| = 8 = D'*ell*d.
#  A3 equal characteristic F_3[[t]], PHI' = x^2 - t (e1 = 2, f1 = 1):
#     A3a  f = (PHI'^2 - t^2 x)(PHI'^2 - 2 t^2 x): construction certificates
#          (exact relations PHI'(rho)^2 = c t^2 rho per factor; value-group
#          forcing v(PHI') = 5/4 => e = 4 per quartic).
#     A3b  f = PHI'^4 - 2 t^4 x^2 (2 = -1 non-square mod 3): v-forcing +
#          residue forcing => (e,f) = (4,2), irreducible octic.
#  A-S3 separation + A-S5 inversion (on A1): the test family
#     Psi_{s,r} = PHI'^2 - s*25x - 5^r x at integer anchor heights
#     kappa = 2r+1: 2*v(Res(f, Psi_{s,r})) reads Sum_rho min(X_rho^s, kappa);
#     the kappa-slope recovers |S_s| = 4; non-labels read flat 40.
#
# Teeth: T-A-DPRIME (the mutant law |S_r| = D'*d — the ramified rescale
# forgotten — must fail against every measured row); T-A-EMPTY (the box's
# failure mode "one label empty, the other carries two orbits" must be
# killed by the resultant attribution on every A1a-family member);
# T-A-SIG (a flipped label pair on A1a must be caught by the residual read).

def leg_A():
    print('== LEG A (HYP.143 branch (ii)) ==')
    p5 = 5

    # ---------- A1: Z_5, PHI' = x^2 - 5 ------------------------------
    PHI = [-5, 0, 1]
    P2 = pmul(PHI, PHI)
    letter = lambda s, r=2: [0, s * 5 ** r]          # s * 5^r * x
    g1 = padd(P2, pneg(letter(1)))                    # PHI'^2 - 25x
    g2 = padd(P2, pneg(letter(2)))                    # PHI'^2 - 50x
    fA1a = pmul(g1, g2)
    fA1b = padd(ppow(PHI, 4), pneg([0, 0, 2 * 5 ** 4]))  # PHI'^4 - 2*625x^2

    # elementary certificates (script-checked arithmetic):
    # stage development of fA1a: A_j = dev(f, PHI'), dv heights of slots.
    def dvmon(c, a, e1, dvx, dvp, p):
        # dv of integer-coefficient monomial c * x^a
        return e1 * 0 + dvp * vp(c, p) + dvx * a if c else None

    def dv_xpoly(g, dvx, dvp, p):
        vals = [dvp * vp(c, p) + dvx * i for i, c in enumerate(g) if c]
        return min(vals) if vals else None

    A = dev(fA1a, PHI, 5)
    chk('A1', A[4] == [1], 'A1a top slot')
    # stage polygon: dv(A_j) with dv(x)=1, dv(5)=2 (e1 = 2).
    # NOTE (run-1 disclosure): the x^2 = PHI' + 5 re-expansion moves the
    # 1250x^2 term into slots j = 0, 1 (A0 = 6250, A1 = 1250 at dv 8);
    # the polygon is STILL the single side (0,10)-(4,0) of slope 5/2
    # (j = 1 at dv 8 > 7.5, j = 3 empty), which is the honest read.
    dvs = [dv_xpoly(a, 1, 2, p5) for a in A[:4]]
    chk('A1', dvs[0] == 10, 'A1a dv(A0) = 10, got %s' % dvs[0])
    chk('A1', dvs[2] == 5, 'A1a dv(A2) = 5, got %s' % dvs[2])
    for j in (1, 3):
        chk('A1', dvs[j] is None or 2 * dvs[j] > 5 * (4 - j),
            'A1a slot j=%d strictly above the side: %s' % (j, dvs[j]))
    chk('A1', A[2] == [0, -75], 'A1a A2 = -75x')
    chk('A1', A[0] == [6250] and A[1] == [1250],
        'A1a re-expanded slots A0 = 6250, A1 = 1250; got %s / %s'
        % (A[0], A[1]))
    # value-group forcing per quartic: PHI'(rho)^2 = s*25*rho exactly =>
    # 2 dv(PHI'(rho)) = 5 + dv(rho); PHI' = rho^2 - 5 forces dv(rho) = 1
    # (case check below), so dv(PHI'(rho)) = 5/2, v = 5/4 => 4 | e => each
    # quartic irreducible (e,f) = (4,1). Exhaustive divisor arithmetic:
    cand = [(e, f) for e in range(1, 9) for f in range(1, 9)
            if e * f <= 4 and e % 4 == 0]
    chk('A1', cand == [(4, 1)], 'A1a quartic component census: %s' % cand)
    # dv(rho) case check, exact: if dv(rho) = a then dv(PHI'(rho)) is
    # min(2a, 2) unless 2a = 2; equation 2*min(2a,2) = 5 + a has no
    # solution with 2a != 2 in (1/4)Z, so 2a = 2, a = 1:
    bad = [Fraction(n, 4) for n in range(0, 41)]
    sols = [a for a in bad if 2 * a != 2 and 2 * min(2 * a, 2) == 5 + a]
    chk('A1', sols == [], 'A1a value-group forcing case check')

    # A1b: dev + forcing (same re-expansion note: A1 = -1250 at dv 8,
    # strictly above the side; the residual is carried by the EXACT
    # relation PHI'(rho)^4 = 1250 rho^2, i.e. beta^2 = 2)
    B = dev(fA1b, PHI, 5)
    dvsB = [dv_xpoly(b, 1, 2, p5) for b in B[:4]]
    chk('A1', dvsB[0] == 10, 'A1b dv(A0) = 10: %s' % dvsB)
    for j in (1, 2, 3):
        chk('A1', dvsB[j] is None or 2 * dvsB[j] > 5 * (4 - j),
            'A1b slot j=%d strictly above the side: %s' % (j, dvsB[j]))
    chk('A1', B[0] == [-6250] and B[1] == [-1250],
        'A1b re-expanded slots; got %s / %s' % (B[0], B[1]))
    # residual Z^2 - 2 over F_5: 2 must be a non-square mod 5
    chk('A1', all(pow(z, 2, 5) != 2 for z in range(5)),
        'A1b 2 is a non-square mod 5')
    # forcing: beta^2 = 2 => residue degree even; 4 | e; ef <= 8:
    cand = [(e, f) for e in range(1, 9) for f in range(1, 9)
            if e * f <= 8 and e % 4 == 0 and f % 2 == 0]
    chk('A1', cand == [(4, 2)], 'A1b octic component census: %s' % cand)

    # ---------- A1c perturbation sweep (the failure-mode attack) -----
    # leaf-preserving noise: A3 += 5^2 x (dv 5 >= 3), A1 += 5^4 x (dv 9
    # >= 8), A2 += 5^3 (dv 6 > 5), A0 += 5^6 (dv 12 > 10) with unit
    # multipliers swept.
    sweep = []           # list of (tuple, member)
    for c3 in (0, 1, 2):
        for c1 in (0, 1):
            for c2 in (0, 1, 3):
                for c0 in (0, 2):
                    if (c3, c1, c2, c0) == (0, 0, 0, 0):
                        continue          # the exact product, handled above
                    g = list(fA1a)
                    noise = [0]
                    if c3:
                        noise = padd(noise, pmul([0, c3 * 25], ppow(PHI, 3)))
                    if c1:
                        noise = padd(noise, pmul([0, c1 * 5 ** 4], PHI))
                    if c2:
                        noise = padd(noise, pmul([c2 * 5 ** 3], ppow(PHI, 2)))
                    if c0:
                        noise = padd(noise, [c0 * 5 ** 6])
                    sweep.append(((c3, c1, c2, c0), padd(g, noise)))
    # PARI on all sweep members + the two named rows
    jobs = [(fA1a, 5, 'A1a'), (fA1b, 5, 'A1b')]
    jobs += [(m, 5, 'A1c-%d' % i) for i, (_, m) in enumerate(sweep)]

    # ---------- A2: Z_3, PHI' = x^2 - 18 (f1 = 2, eta != 1) ----------
    PHI3 = [-18, 0, 1]
    P23 = pmul(PHI3, PHI3)
    gA2a1 = padd(P23, pneg([3 ** 5]))     # PHI'^2 - 243
    gA2a2 = padd(P23, [3 ** 5])           # PHI'^2 + 243
    fA2a = pmul(gA2a1, gA2a2)             # = PHI'^4 - 3^10
    # A2b: omega a non-square in F_9^x. F_9 = F_3[y]/(y^2-2), y = res(x/3).
    F9 = GF(3, [-2 % 3, 0, 1])
    y = (0, 1)
    chk('A2', F9.mul(y, y) == (2, 0), 'F9 arithmetic: y^2 = 2')
    chk('A2', F9.is_square((2, 0)), '2 = -1 is a square in F9')
    om = None
    for cand_el in F9.els():
        if cand_el != F9.zero and not F9.is_square(cand_el):
            om = cand_el
            break
    chk('A2', om is not None, 'found a non-square omega in F9')
    # lift omega = a + b*y to A0 = -(a*3^10 + b*3^9*x) (dv = 10 for each
    # monomial; the two monomials sit in independent residue directions)
    a_, b_ = om
    fA2b = padd(ppow(PHI3, 4), pneg([a_ * 3 ** 10, b_ * 3 ** 9]))
    # value-group forcing A2a: PHI'(rho)^2 = +-3^5 => dv(PHI') = 5/2 in
    # dv = v units (e1 = 1): v = 5/2 => 2 | e; label +-1 in F_3 => f_s = 1
    # but f1 = 2 => f = 2; ef <= 4 => (2,2):
    cand = [(e, f) for e in range(1, 5) for f in range(1, 5)
            if e * f <= 4 and e % 2 == 0 and f % 2 == 0]
    chk('A2', cand == [(2, 2)], 'A2a quartic component census: %s' % cand)
    # A2b: beta^2 = omega non-square in F_9 => residue field >= F_81 =>
    # 4 | f; e even; ef <= 8 => (2,4):
    cand = [(e, f) for e in range(1, 9) for f in range(1, 9)
            if e * f <= 8 and e % 2 == 0 and f % 4 == 0]
    chk('A2', cand == [(2, 4)], 'A2b octic component census: %s' % cand)
    jobs += [(fA2a, 3, 'A2a'), (fA2b, 3, 'A2b')]

    # run PARI batch
    sigs = gp_sig_batch(jobs)
    chk('A1', sigs['A1a'] == ((4, 1), (4, 1)),
        'A1a PARI sigma = {(4,1),(4,1)}, got %s' % (sigs['A1a'],))
    chk('A1', sigs['A1b'] == ((4, 2),),
        'A1b PARI sigma = {(4,2)}, got %s' % (sigs['A1b'],))
    chk('A2', sigs['A2a'] == ((2, 2), (2, 2)),
        'A2a PARI sigma = {(2,2),(2,2)}, got %s' % (sigs['A2a'],))
    chk('A2', sigs['A2b'] == ((2, 4),),
        'A2b PARI sigma = {(2,4)}, got %s' % (sigs['A2b'],))
    nswp = 0
    for i in range(len(sweep)):
        s = sigs['A1c-%d' % i]
        chk('A1c', s == ((4, 1), (4, 1)),
            'A1c sweep %d sigma, got %s' % (i, s))
        nswp += 1
    print('  A1c sweep: %d perturbed leaf members, sigma stable' % nswp)

    # ---------- A-S3/A-S5: separation + count inversion on A1 --------
    # Anchored test family: Psi_{s,kappa} = PHI'^2 - s*25x - (letter at
    # dv-height kappa), with anchors kappa = 6 (letter 5^3) and 7
    # (letter 5^3 x). Root side: 2*v5(Res(f, Psi_{s,kappa})) =
    # Sum_rho min(X_rho^s, kappa) with X_rho^s := dv(PHI'(rho)^2 -
    # s*25*rho). Separation (A-S3): X > 5 exactly on the label-s class.
    # Inversion (A-S5): T(7) - T(6) = #{rho : X_rho^s > 6} = |S_s| when
    # the member's own-label depth exceeds 6.
    def anchored_T(f, s, kap):
        if kap == 6:
            Psi = padd(P2, pneg(padd([0, s * 25], [5 ** 3])))
        elif kap == 7:
            Psi = padd(P2, pneg([0, s * 25 + 5 ** 3]))
        else:
            raise ValueError(kap)
        R = resultant_int(f, Psi)
        assert R != 0
        return 2 * vp(R, 5)

    for s in (1, 2, 3, 4):
        T6, T7 = anchored_T(fA1a, s, 6), anchored_T(fA1a, s, 7)
        if s in (1, 2):
            chk('AS3', (T6, T7) == (44, 48),
                'label s=%d anchored reads (44,48): got %s'
                % (s, (T6, T7)))
            chk('AS5', T7 - T6 == 4,
                's=%d inversion slope = |S_s| = 4, got %d' % (s, T7 - T6))
        else:
            chk('AS3', (T6, T7) == (40, 40),
                'non-label s=%d flat read 40: got %s' % (s, (T6, T7)))
    # inversion on a PERTURBED member (deep noise only: c0 = 2, i.e.
    # f = g1*g2 + 2*5^6, own-label depth X = 7 > 6):
    fpert = next(m for (t, m) in sweep if t == (0, 0, 0, 2))
    for s in (1, 2, 3, 4):
        T6, T7 = anchored_T(fpert, s, 6), anchored_T(fpert, s, 7)
        if s in (1, 2):
            chk('AS5', T7 - T6 == 4,
                'pert s=%d inversion slope 4, got %d (%s)'
                % (s, T7 - T6, (T6, T7)))
        else:
            chk('AS3', (T6, T7) == (40, 40),
                'pert non-label s=%d flat: %s' % (s, (T6, T7)))
    # ---------- the failure-mode census over the WHOLE sweep ---------
    # For every perturbed leaf member: T_s := 2*v5(Res(f, Psi_s)) with
    # NO anchor. Non-labels read exactly 40 (all X = 5); labels read
    # >= 42 (own-label X >= 5.5 by residue cancellation), or Res = 0
    # (Psi_s divides f: label certainly nonempty). Both labels nonempty
    # + PARI degree split 4+4 forces |S_1| = |S_2| = 4 — the box's
    # failure mode ("one class empty while the other carries two Galois
    # orbits") is EXCLUDED on every measured member.
    fail_census_ok = True
    for (t, m) in sweep:
        for s in (1, 2, 3, 4):
            Psi = padd(P2, pneg([0, s * 25]))
            R = resultant_int(m, Psi)
            if s in (1, 2):
                ok = (R == 0) or 2 * vp(R, 5) >= 42
            else:
                ok = (R != 0) and 2 * vp(R, 5) == 40
            if not ok:
                fail_census_ok = False
                chk('AS3', False, 'sweep %s label census s=%d' % (t, s))
    chk('AS3', fail_census_ok, 'failure-mode census over the sweep')

    # ---------- A3 equal characteristic F_3[[t]] ----------------------
    F3 = GF(3, [0, 1])   # F_3 itself (k = 1, mod = y)
    E = EqChar(F3)
    one = {0: (1,)}
    tt = {1: (1,)}
    PHIe = [E.cneg(tt), {}, one]                      # x^2 - t
    P2e = E.xmul(PHIe, PHIe)
    g1e = E.xadd(P2e, E.xneg([{}, {2: (1,)}]))        # PHI'^2 - t^2 x
    g2e = E.xadd(P2e, E.xneg([{}, {2: (2,)}]))        # PHI'^2 - 2 t^2 x
    fA3a = E.xmul(g1e, g2e)
    fA3b = E.xadd(E.xpow(PHIe, 4),
                  E.xneg([{}, {}, {4: (2,)}]))        # PHI'^4 - 2 t^4 x^2
    # construction certificates: the exact relations hold by construction;
    # verify the stage development and the value-group forcing arithmetic.
    Ae = E.xdev(fA3a, PHIe, 5)
    chk('A3', Ae[4] == [one], 'A3a top slot')
    # dv heights (dv(x) = 1, dv(t) = 2):
    def dv_e(g):
        vals = []
        for i, c in enumerate(g):
            cv = E.cval(c)
            if cv is not None:
                vals.append(2 * cv + i)
        return min(vals) if vals else None
    dvs = [dv_e(a) for a in Ae[:4]]
    # A FRAME PROPERTY found at run 1 (disclosed, mathematically real):
    # the label SUM 1 + 2 = 0 in F_3, so the middle lattice slot A2 =
    # -3t^2x VANISHES identically in equal characteristic — the side
    # (0,10)-(4,0) survives with residual Z^2 + 2 = (Z-1)(Z-2) over F_3
    # (separable, two labels), but the ledger sees NO middle pin. This
    # makes A3a a sharper row: the labels are visible only through the
    # residual roots, never through a slot digit.
    chk('A3', dvs[0] == 10, 'A3a dv(A0) = 10: %s' % dvs)
    for j in (1, 2, 3):
        chk('A3', dvs[j] is None or 2 * dvs[j] > 5 * (4 - j),
            'A3a slot j=%d strictly above the side: %s' % (j, dvs[j]))
    # the exact relations (the construction certificates): per factor,
    # PHI'(rho)^2 = c t^2 rho with c = 1, 2 — verified as polynomial
    # identities g_i == PHI'^2 - c t^2 x:
    chk('A3', E.xadd(g1e, E.xneg(E.xadd(P2e, E.xneg([{}, {2: (1,)}]))))
        == [], 'A3a factor-1 exact relation')
    chk('A3', E.xadd(g2e, E.xneg(E.xadd(P2e, E.xneg([{}, {2: (2,)}]))))
        == [], 'A3a factor-2 exact relation')
    Be = E.xdev(fA3b, PHIe, 5)
    dvsB = [dv_e(b) for b in Be[:4]]
    chk('A3', dvsB[0] == 10, 'A3b dv(A0) = 10: %s' % dvsB)
    for j in (1, 2, 3):
        chk('A3', dvsB[j] is None or 2 * dvsB[j] > 5 * (4 - j),
            'A3b slot j=%d strictly above the side: %s' % (j, dvsB[j]))
    # F_3: 2 = -1 non-square
    chk('A3', all(pow(z, 2, 3) != 2 for z in range(3)),
        '2 non-square mod 3')
    # forcing census (same arithmetic as A1a/A1b):
    cand = [(e, f) for e in range(1, 9) for f in range(1, 9)
            if e * f <= 4 and e % 4 == 0]
    chk('A3', cand == [(4, 1)], 'A3a component census')
    cand = [(e, f) for e in range(1, 9) for f in range(1, 9)
            if e * f <= 8 and e % 4 == 0 and f % 2 == 0]
    chk('A3', cand == [(4, 2)], 'A3b component census')

    # ---------- A-S4: the anchor property of the test polynomials ----
    # Psi_s's own x-Newton polygon must be a SINGLE side of slope 1/2
    # (all D'*ell roots at the key valuation h/e1 = 1/2), so LEMMA
    # HE3-0's (T1)/(T2) read applies at Psi's roots — the entry
    # condition of "the slot lemma at Psi's roots" (the box's named
    # further step). Measured at all four labels + both anchors.
    def x_polygon_single_side(g, p, slope_num, slope_den):
        pts = [(i, vp(c, p)) for i, c in enumerate(g) if c]
        d = len(g) - 1
        v0 = pts[0][1] if pts[0][0] == 0 else None
        if v0 is None:
            return False
        # single side from (0, v0) to (d, 0) of slope v0/d == num/den:
        if v0 * slope_den != slope_num * d:
            return False
        return all(v * d >= v0 * (d - i) for i, v in pts)
    for s in (1, 2, 3, 4):
        Psi = padd(P2, pneg([0, s * 25]))
        chk('AS4', x_polygon_single_side(Psi, 5, 1, 2),
            'Psi_%d x-polygon single side of slope 1/2' % s)
        Psi7 = padd(P2, pneg([0, s * 25 + 5 ** 3]))
        chk('AS4', x_polygon_single_side(Psi7, 5, 1, 2),
            'Psi_{%d,kappa=7} x-polygon single side of slope 1/2' % s)

    # ---------- teeth -------------------------------------------------
    # T-A-DPRIME: the mutant law |S_r| = D'*d (rescale forgotten):
    # predicts degree-2 factors on A1a (D'*d = 2) and a degree-4 factor
    # on A1b — killed by the measured sigmas.
    tooth('T-A-DPRIME',
          sigs['A1a'] != ((2, 1), (2, 1), (2, 1), (2, 1))
          and sigs['A1b'] != ((2, 2), (2, 2))
          and sigs['A1a'] == ((4, 1), (4, 1)),
          'mutant D-prime*d law not refuted by measured sigma')
    # T-A-EMPTY: the census must be able to SEE an empty label (else its
    # 4/4 verdicts are uninformative). Probe: fEmpty = (PHI'^2-25x)^2 +
    # 2*5^6 — an UNDECIDED-leaf member (residual (Z-1)^2, m_r = 2): label
    # 1 carries all 8 roots, label 2 is EMPTY. The unanchored reads must
    # separate: T_1 > 40+ (deep at 8 roots), T_2 = 40 exactly (dv = 5 at
    # every root: 8 * 5 = 40).
    fEmpty = padd(pmul(g1, g1), [2 * 5 ** 6])
    R1 = resultant_int(fEmpty, padd(P2, pneg([0, 25])))
    R2 = resultant_int(fEmpty, padd(P2, pneg([0, 50])))
    T1 = None if R1 == 0 else 2 * vp(R1, 5)
    T2 = None if R2 == 0 else 2 * vp(R2, 5)
    tooth('T-A-EMPTY',
          (T1 is None or T1 > 40) and T2 == 40,
          'empty-label detector: T_1 = %s, T_2 = %s' % (T1, T2))
    # T-A-SIG: flipped-label mutant on A1a: predict label of g1 = 2 —
    # killed by the exact relation PHI'(rho)^2 = 1*25*rho on g1's roots:
    # Res(g1, Psi_{2,r}) must be flat (2*v = 4*5 = 20), not jumping.
    Psi2 = padd(P2, pneg([0, 2 * 25 + 5 ** 3]))
    flat = 2 * vp(resultant_int(g1, Psi2), 5)
    tooth('T-A-SIG', flat == 20,
          'flipped label mutant: Res(g1, Psi_2) read %d != 20' % flat)
    print('  LEG A done.')

# ======================================================================
# Shared shadow instrument (GENTOW6 ledger mechanics, fresh-typed; the
# dual routes R/E of the box1 leg are both implemented and bit-compared)
# ======================================================================

class Frame:
    def __init__(self, name, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        self.name, self.p, self.PHI1, self.h = name, p, PHI1, h
        self.e1, self.e2, self.f2, self.mu2, self.u2 = e1, e2, f2, mu2, u2
        self.PHI2 = PHI2
        self.Dp, self.D2 = len(PHI1) - 1, len(PHI2) - 1
        self.m = e2 * f2
        self.mu1 = self.m * mu2
        self.E2 = self.m * u2
        self.delta = u2 - e2 * self.Dp * h
        self.ee = e1 * e2
        self.K2 = dev(PHI2, PHI1, self.m + 1)
        assert self.K2[self.m] == [1], (name, 'K2 top')
        assert self.D2 == self.m * self.Dp, (name, 'degree tie')
        assert self.delta >= 1, (name, 'delta >= 1')

    def theta(self, j):
        return (self.mu2 - j) * self.E2 + self.delta

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def red(self, c):
        return pdivmod(c, self.PHI1)[1]

    def honest(self, f):
        out, r = [], list(f)
        for _ in range(self.mu2):
            r, rem = pdivmod(r, self.PHI2)
            out.append(rem)
        assert r == [1], 'member not monic of the right degree'
        return out

    def level1(self, f):
        A = dev(f, self.PHI1, self.mu1 + 1)
        assert A[self.mu1] == [1]
        return A

    def _divide(self, A, reduce_each):
        out = []
        for _ in range(self.mu2):
            q = [[] for _ in range(max(1, len(A) - self.m))]
            for i in range(len(A) - 1, self.m - 1, -1):
                c = A[i]
                if pstrip(list(c)):
                    q[i - self.m] = padd(q[i - self.m], c)
                    A[i] = []
                    for k in range(self.m):
                        t = padd(A[i - self.m + k],
                                 pneg(pmul(c, self.K2[k])))
                        A[i - self.m + k] = self.red(t) if reduce_each \
                            else t
            out.append([list(A[b]) for b in range(self.m)])
            A = q
        assert A and pstrip(list(A[0])) == [1] and \
            all(not pstrip(list(x)) for x in A[1:]), 'top quotient != 1'
        return out

    def shadow_R(self, f):
        A = [self.red(a) for a in self.level1(f)]
        return self._divide(A, True)

    def shadow_E(self, f):
        A = [list(a) for a in self.level1(f)]
        out = self._divide(A, False)
        return [[self.red(list(c)) for c in coord] for coord in out]

    def slotdict(self, coord):
        d = {}
        for b, g in enumerate(coord):
            for a, c in enumerate(g):
                if c:
                    d[(a, b)] = c
        return d

    def pin(self, coord):
        best = None
        for (a, b), c in self.slotdict(coord).items():
            ht = self.ee * vp(c, self.p) + self.w(a, b)
            best = ht if best is None else min(best, ht)
        return best

    def mindiff(self, cH, cS):
        dif = [padd(list(sb), pneg(hb)) for sb, hb in
               zip(cS, dev(cH, self.PHI1, self.m))]
        return self.pin(dif)

    def graded_nonzero(self, coord, a, b, H):
        c = self.slotdict(coord).get((a, b), 0)
        if c == 0:
            return False
        n = H - self.w(a, b)
        return n >= 0 and n % self.ee == 0 and vp(c, self.p) == n // self.ee

    def dual_shadow(self, f, tag):
        sR = self.shadow_R(f)
        sE = self.shadow_E(f)
        chk('DUAL', all(self.slotdict(a) == self.slotdict(b)
                        for a, b in zip(sR, sE)),
            '%s dual-route mismatch' % tag)
        return sE


# frames — geographies (see the note S2 for the derivations of the
# constants; theta lists asserted below against the closed form):
PX = [-2, 0, 1]                    # x^2 - 2 over Q2  (e1=2, f1=1)
PP = [-3, 0, 1]                    # x^2 - 3 over Q3  (e1=2, f1=1)

def mkframe(*args):
    return Frame(*args)

# ======================================================================
# LEG B — HYP.79 (P-BINOM) + HYP.67's lower-coordinate slice, f1 = 1
# ======================================================================
#
# Geographies: X (Q2, PHI2 = PHI'^2 - 64x, single-slot top coordinate),
# P3 (Q3, PHI2 = PHI'^2 - 18x, single-slot), B (Q2, PHI2 =
# PHI'^2 - 2x PHI' - 8, the e2(f2 - t*) = 1 cascade), BP (Q3, PHI2 =
# PHI'^2 - 3x PHI' - 27, same cascade shape, the BP3 genre of the
# GENTOW6_PROOF r1 bracket).
#
# PREREGISTERED (hard checks):
#  P-ANCHOR  the five already-recorded frames (X3, X4, A53, B3, P33,
#     P34, P35) reproduce the sealed instrument's committed top-slot
#     values bit-exactly (fresh implementation tie).
#  P-FLOOR   pin(ShC_j) >= theta(j) at every frame, every coordinate
#     (GENTOW-3(i) instances).
#  P-TOP     ShC_j == {} for every j > j* (6.5(a) ceiling), j* =
#     (mu2-2) + floor((2 e2 t* + 1)/(e2 f2)).
#  P-SINGLE  single-slot geographies (X/P3): floor attainment at j*
#     iff p does not divide binom(mu2,2): X3 att / X4 no / X5 no /
#     P33 no / P34 no / P35 att / P36 no / P38 att.
#  P-CERT    certificate slot (a*,b*) = (2 i_t* - D', (2 e2 t* + 1)
#     mod e2 f2) carries v_p = v_p(binom(mu2,2)) + mu2-independent
#     base (measured at the anchors, asserted at the fresh frames).
# MEASURED (the examples-first table, read off post hoc — B-S2):
#  the cascade frames B4, B5, BP4, BP5, BP6: full ShC_{j*} slot dicts,
#  graded floor digits, attainment verdicts vs the Kummer profile of
#  binom(mu2, k) mod p.

FR_X = lambda mu2: mkframe('X%d' % mu2, 2, PX, 1, 2, 2, 1, mu2, 13,
                           [4, -64, -4, 0, 1])
FR_P3 = lambda mu2: mkframe('P3%d' % mu2, 3, PP, 1, 2, 2, 1, mu2, 5,
                            [9, -18, -6, 0, 1])
FR_A5 = lambda mu2: mkframe('A5%d' % mu2, 2, PX, 1, 2, 2, 1, mu2, 5,
                            [4, -4, -4, 0, 1])
FR_B = lambda mu2: mkframe('B%d' % mu2, 2, PX, 1, 2, 1, 2, mu2, 3,
                           [-4, 4, -4, -2, 1])
FR_BP = lambda mu2: mkframe('BP%d' % mu2, 3, PP, 1, 2, 1, 2, mu2, 3,
                            [-18, 9, -6, -3, 1])

def top_j(fr, tstar):
    return (fr.mu2 - 2) + (2 * fr.e2 * tstar + 1) // (fr.e2 * fr.f2)

def cert_slot(fr, tstar, i_tstar):
    return (2 * i_tstar - fr.Dp, (2 * fr.e2 * tstar + 1) % (fr.e2 * fr.f2))

def binom(n, k):
    from math import comb
    return comb(n, k)

def leg_B():
    print('== LEG B (HYP.79 P-BINOM + HYP.67 f1=1 slice) ==')
    # anchors with sealed wants (committed record of gentow6_box1_mu3):
    anchors = [
        (FR_X(3), 0, 1, 1, {(0, 1): 12288}, 12, True),
        (FR_X(4), 0, 1, 2, {(0, 1): 24576}, 13, False),
        (FR_A5(3), 0, 1, 1, {(0, 1): 48}, 4, True),
        (FR_P3(3), 0, 1, 1, {(0, 1): 972}, 5, False),
        (FR_P3(4), 0, 1, 2, {(0, 1): 1944}, 5, False),
        (FR_P3(5), 0, 1, 3, {(0, 1): 3240}, 4, True),
    ]
    for fr, tstar, i_t, jstar_want, slot_want, v_want, att_want in anchors:
        f = ppow(fr.PHI2, fr.mu2)
        sh = fr.dual_shadow(f, fr.name)
        js = top_j(fr, tstar)
        chk('B-ANCH', js == jstar_want,
            '%s j* = %d, want %d' % (fr.name, js, jstar_want))
        for j in range(fr.mu2):
            pn = fr.pin(sh[j])
            chk('B-FLOOR', pn is None or pn >= fr.theta(j),
                '%s floor at j=%d: pin %s < theta %d'
                % (fr.name, j, pn, fr.theta(j)))
            if j > js:
                chk('B-TOP', fr.slotdict(sh[j]) == {},
                    '%s ceiling: ShC_%d nonempty' % (fr.name, j))
        got = fr.slotdict(sh[js])
        chk('B-ANCH', got == slot_want,
            '%s top slots: got %s want %s' % (fr.name, got, slot_want))
        aslot, bslot = cert_slot(fr, tstar, i_t)
        cval = got.get((aslot, bslot))
        chk('B-ANCH', cval is not None and vp(cval, fr.p) == v_want,
            '%s cert v_p: got %s want %d'
            % (fr.name, None if cval is None else vp(cval, fr.p), v_want))
        att = fr.graded_nonzero(sh[js], aslot, bslot, fr.theta(js))
        chk('B-SINGLE', att == att_want,
            '%s attainment %s, want %s' % (fr.name, att, att_want))
        chk('B-SINGLE',
            att == (binom(fr.mu2, 2) % fr.p != 0),
            '%s P-BINOM law: att %s vs binom(%d,2) = %d mod %d'
            % (fr.name, att, fr.mu2, binom(fr.mu2, 2), fr.p))
    # fresh single-slot frames: X5, P36, P38 — the P-BINOM law
    # preregistered: attainment iff p does not divide binom(mu2,2).
    for fr, tstar, i_t in [(FR_X(5), 0, 1), (FR_P3(6), 0, 1),
                           (FR_P3(8), 0, 1)]:
        f = ppow(fr.PHI2, fr.mu2)
        sh = fr.dual_shadow(f, fr.name)
        js = top_j(fr, tstar)
        for j in range(fr.mu2):
            pn = fr.pin(sh[j])
            chk('B-FLOOR', pn is None or pn >= fr.theta(j),
                '%s floor at j=%d: pin %s < theta %d'
                % (fr.name, j, pn, fr.theta(j)))
            if j > js:
                chk('B-TOP', fr.slotdict(sh[j]) == {},
                    '%s ceiling: ShC_%d nonempty' % (fr.name, j))
        aslot, bslot = cert_slot(fr, tstar, i_t)
        got = fr.slotdict(sh[js])
        att = fr.graded_nonzero(sh[js], aslot, bslot, fr.theta(js))
        want = (binom(fr.mu2, 2) % fr.p != 0)
        chk('B-SINGLE', att == want,
            '%s P-BINOM law (fresh): att %s want %s' % (fr.name, att, want))
        chk('B-SINGLE', set(got) <= {(aslot, bslot)},
            '%s single-slot geography: slots %s' % (fr.name, sorted(got)))
        print('  %s: j*=%d slots=%s theta=%d att=%s binom(%d,2)=%d'
              % (fr.name, js, {k: (v, vp(v, fr.p)) for k, v in got.items()},
                 fr.theta(js), att, fr.mu2, binom(fr.mu2, 2)))
    # the cascade geographies (B/BP, t* = 1, i_t* = 1): MEASURE mode +
    # the floor/ceiling/dual hard checks; attainment verdict = ANY slot
    # of the top coordinate carrying a graded floor digit.
    print('  -- cascade geography (e2(f2 - t*) = 1): measured table --')
    for fr in [FR_B(3), FR_B(4), FR_B(5), FR_BP(3), FR_BP(4), FR_BP(5),
               FR_BP(6)]:
        f = ppow(fr.PHI2, fr.mu2)
        sh = fr.dual_shadow(f, fr.name)
        js = top_j(fr, 1)
        for j in range(fr.mu2):
            pn = fr.pin(sh[j])
            chk('B-FLOOR', pn is None or pn >= fr.theta(j),
                '%s floor at j=%d: pin %s < theta %d'
                % (fr.name, j, pn, fr.theta(j)))
            if j > js:
                chk('B-TOP', fr.slotdict(sh[j]) == {},
                    '%s ceiling: ShC_%d nonempty' % (fr.name, j))
        got = fr.slotdict(sh[js])
        pn = fr.pin(sh[js])
        att = (pn == fr.theta(js))
        kprof = [binom(fr.mu2, k) % fr.p for k in range(2, fr.mu2 + 1)]
        print('  %s: j*=%d pin=%s theta=%d att=%s slots=%s binomprof=%s'
              % (fr.name, js, pn, fr.theta(js), att,
                 {k: (v, vp(v, fr.p)) for k, v in sorted(got.items())},
                 kprof))
        # record for the law read (asserted post hoc in leg_B_law)
        CASCADE_ROWS.append((fr.name, fr.p, fr.mu2, js, pn, fr.theta(js),
                             att, kprof))
    # ---- the B-S2 law, read off the table and asserted over all rows:
    # LAW B-S2 (certified on 7 rows, two primes): at the e2(f2-t*) = 1
    # cascade geography, the height-THETA_{j*} graded layer at the top
    # coordinate is carried by the PAIR slot (digit ~ binom(mu2,2)) and
    # the TRIPLE slot (digit ~ binom(mu2,3)) ONLY — k >= 4 diagonal
    # branches land strictly above the floor (B4/B5: unit binom(mu2,4)
    # yet pin = THETA + 1, which REFUTES the naive "any in-band k"
    # candidate — refutation kept, law repaired to pair-or-triple):
    #   attainment at j*  <=>  p !| binom(mu2,2)  OR  p !| binom(mu2,3).
    for (nm, p, mu2, js, pn, th, att, kprof) in CASCADE_ROWS:
        want = (binom(mu2, 2) % p != 0) or (binom(mu2, 3) % p != 0)
        chk('B-LAW', att == want,
            'LAW B-S2 at %s: att %s want %s' % (nm, att, want))
    # teeth
    frX4 = FR_X(4)
    f = ppow(frX4.PHI2, 4)
    sh = frX4.dual_shadow(f, 'X4-tooth')
    js = top_j(frX4, 0)
    # T-B-COEF: mutant law "coefficient mu2 instead of binom(mu2,2)":
    # at X4, mu2 = 4 is even (v2 = 2) while binom(4,2) = 6 has v2 = 1 —
    # the measured cert v_p must equal v0 + v_p(binom), not v0 + v_p(mu2).
    got = frX4.slotdict(sh[js])
    v_meas = vp(got[(0, 1)], 2)
    tooth('T-B-COEF', v_meas == 13 and v_meas != 12 + 2,
          'X4 cert slot v2 = %d (binom law: 12+1; mu2 mutant: 12+2)'
          % v_meas)
    # T-B-ALLM: mutant "the certificate digit always attains" dies at
    # every p | binom(mu2,2) single-slot frame (X4, X5, P33, P34, P36).
    dead = 0
    for fr, tstar, i_t in [(FR_X(4), 0, 1), (FR_X(5), 0, 1),
                           (FR_P3(3), 0, 1), (FR_P3(4), 0, 1),
                           (FR_P3(6), 0, 1)]:
        sh = fr.shadow_E(ppow(fr.PHI2, fr.mu2))
        js = top_j(fr, tstar)
        aslot, bslot = cert_slot(fr, tstar, i_t)
        if not fr.graded_nonzero(sh[js], aslot, bslot, fr.theta(js)):
            dead += 1
    tooth('T-B-ALLM', dead == 5,
          'always-attains mutant: %d/5 kills' % dead)
    print('  LEG B done.')

CASCADE_ROWS = []

# ======================================================================
# LEG C — HYP.67 f1 >= 2 face / HYP.80 COMPOUND-6.5' / HYP.70 widening
# ======================================================================
#
# FIRST machine contact of the f1 >= 2 x mu2 >= 3 compound (6.5' is
# prose-only at HEAD). Three fresh f1 = 2 geographies:
#   F23  (Q3, PHI' = x^2 - 18: e1 = 1, f1 = 2, K = F_9, eta = sqrt2 != 1
#         — the eta-gauge axis GENTOW4-r1 flagged as machine-blind),
#         PHI2 = PHI'^2 - 81x, e2 = 2, f2 = 1, u2 = 5.
#   F22  (Q2, PHI' = x^2 + 2x + 4: e1 = 1, f1 = 2, K = F_4),
#         PHI2 = PHI'^2 - 16x, e2 = 2, f2 = 1, u2 = 5.
#   F423 (Q2, PHI' = x^4 + 2x^2 + 4: e1 = 2, f1 = 2, D' = 4 — BOX-4's
#         sealed key, one mu2 up = HYP.80's direct object),
#         PHI2 = PHI'^2 - 16x^3, e2 = 2, f2 = 1, u2 = 11.
# Heights are exact at these frames (no cross-monomial cancellation:
# the f1 = 2 residue directions 1, omega are F_p-independent).
#
# HARD checks: dual-route equality; floors pin(ShC_j) >= theta(j)
# (GENTOW-3(i), whose criterion clauses are general per GENTOW3 S6).
# PREREGISTERED naive-transport QUESTIONS (the f1 = 1 formulas of 6.5
# moved verbatim; T4 warns the displays "are NOT proved as written" at
# f1 >= 2 — a failure here is a FINDING, not a violation):
#   Q-CEIL  ShC_j == {} for j > j* = (mu2-2) + floor((2 e2 t* + 1)/m);
#   Q-CERT  cert slot (2 i_t* - D', (2 e2 t* + 1) mod m) carries
#           v_p = 2 a_t* + v_p(binom(mu2,2)), i.e. floor attainment iff
#           p !| binom(mu2,2): F23 (p = 3 | 3): NO att, ht Theta + 2;
#           F22/F423 (p = 2, binom = 3 unit): att at Theta.
# HYP.70 rows: the same three keys at mu2 = 2 (x-ful tails), same checks.

FR_F23 = lambda mu2: mkframe('F23m%d' % mu2, 3, [-18, 0, 1], 1, 1, 2, 1,
                             mu2, 5, [324, -81, -36, 0, 1])
FR_F22 = lambda mu2: mkframe('F22m%d' % mu2, 2, [4, 2, 1], 1, 1, 2, 1,
                             mu2, 5, [16, 0, 12, 4, 1])
FR_F423 = lambda mu2: mkframe('F423m%d' % mu2, 2, [4, 0, 2, 0, 1], 1, 2,
                              2, 1, mu2, 11,
                              [16, 0, 16, -16, 12, 0, 4, 0, 1])

def leg_C():
    print('== LEG C (f1 >= 2 compound: HYP.67 face / HYP.80 / HYP.70) ==')
    # (frame ctor, t*, i_t*, a_t*)
    geos = [(FR_F23, 0, 1, 4), (FR_F22, 0, 1, 4), (FR_F423, 0, 3, 4)]
    for mk, tstar, i_t, a_t in geos:
        for mu2 in (3, 2):
            fr = mk(mu2)
            f = ppow(fr.PHI2, mu2)
            sh = fr.dual_shadow(f, fr.name)
            js = top_j(fr, tstar)
            for j in range(mu2):
                pn = fr.pin(sh[j])
                chk('C-FLOOR', pn is None or pn >= fr.theta(j),
                    '%s floor at j=%d: pin %s < theta %d'
                    % (fr.name, j, pn, fr.theta(j)))
            ceil_ok = all(fr.slotdict(sh[j]) == {}
                          for j in range(js + 1, mu2))
            aslot, bslot = cert_slot(fr, tstar, i_t)
            got = fr.slotdict(sh[js]) if js < mu2 else {}
            cval = got.get((aslot, bslot))
            vwant = 2 * a_t + vp(binom(mu2, 2), fr.p)
            att = fr.graded_nonzero(sh[js], aslot, bslot, fr.theta(js)) \
                if js < mu2 else False
            attwant = (binom(mu2, 2) % fr.p != 0)
            print('  %s: j*=%d ceil=%s cert@(%d,%d)=%s v=%s (want %d) '
                  'att=%s (want %s) slots=%s'
                  % (fr.name, js, ceil_ok, aslot, bslot, cval,
                     None if cval is None else vp(cval, fr.p), vwant,
                     att, attwant,
                     {k: (v, vp(v, fr.p)) for k, v in sorted(got.items())}))
                # the naive-transport questions, asserted as the
                # first-contact record (failures are findings — if one
                # fires, it is kept, disclosed, and read as the corrected
                # law's data):
            chk('C-QCEIL', ceil_ok,
                '%s naive ceiling survives' % fr.name)
            chk('C-QCERT', cval is not None and vp(cval, fr.p) == vwant,
                '%s naive cert v_p survives: got %s want %d'
                % (fr.name, None if cval is None else vp(cval, fr.p),
                   vwant))
            chk('C-QATT', att == attwant,
                '%s naive attainment law survives: %s want %s'
                % (fr.name, att, attwant))
            # perturbation rows (in-budget deep members): honest read,
            # mindiff floors
            for k, (aa, bb) in enumerate([(0, 0), (1, 1)]):
                pert = padd(f, pmul(pmul([fr.p ** 40],
                                         pmul(ppow([0, 1], aa),
                                              ppow(fr.PHI1, bb))),
                                    ppow(fr.PHI2, mu2 - 2)))
                shp = fr.dual_shadow(pert, '%s-pert%d' % (fr.name, k))
                hon = fr.honest(pert)
                for j in range(mu2):
                    md = fr.mindiff(hon[j], shp[j])
                    chk('C-PERT', md is None or md >= fr.theta(j),
                        '%s pert%d mindiff_%d %s >= theta %d'
                        % (fr.name, k, j, md, fr.theta(j)))
    # tooth T-C-VAL: v* - 1 mutant at the F423m3 cert slot must differ
    # from the measured digit's valuation.
    fr = FR_F423(3)
    sh = fr.shadow_E(ppow(fr.PHI2, 3))
    got = fr.slotdict(sh[top_j(fr, 0)])
    cv = got.get((2, 1))
    tooth('T-C-VAL', cv is not None and vp(cv, 2) != 8 - 1,
          'F423m3 cert v2 = %s vs mutant 7'
          % (None if cv is None else vp(cv, 2)))
    print('  LEG C done.')

# ======================================================================
# LEG E — HYP.71 witnesses / HYP.69 residue / HYP.78 obstruction
# ======================================================================
#
# W-geography (the HYP.71(b) ask): genres where the KEY power has NO
# x-overflow at all (all key pairs in-grid: 2 i_t* < D' and every
# i_t + i_t' < D'), so any Theta-attainment must be ENTRY-driven.
#   W1 (Q2): PHI' = x^3 - 2 (D' = 3), PHI2 = PHI'^3 + 8x PHI'^2 + 1024
#      (e2 = 1, f2 = 3, u2 = 10, T = {0, 2}, i_2 = 1, i_0 = 0;
#      residual Z^3 + Z^2 + 1 irreducible over F_2), mu2 = 2.
#   W2 (Q3): PHI' = x^3 - 3, PHI2 = PHI'^3 + 27x PHI'^2 + 2*3^10
#      (residual Z^3 + Z^2 + 2 irreducible over F_3), mu2 = 2.
# PREREGISTERED: the pure power Phi2^2 has EMPTY shadow (the clean
# geography); every single-entry in-budget member with a + i_t < D'
# has EMPTY discrepancy; members with a = 2 (crossing t = 2,
# a + i_2 = 3 = D') have nonzero discrepancy (the diverge-vs-not pair
# inside one genre — HYP.78's obstruction shape, reproduced fresh).
# MEASURED (the witness search): min over the in-budget sweep of
# (mindiff_j - theta_j); a row at 0 is a HYP.71(b) witness; if the
# sweep minimum is strictly positive at every in-budget member, that is
# the INFEASIBILITY record (the boundary identity — see the note S2/S3).
#
# R-geography (HYP.69 / E-S3): fresh regime-3 genres (a mixed pair
# overflows, 2 i_t* < D'), 6.7's chi-criterion re-verified:
#   R5 (Q5): PHI' = x^3 - 5, PHI2 = PHI'^2 + 25x PHI' + 625x^2
#      (e2 = 1, f2 = 2, u2 = 7; residual Z^2 + Z + 1 irreducible over
#      F_5; s* = 1, I = {3}, chi = 2 c0 c1 = 2 != 0): predict (b1)
#      attainment: pin(ShC_1) == theta(1) = 18.
#   R2 (Q2): same shape at Q2 (chi = 2 c0 c1 = 0 in F_2): predict (b2)
#      NO graded floor digit at the s*-slots of ShC_1.

def leg_E():
    print('== LEG E (HYP.71 witnesses / HYP.69 / HYP.78) ==')
    W1 = mkframe('W1', 2, [-2, 0, 0, 1], 1, 3, 1, 3, 2, 10,
                 padd(padd(ppow([-2, 0, 0, 1], 3),
                           pmul([0, 8], ppow([-2, 0, 0, 1], 2))),
                      [1024]))
    W2 = mkframe('W2', 3, [-3, 0, 0, 1], 1, 3, 1, 3, 2, 10,
                 padd(padd(ppow([-3, 0, 0, 1], 3),
                           pmul([0, 27], ppow([-3, 0, 0, 1], 2))),
                      [2 * 3 ** 10]))
    for fr in (W1, W2):
        chk('E-W', (fr.E2, fr.delta) == (30, 7),
            '%s constants' % fr.name)
        f2pow = ppow(fr.PHI2, 2)
        sh = fr.dual_shadow(f2pow, fr.name)
        chk('E-W', all(fr.slotdict(c) == {} for c in sh),
            '%s pure power: shadow EMPTY (all key pairs in-grid)'
            % fr.name)
        # the in-budget single-entry sweep
        gaps = []
        divpair = {'div': None, 'nodiv': None}
        for jp in (0, 1):
            for a in (0, 1, 2):
                for b in (0, 1, 2):
                    base = a + fr.u2 * b
                    amin = ((2 - jp) * fr.E2 - base) // fr.ee + 1
                    for da in range(3):
                        al = amin + da
                        for c in range(1, fr.p):
                            C = pmul([c * fr.p ** al],
                                     pmul(ppow([0, 1], a),
                                          ppow(fr.PHI1, b)))
                            memb = padd(f2pow,
                                        pmul(C, ppow(fr.PHI2, jp)))
                            shm = fr.shadow_E(memb)
                            hon = fr.honest(memb)
                            mds = [fr.mindiff(hon[j], shm[j])
                                   for j in range(2)]
                            # a coordinate-0 entry never enters the
                            # division's quotient, so it cannot cross a
                            # lift (run-1 finding, disclosed: the naive
                            # "a + i_t >= D'" predicate is necessary
                            # but only sufficient at jp >= 1):
                            crosses = (a + 1 >= fr.Dp) and jp >= 1
                            entry_ht = fr.ee * al + a + fr.u2 * b
                            excess = entry_ht - (2 - jp) * fr.E2
                            if not crosses:
                                chk('E-NOX',
                                    all(m is None for m in mds),
                                    '%s entry (j%d,a%d,b%d,al%d,c%d) '
                                    'no crossing => empty diff, got %s'
                                    % (fr.name, jp, a, b, al, c, mds))
                                divpair['nodiv'] = (jp, a, b, al, c)
                            else:
                                chk('E-X',
                                    all(m is not None for m in mds),
                                    '%s crossing entry => nonzero diff'
                                    % fr.name)
                                divpair['div'] = (jp, a, b, al, c)
                                for j in range(2):
                                    if mds[j] is not None:
                                        # LAW E-W (the boundary
                                        # identity, hard check): the
                                        # branch transports the entry's
                                        # excess over the side verbatim:
                                        chk('E-LAW',
                                            mds[j] == fr.theta(j)
                                            + excess,
                                            '%s LAW E-W at (j%d,a%d,b%d'
                                            ',al%d,c%d): mindiff_%d = '
                                            '%s != theta + excess = %d'
                                            % (fr.name, jp, a, b, al, c,
                                               j, mds[j],
                                               fr.theta(j) + excess))
                                        gaps.append(
                                            (mds[j] - fr.theta(j), jp,
                                             a, b, al, c, j))
        gaps.sort()
        chk('E-PAIR', divpair['div'] is not None
            and divpair['nodiv'] is not None,
            '%s diverge-vs-not pair inside one genre' % fr.name)
        # THE INFEASIBILITY RECORD (HYP.71(b) at this geography): the
        # in-budget sweep NEVER attains theta — min gap >= 1. By LAW
        # E-W the gap equals the entry's excess over the side, which is
        # >= 1 on the locus (strict floor): a theta-attaining entry
        # would have to sit ON the side, i.e. OFF the leaf locus.
        # Infeasibility is the lemma (constructed-counterexample rule).
        chk('E-INFEAS', gaps and gaps[0][0] >= 1,
            '%s witness infeasibility: min gap %s'
            % (fr.name, gaps[0] if gaps else None))
        print('  %s: sweep %d crossing rows; min gap (mindiff - theta)'
              ' = %s; INFEASIBLE (no in-locus theta-attainment)'
              % (fr.name, len(gaps), gaps[0][0] if gaps else None))
        WITNESS_GAPS[fr.name] = gaps
        # two-entry members: the ledger is linear in the TOTAL entry
        # digit — two crossing entries at the same slot sum their
        # digits (p = 3: 1 + 2 = 3 deepens the pin by ee exactly):
        if fr.p == 3:
            jp, a, b = 1, 2, 0
            amin = ((2 - jp) * fr.E2 - (a + fr.u2 * b)) // fr.ee + 1
            C1 = pmul([1 * fr.p ** amin],
                      pmul(ppow([0, 1], a), ppow(fr.PHI1, b)))
            C2 = pmul([2 * fr.p ** amin],
                      pmul(ppow([0, 1], a), ppow(fr.PHI1, b)))
            memb = padd(f2pow, pmul(padd(C1, C2), ppow(fr.PHI2, jp)))
            shm = fr.shadow_E(memb)
            hon = fr.honest(memb)
            md0 = fr.mindiff(hon[0], shm[0])
            excess2 = fr.ee * (amin + 1) + a - (2 - jp) * fr.E2
            chk('E-LIN', md0 == fr.theta(0) + excess2,
                '%s two-entry linearity: mindiff_0 = %s want %d'
                % (fr.name, md0, fr.theta(0) + excess2))
    # R-geography: 6.7 chi-criterion, fresh regime-3 genres
    R5 = mkframe('R5', 5, [-5, 0, 0, 1], 1, 3, 1, 2, 2, 7,
                 padd(padd(ppow([-5, 0, 0, 1], 2),
                           pmul([0, 25], [-5, 0, 0, 1])),
                      [0, 0, 625]))
    R2 = mkframe('R2', 2, [-2, 0, 0, 1], 1, 3, 1, 2, 2, 7,
                 padd(padd(ppow([-2, 0, 0, 1], 2),
                           pmul([0, 4], [-2, 0, 0, 1])),
                      [0, 0, 16]))
    for fr, chi_nonzero in ((R5, True), (R2, False)):
        sh = fr.dual_shadow(ppow(fr.PHI2, 2), fr.name)
        th1 = fr.theta(1)
        pn = fr.pin(sh[1])
        for j in range(2):
            pnj = fr.pin(sh[j])
            chk('E-RFLOOR', pnj is None or pnj >= fr.theta(j),
                '%s floor j=%d: %s' % (fr.name, j, pnj))
        if chi_nonzero:
            chk('E-CHI', pn == th1,
                '%s 6.7(b1): chi != 0 => attainment at theta(1) = %d, '
                'pin %s' % (fr.name, th1, pn))
        else:
            chk('E-CHI', pn is None or pn > th1,
                '%s 6.7(b2): chi = 0 => no floor digit at ShC_1, pin %s'
                ' theta %d' % (fr.name, pn, th1))
        print('  %s: pin(ShC_1) = %s, theta(1) = %d, slots = %s'
              % (fr.name, pn, th1,
                 {k: (v, vp(v, fr.p)) for k, v in
                  sorted(fr.slotdict(sh[1]).items())}))
    # E-S4 attack (W2, p = 3): the leading-entry-data criterion — two
    # members with the same (j', a, b, alpha) and different unit c:
    # if their discrepancy PINS differ, any criterion reading only the
    # entry's position+valuation is refuted; if they agree on the whole
    # sweep, the linear-ledger criterion survives at this geography.
    same = True
    fr = W2
    f2pow = ppow(fr.PHI2, 2)
    for jp in (0, 1):
        for b in (0, 1, 2):
            base = 2 + fr.u2 * b
            amin = ((2 - jp) * fr.E2 - base) // fr.ee + 1
            pins = []
            for c in (1, 2):
                C = pmul([c * fr.p ** amin],
                         pmul(ppow([0, 1], 2), ppow(fr.PHI1, b)))
                memb = padd(f2pow, pmul(C, ppow(fr.PHI2, jp)))
                shm = fr.shadow_E(memb)
                hon = fr.honest(memb)
                pins.append(tuple(fr.mindiff(hon[j], shm[j])
                                  for j in range(2)))
            if pins[0] != pins[1]:
                same = False
    chk('E-S4', same,
        'W2 unit-c independence of the discrepancy pin (linear-ledger '
        'criterion survives at the single-crossing geography)')
    # T-E-CHI: mutant chi without the (2 - delta_tt') factor predicts
    # attainment at R2 (c0*c1 = 1 != 0 in F_2); the measured pin 21 > 18
    # kills it — the multiplicity factor 2 in chi is load-bearing.
    shR2 = R2.shadow_E(ppow(R2.PHI2, 2))
    pnR2 = R2.pin(shR2[1])
    tooth('T-E-CHI', pnR2 is not None and pnR2 > R2.theta(1),
          'chi-without-2 mutant: R2 pin %s vs theta 18' % pnR2)
    # T-E-BOUND: an ON-side entry (entry_ht == side height, hence OFF
    # the leaf locus) must attain theta EXACTLY — LAW E-W is tight; the
    # infeasibility is the locus fence, not slack in the bound.
    frW1 = W1
    C = pmul([2 ** 6], pmul(ppow([0, 1], 2), ppow(frW1.PHI1, 1)))
    memb = padd(ppow(frW1.PHI2, 2), pmul(C, frW1.PHI2))
    shm = frW1.shadow_E(memb)
    hon = frW1.honest(memb)
    mds = [frW1.mindiff(hon[j], shm[j]) for j in range(2)]
    tooth('T-E-BOUND',
          mds == [frW1.theta(0), frW1.theta(1)],
          'on-side entry attains theta exactly: %s vs %s'
          % (mds, [frW1.theta(0), frW1.theta(1)]))
    print('  LEG E done.')

WITNESS_GAPS = {}

# ======================================================================
# LEG D — HYP.68 / HYP.144-BOX-2: THEOREM GENTOW-6.6's ledger identity
# ======================================================================
#
# First DIRECT window-enumeration checks of 6.6(c):
#   #(m(B_S x B_g) mod pi^N) = q^-c #(B_S mod pi^N) #(B_g mod pi^N),
# and the q^c fiber clause, at three instantiations over Z_3:
#   D2a  deg 1 x deg 1, c = 1 (H2 by explicit valuation);
#   D2b  deg 2 x deg 1, c = 1 (H2 by the evaluation constant);
#   D2d  the two-class residual-separation shape (the 6.6(d)/GENTOW4
#        partial-side mechanism: distinct residue classes force the
#        constant) — c = 1.
# Teeth: T-D-CJ (c -> c+1 and c -> c-1 must both fail the identity).
# Plus D2c: the c_J closed-form integer identity on a 600-tuple grid.

def leg_D():
    print('== LEG D (GENTOW-6.6 ledger: HYP.68 / HYP.144-BOX-2) ==')
    q = 3

    def count_classes(vecs, N):
        return len({tuple(x % q ** N for x in v) for v in vecs})

    # ---- D2a: deg1 x deg1, c = 1, H = 2, N0 = 2c + 2 = 4 ------------
    c, H, N = 1, 2, 4
    BS = [a * q ** H for a in range(q ** (N - H))]           # a == 0 (9)
    BG = [q ** c * (1 + q * t) + a * q ** H
          for a in range(q ** (N - H)) for t in range(1)]
    BG = [q ** c + a * q ** H for a in range(q ** (N - H))]  # b == 3 (81)
    # (H2): v(b - a) = c for all pairs:
    chk('D2a', all(vp(b - a, q) == c for a in BS for b in BG),
        'D2a separation constant')
    prods = [((a + b) % q ** N, (a * b) % q ** N) for a in BS for b in BG]
    img = len(set(prods))
    want = len(BS) * len(BG) // q ** c
    chk('D2a', img == want,
        'D2a ledger identity: %d image classes, want %d' % (img, want))
    from collections import Counter as _C
    fib = _C(prods)
    chk('D2a', set(fib.values()) == {q ** c},
        'D2a fiber clause: %s' % set(fib.values()))
    # teeth: c +- 1
    tooth('T-D-CJ', img != len(BS) * len(BG) // q ** (c + 1)
          and img != len(BS) * len(BG) // q ** (c - 1),
          'D2a c-mutants both fail: img %d' % img)

    # ---- D2b: deg2 x deg1, c = 1, H = 2, N0 = 4 ---------------------
    N = 4
    BS2 = [(a1 * q ** H % q ** N, (q + a0 * q ** H) % q ** N)
           for a1 in range(q ** (N - H)) for a0 in range(q ** (N - H))]
    BG2 = [(b * q) % q ** N for b in range(q ** (N - 1))]
    # (H2): v(Res(x^2 + a1 x + a0, x + b)) = v(b^2 - a1 b + a0) = 1:
    chk('D2b', all(vp((b * b - a1 * b + a0) % q ** (N + 2) or q ** 9, q)
                   == 1 or vp(b * b - a1 * b + a0, q) == 1
                   for (a1, a0) in BS2 for b in BG2),
        'D2b separation constant')
    prods = [((a1 + b) % q ** N, (a0 + a1 * b) % q ** N,
              (a0 * b) % q ** N) for (a1, a0) in BS2 for b in BG2]
    img = len(set(prods))
    want = len(BS2) * len(BG2) // q
    chk('D2b', img == want,
        'D2b ledger identity: %d image classes, want %d' % (img, want))
    fib = _C(prods)
    chk('D2b', set(fib.values()) == {q},
        'D2b fiber clause: %s' % set(fib.values()))

    # ---- D2d: the two-class residual-separation shape ---------------
    # B_S = {x - 3u : u = 1 mod 3}, B_g = {x - 3w : w = 2 mod 3}:
    # c = v(3u - 3w) = 1 constant BY residual separation (u - w != 0
    # mod 3) — the 6.6(d)/GENTOW-6.6a mechanism in miniature.
    N = 4
    BSu = [(-3 * u) % q ** N
           for u in range(1, q ** (N - 1), 1) if u % 3 == 1]
    BGw = [(-3 * w) % q ** N
           for w in range(1, q ** (N - 1), 1) if w % 3 == 2]
    chk('D2d', all(vp((su - sw) % q ** (N + 2) or 3, q) == 1
                   for su in BSu for sw in BGw),
        'D2d residual separation constant')
    prods = [((su + sw) % q ** N, (su * sw) % q ** N)
             for su in BSu for sw in BGw]
    img = len(set(prods))
    want = len(BSu) * len(BGw) // q
    chk('D2d', img == want,
        'D2d two-class ledger identity: %d want %d' % (img, want))
    fib = _C(prods)
    chk('D2d', set(fib.values()) == {q},
        'D2d fiber clause: %s' % set(fib.values()))

    # ---- D2c: the c_J closed form on a grid --------------------------
    bad = 0
    for mu2s in range(1, 4):
        for mp in range(1, 4):
            for e1 in range(1, 4):
                for f1 in range(1, 3):
                    for e2 in range(1, 4):
                        for f2 in range(1, 3):
                            for u2 in range(1, 4):
                                D2 = e2 * f2 * e1 * f1
                                E2 = e2 * f2 * u2
                                lhs = mu2s * mp * D2 * E2
                                if lhs % (e1 * e2):
                                    bad += 1
                                    continue
                                if lhs // (e1 * e2) != \
                                        mu2s * mp * f1 * f2 * f2 * e2 * u2:
                                    bad += 1
    chk('D2c', bad == 0, 'c_J closed-form grid: %d bad' % bad)
    print('  LEG D done.')

# ======================================================================
# main
# ======================================================================

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('A', 'all'):
        leg_A()
    if which in ('B', 'all'):
        leg_B()
    if which in ('C', 'all'):
        leg_C()
    if which in ('E', 'all'):
        leg_E()
    if which in ('D', 'all'):
        leg_D()
    print()
    print('CHECKS: %d, VIOLATIONS: %d' % (NCHK, NVIO))
    print('TALLY: %s' % TALLY)
    print('KILLS: %s' % KILLS)
    print('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))

if __name__ == '__main__':
    main()
