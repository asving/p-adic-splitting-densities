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
# main
# ======================================================================

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('A', 'all'):
        leg_A()
    print()
    print('CHECKS: %d, VIOLATIONS: %d' % (NCHK, NVIO))
    print('TALLY: %s' % TALLY)
    print('KILLS: %s' % KILLS)
    print('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))

if __name__ == '__main__':
    main()
