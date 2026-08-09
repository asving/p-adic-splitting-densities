"""HE7 passPE2 FRESH ROUTE — a CONSTRUCTED alpha-refine family at the
d_r = 2 frame (K2 = F_{p^2} a PROPER extension), the first machine exercise
of LEMMAS HE7-12/HE7-13 anywhere with d_r >= 2 — plus a symbolic (S5.8.1)
polytope leg at frames including d_r = 3 and f1 >= 2.

ROUTE DISCLOSURE (differs from all five prior routes): (a) sealed battery =
random members at (2,1,1), l=2, d_r=1, refine hit on 42 members by chance;
(b) HE6R1's l=1/d_r=2 battery = NO refine-path members; (c) r1 peel supp;
(d) PE1's n=12 mu2=3 peel family (l=2, d_r=1, refine SKIPPED); (e) r2's
42-member slot-geometry leg (d_r=1, K2 = F_p).  THIS route CONSTRUCTS the
refine configuration deliberately at l=1, d_r=2: refine residue s2 ranges
over ALL of F_{p^2}^x including s2 NOT IN F_p (impossible at every prior
leg, where K2 = F_p), within-class slot TIES occur (the d_r=2 (SLOT2)(b)
no-cancellation mechanism live on the refine path), and the (LIFT2) lift of
s2 genuinely uses the K-basis {1, beta}.  INSTRUMENT INDEPENDENCE: no import
from he6_checks/he7_checks; own exact integer polynomial arithmetic, own
Bareiss resultant, own reader written from the note's S1/(SLOT2)/S8;
sigma oracle = cypari2 (factor over Q + nfinit + idealprimedec), char 0
only (disclosed; the char-p refine members were covered by the sealed leg).

FRAME.  O = Z_p, (e1,f1,h) = (2,1,1), Phi' = x^2 - p, varpi = x, dv = 2*v_p;
level-2 datum (lam, r) with l = 1 (twist TRIVIAL: n2(k) = x^k, all s(.) = 0),
lam = u in {3,5} (> D'h = 2), r = Z^2 + b irreducible over F_p (b: p=3 -> 1,
p=5 -> 2), d_r = 2, K2 = F_p(beta), beta^2 = -b; D'' = 4, T2 = 2u, dv2 = dv.
Psi = Phi'^2 + a*nrm(u)*Phi' + b*nrm(2u) with a = 0 (occupied slots at T2
exactly: 2u + 0, u + u, 0 + 2u).  Members f = Psi^2 + A1*Psi + A0, deg 8,
mu2 = 2: A1 = lift2(lam2, -2*s2) + noise1, A0 = lift2(2*lam2, s2^2) + noise0
with lam2 in {2u+1, 2u+2} > T2, s2 in F_{p^2}^x (ALL values), noise strictly
above the side.  The read must CONFIRM (not assume) the single side lam2
with residual (Z - s2)^2, then refine by w = lift2(lam2, s2).

PREREGISTERED PREDICTIONS (falsifiers in brackets):
 P1 every member: read confirms single side lam2, residual (Z-s2)^2; Psi's
    occupied slots all exactly T2; dv2(w) = lam2 > T2, res2(w,lam2) = s2.
 P2 off-disk (S5.8.1) at FIVE strata per member (delta = infty; delta > lam;
    TWO middle-band strata delta = (2u-1)/2 [eps1=1/2] and (4u-3)/4
    [eps1=3/4, the PE1 F-2 seed 9/4 at u=3]; eps0 = 1): resultant-sum
    inequality with the note's bound AND the exact off-disk value formula
    sum dv2(Psi(xi)) = deg(g)*(T2 - 2*eps1) AND invariance
    dv2res(g,Psi1) == dv2res(g,Psi).  [any failure kills LEMMA HE7-12]
 P3 HE7-13: dv2res(f,Psi) == 8*lam2; dv2res(f,Psi1) > 8*lam2 STRICT; every
    post-refine slope > lam2; HE7-9(b) count identity at the refined key.
 P4 sigma (full read, refine loop + peel) == PARI on every member; all four
    mu2=2 outcome genres appear: {(4,2)}, {(2,4)}, {(2,2),(2,2)} via split,
    and via two sides; refine chains terminate (bound 12).
 P5 TEETH: T1 wrong-residue w' = lift2(lam2, s2') with s2' != s2 gives
    dv2res(f, Psi - w') == 8*lam2 EXACTLY (no slope increase — the
    residue-match of HE7-13 is load-bearing) on EVERY member; T2 the lazy
    dictionary (repeated residual read as split, no refine) MISMATCHES
    PARI on >= 1 member.
 P6 symbolic polytope: (S5.8.1)'s bound > 0 at every admissible exact
    rational (eps0, delta) configuration in 6 frames incl. d_r = 3, f1 = 2,
    f1 = 3 (the never-exercised HE7-BOX-2 genres, symbolically).

SMOKE RECORD (disclosed): before sealing, run_member was exercised via
import on TWO members only — (p,u,lam2,s2) = (3,3,7,(1,1)) and
(3,3,8,(0,2)), both green (sigma {(4,2)} == PARI, refine fired, tie seen,
lazy tooth caught), plus pari_sigma(x^4+3, 3) = {(4,1)}.  No full row was
run pre-seal; the full battery runs once, after the seal commit.
"""
import sys, os, json, time
from fractions import Fraction as Fr

sys.path.insert(0, '/data/users/asvin/.local/lib/python3.10/site-packages')
import cypari2
pari = cypari2.Pari()
pari.allocatemem(1 << 30)

HERE = os.path.dirname(os.path.abspath(__file__))
BIG = 10 ** 9

RES = {'members': 0, 'checks': {}, 'viol': [], 'genres': {}, 'ties': 0,
       'proper_s2': 0, 'refine_hist': {}, 'examples': [], 'polytope': 0}


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


# ---------------------------------------------------------------- Z[x] exact
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def pneg(a):
    return [-c for c in a]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a = a[:-1]
    return a


def pdivmod_monic(f, g):
    """f = q*g + r with g monic, exact over Z."""
    f = f[:]
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(f) - 1 >= dg and any(f):
        d = len(f) - 1
        c = f[-1]
        if c == 0:
            f = f[:-1]
            continue
        q[d - dg] = c
        for i in range(dg + 1):
            f[d - dg + i] -= c * g[i]
        f = trim(f)
    return trim(q), trim(f)


def development(f, key, mu):
    out, cur = [], f[:]
    for _ in range(mu + 1):
        cur, r = pdivmod_monic(cur, key)
        out.append(r)
    return out


def resultant(f, g):
    """Sylvester determinant, integer Bareiss (exact)."""
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0 or (m == 0 and n == 0):
        return 1
    N = m + n
    M = [[0] * N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(reversed(f)):
            M[i][i + j] = c
    for i in range(m):
        for j, c in enumerate(reversed(g)):
            M[n + i][i + j] = c
    sign, prev = 1, 1
    A = M
    for k in range(N - 1):
        if A[k][k] == 0:
            piv = next((i for i in range(k + 1, N) if A[i][k]), None)
            if piv is None:
                continue
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
            A[i][k] = 0
        prev = A[k][k] if A[k][k] else prev
    return sign * A[N - 1][N - 1]


def vp(n, p):
    if n == 0:
        return BIG
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# --------------------------------------------------- the level-2 frame data
class Frame(object):
    def __init__(self, p, u, b):
        self.p, self.u, self.b = p, u, b       # r = Z^2 + b, beta^2 = -b
        self.T2 = 2 * u
        self.key = [-p, 0, 1]                  # Phi' = x^2 - p
        # Psi = Phi'^2 + 0*nrm(u)*Phi' + b*nrm(2u)  (r = Z^2 + 0*Z + b)
        self.Psi = padd(pmul(self.key, self.key), self.nrm(2 * u, b))

    def nrm(self, m, c=1):
        """c * x^m mod Phi' = c * p^{m//2} x^{m%2}; dv = m exactly."""
        return ([c * self.p ** (m // 2)] if m % 2 == 0
                else [0, c * self.p ** (m // 2)])

    def dv1(self, c):
        """level-1 slot value of c (deg <= 1): min(2v(c0), 2v(c1)+1)."""
        c0 = c[0] if len(c) > 0 else 0
        c1 = c[1] if len(c) > 1 else 0
        return min(2 * vp(c0, self.p), 2 * vp(c1, self.p) + 1)

    def res1(self, c, m):
        """residue in F_p of c(theta)/x(theta)^m if dv1(c) == m else 0."""
        if m < 0 or self.dv1(c) != m:
            return 0
        if m % 2 == 0:
            return (c[0] // self.p ** (m // 2)) % self.p
        return (c[1] // self.p ** (m // 2)) % self.p

    def phidev(self, A):
        """A (deg <= 3) = c0 + c1*Phi': the two level-2 slots."""
        q, r = pdivmod_monic(A, self.key)
        return r, q

    def dv2(self, A):
        if not any(A):
            return BIG
        c0, c1 = self.phidev(A)
        return min(self.dv1(c0), self.dv1(c1) + self.u)

    def res2(self, A, k):
        """level-2 residue of A/n2(k) in K2 = F_{p^2} as (g0, g1)."""
        c0, c1 = self.phidev(A)
        return (self.res1(c0, k), self.res1(c1, k - self.u))

    def lift2(self, k, c2):
        """(LIFT2): W with deg < 4, dv2 = k, res2(W, k) = c2 = (g0, g1)."""
        g0, g1 = c2[0] % self.p, c2[1] % self.p
        out = [0]
        if g0:
            out = padd(out, self.nrm(k, g0))
        if g1:
            out = padd(out, pmul(self.nrm(k - self.u, g1), self.key))
        return trim(out)

    # F_{p^2} arithmetic, beta^2 = -b
    def kmul(self, x, y):
        p, b = self.p, self.b
        return ((x[0] * y[0] - b * x[1] * y[1]) % p,
                (x[0] * y[1] + x[1] * y[0]) % p)

    def kinv(self, x):
        p, b = self.p, self.b
        N = (x[0] * x[0] + b * x[1] * x[1]) % p
        Ni = pow(N, p - 2, p)
        return ((x[0] * Ni) % p, (-x[1] * Ni) % p)

    def slot_values(self, C):
        """occupied slot values of C, deg C <= 4 allowed (top slot via dev)."""
        cs = development(C, self.key, 2)
        out = []
        for s, c in enumerate(cs[:3]):
            m = self.dv1(c) if any(c) else BIG
            if m < BIG:
                out.append((s, m + s * self.u))
        return out


def hull(pts):
    """lower hull sides of [(j, m)] with m possibly BIG; returns
    [(j1,m1,j2,m2)] left-to-right."""
    P = [(j, m) for j, m in pts if m < BIG]
    out = []
    j1, m1 = P[0]
    while (j1, m1) != P[-1]:
        best, bs = None, None
        for j2, m2 in P:
            if j2 <= j1:
                continue
            s = Fr(m1 - m2, j2 - j1)
            if bs is None or s > bs or (s == bs and j2 > best[0]):
                best, bs = (j2, m2), s
        out.append((j1, m1, best[0], best[1]))
        (j1, m1) = best
    return out


ZERO = (0, 0)
ONE = (1, 0)


def read2(f, fr, max_ref=12, lazy=False):
    """the level-2 read at frame fr, from the note's S1/(SLOT2)/S8:
    development, dv2 polygon, K2-residuals (twist trivial at l=1),
    dictionary (e,f) = (2*l2, 2*deg r2); alpha-refine at repeated
    K2-rational linear residual; peel at Psi | f.  lazy=True is TOOTH T2:
    the repeated residual is (mis)read as a split pair, no refine."""
    p = fr.p
    Psi = fr.Psi[:]
    sigma, refines, tie_seen = [], 0, 0
    trace = []
    for step in range(max_ref + 1):
        nf = len(f) - 1
        mu2 = nf // 4
        Ad = development(f, Psi, mu2)
        if len(trim(Ad[mu2])) != 1 or Ad[mu2][0] != 1:
            return {'status': 'BAD-TOP'}
        if not any(Ad[0]):                       # Psi | f: the peel
            q, r = pdivmod_monic(f, Psi)
            if any(r):
                return {'status': 'BAD-PEEL'}
            sigma.append((2, 2))
            trace.append('peel')
            f = q
            if len(f) - 1 == 0:
                break
            continue
        dv2s = [fr.dv2(A) for A in Ad]
        # tie census: min attained at both slots of the attaining A_j
        for j in range(mu2):
            if dv2s[j] < BIG:
                c0, c1 = fr.phidev(Ad[j])
                if fr.dv1(c0) == dv2s[j] and fr.dv1(c1) + fr.u == dv2s[j]:
                    tie_seen = 1
        sides = hull([(j, m) for j, m in enumerate(dv2s)])
        deeper = None
        for (j1, m1, j2, m2) in sides:
            lam2 = Fr(m1 - m2, j2 - j1)
            if lam2 <= fr.T2:
                return {'status': 'NONPRINCIPAL', 'lam2': str(lam2)}
            l2, u2 = lam2.denominator, lam2.numerator
            d2 = (j2 - j1) // l2
            co = []
            for t in range(d2 + 1):
                j = j1 + t * l2
                want = m1 - u2 * t
                co.append(fr.res2(Ad[j], want) if (j <= mu2 and
                          dv2s[j] == want) else ZERO)
            if co[d2] == ZERO:
                return {'status': 'BAD-LEAD'}
            inv = fr.kinv(co[d2])
            co = [fr.kmul(c, inv) for c in co]
            if d2 == 1:
                sigma.append((2 * l2, 2))
                trace.append(('lin', str(lam2)))
            elif d2 == 2:
                # solve Z^2 + co[1] Z + co[0] = 0 over F_{p^2} by scan
                roots = []
                for x in range(p):
                    for y in range(p):
                        z = (x, y)
                        val = fr.kmul(z, z)
                        val = ((val[0] + co[0][0]) % p, (val[1] + co[0][1]) % p)
                        cz = fr.kmul(co[1], z)
                        val = ((val[0] + cz[0]) % p, (val[1] + cz[1]) % p)
                        if val == (0, 0):
                            roots.append(z)
                if not roots:
                    sigma.append((2, 4))
                    trace.append(('inert', str(lam2)))
                elif len(roots) == 2:
                    sigma.extend([(2, 2), (2, 2)])
                    trace.append(('split', str(lam2)))
                else:                             # double root: refine
                    if lazy:
                        sigma.extend([(2, 2), (2, 2)])
                        trace.append(('lazy-split', str(lam2)))
                        continue
                    if l2 != 1:
                        return {'status': 'LEVEL3'}
                    deeper = (int(lam2), roots[0])
                    trace.append(('refine', str(lam2), roots[0]))
            else:
                return {'status': 'D2BIG'}
        if deeper is None:
            break
        lam2i, s2r = deeper
        w = fr.lift2(lam2i, s2r)
        Psi = trim(padd(Psi, pneg(w)))
        sigma = []                  # restart the read at the refined key
        refines += 1
    else:
        return {'status': 'REFINE-OVERFLOW'}
    return {'status': 'OK', 'sigma': tuple(sorted(sigma)),
            'refines': refines, 'tie': tie_seen, 'trace': trace,
            'key': Psi}


def pari_sigma(f, p):
    """sigma(f) over Q_p: factor over Q, per factor nfinit+idealprimedec.
    The multiset of (e, f) of ALL primes above p in prod Q[x]/(F_i) equals
    the multiset over the Q_p-irreducible factors of f (exact, no p-adic
    precision anywhere)."""
    fx = pari('+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c))
    fac = pari.factor(fx)
    out = []
    for i in range(int(pari.matsize(fac)[0])):
        F, mult = fac[i, 0], int(fac[i, 1])
        if int(pari.poldegree(F)) < 1:
            continue
        if mult != 1:
            raise RuntimeError('repeated global factor (disc = 0?)')
        K = pari.nfinit(F)
        for pr in pari.idealprimedec(K, p):
            out.append((int(pr[2]), int(pr[3])))
    return tuple(sorted(out))


def dv2res(g, C, p):
    """sum_{xi: g(xi)=0} dv2(C(xi)) = 2*v_p(Res(g, C)) at l = 1 (dv2 = dv =
    2*v_p); BIG if Res = 0."""
    r = resultant(g, C)
    return BIG if r == 0 else 2 * vp(r, p)


def test1(fr, uk, lk, sres):
    """level-1 test polynomial Psi_{kappa, Z - sres} at kappa = uk/lk:
    Phi'^{lk} + (-sres)*nrm(uk); every root xi has dv(Phi'(xi)) = kappa
    (HE6-1), off the level-2 disk when kappa != lam or residue wrong."""
    out = [0]
    P = [1]
    for _ in range(lk):
        P = pmul(P, fr.key)
    return trim(padd(P, fr.nrm(uk, -sres)))


def run_member(fr, lam2, s2, n1, n0, stats):
    p, u = fr.p, fr.u
    m2s2 = ((-2 * s2[0]) % p, (-2 * s2[1]) % p)
    s2sq = fr.kmul(s2, s2)
    A1 = trim(padd(fr.lift2(lam2, m2s2), n1))
    A0 = trim(padd(fr.lift2(2 * lam2, s2sq), n0))
    f = trim(padd(padd(pmul(fr.Psi, fr.Psi), pmul(A1, fr.Psi)), A0))
    if resultant(f, [c * (i + 1) for i, c in enumerate(f[1:])]) == 0:
        return 'disc0'
    RES['members'] += 1
    # ---- C0/C1: the read confirms the construction; slot geometry
    Ad = development(f, fr.Psi, 2)
    dv2s = [fr.dv2(A) for A in Ad]
    sides = hull([(j, m) for j, m in enumerate(dv2s)])
    if (len(sides) != 1 or Fr(sides[0][1] - sides[0][3],
                              sides[0][2] - sides[0][0]) != lam2):
        viol('C0 polygon not the single side lam2',
             {'dv2s': dv2s, 'lam2': lam2})
        return 'bad'
    r0, r1m = fr.res2(Ad[0], 2 * lam2), fr.res2(Ad[1], lam2)
    if r0 != s2sq or r1m != m2s2:
        viol('C0 residual != (Z - s2)^2', {'r0': r0, 'r1': r1m, 's2': s2})
        return 'bad'
    note('C0-read-confirms')
    sv = fr.slot_values(fr.Psi)
    if any(v != fr.T2 for _, v in sv):
        viol('C1 Psi slot off T2', sv)
        return 'bad'
    w = fr.lift2(lam2, s2)
    if fr.dv2(w) != lam2 or fr.res2(w, lam2) != s2 or lam2 <= fr.T2:
        viol('C1 (LIFT2) contract', {'dv2': fr.dv2(w), 'lam2': lam2})
        return 'bad'
    note('C1-slot-geometry')
    Psi1 = trim(padd(fr.Psi, pneg(w)))
    # ---- C2: off-disk strata (S5.8.1) + exact value formula + invariance
    sp = 1 if (fr.b, 1) != s2 else 2      # any F_p residue != beta-root use
    strata = [
        ('delta=infty', fr.key, Fr(0), Fr(0)),
        ('delta>lam', test1(fr, u + 1, 1, 1), Fr(0), Fr(0)),
        ('mid eps1=1/2', test1(fr, 2 * u - 1, 2, 1), Fr(0), Fr(1, 2)),
        ('mid eps1=3/4 (9/4-seed)', test1(fr, 4 * u - 3, 4, 1),
         Fr(0), Fr(3, 4)),
        ('eps0=1', [-1, 1], Fr(1), Fr(u)),
    ]
    for name, g, e0, e1 in strata:
        dg = len(g) - 1
        a_psi = dv2res(g, fr.Psi, p)
        a_w = dv2res(g, w, p)
        a_p1 = dv2res(g, Psi1, p)
        bound = (lam2 - fr.T2) + e1 - e0          # l(D'-1) = 1 at this frame
        if bound <= 0:
            viol('C2 bound not positive', {'stratum': name})
            return 'bad'
        if a_psi != dg * (fr.T2 - 2 * e1) and name != 'delta=infty':
            viol('C2 off-disk VALUE formula fails',
                 {'stratum': name, 'got': a_psi,
                  'want': str(dg * (fr.T2 - 2 * e1))})
            return 'bad'
        if name == 'delta=infty' and a_psi != dg * fr.T2:
            viol('C2 value formula at delta=infty', {'got': a_psi})
            return 'bad'
        if a_w < BIG and Fr(a_w - a_psi) < dg * bound:
            viol('C2 (S5.8.1) sum inequality FAILS',
                 {'stratum': name, 'w': a_w, 'Psi': a_psi,
                  'need': str(dg * bound)})
            return 'bad'
        if a_p1 != a_psi:
            viol('C2 invariance fails', {'stratum': name, 'Psi': a_psi,
                                         'Psi1': a_p1})
            return 'bad'
        note('C2-offdisk')
    # ---- C3: HE7-13 at the refined key
    a_f0 = dv2res(f, fr.Psi, p)
    a_f1 = dv2res(f, Psi1, p)
    if a_f0 != 8 * lam2:
        viol('C3 dv2res(f, Psi) != 8 lam2', {'got': a_f0})
        return 'bad'
    if not a_f1 > 8 * lam2:
        viol('C3 no strict increase', {'got': a_f1})
        return 'bad'
    Ad1 = development(f, Psi1, 2)
    dv2s1 = [fr.dv2(A) for A in Ad1]
    if any(A and any(A) for A in [Ad1[0]]) or dv2s1[0] < BIG:
        sides1 = hull([(j, m) for j, m in enumerate(dv2s1)])
        slopes = [(Fr(m1 - m2, j2 - j1), j2 - j1)
                  for (j1, m1, j2, m2) in sides1]
        if any(sl <= lam2 for sl, _ in slopes):
            viol('C3 post-refine slope <= lam2', {'slopes': slopes})
            return 'bad'
        if a_f1 < BIG and Fr(a_f1) != 4 * sum(sl * L for sl, L in slopes):
            viol('C3 HE7-9(b) identity at refined key fails',
                 {'lhs': a_f1, 'rhs': str(4 * sum(sl * L
                                                  for sl, L in slopes))})
            return 'bad'
    note('C3-strict-slope')
    # ---- T1 tooth: wrong-residue w' gives NO slope increase
    s2w = ((s2[0] + 1) % p, s2[1])
    if s2w == (0, 0):
        s2w = ((s2[0] + 2) % p, s2[1])
    wbad = fr.lift2(lam2, s2w)
    a_bad = dv2res(f, trim(padd(fr.Psi, pneg(wbad))), p)
    if a_bad != 8 * lam2:
        viol('T1 wrong-residue w\' RAISED the slope sum',
             {'got': a_bad, 'want': 8 * lam2})
        return 'bad'
    note('T1-wrong-residue-flat')
    # ---- C4: sigma, full read vs PARI
    rd = read2(f, fr)
    if rd['status'] != 'OK':
        viol('C4 read status', rd)
        return 'bad'
    sig_pari = pari_sigma(f, p)
    if rd['sigma'] != sig_pari:
        viol('C4 sigma mismatch', {'read': rd['sigma'], 'pari': sig_pari,
                                   'trace': rd['trace']})
        return 'bad'
    note('C4-sigma-PARI')
    RES['genres'][str(rd['sigma'])] = RES['genres'].get(
        str(rd['sigma']), 0) + 1
    RES['refine_hist'][rd['refines']] = RES['refine_hist'].get(
        rd['refines'], 0) + 1
    if rd['tie']:
        RES['ties'] += 1
    if s2[1] != 0:
        RES['proper_s2'] += 1
    # ---- T2 tooth: the lazy dictionary must be CAUGHT by PARI somewhere
    rdl = read2(f, fr, lazy=True)
    if rdl['status'] == 'OK' and rdl['sigma'] != sig_pari:
        stats['lazy_caught'] += 1
    if len(RES['examples']) < 3:
        RES['examples'].append({'p': p, 'u': u, 'lam2': lam2, 's2': s2,
                                'sigma': str(rd['sigma']),
                                'refines': rd['refines'],
                                'dv2res_pre': a_f0, 'dv2res_post': a_f1})
    return 'ok'


def polytope_leg():
    """P6: (S5.8.1)'s positivity over the admissible (eps0, delta) polytope,
    exact rationals, frames incl. d_r = 3 and f1 in {2, 3}."""
    frames = [(2, 1, 1, 2, 1), (2, 1, 1, 1, 2), (3, 2, 2, 3, 3),
              (2, 3, 1, 2, 3), (3, 1, 2, 1, 3), (2, 2, 1, 3, 2)]
    n = 0
    for (e1, f1, h, l, dr) in frames:
        Dp = e1 * f1
        for lam_num in range(l * Dp * h + 1, l * Dp * h + 8):
            lam = Fr(lam_num, l)
            if lam.denominator != l:
                continue
            uu = lam_num
            T2 = l * dr * uu
            for nu_off in [Fr(1, 3), Fr(1), Fr(7, 2)]:
                nu = T2 + nu_off
                # case eps0 > 0: delta = D'(h - eps0), eps1 forced
                for e0 in [Fr(1, 4), Fr(1, 2), Fr(1), Fr(h)]:
                    if e0 > h:
                        continue
                    delta = Dp * (h - e0)
                    e1off = l * (lam - delta)
                    if e1off <= 0:
                        viol('P6 eps1 not > 0 at eps0 > 0',
                             (e1, f1, h, l, dr, str(e0)))
                        return n
                    b = (nu - T2) + e1off - l * (Dp - 1) * e0
                    if b <= 0:
                        viol('P6 bound fails (eps0>0)',
                             {'frame': (e1, f1, h, l, dr), 'e0': str(e0),
                              'lam': str(lam), 'bound': str(b)})
                        return n
                    n += 1
                # case eps0 = 0: delta on a grid incl. both bands + infty
                for delta in [Fr(Dp * h), Fr(Dp * h) + Fr(1, 4),
                              (Fr(Dp * h) + lam) / 2, lam - Fr(1, 8),
                              lam, lam + 3, Fr(BIG)]:
                    e1off = max(Fr(0), l * (lam - delta))
                    b = (nu - T2) + e1off
                    if b <= 0:
                        viol('P6 bound fails (eps0=0)',
                             {'frame': (e1, f1, h, l, dr),
                              'delta': str(delta), 'bound': str(b)})
                        return n
                    n += 1
    return n


def main():
    t0 = time.time()
    print(__doc__.split('\n')[0])
    stats = {'lazy_caught': 0}
    for p, b in [(3, 1), (5, 2)]:
        noises = [([0], [0])]
        for hgt1, hgt0, g in [(1, 1, (1, 0)), (2, 1, (0, 1)),
                              (1, 2, (1, 1)), (3, 3, (2, 1))]:
            noises.append((None, None, hgt1, hgt0, g))
        for u in [3, 5]:
            fr = Frame(p, u, b)
            for lam2 in [2 * u + 1, 2 * u + 2]:
                for x in range(p):
                    for y in range(p):
                        s2 = (x, y)
                        if s2 == (0, 0):
                            continue
                        for nz in noises:
                            if len(nz) == 2:
                                n1, n0 = nz
                            else:
                                _, _, h1, h0, g = nz
                                n1 = fr.lift2(lam2 + h1, g)
                                n0 = fr.lift2(2 * lam2 + h0, g)
                            run_member(fr, lam2, s2, n1, n0, stats)
        print(' p=%d done (%.1fs)' % (p, time.time() - t0))
    RES['polytope'] = polytope_leg()
    RES['lazy_caught'] = stats['lazy_caught']
    RES['secs'] = round(time.time() - t0, 1)
    print('MEMBERS %d  checks %s' % (RES['members'], RES['checks']))
    print('genres %s  refine_hist %s  ties %d  proper-extension s2 %d'
          % (RES['genres'], RES['refine_hist'], RES['ties'],
             RES['proper_s2']))
    print('T2 lazy-dictionary caught by PARI on %d members'
          % stats['lazy_caught'])
    print('P6 polytope configs verified: %d' % RES['polytope'])
    print('VIOLATIONS: %d' % len(RES['viol']))
    print('%.1fs' % (time.time() - t0))
    with open(os.path.join(HERE, 'he7_pe2_fresh_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True, default=str)


if __name__ == '__main__':
    main()
