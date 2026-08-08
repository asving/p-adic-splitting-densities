"""HE6 — the ENLARGED TEST FAMILY at FRACTIONAL heights (HE3-BOX-6's repair),
machine leg.  SEALED PREREGISTRATION (commit 1; legs wired at commit 2).

WHAT IS BEING TESTED.  HE3 (`lean/notes/openmath/HE3_PROOF_2026-08-08.md`)
proves [GENHN-HE(mu)] for mu <= 3 and boxes ONE branch at mu >= 4
(HE3-BOX-6): at a stage-polygon side of dv-slope lam = u/l with l >= 2 AND
residual degree d >= 2, NO element of the stage ring R has dv = lam, so no
test key of the form Phi' + w sits at the side's height and the residue peel
has nothing to recenter on.  HE6's repair: test polynomials of HIGHER DEGREE
at the side's OWN fractional height,

    Psi_{lam,r} := sum_{t=0..d_r} rhat_t * n((d_r - t) u) * Phi'^{l t},
    monic of degree D' * l * d_r,   n(k) = x^k mod Phi'  (dv(n(k)) = k),

for r = Z^{d_r} + ... a monic irreducible over K = residue field of R.  These
are the order-2 Montes keys, written in the program's own normalizer language
(varpi = x, so all normalizers are powers of ONE element and the twist
cocycle is absent).

SETTING for every row: e1 = 2, f1 = 1, h = 1, Phi' = x^2 - pi (pi = p in
char 0, pi = t in char p), D' = e1 f1 = 2, dv = 2 v, K = F_p, varpi = x.
mu = 4, so deg f = 8: the FIRST DEGREE at which HE3-BOX-6 bites (l >= 2 and
d >= 2 need l*d <= mu, so mu >= 4, and a composite stage needs D' >= 2, so
n = D' mu >= 8).

PREREGISTERED PREDICTIONS (written before the run; scored in S8 of
`lean/notes/openmath/HE6_PROOF_2026-08-08.md`):

  P1 (HE6-GEN, the (SEP)-free slope-count identity).  For EVERY rational
     test height kappa = u/l (gcd(u,l) = 1, kappa > D'h) and every monic
     irreducible r over F_p with r not dividing the residual at kappa,
         2 * v(Res(f, Psi_{kappa,r})) == l * d_r * D' * h_F(kappa),
     h_F(kappa) = min_j (dv(A_j) + j kappa), EXACTLY, with no hypothesis of
     the (SEP) kind that HE3-3 needed (integer sampling only).

  P2 (HE6-SEP / nonemptiness).  If r DIVIDES the residual R_lam of the side
     at kappa = lam, the same resultant valuation is STRICTLY GREATER than
     the P1 value.  This strict excess is the whole engine: it certifies the
     label class S_{lam,r} is NONEMPTY, whence (orbit bound + total count)
     |S_{lam,r}| = D' l deg r.

  P3 (HE6-XI, the xi-side).  Every root xi of Psi_{lam,r} carries the label
     (lam, r): Psi is irreducible over the base and 2*v(Res(Psi, Phi')) /
     deg Psi == lam; moreover two distinct r's give MUTUALLY GENERIC test
     polynomials (no excess in Res(Psi_{lam,r}, Psi_{lam,r'})).

  P4 (HE6-SIG).  The predicted sigma at the degenerate side --- l = 2,
     R_lam = (Z - s1)(Z - s2) with s1 != s2 in K^x, so TWO labels each with
     (e_s, f_s) = (2, 1) --- is sigma = {(4,1),(4,1)}: an octic splitting
     into two totally ramified quartics.  PARI factorpadic must confirm it
     on every decided member of the row.  Controls: R_lam irreducible over
     K gives one label (2,2), sigma = {(4,2)}.

  P5 (HE6-RANK).  The OLD family (test keys at INTEGER heights only) is
     RANK-DEFICIENT at that side: its identity family has rank 1 where 2
     labels must be pinned, and admits >= 3 spurious nonnegative solutions
     compatible with all old identities (the l >= 2 analogue of HE3's
     HE-T-UNDET).  The enlarged family has FULL rank = #labels and its
     unique solution is the true class-size vector.

TEETH (each must FIRE; a silent pass is a failure of the instrument):
  T1 HE6-T-UNDET2 : the old integer-height family admits spurious solutions
                    at the l = 2 degenerate side; the new family kills them.
  T2 HE6-T-PLANT  : a deliberately rank-deficient family (one Psi dropped)
                    must be REPORTED as not-separating, not silently passed.
  T3 HE6-T-FLIP   : flipped sigma dictionaries must be caught by PARI.
  T4 HE6-T-BADKEY : a test polynomial built with gcd(u,l) != 1 (so its own
                    Phi'-side residual has degree > 1 and it is reducible)
                    must FAIL the P3 xi-side check.
  T5 HE6-T-CASEB  : two members with IDENTICAL outer data (same lam, same
                    R_lam = (Z-s)^2) but DIFFERENT PARI sigma -- certifying
                    that the repeated-residual case at l >= 2 genuinely
                    needs the DEEPER read (HE6-BOX-1), i.e. that the box is
                    real and not laziness.

CHARACTERISTICS.  Rows run in BOTH characteristics: O = Z_p (p = 3,5,7) and
O = F_p[[t]] (p = 3,5), the latter through an exact F_p[t] coefficient ring
with the same code path.  ORACLE ASYMMETRY (disclosed, inherited by every
unit of this program): PARI factorpadic exists only on the Z_p side, so the
char-p rows are scored against the reader plus the resultant identities.

Artifacts: he6_checks_output.txt, he6_checks_results.json.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

WIP = True      # commit 1: skeleton + smoke; commit 2 flips this to False

PINS = ['he3_checks.py', 'he3_checks_results.json', 'w12_checks.py',
        'w10_checks.py']

BIG = 10 ** 6


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


# ===================================================== coefficient rings
class Zp(object):
    """O = Z_p ; elements are python ints ; char 0."""
    char0 = True

    def __init__(self, p):
        self.p = p
        self.zero, self.one = 0, 1

    def el(self, k):
        return int(k)

    def unif(self, a):
        return self.p ** a

    def val(self, a):
        if a == 0:
            return BIG
        n = 0
        while a % self.p == 0:
            a //= self.p
            n += 1
        return n

    def res_unit(self, a, k):
        """residue in F_p of a / pi^k  (requires val(a) == k)."""
        return (a // self.p ** k) % self.p

    def name(self):
        return 'Z_%d' % self.p


class FpT(object):
    """element of F_p[t]: coeffs low-to-high, mod p, no trailing zeros."""
    __slots__ = ('c', 'p')

    def __init__(self, c, p):
        self.p = p
        c = [x % p for x in c]
        while c and c[-1] == 0:
            c.pop()
        self.c = c

    def __bool__(self):
        return bool(self.c)
    __nonzero__ = __bool__

    def __eq__(self, o):
        if isinstance(o, int):
            return self.c == FpT([o], self.p).c
        return self.c == o.c

    def __hash__(self):
        return hash(tuple(self.c))

    def __add__(self, o):
        if isinstance(o, int):
            o = FpT([o], self.p)
        n = max(len(self.c), len(o.c))
        return FpT([(self.c[i] if i < len(self.c) else 0) +
                    (o.c[i] if i < len(o.c) else 0) for i in range(n)], self.p)
    __radd__ = __add__

    def __neg__(self):
        return FpT([-x for x in self.c], self.p)

    def __sub__(self, o):
        if isinstance(o, int):
            o = FpT([o], self.p)
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if isinstance(o, int):
            return FpT([x * o for x in self.c], self.p)
        if not self.c or not o.c:
            return FpT([], self.p)
        out = [0] * (len(self.c) + len(o.c) - 1)
        for i, a in enumerate(self.c):
            if a:
                for j, b in enumerate(o.c):
                    out[i + j] += a * b
        return FpT(out, self.p)
    __rmul__ = __mul__

    def __floordiv__(self, o):
        """EXACT division (Bareiss only ever divides exactly)."""
        if isinstance(o, int):
            o = FpT([o], self.p)
        if not o.c:
            raise ZeroDivisionError
        num, den, p = self.c[:], o.c, self.p
        dd = len(den) - 1
        inv = pow(den[-1], p - 2, p)
        q = [0] * max(0, len(num) - dd)
        for i in range(len(num) - 1, dd - 1, -1):
            co = (num[i] * inv) % p
            q[i - dd] = co
            if co:
                for j in range(dd + 1):
                    num[i - dd + j] = (num[i - dd + j] - co * den[j]) % p
        if any(x % p for x in num[:dd]):
            raise ValueError('inexact division in F_p[t]')
        return FpT(q, p)

    def __repr__(self):
        return 'FpT(%r)' % (self.c,)


class FpTring(object):
    """O = F_p[[t]] (as F_p[t]) ; char p."""
    char0 = False

    def __init__(self, p):
        self.p = p
        self.zero, self.one = FpT([], p), FpT([1], p)

    def el(self, k):
        return FpT([k], self.p)

    def unif(self, a):
        return FpT([0] * a + [1], self.p)

    def val(self, a):
        if not a:
            return BIG
        for i, c in enumerate(a.c):
            if c:
                return i
        return BIG

    def res_unit(self, a, k):
        return a.c[k] % self.p if k < len(a.c) else 0

    def name(self):
        return 'F_%d[[t]]' % self.p


# ============================================ generic polynomial helpers
def padd(f, g):
    n = max(len(f), len(g))
    return [(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
            for i in range(n)]


def pmul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] = out[i + j] + a * b
    return out


def ppow(f, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, f)
    return out


def pdivmod_monic(f, key):
    d = len(key) - 1
    f = f[:]
    q = [0] * max(1, len(f) - d)
    for i in range(len(f) - 1, d - 1, -1):
        c = f[i]
        if c:
            q[i - d] = c
            for j in range(d + 1):
                f[i - d + j] = f[i - d + j] - c * key[j]
    return q, f[:d]


def development(f, key, mu):
    out, cur = [], f[:]
    for _ in range(mu + 1):
        q, r = pdivmod_monic(cur, key)
        out.append(r)
        cur = q
    return out


def bareiss(M):
    n = len(M)
    if n == 0:
        return 1
    A = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if not A[k][k]:
            piv = None
            for i in range(k + 1, n):
                if A[i][k]:
                    piv = i
                    break
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    out = A[n - 1][n - 1]
    return out if sign == 1 else -out


def resultant(f, g):
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0:
        return 0
    N = m + n
    M = [[0] * N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(f):
            M[i][i + (m - j)] = c
    for i in range(m):
        for j, c in enumerate(g):
            M[n + i][i + (n - j)] = c
    return bareiss(M)


# ================================== the stage frame (e1=2, f1=1, h=1)
E1, F1, H = 2, 1, 1
DP = E1 * F1                      # D' = 2
MU = 4                            # deg f = D' * mu = 8


def key_poly(R):
    """Phi' = x^2 - pi ;  roots of v = 1/2, dv(theta) = h = 1."""
    return [-R.unif(1), R.zero, R.one]


def nrm(k, R):
    """n(k) = x^k mod Phi' = pi^{k//2} x^{k mod 2} ; dv(n(k)) = k EXACTLY.
    All normalizers are powers of the SINGLE element varpi = x, so the
    normalizer cocycle (and with it HE3's twist bookkeeping) is trivial."""
    if k % 2 == 0:
        return [R.unif(k // 2)]
    return [R.zero, R.unif(k // 2)]


def dv_A(A, R):
    """SLOT LEMMA at e1 = 2, h = 1: dv(A(xi)) for any xi with (T1)/(T2).
    The two slots have opposite parities, so the min is never tied."""
    a0 = A[0] if len(A) > 0 else R.zero
    a1 = A[1] if len(A) > 1 else R.zero
    v0 = R.val(a0)
    v1 = R.val(a1)
    c0 = 2 * v0 if v0 < BIG else BIG
    c1 = 2 * v1 + H if v1 < BIG else BIG
    return min(c0, c1)


def res_A(A, R):
    """residue in K = F_p of A / n(dv(A)) ; 0 if A = 0."""
    m = dv_A(A, R)
    if m >= BIG:
        return 0
    if m % 2 == 0:
        return R.res_unit(A[0], m // 2)
    return R.res_unit(A[1], (m - 1) // 2)


# ------------------------------------------------------- the test family
def test_poly(u, l, rco, R):
    """Psi_{kappa,r} at kappa = u/l with r = Z^d + sum_{t<d} rco[t] Z^t:
        Psi = sum_{t=0..d} rhat_t n((d-t)u) Phi'^{l t},  rhat_d = 1.
    Monic of degree D' l d.  For gcd(u,l) = 1 every root xi of Psi has
    dv(Phi'(xi)) = u/l and residue a root of r (LEMMA HE6-1)."""
    key = key_poly(R)
    d = len(rco)
    out = [R.zero]
    for t in range(d + 1):
        co = R.one if t == d else R.el(rco[t])
        term = pmul([c * co for c in nrm((d - t) * u, R)], ppow(key, l * t))
        out = padd(out, term)
    return out


def dv_res(f, g, R):
    """Sum_rho dv(g(rho)) = e1 * v(Res(f, g))."""
    r = resultant(f, g)
    if r == 0 or (hasattr(r, 'c') and not r):
        return BIG
    return E1 * R.val(r)


# -------------------------------------------------- polygon of the stage
def dv_list(A, R):
    """dv(A_j) for j = 0..mu  (A_mu = 1 -> 0)."""
    out = [dv_A(A[j], R) for j in range(MU)]
    out.append(0)
    return out


def hull_sides(dvs):
    """lower convex hull of {(j, dvs[j])}; returns list of sides
    (j1, m1, j2, m2) left-to-right with strictly decreasing slopes."""
    pts = [(j, dvs[j]) for j in range(len(dvs)) if dvs[j] < BIG]
    pts.sort()
    hull = []
    for q in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (q[0] - x1) >= (q[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(q)
    return [(hull[i][0], hull[i][1], hull[i + 1][0], hull[i + 1][1])
            for i in range(len(hull) - 1)]


def side_data(side, A, dvs, R):
    """(lam, l, u, L, d, residual coeff list low-to-high) for one side."""
    j1, m1, j2, m2 = side
    lam = Fr(m1 - m2, j2 - j1)
    l, u = lam.denominator, lam.numerator
    L = j2 - j1
    d = L // l
    co = []
    for t in range(d + 1):
        j = j1 + t * l
        want = m1 - lam * (j - j1)
        if j < MU:
            if dvs[j] == want:
                co.append(res_A(A[j], R))
            else:
                co.append(0)
        else:
            co.append(1 if dvs[j] == want else 0)
    return dict(lam=lam, l=l, u=u, L=L, d=d, res=co)


def factor_Fp(co, p):
    """factor a monic poly over F_p (coeffs low-to-high, leading 1);
    returns list of (irreducible as low-to-high tuple, multiplicity)."""
    def pnorm(c):
        c = [x % p for x in c]
        while c and c[-1] == 0:
            c.pop()
        return c

    def pdiv(a, b):
        a, dd = pnorm(a), len(pnorm(b)) - 1
        b = pnorm(b)
        inv = pow(b[-1], p - 2, p)
        q = [0] * max(0, len(a) - dd)
        for i in range(len(a) - 1, dd - 1, -1):
            c = (a[i] * inv) % p
            q[i - dd] = c
            if c:
                for j in range(dd + 1):
                    a[i - dd + j] = (a[i - dd + j] - c * b[j]) % p
        return pnorm(q), pnorm(a[:dd])

    def irreds(deg):
        out = []
        for tup in itertools.product(range(p), repeat=deg):
            c = list(tup) + [1]
            if deg == 1:
                out.append(c)
            else:
                if any(peval(c, a) == 0 for a in range(p)):
                    continue
                if deg == 2:
                    out.append(c)
        return out

    def peval(c, a):
        s = 0
        for co_ in reversed(c):
            s = (s * a + co_) % p
        return s

    cur = pnorm(co)
    facs = []
    for deg in (1, 2, 3, 4):
        cands = irreds(deg) if deg <= 2 else []
        if deg >= 3:
            cands = [list(t) + [1] for t in itertools.product(range(p),
                     repeat=deg)]
            cands = [c for c in cands if all(peval(c, a) for a in range(p))]
        for c in cands:
            while len(cur) > len(c) - 1:
                q, r = pdiv(cur, c)
                if r:
                    break
                cur = q
                for i, (ff, m) in enumerate(facs):
                    if list(ff) == c:
                        facs[i] = (ff, m + 1)
                        break
                else:
                    facs.append((tuple(c), 1))
        if len(cur) <= 1:
            break
    return facs


def read_labels(A, R, p):
    """the outer stage read: labels, class sizes, sigma (or DEEPER)."""
    dvs = dv_list(A, R)
    out = {'dvs': dvs, 'sides': [], 'labels': [], 'sigma': None,
           'deeper': False}
    if dvs[MU] != 0:
        return out
    for side in hull_sides(dvs):
        sd = side_data(side, A, dvs, R)
        if sd['res'][0] == 0:
            out['deeper'] = True          # residual constant term 0: no side
            continue
        facs = factor_Fp(sd['res'], p)
        sd['facs'] = [(list(f), m) for f, m in facs]
        out['sides'].append(sd)
        for f, m in facs:
            if m > 1:
                out['deeper'] = True
            out['labels'].append(dict(lam=str(sd['lam']), l=sd['l'],
                                      u=sd['u'], r=list(f), m=m,
                                      es=sd['l'], fs=len(f) - 1,
                                      size=DP * sd['l'] * (len(f) - 1)))
    if not out['deeper'] and out['labels']:
        out['sigma'] = tuple(sorted((E1 * lb['es'], F1 * lb['fs'])
                                    for lb in out['labels']))
    return out


def h_F(dvs, kappa):
    return min(dvs[j] + j * kappa for j in range(MU + 1) if dvs[j] < BIG)


# ============================================================ instances
def build_f(A, R):
    key = key_poly(R)
    f, powk = [R.zero], [R.one]
    for j in range(MU):
        f = padd(f, pmul(A[j], powk))
        powk = pmul(powk, key)
    return padd(f, powk)


def instance(u, rco2, R, pert=None):
    """single-side member: side (0, 2u)-(4, 0), lam = u/2, residual
    Z^2 + rco2[1] Z + rco2[0].  pert = optional dict j -> A_j (strictly
    above the lam-line: the deeper digits)."""
    A = [[R.zero], [R.zero], [R.zero], [R.zero]]
    A[0] = [c * R.el(rco2[0]) for c in nrm(2 * u, R)]
    A[2] = [c * R.el(rco2[1]) for c in nrm(u, R)]
    if pert:
        for j, Aj in pert.items():
            A[j] = padd(A[j], Aj)
    return A, build_f(A, R)


# ============================================================ PARI leg
def polystr(f):
    ts = []
    for i, c in enumerate(f):
        if c:
            ts.append('(%d)*x^%d' % (c, i))
    return '+'.join(ts) if ts else '0'


def gp_sig_batch(jobs, p):
    import w12_checks as W12
    import w10_checks as W10
    lines = [W12.GP_FUN]
    for i, (ps, _) in enumerate(jobs):
        lines.append('print("R %d ", sig(%s, %d))' % (i, ps, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            try:
                got[int(idx)] = W12.parse_sig(rest)
            except Exception:
                pass
    return got


# ============================================================ smoke run
def smoke(p=3, u=5):
    R = Zp(p)
    A, f = instance(u, [2, -3], R)           # R_lam = (Z-1)(Z-2) over F_3
    rd = read_labels(A, R, p)
    print('p=%d u=%d  dvs=%s' % (p, u, rd['dvs']))
    print('  labels:', [(lb['lam'], lb['r'], lb['size']) for lb in
                        rd['labels']], 'sigma=', rd['sigma'])
    for rco in ([(-1) % p], [(-2) % p]):     # r = Z - 1, Z - 2
        Ps = test_poly(u, 2, rco, R)
        meas = dv_res(f, Ps, R)
        gen = 2 * 1 * DP * h_F(rd['dvs'], Fr(u, 2))
        print('  r=%s  deg Psi=%d  measured=%s generic=%s  %s'
              % (rco, len(Ps) - 1, meas, gen,
                 'EXCESS' if meas > gen else 'flat'))
    return rd


def main():
    t0 = time.time()
    print('HE6 checks — WIP smoke (commit 1)' if WIP else 'HE6 checks')
    smoke(3, 5)
    smoke(5, 5)
    print('%.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
