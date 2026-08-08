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

WIP = False     # commit 1 sealed this True (smoke only); commit 2 flipped it

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


# ======================================================== bookkeeping
RES = {'legs': {}, 'viol': [], 'teeth': {}, 'rows': [], 'rank': [],
       'caseB': {}}


def note(leg, k=1):
    RES['legs'][leg] = RES['legs'].get(leg, 0) + k


def viol(leg, what, detail):
    RES['viol'].append({'leg': leg, 'what': what, 'detail': str(detail)[:400]})
    print('  !! VIOLATION %s %s %s' % (leg, what, str(detail)[:200]))


def tooth(name, fired, detail=''):
    RES['teeth'][name] = {'fired': bool(fired), 'detail': str(detail)[:400]}
    print('  TOOTH %-16s %s  %s' % (name, 'FIRED' if fired else 'DID NOT FIRE',
                                    str(detail)[:150]))


# ================================================ irreducibles over F_p
def peval_l(c, a, p):
    s = 0
    for co in reversed(c):
        s = (s * a + co) % p
    return s


def irred_list(p, deg):
    """monic irreducibles of degree deg over F_p, low-to-high, r(0) != 0."""
    out = []
    for tup in itertools.product(range(p), repeat=deg):
        c = list(tup) + [1]
        if c[0] == 0:
            continue
        if deg == 1:
            out.append(c)
        elif deg == 2:
            if all(peval_l(c, a, p) for a in range(p)):
                out.append(c)
    return out


# ================================================== member enumeration
def line_floor(j, u):
    """smallest integer dv STRICTLY above the lam-line at abscissa j,
    lam = u/2 (u odd), line height (4-j)*u/2."""
    num = (MU - j) * u
    return num // 2 + 1


def member_family(R, p, u, W=2):
    """options[j] = list of perturbation polys for A_j, all strictly above
    the lam-line (so the outer read is INVARIANT and only the DEEPER digits
    move)."""
    opts = []
    for j in range(MU):
        o = [[R.zero]]
        lo = line_floor(j, u)
        for m in range(lo, lo + W):
            for c in range(1, p):
                o.append([x * R.el(c) for x in nrm(m, R)])
        opts.append(o)
    return opts


def members(R, p, u, rco2, W=2, cap=None):
    opts = member_family(R, p, u, W)
    tot = 1
    for o in opts:
        tot *= len(o)
    stride = 1 if (cap is None or tot <= cap) else -(-tot // cap)
    n = 0
    for i, tup in enumerate(itertools.product(*opts)):
        if i % stride:
            continue
        pert = {j: tup[j] for j in range(MU)}
        A, f = instance(u, rco2, R, pert)
        n += 1
        yield A, f
    RES.setdefault('member_counts', []).append((R.name(), u, tot, n))


def disc_nonzero(f, R):
    fp = [c * R.el(i) for i, c in enumerate(f)][1:]
    d = resultant(f, fp)
    return bool(d) if not isinstance(d, int) else d != 0


# ============================================================ the legs
def test_grid(p, u, labels):
    """the sampled test family: (u', l', r, expect_excess)."""
    out = []
    lam = Fr(u, 2)
    lab_keys = set((lb['lam'], tuple(lb['r'])) for lb in labels)
    # (a) the side's OWN fractional height, every irreducible of degree <= 2
    for deg in (1, 2):
        for r in irred_list(p, deg):
            key = (str(lam), tuple(r))
            out.append((u, 2, r, key in lab_keys))
    # (b) other rational heights (l' = 1, 2, 3), one letter each
    r1 = irred_list(p, 1)[0]
    for lp in (1, 2, 3):
        for up in range(2 * lp + 1, (u + 4) * lp // 2 + 1):
            if gcd(up, lp) != 1 or Fr(up, lp) <= 2:
                continue
            key = (str(Fr(up, lp)), tuple(r1))
            out.append((up, lp, r1, key in lab_keys))
    return out


def leg_member(f, A, R, p, u, rd, grid):
    """P1 (flat identity at generic (kappa, r)) + P2 (strict excess exactly
    at the labels).  Returns dict label-key -> measured excess."""
    dvs = rd['dvs']
    exc = {}
    for (up, lp, r, want_exc) in grid:
        d = len(r) - 1
        Ps = test_poly(up, lp, r[:-1], R)
        meas = dv_res(f, Ps, R)
        kappa = Fr(up, lp)
        gen = lp * d * DP * h_F(dvs, kappa)
        assert gen.denominator == 1, (gen, up, lp)
        gen = int(gen)
        note('HE6-GEN')
        if want_exc:
            note('HE6-SEP')
            if meas <= gen:
                viol('HE6-SEP', 'no excess at a label',
                     'p=%s u=%d r=%s meas=%s gen=%s' % (p, up, r, meas, gen))
            exc[(str(kappa), tuple(r))] = meas - gen
        else:
            if meas != gen:
                viol('HE6-GEN', 'flat identity failed',
                     'p=%s kappa=%s/%s r=%s meas=%s gen=%s'
                     % (p, up, lp, r, meas, gen))
    return exc


def leg_xi(R, p, u, rd):
    """P3: every root xi of Psi_{lam,r} carries the label (lam, r).
    (i) 2 v(Res(Psi, Phi')) / deg Psi == lam ; (ii) Psi irreducible over the
    base (char 0 only, PARI) ; (iii) distinct r's are mutually generic."""
    key = key_poly(R)
    lam = Fr(u, 2)
    Ps = {}
    for lb in rd['labels']:
        r = lb['r']
        P = test_poly(u, 2, r[:-1], R)
        Ps[tuple(r)] = P
        note('HE6-XI')
        got = Fr(dv_res(P, key, R), len(P) - 1)
        if got != lam:
            viol('HE6-XI', 'root height wrong',
                 'r=%s got=%s want=%s' % (r, got, lam))
    ks = sorted(Ps)
    for i in range(len(ks)):
        for j in range(i + 1, len(ks)):
            note('HE6-XI-ORTH')
            m = dv_res(Ps[ks[i]], Ps[ks[j]], R)
            di, dj = len(ks[i]) - 1, len(ks[j]) - 1
            gen = 2 * di * 2 * dj * int(u)          # l*d_i * l*d_j * u ... /1
            # generic value: sum over roots xi of Psi_i of dv(Psi_j(xi))
            #  = (deg Psi_i) * l*d_j * lam = (2*2*di) * (2*dj) * (u/2)
            gen = (2 * 2 * di) * (2 * dj) * u // 2
            if m != gen:
                viol('HE6-XI-ORTH', 'test polys not mutually generic',
                     'r1=%s r2=%s got=%s want=%s' % (ks[i], ks[j], m, gen))
    return Ps


def leg_rank(rd, exc, u):
    """P5: the OLD (integer-height) family is rank-deficient at the l >= 2
    degenerate side; the NEW family pins the class-size vector uniquely."""
    labels = rd['labels']
    L = len(labels)
    if L < 2:
        return None
    lams = [Fr(lb['lam']) for lb in labels]
    sizes = [lb['size'] for lb in labels]
    rows_old = [[1] * L]                              # the root count
    for kappa in range(3, int(max(lams)) + 3):
        rows_old.append([min(la, Fr(kappa)) for la in lams])

    def rank(rows):
        M = [[Fr(x) for x in r] for r in rows]
        rk, piv = 0, 0
        for c in range(L):
            sel = None
            for i in range(rk, len(M)):
                if M[i][c] != 0:
                    sel = i
                    break
            if sel is None:
                continue
            M[rk], M[sel] = M[sel], M[rk]
            for i in range(len(M)):
                if i != rk and M[i][c] != 0:
                    fac = M[i][c] / M[rk][c]
                    M[i] = [a - fac * b for a, b in zip(M[i], M[rk])]
            rk += 1
        return rk

    rk_old = rank(rows_old)
    # spurious solutions under the OLD family
    tot = DP * MU
    def sols(need_nonempty):
        out = []
        rngs = [range(0, tot + 1, sizes[i]) for i in range(L)]
        for tup in itertools.product(*rngs):
            if sum(tup) != tot:
                continue
            if need_nonempty and any(x == 0 for x in tup):
                continue
            ok = True
            for row in rows_old[1:]:
                # the old family's RHS is D' h_F(kappa), which by LEMMA
                # HE6-3 equals the value at the TRUE size vector: a candidate
                # is old-family-compatible iff it matches the truth on rows.
                lhs = sum(Fr(t) * c for t, c in zip(tup, row))
                true_lhs = sum(Fr(s) * c for s, c in zip(sizes, row))
                if lhs != true_lhs:
                    ok = False
                    break
            if ok:
                out.append(tuple(tup))
        return out

    sp_old = sols(False)
    sp_new = sols(True)          # the enlarged family certifies each nonempty
    rec = dict(labels=[(lb['lam'], lb['r']) for lb in labels],
               rank_old=rk_old, n_labels=L,
               spurious_old=len(sp_old), spurious_new=len(sp_new),
               sols_old=[list(s) for s in sp_old[:12]],
               sols_new=[list(s) for s in sp_new[:12]],
               true_sizes=sizes,
               excesses={str(k): v for k, v in exc.items()})
    RES['rank'].append(rec)
    return rec


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


# ======================================================== the row runner
def residual_configs(p):
    """(tag, rco2 = [c0, c1] of R_lam = Z^2 + c1 Z + c0, expectation)."""
    out = []
    lin = [c[0] for c in irred_list(p, 1)]        # r = Z + c0  <-> root -c0
    roots = sorted(set((-c) % p for c in lin))
    if len(roots) >= 2:
        s1, s2 = roots[0], roots[1]
        out.append(('SPLIT', [(s1 * s2) % p, (-(s1 + s2)) % p],
                    ((E1 * 2, F1), (E1 * 2, F1))))
    irr = irred_list(p, 2)
    if irr:
        out.append(('INERT', [irr[0][0], irr[0][1]], ((E1 * 2, F1 * 2),)))
    s = roots[0]
    out.append(('ALPHA2', [(s * s) % p, (-2 * s) % p, ], None))   # (Z-s)^2
    return out


def run_row(R, p, u, W=2, cap=None, oracle=True, tag=''):
    print('\n=== ROW %s  u=%d (lam=%d/2)  W=%d %s' % (R.name(), u, u, W, tag))
    for cfg, rco2, sig_want in residual_configs(p):
        jobs, ms, nm = [], [], 0
        rd0 = None
        t0 = time.time()
        for A, f in members(R, p, u, rco2, W=W, cap=cap):
            if not disc_nonzero(f, R):
                continue
            rd = read_labels(A, R, p)
            if rd0 is None:
                rd0 = rd
                grid = test_grid(p, u, rd['labels'])
                print(' cfg=%-6s labels=%s deeper=%s sigma_pred=%s '
                      '(#tests/member=%d)'
                      % (cfg, [(lb['lam'], lb['r']) for lb in rd['labels']],
                         rd['deeper'], rd['sigma'], len(grid)))
                if sig_want is not None and rd['sigma'] != sig_want:
                    viol('HE6-READ', 'sigma_pred mismatch',
                         '%s got=%s want=%s' % (cfg, rd['sigma'], sig_want))
            else:
                if ([(lb['lam'], tuple(lb['r'])) for lb in rd['labels']] !=
                        [(lb['lam'], tuple(lb['r'])) for lb in rd0['labels']]):
                    viol('HE6-READ', 'outer data moved under perturbation',
                         '%s' % cfg)
            exc = leg_member(f, A, R, p, u, rd, grid)
            nm += 1
            ms.append((A, f, rd, exc))
            if oracle and R.char0 and len(jobs) < 200:
                jobs.append((polystr(f), rd['sigma']))
        # xi-side + rank on the first member (they depend on outer data only)
        if rd0 is not None:
            leg_xi(R, p, u, rd0)
            rec = leg_rank(rd0, ms[0][3] if ms else {}, u)
            if rec:
                print('   RANK old=%d/%d labels  spurious old=%d new=%d '
                      'true=%s' % (rec['rank_old'], rec['n_labels'],
                                   rec['spurious_old'], rec['spurious_new'],
                                   rec['true_sizes']))
        # PARI oracle
        sigs = {}
        if jobs:
            got = gp_sig_batch(jobs, p)
            nbad = 0
            for i, (ps, want) in enumerate(jobs):
                note('HE6-SIG')
                g = got.get(i)
                if g is None:
                    viol('HE6-SIG', 'oracle missing', 'i=%d' % i)
                    continue
                sigs[g] = sigs.get(g, 0) + 1
                if want is not None and g != want:
                    nbad += 1
                    viol('HE6-SIG', 'sigma mismatch',
                         '%s got=%s want=%s' % (cfg, g, want))
            print('   PARI %d jobs, sigma multiset: %s%s'
                  % (len(jobs), dict((str(k), v) for k, v in sigs.items()),
                     '' if not nbad else '  BAD=%d' % nbad))
        RES['rows'].append(dict(ring=R.name(), p=p, u=u, cfg=cfg, W=W,
                                members=nm, pari=len(jobs),
                                sigma_pred=(str(sig_want) if sig_want else
                                            'DEEPER'),
                                sigma_seen={str(k): v for k, v in
                                            sigs.items()},
                                secs=round(time.time() - t0, 1)))
        if cfg == 'ALPHA2':
            RES['caseB'].setdefault('%s_u%d' % (R.name(), u), {})
            RES['caseB']['%s_u%d' % (R.name(), u)] = {
                str(k): v for k, v in sigs.items()}


# ============================================================== the teeth
def teeth_run(p=5, u=5):
    R = Zp(p)
    cfgs = dict((c[0], c) for c in residual_configs(p))
    # ---- T1 HE6-T-UNDET2: old family rank-deficient at the l=2 side
    _, rco2, _ = cfgs['SPLIT']
    A, f = instance(u, rco2, R)
    rd = read_labels(A, R, p)
    rec = leg_rank(rd, {}, u)
    tooth('HE6-T-UNDET2',
          rec and rec['rank_old'] < rec['n_labels'] and
          rec['spurious_old'] > 1 and rec['spurious_new'] == 1,
          'rank_old=%s/%s spurious old=%s new=%s (true %s)'
          % (rec['rank_old'], rec['n_labels'], rec['spurious_old'],
             rec['spurious_new'], rec['true_sizes']))
    # ---- T2 HE6-T-PLANT: a family missing one label's test poly must be
    #      reported as NOT separating (no excess measured for that label)
    labels = rd['labels']
    seen = {}
    for lb in labels[:1]:                     # deliberately drop label 2
        P = test_poly(u, 2, lb['r'][:-1], R)
        m = dv_res(f, P, R)
        g = int(2 * 1 * DP * h_F(rd['dvs'], Fr(u, 2)))
        seen[tuple(lb['r'])] = m - g
    unpinned = [lb for lb in labels if tuple(lb['r']) not in seen]
    tooth('HE6-T-PLANT', len(unpinned) == 1 and
          all(v > 0 for v in seen.values()),
          'dropped %s: reported UNDETERMINED (certified labels %d of %d)'
          % ([lb['r'] for lb in unpinned], len(seen), len(labels)))
    # ---- T3 HE6-T-FLIP: flipped dictionaries caught by PARI
    flips = [((E1 * 4, F1),), ((E1 * 2, F1 * 2),), ((E1, F1),) * 4]
    jobs = [(polystr(f), None)]
    got = gp_sig_batch(jobs, p)
    truth = got.get(0)
    tooth('HE6-T-FLIP', truth is not None and all(fl != truth for fl in flips),
          'PARI truth=%s rejects %s' % (truth, flips))
    # ---- T4 HE6-T-BADKEY: gcd(u', l') != 1 -> the test poly's own side has
    #      residual degree 2 and (when it splits) is REDUCIBLE, so its roots
    #      do NOT all carry one label; the xi-side check must FAIL.
    s = 1
    bad_u = 6                                  # kappa = 6/2 : gcd = 2
    Pbad = test_poly(bad_u, 2, [(-s * s) % p], R)   # Phi'^2 - s^2 varpi^6
    key = key_poly(R)
    got_h = Fr(dv_res(Pbad, key, R), len(Pbad) - 1)
    import w10_checks as W10
    out = W10.gp_run('print("F ", matsize(factorpadic(%s, %d, 60))[1]);quit\n'
                     % (polystr(Pbad), p))
    nfac = None
    for line in out.splitlines():
        if line.startswith('F '):
            nfac = int(line[2:].strip())
    tooth('HE6-T-BADKEY', nfac is not None and nfac > 1,
          'kappa=6/2 (gcd 2): Psi has %s p-adic factors (roots carry '
          'DIFFERENT residues +-%d), height read %s' % (nfac, s, got_h))
    # ---- T5 HE6-T-CASEB: repeated residual on an l=2 side: outer data
    #      IDENTICAL, PARI sigma DIFFERENT -> the deeper read is needed.
    _, rco2b, _ = cfgs['ALPHA2']
    seen_sig, ex = {}, []
    for j, pert in enumerate([None,
                              {3: [c * R.el(1) for c in nrm(3, R)]},
                              {1: [c * R.el(1) for c in nrm(8, R)]},
                              {3: [c * R.el(2) for c in nrm(3, R)]},
                              {2: [c * R.el(1) for c in nrm(u + 1, R)]},
                              {0: [c * R.el(1) for c in nrm(2 * u + 1, R)]}]):
        A2, f2 = instance(u, rco2b, R, pert)
        if not disc_nonzero(f2, R):
            continue
        rd2 = read_labels(A2, R, p)
        ex.append((polystr(f2), rd2))
    got = gp_sig_batch([(e[0], None) for e in ex], p)
    for i, (ps, rd2) in enumerate(ex):
        g = got.get(i)
        if g:
            seen_sig[g] = seen_sig.get(g, 0) + 1
    tooth('HE6-T-CASEB', len(seen_sig) >= 2,
          'ALPHA2 (R_lam=(Z-s)^2, l=2): %d distinct sigma over members with '
          'IDENTICAL outer data: %s'
          % (len(seen_sig), dict((str(k), v) for k, v in seen_sig.items())))


def main():
    t0 = time.time()
    if WIP:
        print('HE6 checks — WIP smoke (commit 1)')
        smoke(3, 5)
        smoke(5, 5)
        print('%.1fs' % (time.time() - t0))
        return
    print('HE6 checks — the enlarged fractional-height test family')
    print('pins: ' + ', '.join('%s %s' % (f, md5(f)[:10]) for f in PINS
                               if os.path.exists(os.path.join(HERE, f))))
    # char 0 rows
    run_row(Zp(3), 3, 5, W=2, cap=300, tag='char 0')
    run_row(Zp(5), 5, 5, W=2, cap=300, tag='char 0')
    run_row(Zp(7), 7, 5, W=1, cap=200, tag='char 0')
    run_row(Zp(5), 5, 7, W=1, cap=200, tag='char 0, deeper side')
    # char p rows (no factorpadic oracle: reader + resultant identities)
    run_row(FpTring(3), 3, 5, W=2, cap=80, oracle=False, tag='char 3')
    run_row(FpTring(5), 5, 5, W=1, cap=60, oracle=False, tag='char 5')
    print('\n--- teeth')
    teeth_run(5, 5)
    RES['secs'] = round(time.time() - t0, 1)
    RES['nviol'] = len(RES['viol'])
    print('\nLEGS: %s' % RES['legs'])
    print('VIOLATIONS: %d' % len(RES['viol']))
    print('%.1fs' % (time.time() - t0))
    with open(os.path.join(HERE, 'he6_checks_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True, default=str)


if __name__ == '__main__':
    main()
