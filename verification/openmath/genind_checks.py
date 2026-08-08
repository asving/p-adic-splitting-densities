#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENIND battery — the general two-species induction, machine leg.
Companion to lean/notes/openmath/GENIND_PROOF_2026-08-08.md (two-commit
seal; verdict appended at commit 2 FROM the committed artifacts).

WHAT IS CHECKED (families; evidence class per family):

  GT-PIN      [NONE] md5 pins of the consumed frozen suppliers.
  GT-PART     [SAME] the five-species partition (DRAIN/DEC/ALPHA/BETA/CS)
              tallies sum to q^(m(N-1)) per center on every row.
  GT-DEPTH0   [SAME, both directions] depth-0 closed-form laws:
              DRAIN0 = q^((m-1)(N-1));
              ALPHA(k) = (q-1) q^(m(N-1) - k m(m+1)/2), exactly the
                visible k (absent keys = predictions too);
              n=4 CS: E4(h) = (q-1) q^(4N-5h-3)   [W-12 S2.5's QRT-(1^2)]
                      F4(k) = (q(q-1)/2) q^(4N-10k-4);
              n=5 CS: V1E2(h) = (q-1) q^(4N-5h-3) (q^(N-(5h+1)/2) - 1)
                      V4E2(v4,h) = (q-1)^2 q^(5N-5v4-5h-4);
              n=4 FULL-side beta genres (k with 4k <= N-1):
                      B22(k)  = ((q-1)(q-2)/2)      q^(4N-10k-4)
                      B31(k)  = (q-1)(q-2)          q^(4N-10k-4)
                      B211(k) = ((q-1)(q-2)(q-3)/2) q^(4N-10k-4)
                      B2Q(k)  = (q-1)(q(q-1)/2)     q^(4N-10k-4).
              An observed key of a predicted class off its law, or a
              predicted-visible key absent, or a CS key outside the S5.3
              genre grammar: violation.
  GT-BDRAIN   [SAME] the n=4 FULL-side beta DRAIN composition in closed
              form (the beta-transport consuming the PROVED n<=3 laws):
              with M = N-4k, R(M) = q^(M-1) + floor((M-1)/2)(q-1)q^(M-2)
              (HEX3 H-4 / W-11) and u3pc(M) = THEOREM HEX3.A per center:
                drained B22  = c q^(6k) [q^(4(M-1)) - (q^(2(M-1))-R(M))^2]
                drained B31  = c q^(6k) q^(M-1) u3pc(M)
                drained B211 = c q^(6k) q^(2(M-1)) R(M)
                drained B2Q  = c q^(6k) q^(2(M-1)) R(M).
  GT-ALPHA    [SAME, pointwise] every depth-0 ALPHA(k) member: the scaled
              state sigma_k(X) re-read at window N-mk gives the SAME
              verdict (and sigma when DEC); fibers over (letter, scaled
              state) all of size exactly q^(k m(m-1)/2); scaled states
              onto the full window-(N-mk) state space.
  GT-BETA     [SAME, pointwise] every depth-0 BETA member: each cluster
              child extracted by the c=k scale + monic Hensel lift;
              reconstruction A*B == ghat coefficient-exact mod pi^(W-D);
              child re-read composes to the parent verdict.
  GT-RECUR    [SAME] the drainage first-step recursion: measured drain
              inside the ALPHA(k) locus == (q-1) q^(k m(m-1)/2) *
              u_m(N-mk) with u_m at the reduced window measured by full
              enumeration (the alpha-transport of drainage, exact).
  GT-BRACKETID [SYM] the bracket lemma GENIND-2(b): sum over
              compositions (k_1..k_r) of mu of prod (q-1) q^(c(m) k_i)
              == (q-1) q^((c(m)+1) mu - 1), integer-exact, for
              m in {2,3,4,5}, mu in {1,2,3}, q in {2,3}.
  GT-CRIT     [SAME] the composite-stage criterion: ZERO CS events on the
              n=3 control rows (any depth); on n=4/5 rows every CS event
              (any depth, any frame) satisfies mu >= 2, e*gamma >= 2,
              4 <= e*mu*gamma <= frame multiplicity; depth-0 CS keys lie
              in the S5.3 genre grammar.
  GT-N3TIE    [NONE] the n=3 control depth-0 first-step species table
              (locus, drained) == HEX3 S5.1 closed forms AND == the
              committed hex3_checks_results.json species tables.
  GT-CONS     [SAME] constructed targeted loci (full sweeps cannot reach
              them): n=4 ALPHA(2) at (Zp,2,9) (4096 members); n=5
              ALPHA(1) at (Zp,2,6)+(Fqt,2,6) (1024 each) and (Zp,3,6)
              (118,098); n=4 BFULL(1) types at (Zp,3,6) (M=2, the
              nontrivial drain composition). Each member must classify to
              its species, counts match the laws, GT-ALPHA/GT-BDRAIN
              logic re-checked on the constructed locus.
  GT-ORACLE   [IND] PARI (cypari2): for every DEC member of the oracle
              rows, disc != 0 and the sigma multiset {(e,f)} from
              nfinit/idealprimedec over the Q-factors of the canonical
              integer lift == the reader's sigma.

TEETH (preregistered exact fire counts; off-count => RED):
  GT-T-ALPHA   alpha-law exponent m(m+1)/2 -> m(m+1)/2 - 1: must mismatch
               on every row/leg with a realized ALPHA key.
  GT-T-CS      E4 law 5h -> 5h-1: must mismatch on every n=4 row.
  GT-T-CRIT    "n=5 is composite-free": must be refuted on every n=5 row
               with a realized CS key (N >= 4 rows).
  GT-T-BRACKET bracket exponent c+1 -> c: must fail all 24 GT-BRACKETID
               identities.

ROSTER (full sweeps, per-center cluster stratum, states = q^{m(N-1)},
both ring kinds Zp / Fqt at prime q — prime-power q carried by the
supplier batteries, GENIND-BOX-3):
  n=3 control: (2,5), (3,4)            x {Zp, Fqt}
  n=4:  (2,4) (2,5) (2,6) (3,3) (3,4) (5,3)   x {Zp, Fqt}
  n=5:  (2,4) (2,5) (3,3)              x {Zp, Fqt}
  constructed legs + oracle rows as listed above.

PRE-SEAL SMOKE DISCLOSED (full record; also in the note S10): --smoke
covers (Zp,2,5) n=3, (Zp,2,4) n=4, (Fqt,3,3) n=4, (Zp,2,4) n=5, the
bracket identities, the n=5 alpha constructed leg; no oracle, no
n3-tie. Smoke run 1: RED, 1 violation — the predictor listed
('V4E2',1,1) at (Zp,2,4,n5) but the hull convexity at the (4,v4)
vertex forces h >= 2 v4 + 1 (the traced member reads as a single
e=5 decided side): a MATH-side correction, the S5.3 parameter set
gained the vertex condition (V4E2 first visible at N=8, hence
PREDICTED-ABSENT on this roster). Smoke run 2: GREEN, 736 checks / 0.
Three further disclosed pre-seal probes (code paths smoke misses):
n3_tie ran clean (0 violations); oracle_row(2,4,n=4) ran clean
(3,264 decided scored, 0 bad) — so the full run's oracle leg on that
row is a REPEAT, disclosed; cost probe run_row(Fqt,2,6,n=4) 13.6 s,
0 violations, verdicts 939520/42496/66560. No full battery run before
the seal.

Exact integer arithmetic; deterministic; cypari2 only in GT-ORACLE.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
# user site-packages (cypari2 2.2.0 lives there; the system python 3.10
# on this box does not enable the user site)
sys.path.append(os.path.expanduser(
    '~/.local/lib/python3.10/site-packages'))

PINS = {
    'w11_checks.py':             '500aae152bb5b5e9df3712904a6d73a6',
    'w12_checks.py':             '7dc040d94fbbb1e8d20ac817b665d418',
    'hex3_checks.py':            '83faf7edb554811cd657691d7ea256cc',
    'hmenu3_checks.py':          '65326f85c218087261f434f8b8cc8dda',
    'hex3_checks_results.json':  'ce6f41162a22b0bd66a641e98cb4d56e',
}

FAMILIES = ['GT-PIN', 'GT-PART', 'GT-DEPTH0', 'GT-BDRAIN', 'GT-ALPHA',
            'GT-BETA', 'GT-RECUR', 'GT-BRACKETID', 'GT-CRIT',
            'GT-N3TIE', 'GT-CONS', 'GT-ORACLE']
TEETH = ['GT-T-ALPHA', 'GT-T-CS', 'GT-T-CRIT', 'GT-T-BRACKET']
TEETH_EXPECT = {'GT-T-ALPHA': 12, 'GT-T-CS': 12, 'GT-T-CRIT': 4,
                'GT-T-BRACKET': 24}

VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
LOG = []


def say(msg):
    print(msg, flush=True)
    LOG.append(msg)


def note(fam, n=1):
    NCHK[fam] += n


def viol(fam, tag, detail):
    VIOL[fam].append((tag, str(detail)[:300]))
    say('  VIOLATION %s %s %s' % (fam, tag, str(detail)[:300]))


# ---------------------------------------------------------------- rings
class Zp(object):
    kind = 'Zp'

    def __init__(self, p, N):
        self.p, self.N, self.M = p, N, p ** N

    def zero(self):
        return 0

    def one(self):
        return 1

    def add(self, a, b):
        return (a + b) % self.M

    def sub(self, a, b):
        return (a - b) % self.M

    def mul(self, a, b):
        return (a * b) % self.M

    def val(self, a, W):
        a %= self.M
        if a == 0:
            return None
        v = 0
        while a % self.p == 0:
            a //= self.p
            v += 1
        return v if v < W else None

    def res(self, a, h):
        return ((a % self.M) // self.p ** h) % self.p

    def lift(self, c):
        return c % self.p

    def rint(self, m):
        return m % self.M

    def pipw(self, t):
        return self.p ** t

    def divpi(self, a, t):
        a %= self.M
        assert a % (self.p ** t) == 0, 'inexact division'
        return a // self.p ** t

    def eqmod(self, a, b, W):
        return (a - b) % (self.p ** W) == 0


class Fqt(object):
    kind = 'Fqt'

    def __init__(self, p, N):
        self.p, self.N = p, N

    def zero(self):
        return (0,) * self.N

    def one(self):
        return (1,) + (0,) * (self.N - 1)

    def add(self, a, b):
        p = self.p
        return tuple((x + y) % p for x, y in zip(a, b))

    def sub(self, a, b):
        p = self.p
        return tuple((x - y) % p for x, y in zip(a, b))

    def mul(self, a, b):
        p, N = self.p, self.N
        out = [0] * N
        for i, x in enumerate(a):
            if x:
                for j in range(N - i):
                    y = b[j]
                    if y:
                        out[i + j] = (out[i + j] + x * y) % p
        return tuple(out)

    def val(self, a, W):
        for i in range(min(W, self.N)):
            if a[i]:
                return i
        return None

    def res(self, a, h):
        return a[h] if h < self.N else 0

    def lift(self, c):
        return (c % self.p,) + (0,) * (self.N - 1)

    def rint(self, m):
        return (m % self.p,) + (0,) * (self.N - 1)

    def pipw(self, t):
        return tuple(1 if i == t else 0 for i in range(self.N))

    def divpi(self, a, t):
        assert all(a[i] == 0 for i in range(min(t, self.N))), 'inexact'
        return a[t:] + (0,) * t

    def eqmod(self, a, b, W):
        return a[:W] == b[:W]


# ------------------------------------------------- F_p polynomial helpers
def kp_trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def kp_mul(f, g, p):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        if x:
            for j, y in enumerate(g):
                if y:
                    out[i + j] = (out[i + j] + x * y) % p
    return kp_trim(out)


def kp_divmod(f, g, p):
    """divide f by g (g monic-normalizable) over F_p; returns (q, r)."""
    f = list(f)
    dg = len(g) - 1
    inv = pow(g[-1], p - 2, p)
    q = [0] * max(0, len(f) - dg)
    while len(f) - 1 >= dg and kp_trim(list(f)):
        f = kp_trim(f)
        if len(f) - 1 < dg:
            break
        c = (f[-1] * inv) % p
        s = len(f) - 1 - dg
        q[s] = c
        for i in range(dg + 1):
            f[s + i] = (f[s + i] - c * g[i]) % p
    return kp_trim(q), kp_trim(f)


def kp_gcd(f, g, p):
    f, g = kp_trim(list(f)), kp_trim(list(g))
    while g:
        f, g = g, kp_divmod(f, g, p)[1]
    if f:
        inv = pow(f[-1], p - 2, p)
        f = [(c * inv) % p for c in f]
    return f


def kp_deriv(f, p):
    return kp_trim([(i * f[i]) % p for i in range(1, len(f))])


def kp_bezout(a, b, p):
    """u*a + v*b = g (monic gcd); returns (u, v, g)."""
    r0, r1 = kp_trim(list(a)), kp_trim(list(b))
    u0, u1 = [1], []
    v0, v1 = [], [1]
    while r1:
        q, r = kp_divmod(r0, r1, p)
        r0, r1 = r1, r
        u0, u1 = u1, kp_trim([(x - y) % p for x, y in
                              itertools.zip_longest(u0, kp_mul(q, u1, p),
                                                    fillvalue=0)])
        v0, v1 = v1, kp_trim([(x - y) % p for x, y in
                              itertools.zip_longest(v0, kp_mul(q, v1, p),
                                                    fillvalue=0)])
    if r0:
        inv = pow(r0[-1], p - 2, p)
        r0 = [(c * inv) % p for c in r0]
        u0 = [(c * inv) % p for c in u0]
        v0 = [(c * inv) % p for c in v0]
    return u0, v0, r0


def kp_roots_mult(f, p):
    """[(z, mult)] over F_p plus the rootless cofactor."""
    out = []
    poly = kp_trim(list(f))
    for z in range(p):
        m = 0
        while len(poly) > 1:
            # synthetic division by (y - z)
            n = len(poly) - 1
            quot = [0] * n
            acc = poly[n]
            for i in range(n - 1, -1, -1):
                quot[i] = acc
                acc = (poly[i] + acc * z) % p
            if acc == 0:
                m += 1
                poly = quot
            else:
                break
        if m:
            out.append((z, m))
    return out, poly


def kp_factor_rootless(C, p):
    """factor a rootless poly of degree <= 5 over F_p into irreducible
    degrees; returns list of degrees (with multiplicity) — separable
    input assumed."""
    C = kp_trim(list(C))
    degs = []
    # try monic rootless quadratics
    changed = True
    while changed and len(C) - 1 >= 4:
        changed = False
        for a in range(p):
            for b in range(p):
                psi = [b, a, 1]
                if any(((z * z + a * z + b) % p) == 0 for z in range(p)):
                    continue
                q, r = kp_divmod(C, psi, p)
                if not r:
                    degs.append(2)
                    C = q
                    changed = True
                    break
            if changed:
                break
    if len(C) - 1 > 0:
        degs.append(len(C) - 1)
    return degs


# ------------------------------------------------------------ the reader
class CSExit(object):
    __slots__ = ('genres',)

    def __init__(self, genres):
        self.genres = genres


def hull_lower(pts):
    h = []
    for pt in pts:
        while len(h) >= 2:
            (x1, y1), (x2, y2) = h[-2], h[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                h.pop()
            else:
                break
        h.append(pt)
    return h


def poly_shift(R, coeffs, s):
    """Taylor shift: coefficients of f(x+s); coeffs = [c0..cm] full."""
    c = list(coeffs)
    m = len(c) - 1
    for i in range(m):
        for j in range(m - 1, i - 1, -1):
            c[j] = R.add(c[j], R.mul(c[j + 1], s))
    return c


def poly_mul_ring(R, f, g):
    out = [R.zero()] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            out[i + j] = R.add(out[i + j], R.mul(x, y))
    return out


def hensel_monic_factor(R, W, g, Abar, p):
    """g: ring coeff list (deg n, leading may be non-unit); Abar: monic
    F_p poly (list of ints) with Abar | gbar and gcd(Abar, gbar/Abar)=1.
    Returns (A, B): g == A*B mod pi^W with A monic lifting Abar."""
    n = len(g) - 1
    gbar = [R.res(c, 0) for c in g]
    Bbar, rem = kp_divmod(kp_trim(list(gbar)), Abar, p)
    assert not rem, 'Abar does not divide gbar'
    U, V, one = kp_bezout(Abar, Bbar, p)
    assert one == [1], 'factors not coprime'
    A = [R.lift(c) for c in Abar]
    B = [R.lift(c) for c in Bbar] + \
        [R.zero()] * (n - (len(Abar) - 1) + 1 - len(Bbar))
    for i in range(1, W):
        prod = poly_mul_ring(R, A, B)
        e = [R.sub(g[j] if j < len(g) else R.zero(),
                   prod[j] if j < len(prod) else R.zero())
             for j in range(n + 1)]
        ebar = [R.res(c, i) for c in e]
        ebar = kp_trim(ebar)
        if not ebar:
            continue
        dA = kp_divmod(kp_mul(V, ebar, p), Abar, p)[1]
        num = kp_trim([(x - y) % p for x, y in itertools.zip_longest(
            ebar, kp_mul(Bbar, dA, p), fillvalue=0)])
        dB, r2 = kp_divmod(num, Abar, p)
        assert not r2, 'hensel step remainder'
        pi_i = R.pipw(i)
        for j, c in enumerate(dA):
            if c:
                A[j] = R.add(A[j], R.mul(R.lift(c), pi_i))
        for j, c in enumerate(dB):
            if c and j < len(B):
                B[j] = R.add(B[j], R.mul(R.lift(c), pi_i))
    return A, B


def sides_of(R, W, coeffs, m):
    """polygon sides of the cluster frame; coeffs=[a0..a(m-1)], monic.
    Returns list of (j0,y0,j1,y1,e,h,g,rc) with rc the residual coeff
    ints (F_p), rc[i] at abscissa j0+i*e."""
    pts = []
    for j in range(m):
        v = R.val(coeffs[j], W)
        if v is not None:
            pts.append((j, v))
    pts.append((m, 0))
    hv = hull_lower(pts)
    out = []
    for i in range(len(hv) - 1):
        (j0, y0), (j1, y1) = hv[i], hv[i + 1]
        dx, dy = j1 - j0, y0 - y1
        gg = gcd(dx, dy)
        e, h, g = dx // gg, dy // gg, gg
        rc = []
        for t in range(g + 1):
            j = j0 + t * e
            ht = y0 - t * h
            rc.append(1 if j == m else R.res(coeffs[j], ht))
        out.append((j0, y0, j1, y1, e, h, g, rc))
    return out


def read_cluster(R, W, coeffs, ctx, top_events=None):
    """conservative read of the cluster frame (all v(a_j) >= 1), monic
    degree m = len(coeffs). Returns (verdict, sigma) with verdict in
    {'DEC','DRAIN','CS'}; sigma a sorted tuple of (e,f) or None.
    ctx: dict with 'cs_events' list, 'p'. top_events: if a list, the
    depth-0 event record of THIS frame is appended (species keys)."""
    p = ctx['p']
    m = len(coeffs)
    it = 0
    first = True
    while True:
        it += 1
        assert it <= 6 * W + 12, 'read loop cap'
        if R.val(coeffs[0], W) is None:
            if first and top_events is not None:
                top_events.append(('DRAIN',))
            return 'DRAIN', None
        sides = sides_of(R, W, coeffs, m)
        pieces = []          # decided (e, f) pieces
        children = []        # (mu, k, z, D) cluster children
        cs = []              # CS genre records
        for (j0, y0, j1, y1, e, h, g, rc) in sides:
            roots, cof = kp_roots_mult(rc, p)
            simple_root_count = 0
            for (z, mu) in roots:
                assert z != 0 or j0 > 0, 'zero residual root at vertex'
                if mu == 1:
                    pieces.append((e, 1))
                    simple_root_count += 1
                elif e == 1:
                    children.append((mu, h, z, j0, y0))
                else:
                    cs.append((m, (j0, j1), e, 1, mu, h))
            cofdeg = len(cof) - 1 if cof else 0
            if cofdeg > 0:
                dC = kp_deriv(cof, p)
                if not dC:
                    assert p == 2 and cofdeg == 4, 'p-power cofactor'
                    cs.append((m, (j0, j1), e, 2, 2, h))
                else:
                    G = kp_gcd(cof, dC, p)
                    if len(G) - 1 == 0:
                        for dpi in kp_factor_rootless(cof, p):
                            pieces.append((e, dpi))
                    else:
                        assert len(G) - 1 == 2, 'unexpected gcd degree'
                        q2, r2 = kp_divmod(cof, kp_mul(G, G, p), p)
                        assert not r2, 'psi^2 does not divide'
                        cs.append((m, (j0, j1), e, 2, 2, h))
                        for dpi in kp_factor_rootless(q2, p):
                            pieces.append((e, dpi))
        # classify the event
        is_alpha = (len(sides) == 1 and sides[0][4] == 1 and
                    len(children) == 1 and children[0][0] == m and
                    not pieces and not cs)
        if first and top_events is not None:
            if cs:
                key = cs_genre_key(m, cs, sides)
                top_events.append(('CS', key))
            elif is_alpha:
                top_events.append(('ALPHA', children[0][1]))
            elif children:
                top_events.append(beta_key(m, sides, children, pieces))
            else:
                top_events.append(('DEC',))
        first = False
        if cs:
            for rec in cs:
                ctx['cs_events'].append(rec)
            return 'CS', None
        if not children:
            return 'DEC', tuple(sorted(pieces))
        if is_alpha:
            (mu, k, z, _, _) = children[0]
            s = R.mul(R.lift(z), R.pipw(k))
            full = list(coeffs) + [R.one()]
            full = poly_shift(R, full, s)
            coeffs = full[:m]
            continue
        # beta: extract each child, read, combine
        verdicts = []
        for (mu, k, z, j0, y0) in children:
            child, Wc = extract_child(R, W, coeffs, m, k, z, p)
            v2, s2 = read_cluster(R, Wc, child, ctx)
            verdicts.append((v2, s2))
        if any(v == 'CS' for v, _ in verdicts):
            return 'CS', None
        if any(v == 'DRAIN' for v, _ in verdicts):
            return 'DRAIN', None
        sig = list(pieces)
        for v2, s2 in verdicts:
            sig.extend(list(s2))
        return 'DEC', tuple(sorted(sig))


def cs_genre_key(m, cs, sides):
    rec = cs[0]
    (_, (j0, j1), e, gam, mu, h) = rec
    if m == 4 and (j0, j1) == (0, 4) and e == 2 and gam == 1:
        return ('E4', h)
    if m == 4 and (j0, j1) == (0, 4) and e == 1 and gam == 2:
        return ('F4', h)
    if m == 5 and (j0, j1) == (1, 5) and e == 2 and gam == 1:
        return ('V1E2', h)
    if m == 5 and (j0, j1) == (0, 4) and e == 2 and gam == 1:
        # v4 = the height at abscissa 4 = y1 of that side
        for (a0, b0, a1, b1, ee, hh, gg, rc) in sides:
            if (a0, a1) == (0, 4):
                return ('V4E2', b1, hh)
    if m == 5 and (j0, j1) == (1, 5) and e == 1 and gam == 2:
        return ('V1E1Q', h)
    if m == 5 and (j0, j1) == (0, 4) and e == 1 and gam == 2:
        return ('V4E1Q', h)
    if m == 5 and (j0, j1) == (0, 5) and e == 1 and gam == 2:
        return ('FULLQ', h)
    return ('CSOTHER', m, (j0, j1), e, gam, mu, h)


def beta_key(m, sides, children, pieces):
    parts = tuple(sorted((mu for (mu, k, z, _, _) in children),
                         reverse=True))
    if len(sides) == 1 and sides[0][4] == 1:
        k = sides[0][5]
        roots_sig = parts
        npieces = len(pieces)
        if m == 4:
            if parts == (2, 2):
                return ('B22', k)
            if parts == (3,):
                return ('B31', k)
            if parts == (2,) and npieces == 2 and all(
                    pc == (1, 1) for pc in pieces):
                return ('B211', k)
            if parts == (2,) and npieces == 1 and pieces[0] == (1, 2):
                return ('B2Q', k)
        return ('BFULL', m, k, parts, tuple(sorted(pieces)))
    return ('BOTHER', m, parts, tuple(sorted(pieces)),
            tuple((s[0], s[1], s[2], s[3]) for s in sides))


def extract_child(R, W, coeffs, m, k, z, p):
    """extract the (mu,1) child block at residual root z on the
    integer-slope-k side: c=k scaling with D = min_j (v(a_j)+jk), Hensel
    lift of the monic factor with reduction (y-z)^mu. Returns
    (child_cluster_coeffs [b0..b(mu-1)] recentered at z, W_child)."""
    full = list(coeffs) + [R.one()]
    D = None
    for j in range(m + 1):
        v = R.val(full[j], W) if j < m else 0
        if v is None:
            continue
        t = v + j * k
        if D is None or t < D:
            D = t
    ghat = []
    for j in range(m + 1):
        # ghat_j = a_j * pi^(jk) / pi^D
        if j * k >= D:
            ghat.append(R.mul(full[j], R.pipw(j * k - D)))
        else:
            ghat.append(R.divpi(full[j], D - j * k))
    Wc = W - D
    assert Wc >= 1, 'child window empty'
    gbar = [R.res(c, 0) for c in ghat]
    # multiplicity of z in gbar
    roots, _ = kp_roots_mult(gbar, p)
    mu = dict(((zz, mm) for zz, mm in roots)).get(z)
    assert mu is not None and mu >= 2, 'child root missing'
    Abar = [1]
    for _ in range(mu):
        Abar = kp_mul(Abar, [(-z) % p, 1], p)
    A, B = hensel_monic_factor(R, Wc, ghat, Abar, p)
    # reconstruction check hook (returned via ctx by caller if needed)
    extract_child.last = (ghat, A, B, Wc)
    # recenter A at z (unit shift)
    A = poly_shift(R, A, R.lift(z))
    child = A[:mu]
    return child, Wc


# ------------------------------------------------------- closed-form laws
def R_law(M, q):
    if M <= 1:
        return 1
    return q ** (M - 1) + ((M - 1) // 2) * (q - 1) * q ** (M - 2)


def u3pc(q, N):
    """THEOREM HEX3.A per-center u(q, N)."""
    if N <= 1:
        return 1
    tot = q ** (2 * N - 2)
    k = 1
    while N - 3 * k >= 1:
        tot += (q - 1) * q ** (4 * k - 1) * (q ** (N - 3 * k) - 1) \
            * R_law(N - 3 * k, q)
        k += 1
    return tot


def alpha_law(m, q, N, k, corrupt=False):
    ex = m * (m + 1) // 2 - (1 if corrupt else 0)
    return (q - 1) * q ** (m * (N - 1) - k * ex)


def depth0_pred(m, q, N, alpha_bad=False, e4_bad=False):
    """predicted depth-0 keys -> counts (per center)."""
    pred = {('DRAIN',): q ** ((m - 1) * (N - 1))}
    k = 1
    while m * k <= N - 1:
        pred[('ALPHA', k)] = alpha_law(m, q, N, k, corrupt=alpha_bad)
        k += 1
    if m == 4:
        h = 1
        while 2 * h <= N - 1:
            ex = 5 * h - (1 if e4_bad else 0)
            pred[('CS', ('E4', h))] = (q - 1) * q ** (4 * N - ex - 3)
            h += 2
        k = 1
        while 4 * k <= N - 1:
            pred[('CS', ('F4', k))] = (q * (q - 1) // 2) \
                * q ** (4 * N - 10 * k - 4)
            c22 = (q - 1) * (q - 2) // 2
            c31 = (q - 1) * (q - 2)
            c211 = (q - 1) * (q - 2) * (q - 3) // 2
            c2q = (q - 1) * (q * (q - 1) // 2)
            base = q ** (4 * N - 10 * k - 4)
            for key, c in (('B22', c22), ('B31', c31), ('B211', c211),
                           ('B2Q', c2q)):
                pred[(key, k)] = c * base
            k += 1
    if m == 5:
        h = 1
        while 2 * h <= N - 1:
            head = N - (5 * h + 1) // 2
            cnt = (q - 1) * q ** (4 * N - 5 * h - 3) * \
                (q ** head - 1) if head >= 1 else 0
            pred[('CS', ('V1E2', h))] = cnt
            h += 2
        for v4 in range(1, N):
            for h in range(2 * v4 + 1, N, 2):
                # vertex condition h >= 2 v4 + 1 (hull convexity at the
                # (4, v4) vertex); first visible window N = 8
                if v4 + 2 * h <= N - 1:
                    pred[('CS', ('V4E2', v4, h))] = \
                        (q - 1) ** 2 * q ** (5 * N - 5 * v4 - 5 * h - 4)
    return {kk: vv for kk, vv in pred.items() if vv > 0}


def bdrain_pred(q, N, k):
    """n=4 FULL-side beta drain laws (per center)."""
    M = N - 4 * k
    R_ = R_law(M, q)
    u3 = u3pc(q, M)
    q2 = q ** (2 * (M - 1))
    out = {}
    out[('B22', k)] = ((q - 1) * (q - 2) // 2) * q ** (6 * k) * \
        (q2 * q2 - (q2 - R_) ** 2)
    out[('B31', k)] = (q - 1) * (q - 2) * q ** (6 * k) * \
        q ** (M - 1) * u3
    out[('B211', k)] = ((q - 1) * (q - 2) * (q - 3) // 2) * \
        q ** (6 * k) * q2 * R_
    out[('B2Q', k)] = (q - 1) * (q * (q - 1) // 2) * q ** (6 * k) * \
        q2 * R_
    return {kk: vv for kk, vv in out.items() if vv > 0}


def hex3_species_pred(q, N):
    """HEX3 S5.1 depth-0 (locus, drained) table for the n=3 control."""
    out = {}
    out['B0ZERO'] = (q ** (2 * N - 2), q ** (2 * N - 2))
    for k in range(1, N):
        if 3 * k > N - 1:
            break
        M = N - 3 * k
        out['ALPHA(%d)' % k] = ((q - 1) * q ** (3 * N - 3 - 6 * k),
                                (q - 1) * q ** (3 * k) * u3pc(q, M))
        f11 = (q - 1) * (q - 2)
        if f11:
            out['FULL11SQ(%d)' % k] = (
                f11 * q ** (3 * N - 3 - 6 * k),
                f11 * q ** (3 * k + M - 1) * R_law(M, q))
        for u0 in range(3 * k + 1, N):
            w = u0 - 3 * k
            out['VERT1(%d,%d)' % (u0, k)] = (
                (q - 1) ** 2 * q ** (3 * N - 3 - u0 - 3 * k),
                (q - 1) ** 2 * q ** (3 * k + M - 1 - w) * R_law(M, q))
    for t in range(1, N):
        for u0 in range(3 * t + 1, N):
            if (u0 - t) % 2:
                continue
            j = (u0 - 3 * t) // 2
            if j < 1:
                continue
            M = N - 3 * t
            out['VERT2(%d,%d)' % (u0, t)] = (
                (q - 1) ** 2 * q ** (3 * N - 3 - u0 - t - (u0 + t) // 2),
                (q - 1) ** 2 * q ** (3 * t + M - 1 + j)
                * R_law(M - 2 * j, q))
    return out


# --------------------------------------------------------- state iterators
def iter_states(R, W, m):
    """all per-center cluster states: m coordinates, each pi-divisible
    in O/pi^W."""
    if R.kind == 'Zp':
        p = R.p
        vals = [p * x for x in range(p ** (W - 1))]
        return itertools.product(vals, repeat=m)
    else:
        p = R.p
        digs = list(itertools.product(range(p), repeat=W - 1))
        vals = [(0,) + d + (0,) * (R.N - W) for d in digs]
        return itertools.product(vals, repeat=m)


def state_count(q, W, m):
    return q ** (m * (W - 1))


# ----------------------------------------------------------- row driver
def run_row(kind, q, N, m, do_beta_pointwise=True, results=None):
    t0 = time.time()
    R = Zp(q, N) if kind == 'Zp' else Fqt(q, N)
    ctx = {'p': q, 'cs_events': []}
    tallies = {}
    drains = {}
    verdicts = {'DEC': 0, 'DRAIN': 0, 'CS': 0}
    alpha_fibers = {}
    total = 0
    for st in iter_states(R, N, m):
        total += 1
        coeffs = list(st)
        ev = []
        v, sig = read_cluster(R, N, coeffs, ctx, top_events=ev)
        key = ev[0]
        tallies[key] = tallies.get(key, 0) + 1
        if v == 'DRAIN':
            drains[key] = drains.get(key, 0) + 1
        verdicts[v] += 1
        # pointwise alpha transport
        if key[0] == 'ALPHA':
            k = key[1]
            zk = alpha_check(R, N, list(st), m, k, q, v, sig, ctx)
            if zk is not None:
                alpha_fibers.setdefault(zk, 0)
                alpha_fibers[zk] += 1
        elif do_beta_pointwise and key[0] in ('B22', 'B31', 'B211',
                                              'B2Q', 'BFULL', 'BOTHER'):
            beta_check(R, N, list(st), m, q, v, ctx)
    # families
    note('GT-PART')
    if total != state_count(q, N, m) or sum(tallies.values()) != total:
        viol('GT-PART', '%s,%d,%d,n%d' % (kind, q, N, m),
             (total, sum(tallies.values())))
    # depth-0 laws both directions
    pred = depth0_pred(m, q, N)
    for kk, vv in pred.items():
        note('GT-DEPTH0')
        got = tallies.get(kk if kk[0] != 'CS' else kk, 0)
        if got != vv:
            viol('GT-DEPTH0', '%s,%d,%d,n%d,%s' % (kind, q, N, m, kk),
                 'want %d got %d' % (vv, got))
    for kk in tallies:
        if kk[0] in ('DRAIN', 'ALPHA', 'CS', 'B22', 'B31', 'B211',
                     'B2Q'):
            note('GT-DEPTH0')
            if kk not in pred:
                if kk[0] == 'CS' and kk[1][0] == 'CSOTHER':
                    viol('GT-CRIT', '%s,%d,%d,n%d' % (kind, q, N, m),
                         'unlisted CS genre %s' % (kk,))
                else:
                    viol('GT-DEPTH0', '%s,%d,%d,n%d,%s'
                         % (kind, q, N, m, kk),
                         'unpredicted key, count %d' % tallies[kk])
    # n=4 beta drain closed forms
    if m == 4:
        k = 1
        while 4 * k <= N - 1:
            for kk, vv in bdrain_pred(q, N, k).items():
                note('GT-BDRAIN')
                got = drains.get(kk, 0)
                if got != vv:
                    viol('GT-BDRAIN', '%s,%d,%d,%s' % (kind, q, N, kk),
                         'want %d got %d' % (vv, got))
            k += 1
    # alpha fibers: sizes and onto
    for (k, z, chstate), cnt in alpha_fibers.items():
        note('GT-ALPHA')
        if cnt != q ** (k * m * (m - 1) // 2):
            viol('GT-ALPHA', '%s,%d,%d fiber' % (kind, q, N),
                 ((k, z), cnt))
    for k in set(k for (k, z, ch) in alpha_fibers):
        seen = set(ch for (k2, z, ch) in alpha_fibers if k2 == k)
        note('GT-ALPHA')
        if len(seen) != state_count(q, N - m * k, m):
            viol('GT-ALPHA', '%s,%d,%d onto k=%d' % (kind, q, N, k),
                 (len(seen), state_count(q, N - m * k, m)))
    # drainage recursion (alpha transport of drains, exact)
    k = 1
    while m * k <= N - 1:
        akey = ('ALPHA', k)
        if akey in tallies:
            u_small = measure_u(kind, q, N - m * k, m)
            want = (q - 1) * q ** (k * m * (m - 1) // 2) * u_small
            note('GT-RECUR')
            if drains.get(akey, 0) != want:
                viol('GT-RECUR', '%s,%d,%d,k=%d' % (kind, q, N, k),
                     'want %d got %d' % (want, drains.get(akey, 0)))
        k += 1
    # criterion
    note('GT-CRIT')
    for rec in ctx['cs_events']:
        (fm, span, e, gam, mu, h) = rec
        if not (mu >= 2 and e * gam >= 2 and 4 <= e * mu * gam <= fm):
            viol('GT-CRIT', '%s,%d,%d,n%d' % (kind, q, N, m),
                 'criterion violated %s' % (rec,))
    if m == 3 and ctx['cs_events']:
        viol('GT-CRIT', '%s,%d,%d,n3' % (kind, q, N),
             '%d CS events at n=3' % len(ctx['cs_events']))
    say('  row %s q=%d N=%d n=%d: %d states, %d dec / %d drain / %d cs'
        ' (%.1fs)' % (kind, q, N, m, total, verdicts['DEC'],
                      verdicts['DRAIN'], verdicts['CS'],
                      time.time() - t0))
    if results is not None:
        results['rows']['%s,%d,%d,n%d' % (kind, q, N, m)] = {
            'total': total, 'verdicts': verdicts,
            'depth0': {str(kk): vv for kk, vv in
                       sorted(tallies.items(), key=str)},
            'drains': {str(kk): vv for kk, vv in
                       sorted(drains.items(), key=str)},
            'cs_events': len(ctx['cs_events'])}
    return tallies, drains, verdicts


_U_CACHE = {}


def measure_u(kind, q, W, m):
    """full-enumeration per-center drain count of the (m,1) system at
    window W (small windows only)."""
    keyc = (kind, q, W, m)
    if keyc in _U_CACHE:
        return _U_CACHE[keyc]
    if W <= 1:
        _U_CACHE[keyc] = 1
        return 1
    R = Zp(q, W) if kind == 'Zp' else Fqt(q, W)
    ctx = {'p': q, 'cs_events': []}
    n_drain = 0
    for st in iter_states(R, W, m):
        v, _ = read_cluster(R, W, list(st), ctx)
        if v == 'DRAIN':
            n_drain += 1
    _U_CACHE[keyc] = n_drain
    return n_drain


def alpha_check(R, N, st, m, k, q, v_parent, sig_parent, ctx):
    """pointwise alpha transport; returns fiber key (k, z, childstate)."""
    # find letter z from the residual at the full side
    z = None
    for zz in range(1, q):
        # pin: digit of a0 at height m*k must be (-zz)^m
        if R.res(st[0], m * k) == pow((-zz) % q, m, q):
            # confirm full residual == (y-zz)^m
            ok = True
            for j in range(m):
                cf = _binom_coeff(m, j, zz, q)
                if R.res(st[j], (m - j) * k) != cf:
                    ok = False
                    break
            if ok:
                z = zz
                break
    if z is None:
        viol('GT-ALPHA', 'letter', 'no letter found')
        return None
    s = R.mul(R.lift(z), R.pipw(k))
    full = poly_shift(R, list(st) + [R.one()], s)
    scaled = []
    for j in range(m):
        scaled.append(R.divpi(full[j], (m - j) * k))
    Wc = N - m * k
    ctx2 = {'p': q, 'cs_events': ctx['cs_events']}
    v2, s2 = read_cluster(R, Wc, scaled, ctx2)
    note('GT-ALPHA')
    if v2 != v_parent or (v2 == 'DEC' and s2 != sig_parent):
        viol('GT-ALPHA', 'pointwise', (v_parent, v2, sig_parent, s2))
    chkey = tuple(_trunc(R, c, Wc) for c in scaled)
    return (k, z, chkey)


def _binom_coeff(m, j, z, q):
    from math import comb
    return (comb(m, j) * pow((-z) % q, m - j, q)) % q


def _trunc(R, c, W):
    if R.kind == 'Zp':
        return c % (R.p ** W)
    return c[:W]


def beta_check(R, N, st, m, q, v_parent, ctx):
    """pointwise beta reconstruction: re-run the side scan, extract every
    cluster child, check A*B == ghat mod pi^Wc."""
    sides = sides_of(R, N, st, m)
    for (j0, y0, j1, y1, e, h, g, rc) in sides:
        if e != 1:
            continue
        roots, _ = kp_roots_mult(rc, q)
        for (z, mu) in roots:
            if mu < 2:
                continue
            child, Wc = extract_child(R, N, st, m, h, z, q)
            ghat, A, B, Wc2 = extract_child.last
            prod = poly_mul_ring(R, A, B)
            note('GT-BETA')
            ok = all(R.eqmod(prod[j] if j < len(prod) else R.zero(),
                             ghat[j] if j < len(ghat) else R.zero(), Wc2)
                     for j in range(len(ghat)))
            if not ok:
                viol('GT-BETA', 'reconstruct',
                     ('%s N=%d m=%d' % (R.kind, N, m), z, mu, h))


# ------------------------------------------------- bracket identity leg
def bracket_id(corrupt=False):
    def compositions(mu):
        if mu == 0:
            yield ()
            return
        for k in range(1, mu + 1):
            for rest in compositions(mu - k):
                yield (k,) + rest
    bad = 0
    for m in (2, 3, 4, 5):
        c = m * (m - 1) // 2
        for mu in (1, 2, 3):
            for q in (2, 3):
                lhs = 0
                for comp in compositions(mu):
                    t = 1
                    for k in comp:
                        t *= (q - 1) * q ** (c * k)
                    lhs += t
                ex = (c + 1) if not corrupt else c
                rhs = (q - 1) * q ** (ex * mu - 1)
                if not corrupt:
                    note('GT-BRACKETID')
                    if lhs != rhs:
                        viol('GT-BRACKETID', 'm=%d mu=%d q=%d'
                             % (m, mu, q), (lhs, rhs))
                else:
                    if lhs != rhs:
                        bad += 1
    return bad


# ------------------------------------------------------ constructed legs
def constructed_alpha(kind, q, N, m, k, results):
    """generate the full ALPHA(k) locus at (kind,q,N,m); classify,
    count, pointwise-transport each member."""
    R = Zp(q, N) if kind == 'Zp' else Fqt(q, N)
    ctx = {'p': q, 'cs_events': []}
    from math import comb
    cnt = 0
    mismatch = 0
    for z in range(1, q):
        pins = [(comb(m, j) * pow((-z) % q, m - j, q)) % q
                for j in range(m)]
        free_ranges = []
        for j in range(m):
            lo = (m - j) * k + 1
            free_ranges.append(list(range(lo, N)))
        # iterate free digits coordinatewise
        def gen_coord(j):
            base_h = (m - j) * k
            outs = []
            heights = free_ranges[j]
            for digs in itertools.product(range(q), repeat=len(heights)):
                if kind == 'Zp':
                    val = pins[j] * q ** base_h
                    for hh, dg in zip(heights, digs):
                        val += dg * q ** hh
                    outs.append(val)
                else:
                    a = [0] * R.N
                    a[base_h] = pins[j]
                    for hh, dg in zip(heights, digs):
                        a[hh] = dg
                    outs.append(tuple(a))
            return outs
        coords = [gen_coord(j) for j in range(m)]
        for st in itertools.product(*coords):
            cnt += 1
            ev = []
            v, sig = read_cluster(R, N, list(st), ctx, top_events=ev)
            if ev[0] != ('ALPHA', k):
                mismatch += 1
    want = alpha_law(m, q, N, k)
    note('GT-CONS')
    if cnt != want or mismatch:
        viol('GT-CONS', 'alpha %s,%d,%d,n%d,k%d' % (kind, q, N, m, k),
             'count %d want %d mismatch %d' % (cnt, want, mismatch))
    say('  constructed ALPHA(k=%d) %s q=%d N=%d n=%d: %d members,'
        ' %d misclassified' % (k, kind, q, N, m, cnt, mismatch))
    results['constructed']['alpha,%s,%d,%d,n%d,k%d'
                           % (kind, q, N, m, k)] = cnt
    return cnt


def constructed_bfull(kind, q, N, k, results):
    """generate the n=4 FULL(k) beta loci of types 22/31/2Q at (q,N);
    classify + drain-compose against the closed laws."""
    R = Zp(q, N) if kind == 'Zp' else Fqt(q, N)
    ctx = {'p': q, 'cs_events': []}
    m = 4
    types = {}
    # residual polynomials by type
    for z1 in range(1, q):
        for z2 in range(z1 + 1, q):
            rc = kp_mul(kp_mul([(-z1) % q, 1], [(-z1) % q, 1], q),
                        kp_mul([(-z2) % q, 1], [(-z2) % q, 1], q), q)
            types.setdefault(('B22', k), []).append(rc)
    for z in range(1, q):
        for w in range(1, q):
            if w == z:
                continue
            rc = kp_mul(kp_mul(kp_mul([(-z) % q, 1], [(-z) % q, 1], q),
                               [(-z) % q, 1], q), [(-w) % q, 1], q)
            types.setdefault(('B31', k), []).append(rc)
    for z in range(1, q):
        for a in range(q):
            for b in range(q):
                psi = [b, a, 1]
                if any(((t * t + a * t + b) % q) == 0 for t in range(q)):
                    continue
                rc = kp_mul(kp_mul([(-z) % q, 1], [(-z) % q, 1], q),
                            psi, q)
                types.setdefault(('B2Q', k), []).append(rc)
    for key, rcs in sorted(types.items()):
        cnt = 0
        drained = 0
        mis = 0
        for rc in rcs:
            rc = rc + [0] * (5 - len(rc))
            heights = [(4 - j) * k for j in range(4)]
            free = [list(range(h + 1, N)) for h in heights]
            def gen_coord(j):
                outs = []
                for digs in itertools.product(range(q),
                                              repeat=len(free[j])):
                    if kind == 'Zp':
                        val = rc[j] * q ** heights[j]
                        for hh, dg in zip(free[j], digs):
                            val += dg * q ** hh
                        outs.append(val)
                    else:
                        a = [0] * R.N
                        a[heights[j]] = rc[j]
                        for hh, dg in zip(free[j], digs):
                            a[hh] = dg
                        outs.append(tuple(a))
                return outs
            coords = [gen_coord(j) for j in range(4)]
            for st in itertools.product(*coords):
                cnt += 1
                ev = []
                v, sig = read_cluster(R, N, list(st), ctx,
                                      top_events=ev)
                if ev[0] != key:
                    mis += 1
                if v == 'DRAIN':
                    drained += 1
        want = depth0_pred(4, q, N).get(key, 0)
        wantd = bdrain_pred(q, N, k).get(key, 0)
        note('GT-CONS', 2)
        if cnt != want or mis:
            viol('GT-CONS', 'bfull %s %s' % (key, (kind, q, N)),
                 'count %d want %d mis %d' % (cnt, want, mis))
        if drained != wantd:
            viol('GT-CONS', 'bfull-drain %s %s' % (key, (kind, q, N)),
                 'drained %d want %d' % (drained, wantd))
        say('  constructed %s %s q=%d N=%d: %d members, %d drained'
            ' (want %d/%d)' % (key, kind, q, N, cnt, drained, want,
                               wantd))
        results['constructed']['bfull,%s,%s,%d,%d'
                               % (key, kind, q, N)] = [cnt, drained]


# ------------------------------------------------------------ n=3 tie
def n3_tie(results):
    path = os.path.join(HERE, 'hex3_checks_results.json')
    with open(path) as fh:
        hex3 = json.load(fh)
    for (kind, q, N) in [('Zp', 2, 5), ('Zp', 3, 4)]:
        R = Zp(q, N)
        ctx = {'p': q, 'cs_events': []}
        # my own depth-0 first-step read: species (locus, drained)
        tab = {}
        for st in iter_states(R, N, 3):
            ev = []
            v, sig = read_cluster(R, N, list(st), ctx, top_events=ev)
            key = my_key_to_hex3(ev[0], R, st, N)
            loc, dr = tab.get(key, (0, 0))
            tab[key] = (loc + 1, dr + (1 if v == 'DRAIN' else 0))
        # closed-form leg: HEX3 S5.1 table
        pred = hex3_species_pred(q, N)
        for kk, vv in pred.items():
            note('GT-N3TIE')
            got = tab.get(kk, (0, 0))
            if got != vv:
                viol('GT-N3TIE', '%s@%s,%d,%d' % (kk, kind, q, N),
                     'want %s got %s' % (vv, got))
        # committed-JSON leg
        row = None
        for rv in hex3['rows']:
            if (rv['kind'], rv['q'], rv['N']) == (kind, q, N):
                row = rv
        note('GT-N3TIE')
        if row is None:
            viol('GT-N3TIE', 'row missing', (kind, q, N))
        else:
            mine_u = sum(dr for (_, dr) in tab.values())
            if mine_u != row['u_measured']:
                viol('GT-N3TIE', 'u@%s,%d,%d' % (kind, q, N),
                     'mine %d committed %d' % (mine_u,
                                               row['u_measured']))
            for kk, (loc, dr) in sorted(row['species_tally'].items()):
                note('GT-N3TIE')
                mykey = hexkey_to_mine(kk)
                got = tab.get(mykey, (0, 0))
                if got != (loc, dr):
                    viol('GT-N3TIE', 'json %s@%s,%d,%d'
                         % (kk, kind, q, N),
                         'committed %s mine %s' % ((loc, dr), got))
        results['n3tie']['%s,%d,%d' % (kind, q, N)] = \
            {str(k): v for k, v in sorted(tab.items())}


def hexkey_to_mine(kk):
    """hex3 JSON species key string -> my n3 key string."""
    t = eval(kk)   # committed artifact, trusted tuple literal
    if t == ('B0ZERO',):
        return 'B0ZERO'
    if t == ('DECIDED',):
        return 'DEC'
    if t[0] == 'ALPHA':
        return 'ALPHA(%d)' % t[1]
    if t[0] == 'FULL11SQ':
        return 'FULL11SQ(%d)' % t[1]
    if t[0] == 'VERT1':
        return 'VERT1(%d,%d)' % (t[1], t[2])
    if t[0] == 'VERT2':
        return 'VERT2(%d,%d)' % (t[1], t[2])
    return str(t)


def my_key_to_hex3(ev, R, st, N):
    if ev == ('DRAIN',):
        return 'B0ZERO'
    if ev == ('DEC',):
        return 'DEC'
    if ev[0] == 'ALPHA':
        return 'ALPHA(%d)' % ev[1]
    if ev[0] in ('BFULL', 'BOTHER', 'B22', 'B31', 'B211', 'B2Q'):
        # reconstruct hex3 keys from the polygon
        sides = sides_of(R, N, list(st), 3)
        u0 = R.val(st[0], N)
        if len(sides) == 1:
            return 'FULL11SQ(%d)' % sides[0][5]
        verts = [s_[2] for s_ in sides[:-1]]    # interior vertices
        if 1 in verts:
            k = sides[-1][5]                    # right side slope
            return 'VERT1(%d,%d)' % (u0, k)
        if 2 in verts:
            t = sides[-1][1]                    # height at abscissa 2
            return 'VERT2(%d,%d)' % (u0, t)
    return 'DEC'


# ------------------------------------------------------------- oracle
def oracle_row(q, N, m, results):
    import cypari2
    pari = cypari2.Pari()
    R = Zp(q, N)
    ctx = {'p': q, 'cs_events': []}
    n_dec = 0
    bad = 0
    for st in iter_states(R, N, m):
        v, sig = read_cluster(R, N, list(st), ctx)
        if v != 'DEC':
            continue
        n_dec += 1
        coeffs = [int(c) for c in st] + [1]     # c0..c(m-1), 1
        fx = pari.Polrev(coeffs)
        disc = pari.poldisc(fx)
        note('GT-ORACLE')
        if disc == 0:
            bad += 1
            viol('GT-ORACLE', 'disc0 %d,%d,n%d' % (q, N, m), coeffs)
            continue
        sig_or = []
        fac = pari.factor(fx)
        nfac = int(fac.matsize()[0])
        for i in range(nfac):
            gj = fac[0][i]
            mult = int(fac[1][i])
            assert mult == 1, 'repeated Q-factor on decided member'
            if int(pari.poldegree(gj)) == 1:
                # rational linear factor: complete at q with e=f=1
                sig_or.append((1, 1))
                continue
            nf = pari.nfinit(gj)
            for pr in pari.idealprimedec(nf, q):
                sig_or.append((int(pr[2]), int(pr[3])))
        note('GT-ORACLE')
        if tuple(sorted(sig_or)) != sig:
            bad += 1
            viol('GT-ORACLE', 'sigma %d,%d,n%d' % (q, N, m),
                 (coeffs, sig, tuple(sorted(sig_or))))
    say('  oracle Zp q=%d N=%d n=%d: %d decided scored, %d bad'
        % (q, N, m, n_dec, bad))
    results['oracle']['%d,%d,n%d' % (q, N, m)] = [n_dec, bad]


# --------------------------------------------------------------- teeth
def run_teeth(all_tallies):
    # GT-T-ALPHA: corrupt exponent must mismatch wherever ALPHA realized
    for (rowkey, m, q, N, tallies) in all_tallies:
        pred_bad = depth0_pred(m, q, N, alpha_bad=True)
        fired = False
        for kk, vv in pred_bad.items():
            if kk[0] == 'ALPHA' and tallies.get(kk, 0) != vv:
                fired = True
        if any(kk[0] == 'ALPHA' for kk in tallies):
            if fired:
                FIRE['GT-T-ALPHA'] += 1
            else:
                viol('GT-DEPTH0', 'tooth', 'GT-T-ALPHA silent on %s'
                     % rowkey)
    # constructed alpha legs count as firings too (handled in main)
    # GT-T-CS: corrupt E4 exponent on every n=4 row
    for (rowkey, m, q, N, tallies) in all_tallies:
        if m != 4:
            continue
        pred_bad = depth0_pred(m, q, N, e4_bad=True)
        fired = False
        for kk, vv in pred_bad.items():
            if kk[0] == 'CS' and kk[1][0] == 'E4' \
                    and tallies.get(kk, 0) != vv:
                fired = True
        if fired:
            FIRE['GT-T-CS'] += 1
        else:
            viol('GT-DEPTH0', 'tooth', 'GT-T-CS silent on %s' % rowkey)
    # GT-T-CRIT: "n=5 composite-free" must be refuted where CS realized
    for (rowkey, m, q, N, tallies) in all_tallies:
        if m != 5:
            continue
        has_cs = any(kk[0] == 'CS' for kk in tallies)
        if has_cs:
            FIRE['GT-T-CRIT'] += 1
    # GT-T-BRACKET
    FIRE['GT-T-BRACKET'] = bracket_id(corrupt=True)


# ---------------------------------------------------------------- main
ROWS = {
    3: [(2, 5), (3, 4)],
    4: [(2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (5, 3)],
    5: [(2, 4), (2, 5), (3, 3)],
}
ROWS_SMOKE = {
    3: [(2, 5)],
    4: [(2, 4), (3, 3)],
    5: [(2, 4)],
}


def main(smoke=False):
    t0 = time.time()
    say('GENIND battery %s' % ('SMOKE' if smoke else 'FULL'))
    results = {'rows': {}, 'constructed': {}, 'n3tie': {}, 'oracle': {},
               'smoke': smoke}
    # pins
    for fn, want in PINS.items():
        note('GT-PIN')
        path = os.path.join(HERE, fn)
        got = hashlib.md5(open(path, 'rb').read()).hexdigest()
        if got != want:
            viol('GT-PIN', fn, got)
    # bracket identities
    bracket_id(corrupt=False)
    # sweeps
    rows = ROWS_SMOKE if smoke else ROWS
    all_tallies = []
    for m in sorted(rows):
        for (q, N) in rows[m]:
            for kind in (('Zp', 'Fqt') if not smoke else
                         (('Zp',) if (m, q) != (4, 3) else ('Fqt',))):
                tal, dr, ver = run_row(kind, q, N, m, results=results)
                all_tallies.append(('%s,%d,%d,n%d' % (kind, q, N, m),
                                    m, q, N, tal))
    # char ties: species tallies equal across kinds at shared (q,N,m)
    if not smoke:
        seen = {}
        for (rowkey, m, q, N, tal) in all_tallies:
            kind = rowkey.split(',')[0]
            seen.setdefault((m, q, N), {})[kind] = tal
        for (m, q, N), kinds in sorted(seen.items()):
            if len(kinds) == 2:
                note('GT-PART')
                if kinds['Zp'] != kinds['Fqt']:
                    viol('GT-PART', 'char n%d,%d,%d' % (m, q, N),
                         'Zp vs Fqt depth-0 tallies differ')
    # constructed legs
    if smoke:
        constructed_alpha('Zp', 2, 6, 5, 1, results)
    else:
        constructed_alpha('Zp', 2, 9, 4, 2, results)
        constructed_alpha('Zp', 2, 6, 5, 1, results)
        constructed_alpha('Fqt', 2, 6, 5, 1, results)
        constructed_alpha('Zp', 3, 6, 5, 1, results)
        constructed_bfull('Zp', 3, 6, 1, results)
        FIRE['GT-T-ALPHA'] += 4   # the four constructed alpha legs
        # (each re-checked against the corrupted law below)
        for (kind, q, N, m, k) in [('Zp', 2, 9, 4, 2),
                                   ('Zp', 2, 6, 5, 1),
                                   ('Fqt', 2, 6, 5, 1),
                                   ('Zp', 3, 6, 5, 1)]:
            got = results['constructed']['alpha,%s,%d,%d,n%d,k%d'
                                         % (kind, q, N, m, k)]
            if got == alpha_law(m, q, N, k, corrupt=True):
                FIRE['GT-T-ALPHA'] -= 1
                viol('GT-CONS', 'tooth',
                     'corrupted alpha law matches on %s' % kind)
    # n=3 tie
    if not smoke:
        n3_tie(results)
    # oracle
    if not smoke:
        oracle_row(2, 4, 4, results)
        oracle_row(3, 3, 4, results)
        oracle_row(2, 4, 5, results)
    # teeth
    run_teeth(all_tallies)
    # verdict
    say('')
    nv = 0
    for f in FAMILIES:
        say('%-13s checks %-8d violations %d'
            % (f, NCHK[f], len(VIOL[f])))
        nv += len(VIOL[f])
    teeth_ok = True
    for t in TEETH:
        want = TEETH_EXPECT[t]
        if smoke:
            say('%-13s fired %d (smoke: count not enforced)'
                % (t, FIRE[t]))
        else:
            ok = FIRE[t] == want
            teeth_ok = teeth_ok and ok
            say('%-13s fired %d / expected %d %s'
                % (t, FIRE[t], want, 'OK' if ok else 'RED'))
    verdict = 'GREEN' if (nv == 0 and (smoke or teeth_ok)) else 'RED'
    say('')
    say('VERDICT: %s — %d checks, %d violations, %.1f s'
        % (verdict, sum(NCHK.values()), nv, time.time() - t0))
    results['verdict'] = verdict
    results['checks'] = sum(NCHK.values())
    results['violations'] = nv
    results['teeth'] = dict(FIRE)
    results['elapsed_s'] = round(time.time() - t0, 1)
    out = os.path.join(HERE, 'genind_checks_results.json')
    with open(out, 'w') as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    txt = os.path.join(HERE, 'genind_checks_output.txt')
    with open(txt, 'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
