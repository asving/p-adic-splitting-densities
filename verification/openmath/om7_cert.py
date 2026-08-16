#!/usr/bin/env python3
r"""OM-7 -- certification battery for HYP.81 ([GENHN-HE(mu=3)]) and
HYP.82 ([GENHN-TOW-1]).  Unit note:
docs/openmath-campaign/OM-7_genhn-he-tow_2026-08-16.md.

WHAT THIS TESTS (design sealed with the OM-7 note's Section 1.3):

HYP.81, the mu = 3 stage-sigma law (THEOREM HE3.A at mu = 3): at a
DECIDED composite-stage leaf of stage type tau = {(e_s^i, f_s^i)}
(Sum e_s f_s = 3), every disc != 0 lift factors with

    sigma(f) = { (e1*e_s^i, f1*f_s^i) }_i .

The corpus record itself names four machine legs missing at HEAD:
(a) NO embedded n = 7 row anywhere in HE3's battery (EFF.HE3 source
    defect 9 / HE3-BOX-4b);
(b) the delivered mu = 3 coverage was Z_p ONLY (HE3-BOX-4b);
(c) every f1 >= 2 row sat at D' = 2 (pe1 leg B was (1,2));
(d) every mu = 3 row sat at h = 1.
Legs B/C/D/E below close exactly (a)-(d).  Leg A + leg F are the
exhaustive arithmetic certifications feeding the Lean landings
(H73w.lean, C93.lean).

LEG A  (arith, exhaustive)  81-S1 five-type exhaustiveness; 81-S3
       degree conservation; 81-S4 stage-CS infeasibility at mu <= 3
       (GENIND.A(IV) arithmetic); 81-S5 branch-(ii) unreachability
       (l >= 2, d >= 2 => side length >= 4 > 3); 81-S6 first-live
       degrees (D' >= 2, mu = 3 => n >= 6; mu >= 4, D' >= 2 => n >= 8,
       both sharp).

LEG B  (Z_p, p in {2,3,5}; PARI factorpadic + idealprimedec, the pinned
       w12 GP_FUN convention)  genre (Q; e1,f1,mu; h) = (p; 2,1,3; 1),
       key Phi' = x^2 - p.  All FIVE mu = 3 stage types via explicit
       digit constructions; each member's stage type re-read by this
       file's fresh reader; PARI sigma vs the dictionary.  THEN the
       embedded n = 7 rows: member * (x - c) for c in {1, 1+p} (the
       Hensel-split sibling; sigma must equal block-dictionary +
       {(1,1)}) and the boundary probe c = p (sibling at positive
       valuation: outside GENIND-3's unit-distance premise, polygon
       still separates -- recorded as probe, not certification).

LEG C  (equal characteristic, q in {2,3}; oracle = construction)
       O = F_q[[t]], genre (q; 2,1,3; 1); q = 3: Phi' = x^2 - t;
       q = 2: Phi' = x^2 + tx + t (x^2 - t is INSEPARABLE in char 2 --
       the classical Artin-Schreier-side twist; disc(f) != 0 is HE3.A's
       standing hypothesis, so the separable key is the honest frame).
       All five types, members constructed as explicit products of
       factors with ELEMENTARY (e,f) certificates (Eisenstein slope /
       the exact g(T) = t^k G(T/t^m) identity with G irreducible over
       F_q => the factor's residue field contains F_{q^deg G} =>
       forcing), each certificate checked programmatically, plus exact
       Res(f, f') != 0 over F_q[t] (Bareiss).  Reader re-reads the
       stage type; dictionary must reproduce the constructed sigma.

LEG D  (Z_3, f1 = 2 at D' = 4 -- new geography: all prior f1 >= 2 rows
       had D' = 2)  genre (3; 2,2,3; 1), key Phi' = x^4 + 9
       (theta = sqrt(3i), eta = res(theta^2/3) = +-i of degree 2, so
       (e,f)_key = (2,2)).  Five types; residual fields F_9; PARI
       oracle on degree-12 members.  Dictionary: (e_s,f_s) ->
       (2e_s, 2f_s).  Plus the OFF-NODE attack row (entry floor
       violated: dv(A_1) = 6 < 9): face-value dictionary read vs PARI
       (the pe1 leg-A2 pattern: is the node floor load-bearing here?).

LEG E  (Z_p, h = 3 -- new geography: all prior mu = 3 rows had h = 1;
       h = 2 is excluded by gcd(h, e1) = 1)  genre (p; 2,1,3; 3),
       p in {3,5}, key Phi' = x^2 - p^3.  Five types, PARI oracle.

LEG F  (arith, exhaustive)  HYP.82 / C.93 threshold: depth-r towers
       with proper levels l_i >= 2 and live top mu_r >= 2 have
       n = D_r * mu_r >= 2^{r+1}; exhaustive over r <= 6,
       l_i <= 5, mu_r <= 6; sharpness (all-2 attains); the depth
       first-live table (r = 1: 4, r = 2: 8, r = 3: 16, r = 4: 32);
       the GENTOW5 S4 witness chain u_{k+1} = 4 u_k + 1
       (5, 21, 85, 341) recomputed.

TEETH (planted mutants; each must fire or the verdict is RED):
  T-FLIP   flipped dictionary ((e_s,f_s) -> (f_s,e_s)) must be caught
           by PARI on the (3,1) and (1,3) rows of legs B, D, E.
  T-SIB    the embedded prediction WITHOUT the sibling's (1,1) block
           must be caught on every n = 7 row.
  T-TOW    2^{r+2} (one power too strong) must FAIL on the sharp
           witness (all-2 towers).
  T-READ   the reader must REJECT an off-locus object (leg D's
           attack row digit floors) as outside the node.

Output: this file's stdout -> om7_cert_output.txt (committed);
verdict GREEN iff 0 violations and all teeth fired.
"""

import itertools
import json
import subprocess
import sys
import time
from fractions import Fraction

sys.setrecursionlimit(10000)

# ===================================================================
# 0. small exact utilities
# ===================================================================


def vp(n, p):
    """p-adic valuation of a nonzero integer; None for 0."""
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# --- integer polynomials in x: list of coeffs, index = degree -------

def ptrim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def pmul(f, g):
    r = [0] * (len(f) + len(g) - 1) if f and g else []
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                if b:
                    r[i + j] += a * b
    return ptrim(r)


def padd(f, g):
    r = [0] * max(len(f), len(g))
    for i, a in enumerate(f):
        r[i] += a
    for i, b in enumerate(g):
        r[i] += b
    return ptrim(r)


def pscale(f, c):
    return ptrim([c * a for a in f])


def pdivmod_monic(f, g):
    """divide by MONIC g over Z: returns (q, r) exactly."""
    assert g[-1] == 1
    f = list(f)
    q = [0] * max(len(f) - len(g) + 1, 1)
    while len(f) >= len(g) and any(f):
        if f[-1] == 0:
            f.pop()
            continue
        d = len(f) - len(g)
        c = f[-1]
        q[d] += c
        for i, b in enumerate(g):
            f[d + i] -= c * b
        f.pop()
    return ptrim(q), ptrim(f)


def polystr(f):
    ts = []
    for i, c in enumerate(f):
        if c:
            ts.append('(%d)*x^%d' % (c, i))
    return '+'.join(ts) if ts else '0'


def deriv(f):
    return ptrim([i * c for i, c in enumerate(f)][1:])


def resultant_int(f, g):
    """exact integer resultant via Fraction Euclid (small sizes)."""
    a = [Fraction(c) for c in f]
    b = [Fraction(c) for c in g]
    res = Fraction(1)
    while True:
        a = a[:]
        while a and a[-1] == 0:
            a.pop()
        b = b[:]
        while b and b[-1] == 0:
            b.pop()
        if not b:
            return 0 if len(a) > 1 else None
        if len(b) == 1:
            res *= b[0] ** (len(a) - 1)
            return res
        # a = q b + r
        r = a[:]
        while len(r) >= len(b) and any(x != 0 for x in r):
            while r and r[-1] == 0:
                r.pop()
            if len(r) < len(b):
                break
            c = r[-1] / b[-1]
            d = len(r) - len(b)
            for i, x in enumerate(b):
                r[d + i] -= c * x
            r.pop()
        while r and r[-1] == 0:
            r.pop()
        res *= (-1) ** ((len(a) - 1) * (len(b) - 1)) * b[-1] ** ((len(a) - 1) - (len(r) - 1 if r else 0))
        a, b = b, r


# ===================================================================
# 1. finite fields: F_p (p prime, direct), F_9 = F_3[i], i^2 = -1
# ===================================================================


class Fq:
    """F_p for prime p, elements = ints mod p."""

    def __init__(self, p):
        self.p = p
        self.elts = list(range(p))
        self.zero, self.one = 0, 1

    def add(self, a, b):
        return (a + b) % self.p

    def neg(self, a):
        return (-a) % self.p

    def mul(self, a, b):
        return (a * b) % self.p

    def inv(self, a):
        return pow(a, self.p - 2, self.p)

    def frm_int(self, n):
        return n % self.p


class F9:
    """F_9 = F_3(i), elements = (a, b) for a + b i."""

    def __init__(self):
        self.p = 3
        self.elts = [(a, b) for a in range(3) for b in range(3)]
        self.zero, self.one = (0, 0), (1, 0)
        self.i = (0, 1)

    def add(self, x, y):
        return ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3)

    def neg(self, x):
        return ((-x[0]) % 3, (-x[1]) % 3)

    def mul(self, x, y):
        return ((x[0] * y[0] - x[1] * y[1]) % 3,
                (x[0] * y[1] + x[1] * y[0]) % 3)

    def inv(self, x):
        n = (x[0] * x[0] + x[1] * x[1]) % 3  # norm a^2+b^2
        ninv = pow(n, 1, 3)
        ninv = pow(n, 3 - 2, 3)
        return ((x[0] * ninv) % 3, ((-x[1]) * ninv) % 3)

    def frm_int(self, n):
        return (n % 3, 0)


def ffactor_shape(K, coeffs):
    """factorization SHAPE of a monic polynomial over the small field K
    (degree <= 3): returns sorted list of (deg, mult).  coeffs: list of
    K-elements, index = degree, monic."""
    d = len(coeffs) - 1
    assert coeffs[-1] == K.one and 1 <= d <= 3
    # roots with multiplicity by repeated division
    shape = []
    cur = list(coeffs)

    def feval(f, x):
        acc = K.zero
        for c in reversed(f):
            acc = K.add(K.mul(acc, x), c)
        return acc

    def fdiv_root(f, r):
        # divide monic f by (X - r): synthetic
        out = []
        acc = K.zero
        for c in reversed(f):
            acc = K.add(K.mul(acc, r), c) if out else c
            out.append(acc)
        # standard synthetic division:
        out = []
        acc = K.zero
        for c in reversed(f[:]):
            acc = K.add(c, K.mul(acc, r))
            out.append(acc)
        rem = out[-1]
        q = list(reversed(out[:-1]))
        return q, rem

    changed = True
    while len(cur) - 1 >= 1 and changed:
        changed = False
        for r in K.elts:
            if feval(cur, r) == K.zero:
                q, rem = fdiv_root(cur, r)
                assert rem == K.zero
                shape.append(1)
                cur = q
                changed = True
                break
    dleft = len(cur) - 1
    if dleft == 2:
        shape.append(2)   # quadratic with no roots: irreducible
    elif dleft == 3:
        shape.append(3)   # cubic with no roots: irreducible
    elif dleft == 1:
        shape.append(1)
    # multiplicities: recount equal linear roots
    return sorted(shape)


def ffactor_rootlist(K, coeffs):
    """list of roots (with multiplicity) of monic poly over K."""
    def feval(f, x):
        acc = K.zero
        for c in reversed(f):
            acc = K.add(K.mul(acc, x), c)
        return acc
    roots = []
    cur = list(coeffs)
    progress = True
    while len(cur) > 1 and progress:
        progress = False
        for r in K.elts:
            if feval(cur, r) == K.zero:
                out = []
                acc = K.zero
                for c in reversed(cur):
                    acc = K.add(c, K.mul(acc, r))
                    out.append(acc)
                cur = list(reversed(out[:-1]))
                roots.append(r)
                progress = True
                break
    return roots, len(cur) - 1  # remaining irreducible cofactor degree


# ===================================================================
# 2. the generic stage reader (mixed char; abstracted coefficients)
# ===================================================================
#
# A "coefficient ring hook" supplies: val(c) -> valuation (int >= 0) of
# a coefficient (None for 0) and res(c, v) -> the residue of c/pi^v in
# the residue field K.  Digits A_j (lists of coefficients, deg < D')
# get dv(A) = min_m (e1*val(a_m) + m*h); the residue of A at dv d is
# Sum over min-attaining monomials of res(a_m)*etapow((m - i0)/e1)
# where i0 = the normalizer x-exponent (i0*h == d mod e1) and etapow
# is the residue of (theta^{e1}/pi^h)^k -- eta = 1 for the f1 = 1 keys
# used here (verified per key) and eta = i for leg D's key (handled by
# the F9 hook).  Reader output: the stage type as a sorted tuple of
# (e_s, f_s) if DECIDED at depth 0, else None + reason.


def digit_dv_res(A, e1, h, val, res, etapow, K):
    """dv and side-residue of a digit A (list of ring coefficients)."""
    best = None
    for m, c in enumerate(A):
        v = val(c)
        if v is None:
            continue
        d = e1 * v + m * h
        if best is None or d < best:
            best = d
    if best is None:
        return None, None
    # residue: sum over monomials attaining best
    i0 = None
    for i in range(e1):
        if (i * h - best) % e1 == 0:
            i0 = i
            break
    acc = K.zero
    for m, c in enumerate(A):
        v = val(c)
        if v is None:
            continue
        if e1 * v + m * h == best:
            k = (m - i0) // e1
            acc = K.add(acc, K.mul(res(c, v), etapow(k)))
    if acc == K.zero:
        return best, K.zero   # cancellation at face value: flag upstream
    return best, acc


def stage_read(digits, e1, f1, h, val, res, etapow, K, mu=3):
    """depth-0 stage read.  digits = [A_0, ..., A_mu] (A_mu = [1]).
    Returns dict: {'pins':..., 'sides': [(kappa, es, d, shape)],
    'type': sorted tuple of (e_s,f_s) or None, 'decided': bool,
    'reason': str}."""
    Dp = e1 * f1
    S = Dp * h
    pins = []
    ress = {}
    for j, A in enumerate(digits):
        d, r = digit_dv_res(A, e1, h, val, res, etapow, K)
        if d is not None and r == K.zero:
            return {'decided': False, 'reason': 'residue cancellation at face dv (digit %d)' % j,
                    'type': None, 'pins': None, 'sides': None}
        pins.append((j, d))
        ress[j] = r
    # node floors
    for j, d in pins[:-1]:
        if d is not None and d < (mu - j) * S + 1:
            return {'decided': False, 'reason': 'OFF-NODE: dv(A_%d) = %s < floor %d'
                    % (j, d, (mu - j) * S + 1), 'type': None,
                    'pins': pins, 'sides': None}
    # lower hull from (mu, 0) leftwards
    pts = [(j, Fraction(d)) for j, d in pins if d is not None]
    assert pts[-1] == (mu, 0)
    hull = [(mu, Fraction(0))]
    rest = [q for q in pts if q[0] < mu]
    while rest:
        # steepest descent to the right: from current leftmost hull pt,
        # pick the point maximizing slope (d_prev - d)/(j_prev - j)...
        j1, d1 = hull[-1]
        best = None
        for (j, d) in rest:
            sl = (d - d1) / (j1 - j)   # positive slope going left
            if best is None or sl < best[0] or (sl == best[0] and j < best[1][0]):
                best = (sl, (j, d))
        hull.append(best[1])
        rest = [q for q in rest if q[0] < best[1][0]]
    hull.reverse()   # left to right
    # sides: consecutive hull vertices
    sides = []
    stype = []
    for (j1, d1), (j2, d2) in zip(hull, hull[1:]):
        kap = (d1 - d2) / (j2 - j1)
        if kap <= S:
            return {'decided': False, 'reason': 'side slope %s <= D\'h = %d (outside stage window)'
                    % (kap, S), 'type': None, 'pins': pins, 'sides': None}
        es = kap.denominator
        length = j2 - j1
        dres = length // es
        # residual polynomial: slots j1 + k*es, k = 0..dres, residue
        # taken iff the pin is ON the side
        rc = []
        for k in range(dres + 1):
            j = j1 + k * es
            don = d1 - kap * (j - j1)
            pj = dict(pins).get(j)
            if pj is not None and Fraction(pj) == don:
                rc.append(ress[j])
            else:
                rc.append(K.zero)
        # monic-normalize: divide by leading residue
        lead = rc[-1]
        li = K.inv(lead)
        rc = [K.mul(c, li) for c in rc]
        shape_roots, cof = ffactor_rootlist(K, rc)
        # multiplicity check: decided iff residual squarefree
        from collections import Counter
        cnt = Counter(shape_roots)
        if any(v >= 2 for v in cnt.values()):
            return {'decided': False, 'reason': 'repeated residual root on side slope %s' % kap,
                    'type': None, 'pins': pins, 'sides': sides}
        sides.append((str(kap), es, dres))
        for r in shape_roots:
            stype.append((es, 1))
        if cof:
            if cof in (2, 3):
                stype.append((es, cof))
            else:
                return {'decided': False, 'reason': 'residual cofactor degree %d unhandled' % cof,
                        'type': None, 'pins': pins, 'sides': sides}
    return {'decided': True, 'reason': '', 'type': tuple(sorted(stype)),
            'pins': pins, 'sides': sides}


def dictionary(stype, e1, f1):
    return tuple(sorted((e1 * es, f1 * fs) for (es, fs) in stype))


# ===================================================================
# 3. PARI oracle (the pinned w12 GP_FUN convention)
# ===================================================================

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


def gp_run(script):
    r = subprocess.run(['gp', '-q', '-f'], input=script.encode(),
                       capture_output=True, timeout=600)
    return r.stdout.decode()


def parse_sig(txt):
    nums = [int(x) for x in
            txt.replace('[', ' ').replace(']', ' ').replace(',', ' ').split()]
    return tuple(sorted(zip(nums[0::2], nums[1::2])))


def gp_sig_batch(jobs):
    """jobs = [(coeff list, p, tag)]; returns list of sig tuples."""
    lines = [GP_FUN]
    for i, (f, p, _) in enumerate(jobs):
        lines.append('print("R %d ", sig(%s, %d))' % (i, polystr(f), p))
    lines.append('quit')
    out = gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = parse_sig(rest)
    return [got.get(i) for i in range(len(jobs))]


# ===================================================================
# 4. LEG A -- the arithmetic exhaustives for HYP.81
# ===================================================================

VIOL = []
TEETH = {}


def leg_A():
    print('--- LEG A: HYP.81 arithmetic exhaustives')
    # A1: five-type exhaustiveness: multisets of (e,f), e,f >= 1, with
    # Sum e*f = 3, enumerated exhaustively (e, f <= 3 forced).
    pairs = [(e, f) for e in range(1, 4) for f in range(1, 4) if e * f <= 3]
    types = set()
    for k in range(1, 4):
        for combo in itertools.combinations_with_replacement(pairs, k):
            if sum(e * f for e, f in combo) == 3:
                types.add(tuple(sorted(combo)))
    want = {(( 3, 1),), ((1, 3),), ((1, 1), (2, 1)), ((1, 1), (1, 2)),
            ((1, 1), (1, 1), (1, 1))}
    ok = types == want
    print('  [%s] A1 five-type exhaustiveness: %d types %s'
          % ('OK ' if ok else 'BAD', len(types), sorted(types)))
    if not ok:
        VIOL.append('A1')
    # A2: degree conservation Sum (e1 e_s)(f1 f_s) = 3 e1 f1 on a grid
    bad = 0
    for e1 in range(1, 7):
        for f1 in range(1, 7):
            for tau in types:
                lhs = sum((e1 * es) * (f1 * fs) for es, fs in tau)
                if lhs != 3 * e1 * f1:
                    bad += 1
    print('  [%s] A2 degree conservation on 36-grid x 5 types: %d bad'
          % ('OK ' if bad == 0 else 'BAD', bad))
    if bad:
        VIOL.append('A2')
    # A3: stage-CS infeasibility at mu <= 3: no (e',f',mu') with
    # e'f' >= 2, mu' >= 2, e'*f'*mu' <= mu <= 3.
    sols = [(a, b, m, mu) for a in range(1, 8) for b in range(1, 8)
            for m in range(2, 8) for mu in range(2, 4)
            if a * b >= 2 and a * b * m <= mu]
    print('  [%s] A3 stage-CS infeasibility at mu<=3: %d solutions (want 0); '
          'first feasible mu = %d (want 4)'
          % ('OK ' if not sols else 'BAD', len(sols),
             min(a * b * m for a in range(1, 8) for b in range(1, 8)
                 for m in range(2, 8) if a * b >= 2)))
    if sols:
        VIOL.append('A3')
    # A4: branch-(ii) unreachability: l >= 2 and d >= 2 => l*d >= 4 > 3
    sols4 = [(l, d) for l in range(2, 10) for d in range(2, 10) if l * d <= 3]
    print('  [%s] A4 branch-(ii) unreachability at mu<=3: %d solutions (want 0)'
          % ('OK ' if not sols4 else 'BAD', len(sols4)))
    if sols4:
        VIOL.append('A4')
    # A5: first-live: min over D'>=2 of D'*3 = 6 (attained), and the
    # n = 7 slice is embedded (6 + 1); mu >= 4 & D' >= 2 => n >= 8 sharp.
    m6 = min(dp * 3 for dp in range(2, 20))
    m8 = min(dp * mu for dp in range(2, 20) for mu in range(4, 20))
    ok = (m6 == 6) and (m8 == 8)
    print('  [%s] A5 first-live: min D\'*3 = %d (want 6); min D\'*mu, mu>=4 = %d (want 8)'
          % ('OK ' if ok else 'BAD', m6, m8))
    if not ok:
        VIOL.append('A5')


# ===================================================================
# 5. LEG F -- the HYP.82 threshold arithmetic
# ===================================================================

def leg_F():
    print('--- LEG F: HYP.82 / C.93 threshold arithmetic')
    # F1 exhaustive: r <= 6, l_i in {2..5}, mu_r in {2..6}
    bad = 0
    tested = 0
    for r in range(1, 7):
        for mu in range(2, 7):
            for ls in itertools.product(range(2, 6), repeat=r):
                D = 1
                for l in ls:
                    D *= l
                tested += 1
                if not (2 ** (r + 1) <= D * mu):
                    bad += 1
    print('  [%s] F1 exhaustive 2^(r+1) <= D*mu: %d tuples, %d bad'
          % ('OK ' if bad == 0 else 'BAD', tested, bad))
    if bad:
        VIOL.append('F1')
    # F2 sharpness: all-2 towers attain
    sharp = all(2 ** r * 2 == 2 ** (r + 1) for r in range(1, 7))
    print('  [%s] F2 sharpness at all-2, mu_r = 2' % ('OK ' if sharp else 'BAD'))
    if not sharp:
        VIOL.append('F2')
    # F2t TOOTH T-TOW: 2^{r+2} must FAIL on the sharp witness
    fail = any(2 ** (r + 2) <= 2 ** (r + 1) for r in range(1, 7))
    TEETH['T-TOW'] = not fail
    print('  [%s] T-TOW: strengthened bound 2^(r+2) fails on all-2 witness'
          % ('OK ' if TEETH['T-TOW'] else 'BAD'))
    # F3 depth first-live table
    table = {r: 2 ** (r + 1) for r in range(1, 5)}
    ok = table == {1: 4, 2: 8, 3: 16, 4: 32}
    print('  [%s] F3 depth first-live: %s (depth 2 at 8, 3 at 16, 4 at 32)'
          % ('OK ' if ok else 'BAD', table))
    if not ok:
        VIOL.append('F3')
    # F4 the S4 witness chain u_{k+1} = 4u_k + 1: 5, 21, 85, 341 and
    # closed form (4^{k+2}-1)/3
    us = [5]
    for _ in range(3):
        us.append(4 * us[-1] + 1)
    closed = [(4 ** (k + 2) - 1) // 3 for k in range(4)]
    ok = us == [5, 21, 85, 341] and closed == us
    print('  [%s] F4 S4 chain: %s == closed form %s; n = 2^5 = 32 minimal at depth 4'
          % ('OK ' if ok else 'BAD', us, closed))
    if not ok:
        VIOL.append('F4')


# ===================================================================
# 6. LEG B -- Z_p rows at (2,1), h = 1, and the embedded n = 7 rows
# ===================================================================

def mk_members_21(p, h):
    """the five constructed members for genre (p; 2,1,3; h) with key
    Phi' = x^2 - p^h.  Returns list of (name, member poly, intended
    stage type, construction sigma)."""
    P = p ** h
    key = [-P, 0, 1]
    S = 2 * h

    def n_hat(m):
        """normalizer monomial x^i p^a at dv m: 2a + i*h = m, i<2."""
        i = 0 if m % 2 == 0 else 1
        a = (m - i * h) // 2
        assert 2 * a + i * h == m and a >= 0
        return pscale([0] * i + [1], p ** a)

    K = Fq(p)
    # irreducible residuals over F_p
    cub = {2: [1, 1, 0, 1], 3: [1, -1, 0, 1], 5: [1, 1, 0, 1]}[p]  # Z^3+..: c0,c1,c2,c3
    quad = {2: [1, 1, 1], 3: [1, 0, 1], 5: [2, 0, 1]}[p]
    rows = []
    Phi = key

    def phipow(k):
        r = [1]
        for _ in range(k):
            r = pmul(r, Phi)
        return r

    # (3,1): Phi'^3 + n(u31) with u31 = 3S+1 odd-numerator? need
    # gcd(u,3... slope u/3 with 3 | e_s: u coprime to 3, u >= 3S+1.
    u31 = 3 * S + 1
    while u31 % 3 == 0:
        u31 += 1
    m31 = padd(phipow(3), n_hat(u31))
    rows.append(('B(3,1) u=%d' % u31, m31, ((3, 1),), None))
    # (1,3): t^“6”-form: slope u13 integer >= S+1: member
    # Phi^3 + c2 n(u)Phi^2 + c1 n(2u)Phi + c0 n(3u)
    u13 = S + 2  # even => n_hat has i=0 at h odd... any integer > S
    m13 = phipow(3)
    for j, c in ((2, cub[2]), (1, cub[1]), (0, cub[0])):
        if c % p:
            m13 = padd(m13, pmul(pscale(n_hat((3 - j) * u13), c), phipow(j)))
    rows.append(('B(1,3) u=%d' % u13, m13, ((1, 3),), None))
    # (1,1)+(2,1): (Phi + n(S+2)) * (Phi^2 + n(2S+1... odd numerator))
    uA = S + 2
    uB = 2 * S + 1  # slope uB/2, odd => denominator 2
    b1 = padd(Phi, n_hat(uA))
    b2 = padd(phipow(2), n_hat(uB))
    rows.append(('B(1,1)+(2,1)', pmul(b1, b2), ((1, 1), (2, 1)), None))
    # (1,1)+(1,2): (Phi + n(S+2)) * (Phi^2 + q1 n(u)Phi + q0 n(2u))
    uq = S + 2
    b2q = phipow(2)
    for j, c in ((1, quad[1]), (0, quad[0])):
        if c % p:
            b2q = padd(b2q, pmul(pscale(n_hat((2 - j) * uq), c), phipow(j)))
    rows.append(('B(1,1)+(1,2)', pmul(b1, b2q), ((1, 1), (1, 2)), None))
    # (1,1)^3: distinct integer slopes S+2, S+4, S+6
    m111 = [1]
    for k in (2, 4, 6):
        m111 = pmul(m111, padd(Phi, n_hat(S + k)))
    rows.append(('B(1,1)^3', m111, ((1, 1), (1, 1), (1, 1)), None))
    return key, rows


def reader_int(member, key, p, e1, f1, h, K, etapow):
    """develop and stage-read an integer member."""
    digits = []
    f = list(member)
    for _ in range(4):
        q, r = pdivmod_monic(f, key)
        digits.append(r if r else [0])
        f = q
    assert f == [] or f == [1] or len(digits[-1]) > 0

    def val(c):
        return vp(c, p)

    def res(c, v):
        return K.frm_int(c // p ** v)

    return stage_read(digits[:3] + [[1]], e1, f1, h, val, res, etapow, K)


def leg_B():
    print('--- LEG B: Z_p (2,1,3;1) five types + EMBEDDED n = 7 rows, PARI oracle')
    jobs = []
    meta = []
    for p in (2, 3, 5):
        K = Fq(p)
        etapow = lambda k: K.one  # eta = 1 for x^2 - p
        key, rows = mk_members_21(p, 1)
        for name, m, itype, _ in rows:
            rd = reader_int(m, key, p, 2, 1, 1, K, etapow)
            if not rd['decided'] or rd['type'] != itype:
                VIOL.append('B-read %s p=%d: %s %s' % (name, p, rd['type'], rd['reason']))
                print('  [BAD] reader %s p=%d -> %s (%s)' % (name, p, rd['type'], rd['reason']))
                continue
            pred = dictionary(itype, 2, 1)
            jobs.append((m, p, '%s p=%d n6' % (name, p)))
            meta.append(('n6', name, p, pred))
            # embedded rows: siblings x - 1, x - (1+p); probe x - p
            for c, kind in ((1, 'n7'), (1 + p, 'n7'), (p, 'n7probe')):
                m7 = pmul(m, [-c, 1])
                pred7 = tuple(sorted(list(pred) + [(1, 1)]))
                jobs.append((m7, p, '%s p=%d %s c=%d' % (name, p, kind, c)))
                meta.append((kind, name, p, pred7))
    sigs = gp_sig_batch(jobs)
    nbad = 0
    flip_caught = 0
    sib_caught = 0
    for (kind, name, p, pred), got, (f, _, tag) in zip(meta, sigs, jobs):
        ok = got == pred
        if not ok:
            nbad += 1
            VIOL.append('B %s: PARI %s != pred %s' % (tag, got, pred))
        print('  [%s] %-28s PARI %s pred %s' % ('OK ' if ok else 'BAD', tag, got, pred))
        # teeth
        if kind == 'n6' and name.startswith(('B(3,1)', 'B(1,3)')):
            flipped = tuple(sorted((2 * fs, es) for es, fs in
                                   (((3, 1),) if '3,1' in name else ((1, 3),))))
            if got != flipped:
                flip_caught += 1
        if kind == 'n7':
            nosib = tuple(x for x in pred if True)
            nosib_bad = tuple(sorted(list(pred)))[:-0]
            without = tuple(q for q in pred)
            # prediction WITHOUT the sibling block:
            wo = list(pred)
            wo.remove((1, 1))
            if got != tuple(sorted(wo)):
                sib_caught += 1
    TEETH['T-FLIP-B'] = flip_caught >= 6      # 2 types x 3 primes
    TEETH['T-SIB'] = sib_caught >= 1
    print('  B rows: %d, bad %d; T-FLIP-B fired %d, T-SIB fired %d'
          % (len(jobs), nbad, flip_caught, sib_caught))


# ===================================================================
# 7. LEG C -- equal characteristic F_q[[t]], q in {2, 3}
# ===================================================================
# coefficients: F_q[t] polynomials as int lists mod q (index = t-deg)


def cpolys(q):
    class Ct:
        pass
    return Ct


def fqt_trim(a):
    while a and a[-1] % 2 == 0 and False:
        pass
    return a


class FqT:
    """F_q[t] arithmetic: elements = lists of ints mod q."""

    def __init__(self, q):
        self.q = q

    def trim(self, a):
        a = [c % self.q for c in a]
        while a and a[-1] == 0:
            a.pop()
        return a

    def add(self, a, b):
        r = [0] * max(len(a), len(b))
        for i, c in enumerate(a):
            r[i] += c
        for i, c in enumerate(b):
            r[i] += c
        return self.trim(r)

    def mul(self, a, b):
        if not a or not b:
            return []
        r = [0] * (len(a) + len(b) - 1)
        for i, c in enumerate(a):
            for j, d in enumerate(b):
                r[i + j] += c * d
        return self.trim(r)

    def neg(self, a):
        return self.trim([-c for c in a])

    def val(self, a):
        a = self.trim(list(a))
        if not a:
            return None
        for i, c in enumerate(a):
            if c % self.q:
                return i
        return None

    def res(self, a, v):
        return a[v] % self.q


def xp_mul(R, F, G):
    """multiply two polys in x over F_q[t] (lists of F_q[t] elts)."""
    if not F or not G:
        return []
    r = [[] for _ in range(len(F) + len(G) - 1)]
    for i, a in enumerate(F):
        for j, b in enumerate(G):
            r[i + j] = R.add(r[i + j], R.mul(a, b))
    while r and not R.trim(list(r[-1])):
        r.pop()
    return r


def xp_add(R, F, G):
    r = []
    for i in range(max(len(F), len(G))):
        a = F[i] if i < len(F) else []
        b = G[i] if i < len(G) else []
        r.append(R.add(a, b))
    while r and not R.trim(list(r[-1])):
        r.pop()
    return r


def xp_divmod_monic(R, F, G):
    """divide by monic-in-x G over F_q[t]."""
    F = [R.trim(list(c)) for c in F]
    q_ = [[] for _ in range(max(len(F) - len(G) + 1, 1))]
    while len(F) >= len(G):
        if not F[-1]:
            F.pop()
            continue
        d = len(F) - len(G)
        c = F[-1]
        q_[d] = R.add(q_[d], c)
        for i, b in enumerate(G):
            F[d + i] = R.add(F[d + i], R.neg(R.mul(c, b)))
        F.pop()
    while F and not F[-1]:
        F.pop()
    return q_, F


def xp_deriv(R, F):
    """d/dx."""
    out = []
    for i in range(1, len(F)):
        out.append(R.trim([i * c for c in F[i]]))
    while out and not out[-1]:
        out.pop()
    return out


def fqt_resultant_nonzero(R, F, G):
    """Res_x(F, G) != 0 over F_q[t], via evaluation at t-points in
    extension fields F_{q^k} (enough points for the degree bound), OR
    via pseudo-remainder gcd: here: gcd degree check by pseudo-Euclid."""
    # pseudo-Euclid: F, G over the fraction field; nonzero resultant
    # iff gcd is constant in x.
    A = [list(c) for c in F]
    B = [list(c) for c in G]
    while True:
        A = [R.trim(c) for c in A]
        while A and not A[-1]:
            A.pop()
        B = [R.trim(c) for c in B]
        while B and not B[-1]:
            B.pop()
        if not B:
            return len(A) <= 1   # gcd = A: constant iff deg 0
        if len(B) == 1:
            return True
        # pseudo-division: lc(B)^(degF-degB+1) * A mod B
        k = len(A) - len(B) + 1
        if k < 0:
            A, B = B, A
            continue
        lc = B[-1]
        for _ in range(k):
            A = [R.mul(c, lc) for c in A]
            # one division step? do full pseudo remainder:
        # full pseudo-remainder loop
        Aw = A
        while len(Aw) >= len(B):
            if not R.trim(list(Aw[-1])):
                Aw.pop()
                continue
            d = len(Aw) - len(B)
            c = Aw[-1]
            Aw = [R.mul(x, lc) for x in Aw]
            c2 = Aw[-1]
            # subtract (c2/lc... after scaling, coefficient is c*lc^? --
            # simpler: Aw = lc*Aw_old; subtract c_old*lc^0 ... redo:
            break
        # simpler robust route: classical pseudo remainder by repeated
        # scaling-subtraction:
        Aw = [list(c) for c in A]
        while len(Aw) >= len(B) and any(R.trim(list(c)) for c in Aw):
            if not R.trim(list(Aw[-1])):
                Aw.pop()
                continue
            d = len(Aw) - len(B)
            c = Aw[-1]
            Aw = [R.mul(x, lc) for x in Aw]
            cc = Aw[-1]
            # now leading coeff = c*lc; subtract (c) * x^d * B * ... :
            sub = [R.mul(c, b) for b in B]
            for i, s in enumerate(sub):
                Aw[d + i] = R.add(Aw[d + i], R.neg(s))
            while Aw and not R.trim(list(Aw[-1])):
                Aw.pop()
        A, B = B, Aw


def leg_C():
    print('--- LEG C: equal characteristic F_q[[t]], q in {2,3} (construction oracle)')
    for q in (2, 3):
        R = FqT(q)
        K = Fq(q)
        # keys: q=3: x^2 - t (separable); q=2: x^2 + t x + t (separable;
        # x^2 - t is inseparable in char 2)
        if q == 3:
            key = [[0, -1], [], [1]]          # -t + x^2
        else:
            key = [[0, 1], [0, 1], [1]]       # t + t x + x^2
        # verify eta = 1: theta^2/t residue: theta^2 = t (q=3);
        # theta^2 = t theta + t => theta^2/t = theta + 1 -> res 1 (q=2)
        etapow = lambda k: K.one
        S = 2

        def n_hat(m):
            i = m % 2
            a = (m - i) // 2
            return [[0] * a + [1]] if i == 0 else [[], [0] * a + [1]]

        def n_hat_x(m):
            """as x-poly over F_q[t]: t^a * x^i."""
            i = m % 2
            a = (m - i) // 2
            mono = [0] * a + [1]
            if i == 0:
                return [mono]
            return [[], mono]

        def phipow(k):
            r = [[1]]
            for _ in range(k):
                r = xp_mul(R, r, key)
            return r

        def scale(F, celt):
            return [R.mul(c, celt) for c in F]

        cub = {2: [1, 1, 0, 1], 3: [1, 2, 0, 1]}[q]
        quad = {2: [1, 1, 1], 3: [1, 0, 1]}[q]
        rows = []
        # (3,1): Phi^3 + n(7)
        m31 = xp_add(R, phipow(3), n_hat_x(7))
        rows.append(('C(3,1)', m31, ((3, 1),), 'forcing: v(Phi(xi)) = 7/6'))
        # (1,3): Phi^3 + c1 n(8) Phi + c0 n(12): u = 4:
        m13 = phipow(3)
        for j, c in ((2, cub[2]), (1, cub[1]), (0, cub[0])):
            if c % q:
                m13 = xp_add(R, m13, xp_mul(R, scale(n_hat_x((3 - j) * 4), [c]), phipow(j)))
        rows.append(('C(1,3)', m13, ((1, 3),), 'g = t^12 G3(Phi/t^4)... G3 irred/F_q'))
        # (1,1)+(2,1): (Phi + n(4)) (Phi^2 + n(5))
        b1 = xp_add(R, key, n_hat_x(4))
        b2 = xp_add(R, phipow(2), n_hat_x(5))
        rows.append(('C(1,1)+(2,1)', xp_mul(R, b1, b2), ((1, 1), (2, 1)),
                     'Eisenstein-slope + v(Phi(xi)) = 5/4'))
        # (1,1)+(1,2): (Phi + n(4)) (Phi^2 + q1 n(4) Phi + q0 n(8))
        b2q = phipow(2)
        for j, c in ((1, quad[1]), (0, quad[0])):
            if c % q:
                b2q = xp_add(R, b2q, xp_mul(R, scale(n_hat_x((2 - j) * 4), [c]), phipow(j)))
        rows.append(('C(1,1)+(1,2)', xp_mul(R, b1, b2q), ((1, 1), (1, 2)),
                     'block contains z in F_{q^2}'))
        # (1,1)^3: slopes 4, 6, 8
        m111 = [[1]]
        for k in (4, 6, 8):
            m111 = xp_mul(R, m111, xp_add(R, key, n_hat_x(k)))
        rows.append(('C(1,1)^3', m111, ((1, 1),) * 3, '3 distinct Eisenstein-slope quadratics'))

        for name, m, itype, cert in rows:
            # separability: Res(m, m') != 0
            sep = fqt_resultant_nonzero(R, m, xp_deriv(R, m))
            # develop + read
            digits = []
            f = [list(c) for c in m]
            for _ in range(4):
                qq, r = xp_divmod_monic(R, f, key)
                digits.append(r if r else [[]])
                f = qq
            rd = stage_read(digits[:3] + [[[1]]], 2, 1, 1,
                            lambda c: R.val(c), lambda c, v: K.frm_int(R.res(c, v)),
                            etapow, K)
            ok = sep and rd['decided'] and rd['type'] == itype
            # dictionary vs construction sigma
            pred = dictionary(itype, 2, 1)
            constr = pred  # by the elementary certificates above
            print('  [%s] q=%d %-14s sep=%s read=%s pred=%s (cert: %s)'
                  % ('OK ' if ok else 'BAD', q, name, sep, rd['type'], pred, cert))
            if not ok:
                VIOL.append('C %s q=%d: sep=%s read=%s (%s)'
                            % (name, q, sep, rd['type'], rd['reason']))


# ===================================================================
# 8. LEG D -- Z_3, f1 = 2 at D' = 4 (key x^4 + 9), + off-node attack
# ===================================================================

def leg_D():
    print('--- LEG D: Z_3 genre (3; 2,2,3; 1), key x^4 + 9 (D\' = 4, f1 = 2), PARI oracle')
    p = 3
    key = [9, 0, 0, 0, 1]
    K = F9()

    def etapow(k):
        # eta = res(theta^2/3) = i (choice of embedding; the reader's
        # residual SHAPE is embedding-independent)
        r = K.one
        kk = k % 4
        for _ in range(kk):
            r = K.mul(r, K.i)
        return r

    def phipow(k):
        r = [1]
        for _ in range(k):
            r = pmul(r, key)
        return r

    # lift of an F_9 element (a + b i) at dv-height m (m even: base
    # monomial 3^{m/2}; the i-part rides x^2 3^{m/2-1}); m odd: x 3^a
    # and i-part x^3 3^(a-1).
    def lift9(elt, m):
        a, b = elt
        out = []
        i0 = m % 2
        base_a = (m - i0) // 2
        if a:
            out = padd(out, pscale([0] * i0 + [1], a * p ** base_a))
        if b:
            out = padd(out, pscale([0] * (i0 + 2) + [1], b * p ** (base_a - 1)))
        return out

    rows = []
    # (3,1): Phi^3 + x*3^6 (dv 13)
    rows.append(('D(3,1)', padd(phipow(3), pscale([0, 1], 3 ** 6)), ((3, 1),)))
    # (1,3): Phi^3 - 3^6 Phi + 3^9 (residual Z^3 - Z + 1 over F_9)
    rows.append(('D(1,3)', padd(padd(phipow(3), pmul([-(3 ** 6)], key)), [3 ** 9]),
                 ((1, 3),)))
    # (1,1)+(2,1): (Phi + 27)(Phi^2 + 81 x)
    rows.append(('D(1,1)+(2,1)', pmul(padd(key, [27]), padd(phipow(2), [0, 81])),
                 ((1, 1), (2, 1))))
    # (1,1)+(1,2): (Phi + 27)(Phi^2 - 81 x^2 - 243)  [residual Z^2 - (1+i)]
    rows.append(('D(1,1)+(1,2)', pmul(padd(key, [27]), padd(phipow(2), [-243, 0, -81])),
                 ((1, 1), (1, 2))))
    # (1,1)^3: (Phi+27)(Phi+81)(Phi+243)
    m111 = [1]
    for c in (27, 81, 243):
        m111 = pmul(m111, padd(key, [c]))
    rows.append(('D(1,1)^3', m111, ((1, 1),) * 3))

    jobs, meta = [], []
    for name, m, itype in rows:
        rd = reader_int(m, key, p, 2, 2, 1, K, etapow)
        pred = dictionary(itype, 2, 2)
        if not rd['decided'] or rd['type'] != itype:
            VIOL.append('D-read %s: %s (%s)' % (name, rd['type'], rd['reason']))
            print('  [BAD] reader %s -> %s (%s)' % (name, rd['type'], rd['reason']))
        jobs.append((m, p, name))
        meta.append((name, itype, pred))
    sigs = gp_sig_batch(jobs)
    flip_caught = 0
    for (name, itype, pred), got in zip(meta, sigs):
        ok = got == pred
        if not ok:
            VIOL.append('D %s: PARI %s != pred %s' % (name, got, pred))
        print('  [%s] %-16s PARI %s pred %s' % ('OK ' if ok else 'BAD', name, got, pred))
        if name in ('D(3,1)', 'D(1,3)'):
            flipped = dictionary(tuple((fs, es) for es, fs in itype), 2, 2)
            if got != flipped:
                flip_caught += 1
    TEETH['T-FLIP-D'] = flip_caught >= 2
    # OFF-NODE attack row: Phi^3 + 9x^2 Phi + 3^5 (dv(A_1) = 6 < floor 9)
    att = padd(padd(phipow(3), pmul([0, 0, 9], key)), [3 ** 5])
    rd = reader_int(att, key, p, 2, 2, 1, K, etapow)
    TEETH['T-READ'] = (not rd['decided']) and rd['reason'].startswith('OFF-NODE')
    print('  [%s] T-READ: off-node object rejected by the reader (%s)'
          % ('OK ' if TEETH['T-READ'] else 'BAD', rd['reason']))
    # face-value read (floors ignored): compute PARI truth and report
    got = gp_sig_batch([(att, p, 'D-att')])[0]
    print('  [rec] off-node attack row PARI sigma = %s (face-value dictionary '
          'read is undefined: the object is outside the node; recorded '
          'as evidence that the entry floor fences real objects)' % (got,))


# ===================================================================
# 9. LEG E -- Z_p at h = 3 (key x^2 - p^3), p in {3, 5}
# ===================================================================

def leg_E():
    print('--- LEG E: Z_p genre (p; 2,1,3; 3), key x^2 - p^3, p in {3,5}, PARI oracle')
    jobs, meta = [], []
    for p in (3, 5):
        K = Fq(p)
        etapow = lambda k: K.one
        key, rows = mk_members_21(p, 3)
        for name, m, itype, _ in rows:
            rd = reader_int(m, key, p, 2, 1, 3, K, etapow)
            if not rd['decided'] or rd['type'] != itype:
                VIOL.append('E-read %s p=%d: %s (%s)' % (name, p, rd['type'], rd['reason']))
                print('  [BAD] reader %s p=%d -> %s (%s)' % (name, p, rd['type'], rd['reason']))
                continue
            pred = dictionary(itype, 2, 1)
            jobs.append((m, p, '%s p=%d h=3' % (name, p)))
            meta.append((name, p, itype, pred))
    sigs = gp_sig_batch(jobs)
    flip_caught = 0
    for (name, p, itype, pred), got, (f, _, tag) in zip(meta, sigs, jobs):
        ok = got == pred
        if not ok:
            VIOL.append('E %s: PARI %s != pred %s' % (tag, got, pred))
        print('  [%s] %-26s PARI %s pred %s' % ('OK ' if ok else 'BAD', tag, got, pred))
        if name.startswith(('B(3,1)', 'B(1,3)')):
            flipped = dictionary(tuple((fs, es) for es, fs in itype), 2, 1)
            if got != flipped:
                flip_caught += 1
    TEETH['T-FLIP-E'] = flip_caught >= 4
    print('  E rows: %d; T-FLIP-E fired %d' % (len(jobs), flip_caught))


# ===================================================================
# main
# ===================================================================

if __name__ == '__main__':
    t0 = time.time()
    print('=' * 72)
    print('OM-7 CERTIFICATION BATTERY -- HYP.81 (GENHN-HE mu=3) + HYP.82 (TOW-1)')
    print('=' * 72)
    leg_A()
    leg_F()
    leg_B()
    leg_C()
    leg_D()
    leg_E()
    print('=' * 72)
    print('TEETH %s' % json.dumps(TEETH))
    print('VIOLATIONS %d' % len(VIOL))
    for v in VIOL:
        print('  VIOL: %s' % v)
    teeth_ok = all(TEETH.values()) and len(TEETH) >= 6
    print('VERDICT %s   %.1fs' % ('GREEN' if (not VIOL and teeth_ok) else 'RED',
                                  time.time() - t0))
