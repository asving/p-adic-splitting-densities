#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""HE6 r1 / RECONCILIATION battery — THE WIDENED BOX'S OTHER BRANCH:
   the level-2 read at an ELL = 1 side whose residual is a REPEATED
   IRREDUCIBLE factor of DEGREE 2 (Codex HE6-PE1 finding 1's crack).

WHAT THIS TESTS AND WHY IT IS NEW
---------------------------------
HE6 (@1f5a417) proved the class-size law at every side with a SEPARABLE
residual and boxed HE6-BOX-1 at "ell >= 2 + repeated residual".  Codex's
hostile pass PE1 (CODEX_HE6PE1_2026-08-08.md, finding 1, UPHELD CRITICAL)
showed the box is too narrow: a side with ell = 1 (INTEGER slope) carrying a
repeated IRREDUCIBLE residual factor of degree d_r >= 2 is equally
undecided by the outer data — HE3's stage-alpha recentering is unavailable
(no element of the stage ring has residue beta in K(beta) \\ K), and the
stage-CS route supplies forcing but not counting.  The widened box is
"a repeated irreducible residual factor r with (ell, d_r) != (1,1)".

HE7 (@62d683f) proved (SLOT2)/(LIFT2) and the level ladder.  Its battery
`he7_checks.py` exercises ONLY ell = 2, d_r = 1 (K2 = K = F_p, beta = s a
SCALAR).  THIS runner exercises the OTHER branch of the widened box:

    (e1, f1, h) = (2, 1, 1),  Phi' = x^2 - pi,  D' = 2,  varpi = x,
    mu = 4,  deg f = 8,  ell = 1  (lambda in Z, lambda >= 3 > D'h = 2),
    R_lambda = r^2  with  r in F_p[Z] irreducible of DEGREE 2, r(0) != 0,
    ==> D'' = D' * ell * d_r = 4,  K2 = F_p[beta]/(r) = F_{p^2},
        dv2 = ell * dv = dv,  T2 = ell * d_r * u = 2 * lambda,
        n2(k) = varpi^{m} Phi'^{s} with ell m + s u = k, 0 <= s < ell = 1,
        so s == 0, m == k: THE LEVEL-2 NORMALIZER SYSTEM DEGENERATES TO
        varpi-POWERS AND THE LEVEL-2 TWIST COCYCLE IS TRIVIAL (tooth).
    Block = everything (|S| = D'L_lambda = 8 = deg f), so f_S = f, mu2 = 2.

So the two branches of the widened box separate the two mechanisms of
(SLOT2)'s exactness: at ell >= 2 the ell classes separate by gcd(u,ell) = 1
(VALUE direction); at ell = 1 the d_r within-class slots separate by
K-linear independence of {1, beta, ..., beta^{d_r-1}} (RESIDUE direction).
he7_checks.py tested the first; this runner tests the second, and its
HE6R1-T-BASIS tooth kills a reader that adds the within-class residues in
K instead of in K2.

THE LEVEL-2 SIGMA DICTIONARY AT THIS FRAME (mu2 = 2; e = e1*ell*ell2 =
2*ell2, f = f1*d_r*deg r2 = 2*deg r2), exhaustively:

    level-2 polygon                        (ell2, d_r2)  (e, f)     sigma
    one side, length 2, lambda2 not in Z   (2, 1)        (4, 2)     {(4,2)}
    one side, length 2, lambda2 in Z, R2 inert over K2   (1, 2) (2,4)  {(2,4)}
    one side, length 2, lambda2 in Z, R2 split over K2   (1,1)x2 (2,2)  {(2,2),(2,2)}
    two sides of length 1                  (1,1)x2       (2,2)      {(2,2),(2,2)}
    one side, R2 = (Z - s2)^2, s2 in K2     alpha-refine -> one of the above

NOTE the alphabet {(4,2)}, {(2,4)}, {(2,2),(2,2)} is DISJOINT from the
ell = 2 branch's alphabet ({(8,1)}, {(4,2)}, {(4,1),(4,1)}) except for
{(4,2)}: the two branches of the widened box are different mathematics
with different outputs, which is why a fresh machine leg is owed.

PREREGISTERED PREDICTIONS (written before the full run; commit 1 seals this
file unrun, commit 2 appends the verdict FROM the committed artifacts)
--------------------------------------------------------------------------
P1 (HE6R1-READ2 / HE6R1-SIG2, THE HEADLINE).  On every member the ell = 1
   level-2 read returns a sigma from the three-element alphabet above and
   PARI factorpadic AGREES, member by member, 0 mismatches.
P2 (HE6R1-SLOT2).  For every C in O[x] with deg C < D'' = 4:
   v(Res(f, C)) = 4 * dv2(C) EXACTLY  (= deg f * dv2 / (e1*ell) with
   dv2 = e1*ell*v = 2v), exercising BOTH beta-slots s = 0, 1 and their ties.
P3 (HE6R1-LIFT2, the d_r >= 2 SHARPNESS leg HE7-BOX-2 could not run).  By
   exhaustive enumeration over C with deg C < D'': the level-2 heights at
   which res2(., k) is ONTO K2 = F_{p^2} are exactly {k : k >= lambda}
   (= HE7's W2 = {k : m(k) - t*u in W1 for all t < d_r} at ell = 1, where
   W1 = Z_{>=0} because f1 = 1); every k >= the closed-form threshold
   (d_r - 1)u + (D' - 1)h = lambda + 1 IS onto, and every k < lambda is NOT
   (only F_p subsetneq K2 is reached).  This is the FIRST machine leg of
   this program at d_r >= 2, i.e. with K2 a PROPER extension of K.
P4 (HE6R1-GEN2).  The level-2 flat identity at rational LEVEL-2 heights:
   e1*ell*v(Res(f, Psi2)) = D''*ell2*d2*h_F2(kappa2) for kappa2 = u2/ell2 >
   T2 with ell2 in {1,2} and r2,0 irreducible over K2 of degree 3 > mu2.
P5 (HE6R1-SEP2).  STRICT excess in the same identity exactly when
   r2 | R_{lambda2} (the nonemptiness certificate of LEMMA HE7-10 at ell=1).

TEETH (each must FIRE; a tooth that does not fire is a violation)
  HE6R1-T-CRACK    : >= 2 distinct PARI sigma inside ONE row of IDENTICAL
                     outer data (same polygon, same residual r^2) => the
                     ell = 1 / d_r = 2 configuration is genuinely undecided
                     by the outer data.  This is HE6-T-CASEB's certificate
                     for the OTHER branch of the widened box: it is what
                     makes Codex finding 1's widening non-vacuous.
  HE6R1-T-NAIVEHE6A: the planted "treat r^2 as separable" dictionary
                     (one label of size D'*ell*d_r = 4, sigma
                     {(2,2),(2,2)}) is REFUTED by PARI on some member.
  HE6R1-T-BASIS    : a C whose two attaining beta-slots carry gamma_0 =
                     -gamma_1 != 0 has NO cancellation (v(Res) = 4k
                     exactly), i.e. the within-class residues are
                     K-independent in K2 — the ell = 1 replacement for
                     gcd(u, ell) = 1.  A reader summing them in K would
                     predict a strictly larger dv2.
  HE6R1-T-TWIST0   : every level-2 twist exponent computed at ell = 1 is 0
                     (the cocycle degenerates: HE6's twist-free convention
                     IS available at ell = 1, unlike ell >= 2).
  HE6R1-T-WITHHOLD : with one level-2 residual withheld the reader reports
                     UNDETERMINED (it does not silently accept).

INSTRUMENT / IMPORT PINS.  Rings, resultants, Phi'-development, level-1
slot value/residue, normalizers, hull, member enumeration and the PARI
bridge are IMPORTED from the sealed he6_checks.py; the level-2 layer over
K2 = F_{p^2} (arithmetic, residual assembly, factorisation, the reader, the
alpha-refine) is fresh here.  md5 pins of every import are printed and
recorded in the artifacts.

SMOKE RECORD (disclosed at the seal; run BEFORE commit 1, `python3
he6r1_checks.py` with no flags — the smoke path only).  p = 3, lambda = 3,
r = Z^2 + 1, member f = x^8 - 3x^6 + 27x^4 - 189x^2 + 1053: reader status OK,
mu2 = 2, sigma = {(4,2)}; 36 (SLOT2) identities, 6 (GEN2) flat identities,
1 (SEP2) strict excess, 0 violations.  P3 tables computed in five frames
(onto exactly at k >= lambda in each; closed-form threshold lambda + 1
sufficient, not tight).  Teeth on the smoke frame: ALL FIVE FIRED — CRACK saw
three distinct PARI sigma ({(4,2)} 47, {(2,4)} 6, {(2,2),(2,2)} 1) on 54
members of IDENTICAL outer data with the level-2 read agreeing 54/54.  The
full battery (`--full`) adds six further rows, both characteristics, the
c1-live letters and a second lambda, and is scored at commit 2 from the
committed artifacts.

Artifacts: he6r1_checks_output.txt, he6r1_checks_results.json.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import he6_checks as H6
from he6_checks import (Zp, FpTring, padd, pmul, ppow, development,
                        resultant, key_poly, nrm, dv_A, res_A, test_poly,
                        build_f, polystr, gp_sig_batch, disc_nonzero,
                        hull_sides, BIG, E1, F1, H, DP, MU)

PINS = ['he6_checks.py', 'he7_checks.py', 'w12_checks.py', 'w10_checks.py']


def pstr(f):
    """[r1-fix, print-only, no predicate touched] polystr breaks on the
    char-p ring's FpT coefficients; fall back to a plain rendering there."""
    try:
        return polystr(f)
    except TypeError:
        return '[' + ','.join(str(c) for c in f) + ']'


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


RES = {'legs': {}, 'viol': [], 'teeth': {}, 'rows': [], 'lift2': [],
       'crack': {}, 'notes': [], 'pins': {}}


def note(leg, k=1):
    RES['legs'][leg] = RES['legs'].get(leg, 0) + k


def viol(leg, what, detail):
    RES['viol'].append({'leg': leg, 'what': what, 'detail': str(detail)[:400]})
    print('  !! VIOLATION %s %s %s' % (leg, what, str(detail)[:220]))


def tooth(name, fired, detail=''):
    RES['teeth'][name] = {'fired': bool(fired), 'detail': str(detail)[:500]}
    print('  TOOTH %-18s %s  %s' % (name, 'FIRED' if fired else 'DID NOT FIRE',
                                    str(detail)[:170]))


# ===================================================== K2 = F_p[beta]/(r)
class K2(object):
    """K2 = K[Z]/(r), r = Z^2 + c1 Z + c0 irreducible over K = F_p.
    elements are pairs (a0, a1) meaning a0 + a1*beta;  beta^2 = -c1 beta - c0."""

    def __init__(self, p, c0, c1):
        self.p, self.c0, self.c1 = p, c0 % p, c1 % p
        self.zero, self.one = (0, 0), (1, 0)
        self.els = [(a, b) for a in range(p) for b in range(p)]
        assert all(self.pev([c0, c1, 1], (a, 0)) != (0, 0) for a in range(p)), \
            'r must be irreducible over F_p'

    def add(self, x, y):
        p = self.p
        return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)

    def neg(self, x):
        p = self.p
        return ((-x[0]) % p, (-x[1]) % p)

    def mul(self, x, y):
        p, c0, c1 = self.p, self.c0, self.c1
        a0, a1 = x
        b0, b1 = y
        return ((a0 * b0 - a1 * b1 * c0) % p,
                (a0 * b1 + a1 * b0 - a1 * b1 * c1) % p)

    def scal(self, a, x):
        p = self.p
        return ((a * x[0]) % p, (a * x[1]) % p)

    def inv(self, x):
        for y in self.els:
            if self.mul(x, y) == self.one:
                return y
        raise ZeroDivisionError('no inverse in K2: %s' % (x,))

    def pev(self, co, z):
        """evaluate a K2-polynomial (or an F_p one, ints allowed) at z in K2."""
        out = (0, 0)
        for c in reversed(co):
            cc = c if isinstance(c, tuple) else (c % self.p, 0)
            out = self.add(self.mul(out, z), cc)
        return out

    def monic(self, co):
        inv = self.inv(co[-1])
        return [self.mul(inv, c) for c in co]

    def pdiv_linear(self, co, root):
        """divide monic K2-poly co by (Z - root); returns quotient (exact)."""
        n = len(co) - 1
        q = [self.zero] * n
        cur = co[-1]
        for i in range(n - 1, -1, -1):
            q[i] = cur
            cur = self.add(co[i], self.mul(root, cur))
        assert cur == self.zero, 'not a root'
        return q

    def factor(self, co):
        """factor a monic K2-poly of degree <= 3 into (irreducible, mult).
        degree <= 3 needs only root finding over K2."""
        co = self.monic([c if isinstance(c, tuple) else (c % self.p, 0)
                         for c in co])
        out, cur = [], co
        while len(cur) - 1 > 0:
            root = None
            for z in self.els:
                if self.pev(cur, z) == self.zero:
                    root = z
                    break
            if root is None:
                out.append((tuple(cur), 1))       # irreducible of degree >= 2
                break
            fac = tuple([self.neg(root), self.one])
            cur = self.pdiv_linear(cur, root)
            hit = False
            for i, (ff, m) in enumerate(out):
                if ff == fac:
                    out[i] = (ff, m + 1)
                    hit = True
            if not hit:
                out.append((fac, 1))
        return out

    def irred_deg(self, d):
        """one monic irreducible of degree d over K2 with nonzero constant."""
        for tup in itertools.product(self.els, repeat=d):
            co = list(tup) + [self.one]
            if co[0] == self.zero:
                continue
            if any(self.pev(co, z) == self.zero for z in self.els):
                continue
            if d <= 3:
                return co
        raise RuntimeError('no irreducible of degree %d found' % d)


# ============================================ the level-2 frame at ell = 1
class L2Frame1(object):
    """the level-2 datum at an ELL = 1 side with a degree-2 residual letter:
    lam = u in Z (u > D'h = 2), r = Z^2 + c1 Z + c0 irreducible over F_p."""

    def __init__(self, R, p, u, c0, c1):
        self.R, self.p, self.u, self.l, self.dr = R, p, u, 1, 2
        self.c0, self.c1 = c0 % p, c1 % p
        self.K2 = K2(p, c0, c1)
        self.T2 = self.l * self.dr * u              # = 2u
        self.Dpp = DP * self.l * self.dr            # D'' = 4
        self.key = key_poly(R)                      # Phi' = x^2 - pi
        # Psi = Phi'^{d_r} + c1 * n(u) Phi' + c0 * n(2u)     (ell = 1)
        self.Psi = test_poly(u, 1, [self.c0, self.c1], R)
        assert len(self.Psi) - 1 == self.Dpp

    # ---- n2(k) = varpi^{m} Phi'^{s},  ell*m + s*u = k, 0 <= s < ell = 1
    def n2ms(self, k):
        return k, 0

    def twist(self, m1, u2, t):
        """(s(m1 - t u2) + t s(u2) - s(m1)) / ell — identically 0 at ell = 1."""
        return (self.n2ms(m1 - t * u2)[1] + t * self.n2ms(u2)[1]
                - self.n2ms(m1)[1]) // self.l

    # ---- (SLOT2) at ell = 1: dv2 = dv, slots = the d_r Phi'-slots
    def phidev(self, C):
        return development(C, self.key, self.dr - 1)

    def dv2(self, C):
        best = BIG
        for s, c in enumerate(self.phidev(C)):
            m = dv_A(c, self.R)
            if m < BIG:
                best = min(best, self.l * m + s * self.u)
        return best

    def res2(self, C, k):
        """level-2 residue of C/n2(k) as an element of K2 (beta-basis)."""
        m0, s0 = self.n2ms(k)
        cs = self.phidev(C)
        out = (0, 0)
        for t in range(self.dr):
            mt = m0 - t * self.u
            c = cs[s0 + self.l * t]
            if mt >= 0 and dv_A(c, self.R) == mt:
                g = res_A(c, self.R) % self.p
                comp = [0, 0]
                comp[t] = g
                out = self.K2.add(out, tuple(comp))
        return out

    def lift2(self, k, c):
        """(LIFT2) at ell = 1: C with deg C < D'', dv2(C) = k, res2 = c."""
        m0, s0 = self.n2ms(k)
        if m0 < 0:
            return None
        R = self.R
        out = [R.zero]
        got = False
        for t in range(self.dr):
            mt = m0 - t * self.u
            g = c[t] % self.p
            if g == 0:
                continue
            if mt < 0:
                return None
            got = True
            blk = pmul([x * R.el(g) for x in nrm(mt, R)],
                       ppow(self.key, s0 + self.l * t))
            out = padd(out, blk)
        return out if got else None


# ================================================ the level-2 read at ell=1
def level2_read(f, fr, maxref=40, withhold=None, naive_K=False):
    """develop f in Psi-powers, read the level-2 polygon in dv2, factor the
    residuals over K2 = F_{p^2}, apply THEOREM HE7.A's dictionary with
    (e, f) = (e1*ell*ell2, f1*d_r*deg r2).  naive_K=True collapses the
    beta-basis (the HE6R1-T-BASIS control)."""
    R, p, l, dr, u = fr.R, fr.p, fr.l, fr.dr, fr.u
    nf = len(f) - 1
    if nf % fr.Dpp:
        return {'status': 'DEGENERATE-deg'}
    mu2 = nf // fr.Dpp
    Psi, KK, trace = fr.Psi, fr.K2, []
    for step in range(maxref + 1):
        Ad = development(f, Psi, mu2)
        dv2s = [fr.dv2(Ad[j]) for j in range(mu2 + 1)]
        if dv2s[mu2] != 0:
            return {'status': 'DEGENERATE-top', 'dv2s': dv2s}
        sides = hull_sides(dv2s)
        blocks, deeper, undet, cur = [], None, False, []
        for side in sides:
            j1, m1, j2, m2 = side
            lam2 = Fr(m1 - m2, j2 - j1)
            if lam2 <= fr.T2:
                return {'status': 'NONPRINCIPAL', 'lam2': str(lam2),
                        'T2': fr.T2, 'dv2s': dv2s}
            l2, u2 = lam2.denominator, lam2.numerator
            d2 = (j2 - j1) // l2
            co = []
            for t in range(d2 + 1):
                j = j1 + t * l2
                want = m1 - lam2 * (j - j1)
                if want.denominator != 1:
                    co.append(KK.zero)
                    continue
                want = int(want)
                if dv2s[j] == want:
                    g = fr.res2(Ad[j], want)
                    if naive_K:
                        g = ((g[0] + g[1]) % p, 0)     # the DEFEATED reader
                    tw = fr.twist(m1, u2, t)
                    if tw:
                        return {'status': 'TWIST-NONTRIVIAL', 'tw': tw}
                    co.append(g)
                else:
                    co.append(KK.zero)
            if withhold is not None and str(lam2) == withhold:
                undet = True
                trace.append({'lam2': str(lam2), 'residual': 'WITHHELD'})
                continue
            if co[d2] == KK.zero:
                return {'status': 'DEGENERATE-lead', 'dv2s': dv2s,
                        'lam2': str(lam2)}
            facs = KK.factor(co)
            sd = {'lam2': str(lam2), 'residual': [list(x) for x in co],
                  'facs': [([list(y) for y in ff], m) for ff, m in facs]}
            trace.append(sd)
            cur.append(sd)
            for ff, m in facs:
                if m > 1:
                    deeper = (lam2, l2, u2, ff, m, d2)
                else:
                    blocks.append((E1 * l * l2, F1 * dr * (len(ff) - 1)))
        if undet:
            return {'status': 'UNDETERMINED', 'trace': trace}
        if deeper is None:
            tot = sum(a * b for a, b in blocks)
            if tot != nf:
                return {'status': 'BADTOTAL', 'blocks': blocks, 'tot': tot,
                        'trace': trace}
            return {'status': 'OK', 'sigma': tuple(sorted(blocks)),
                    'trace': trace, 'refines': step, 'mu2': mu2}
        lam2, l2, u2, ff, m, d2 = deeper
        if l2 != 1 or len(ff) != 2:
            # repeated factor with (ell2, d_r2) != (1,1): the WIDENED box one
            # level up -> level 3.  Predicted impossible at mu2 = 2 (needs
            # mult * ell2 * d_r2 >= 4 > mu2) — THEOREM HE7.C.
            return {'status': 'LEVEL3', 'lam2': str(lam2), 'l2': l2,
                    'deg_r2': len(ff) - 1, 'mult': m, 'trace': trace}
        s2 = KK.neg(ff[0])                     # the K2-rational double root
        w = fr.lift2(int(lam2), s2)
        if w is None:
            return {'status': 'REFINE-BLOCKED', 'lam2': str(lam2)}
        Psi = padd(Psi, [-c for c in w])
        trace.append({'refine': str(lam2), 's2': list(s2)})
    return {'status': 'REFINE-OVERFLOW', 'trace': trace}


# ==================================================== member construction
def instance1(u, c0, c1, R, pert=None):
    """single-side member at ELL = 1: side (0, 4u)-(4, 0), slope lambda = u,
    residual R_lambda = r^2 with r = Z^2 + c1 Z + c0 (so the residual has a
    REPEATED IRREDUCIBLE factor of degree 2 — the widened box's ell=1 crack).
    pert: dict j -> A_j STRICTLY above the lambda-line (deeper digits only)."""
    p = R.p
    rr = [(c0 * c0) % p, (2 * c0 * c1) % p, (c1 * c1 + 2 * c0) % p,
          (2 * c1) % p, 1]                      # coefficients of r^2
    A = []
    for j in range(MU):
        cj = rr[j]
        A.append([x * R.el(cj) for x in nrm((MU - j) * u, R)] if cj
                 else [R.zero])
    if pert:
        for j, Aj in pert.items():
            A[j] = padd(A[j], Aj)
    return A, build_f(A, R)


def member_opts(R, p, u, W=2):
    opts = []
    for j in range(MU):
        o = [[R.zero]]
        lo = (MU - j) * u + 1                   # strictly above the line
        for m in range(lo, lo + W):
            for c in range(1, p):
                o.append([x * R.el(c) for x in nrm(m, R)])
        opts.append(o)
    return opts


def members1(R, p, u, c0, c1, W=2, cap=None):
    opts = member_opts(R, p, u, W)
    tot = 1
    for o in opts:
        tot *= len(o)
    stride = 1 if (cap is None or tot <= cap) else -(-tot // cap)
    n = 0
    for i, tup in enumerate(itertools.product(*opts)):
        if i % stride:
            continue
        A, f = instance1(u, c0, c1, R, {j: tup[j] for j in range(MU)})
        n += 1
        yield A, f
    RES.setdefault('member_counts', []).append((R.name(), u, c0, c1, tot, n))


# ============================================================ legs P2, P3
def leg_slot2(f, fr, ncheck=10):
    """P2: v(Res(f, C)) = 4 * dv2(C) exactly, both beta-slots and ties."""
    R, p, u = fr.R, fr.p, fr.u
    Cs = []
    for m0 in range(0, 3):
        for m1 in range(0, 3):
            for a in range(1, min(p, 3)):
                for b in range(1, min(p, 3)):
                    c0 = [x * R.el(a) for x in nrm(m0, R)]
                    c1 = [x * R.el(b) for x in nrm(m1, R)]
                    Cs.append(padd(c0, pmul(c1, fr.key)))
    Cs = Cs[:ncheck * 4]
    for C in Cs:
        d2 = fr.dv2(C)
        rr = resultant(f, C)
        if rr == 0 or (hasattr(rr, 'c') and not rr):
            continue
        got = R.val(rr)
        want = (len(f) - 1) * d2 // (E1 * fr.l)
        note('HE6R1-SLOT2')
        if got != want:
            viol('HE6R1-SLOT2', 'v(Res) != deg f * dv2 / (e1 ell)',
                 dict(got=got, want=want, dv2=d2))


def lift2_reach(fr, kmax, hmax=4):
    """P3: EXHAUSTIVE reachable-residue sets at every level-2 height k."""
    R, p, u = fr.R, fr.p, fr.u
    reach = {}
    cand = [[R.zero]]
    for m in range(0, hmax + 1):
        for a in range(1, p):
            cand.append([x * R.el(a) for x in nrm(m, R)])
    for c0 in cand:
        for c1 in cand:
            C = padd(c0, pmul(c1, fr.key))
            k = fr.dv2(C)
            if k >= BIG or k > kmax:
                continue
            reach.setdefault(k, set()).add(fr.res2(C, k))
    return reach


def build_psi2(fr, u2, l2, r2co):
    """DEFINITION HE7-3 at ell = 1 (twist trivial): Psi2 = Psi^{l2 d2} +
    sum_{t<d2} C_t Psi^{l2 t} with dv2(C_t) = (d2-t)u2, res2 = r2co[t]."""
    R = fr.R
    d2 = len(r2co)
    out = ppow(fr.Psi, l2 * d2)
    for t in range(d2):
        c = r2co[t]
        if c == fr.K2.zero:
            continue
        Ct = fr.lift2((d2 - t) * u2, c)
        if Ct is None:
            return None
        out = padd(out, pmul(Ct, ppow(fr.Psi, l2 * t)))
    return out


def h_F2(dv2s, kappa2):
    return min(dv2s[j] + j * kappa2 for j in range(len(dv2s))
               if dv2s[j] < BIG)


def leg_gen2(f, fr, grid):
    """P4 (flat, generic letter) + P5 (STRICT excess exactly at the label)."""
    R, p = fr.R, fr.p
    mu2 = (len(f) - 1) // fr.Dpp
    Ad = development(f, fr.Psi, mu2)
    dv2s = [fr.dv2(Ad[j]) for j in range(mu2 + 1)]
    for (u2, l2, r2co, expect_excess) in grid:
        P2 = build_psi2(fr, u2, l2, r2co)
        if P2 is None:
            continue
        rr = resultant(f, P2)
        if rr == 0 or (hasattr(rr, 'c') and not rr):
            note('HE6R1-SEP2-inf')
            continue
        got = E1 * fr.l * R.val(rr)
        kappa2 = Fr(u2, l2)
        flat = fr.Dpp * l2 * len(r2co) * h_F2(dv2s, kappa2)
        if flat.denominator != 1:
            continue
        flat = int(flat)
        if expect_excess:
            note('HE6R1-SEP2')
            if got <= flat:
                viol('HE6R1-SEP2', 'no strict excess at the level-2 label',
                     dict(got=got, flat=flat, kappa2=str(kappa2)))
        else:
            note('HE6R1-GEN2')
            if got != flat:
                viol('HE6R1-GEN2', 'flat identity failed',
                     dict(got=got, flat=flat, kappa2=str(kappa2)))


def grid2(fr, mu2=2):
    """test grid: kappa2 = u2/l2 > T2 with a GENERIC letter of degree 3 over
    K2 (never divides a level-2 residual of degree <= mu2 = 2), plus the
    read's own labels (P5)."""
    KK = fr.K2
    gen = KK.irred_deg(3)[:-1]         # monic, low-to-high, drop the 1
    out = []
    for l2 in (1, 2):
        for u2 in range(l2 * fr.T2 + 1, l2 * fr.T2 + 3 * l2 + 1):
            if gcd(u2, l2) != 1:
                continue
            out.append((u2, l2, list(gen), False))
    return out


def grid2_labels(f, fr):
    """P5 grid: the read's own level-2 labels (r2 | R_{lambda2})."""
    rd = level2_read(f, fr)
    out = []
    if rd['status'] != 'OK':
        return out
    for sd in rd['trace']:
        if 'facs' not in sd:
            continue
        lam2 = Fr(sd['lam2'])
        for ff, m in sd['facs']:
            r2 = [tuple(y) for y in ff][:-1]
            out.append((lam2.numerator, lam2.denominator, r2, True))
    return out


# ==================================================================== rows
def run_row(R, p, u, c0, c1, W=2, cap=140, oracle=True, tag=''):
    t0 = time.time()
    name = '%s lam=%d r=Z^2+%dZ+%d %s' % (R.name(), u, c1, c0, tag)
    print('\n== ROW %s ==' % name)
    fr = L2Frame1(R, p, u, c0, c1)
    print('   Psi = %s   D\'\' = %d  T2 = %d  K2 = F_%d^2'
          % (pstr(fr.Psi), fr.Dpp, fr.T2, p))
    rows, jobs, sigs = [], [], {}
    nmem = 0
    for A, f in members1(R, p, u, c0, c1, W=W, cap=cap):
        if not disc_nonzero(f, R):
            continue
        nmem += 1
        rd = level2_read(f, fr)
        rec = {'f': pstr(f), 'status': rd['status'],
               'sigma': rd.get('sigma'), 'refines': rd.get('refines')}
        if rd['status'] != 'OK':
            viol('HE6R1-READ2', 'reader did not decide', rec)
        else:
            note('HE6R1-READ2')
            if rd['sigma'] not in (((2, 4),), ((4, 2),), ((2, 2), (2, 2))):
                viol('HE6R1-READ2', 'sigma outside the mu2=2 alphabet', rec)
        if nmem <= 6:
            leg_slot2(f, fr)
            leg_gen2(f, fr, grid2(fr) + grid2_labels(f, fr))
        if oracle and R.char0:
            jobs.append((polystr(f), rec))
        rows.append(rec)
    if jobs:
        got = gp_sig_batch([(j[0], None) for j in jobs], p)
        for i, (ps, rec) in enumerate(jobs):
            if i not in got:
                continue
            sg = tuple(sorted(tuple(x) for x in got[i]))
            rec['pari'] = sg
            note('HE6R1-SIG2')
            sigs[sg] = sigs.get(sg, 0) + 1
            if rec['sigma'] != sg:
                viol('HE6R1-SIG2', 'level-2 read != PARI',
                     dict(read=rec['sigma'], pari=sg, f=ps))
    cnt = {}
    for r in rows:
        if r.get('sigma'):
            k = str(r['sigma'])
            cnt[k] = cnt.get(k, 0) + 1
    out = {'row': name, 'members': nmem, 'pari': sum(sigs.values()),
           'sigma_counts': cnt,
           'pari_counts': {str(k): v for k, v in sigs.items()},
           'secs': round(time.time() - t0, 1)}
    RES['rows'].append(out)
    print('   members %d  pari %d  sigma %s  (%.1fs)'
          % (nmem, out['pari'], cnt, out['secs']))
    return out, rows, fr


# =================================================================== teeth
def teeth_run(p=5, u=3, c0=2, c1=0):
    print('\n== TEETH (p = %d, lambda = %d, r = Z^2+%dZ+%d) ==' % (p, u, c1, c0))
    R = Zp(p)
    fr = L2Frame1(R, p, u, c0, c1)

    # --- T-CRACK: >= 2 distinct PARI sigma on IDENTICAL outer data
    seen, jobs, reads = {}, [], []
    for A, f in members1(R, p, u, c0, c1, W=2, cap=60):
        if not disc_nonzero(f, R):
            continue
        rd = level2_read(f, fr)
        if rd['status'] != 'OK':
            continue
        jobs.append((polystr(f), None))
        reads.append(rd['sigma'])
    got = gp_sig_batch(jobs, p)
    agree, bad = 0, []
    for i, sg in got.items():
        s = tuple(sorted(tuple(x) for x in sg))
        seen[s] = seen.get(s, 0) + 1
        if reads[i] == s:
            agree += 1
        else:
            bad.append((jobs[i][0], reads[i], s))
    tooth('HE6R1-T-CRACK', len(seen) >= 2,
          'distinct PARI sigma on identical outer data: %s  (read agrees %d/%d)'
          % (sorted(seen.items()), agree, len(got)))
    RES['crack'] = {'sigma': {str(k): v for k, v in seen.items()},
                    'agree': agree, 'pari': len(got), 'bad': bad[:5]}
    if bad:
        viol('HE6R1-T-CRACK', 'read != PARI inside the tooth', bad[:3])

    # --- T-NAIVEHE6A: the "treat r^2 as separable" dictionary is refuted
    naive = ((2, 2), (2, 2))                # D'*ell*d_r = 4 per label, twice
    refuted = sum(v for k, v in seen.items() if k != naive)
    tooth('HE6R1-T-NAIVEHE6A', refuted > 0,
          'members whose PARI sigma refutes the planted separable dictionary '
          '%s: %d of %d' % (str(naive), refuted, sum(seen.values())))

    # --- T-BASIS: gamma_0 = -gamma_1 != 0 does NOT cancel (K2-independence)
    #     (the UNPERTURBED member is literally Psi^2, disc = 0, so the teeth
    #      run on a fixed member with one deeper digit switched on)
    base = {3: nrm(u + 1, R)}
    A, f = instance1(u, c0, c1, R, base)
    assert disc_nonzero(f, R), 'tooth base member is degenerate'
    ok, det = True, []
    for a in range(1, min(p, 4)):
        # slot 0 at height k, slot 1 at height k - u : both attain k
        k = u + 2
        c_0 = [x * R.el(a) for x in nrm(k, R)]
        c_1 = [x * R.el((-a) % p) for x in nrm(k - u, R)]
        C = padd(c_0, pmul(c_1, fr.key))
        d2, r2v = fr.dv2(C), fr.res2(C, fr.dv2(C))
        rr = resultant(f, C)
        got = R.val(rr)
        want = (len(f) - 1) * d2 // (E1 * fr.l)
        naive_zero = (r2v[0] + r2v[1]) % p == 0
        det.append(dict(a=a, dv2=d2, res2=list(r2v), vRes=got, want=want,
                        naive_reader_sees_cancellation=naive_zero))
        if got != want or r2v == fr.K2.zero:
            ok = False
    tooth('HE6R1-T-BASIS', ok and all(d['naive_reader_sees_cancellation']
                                      for d in det),
          'no cancellation at gamma_0 = -gamma_1 (K2-independence); a naive '
          'K-summing reader WOULD cancel: %s' % det[:2])

    # --- T-TWIST0: every level-2 twist exponent vanishes at ell = 1
    tws = [fr.twist(m1, u2, t) for m1 in range(1, 30) for u2 in range(1, 12)
           for t in range(0, 4)]
    tooth('HE6R1-T-TWIST0', all(x == 0 for x in tws),
          '%d twist exponents computed, all zero (n2(k) = varpi^k at ell = 1)'
          % len(tws))

    # --- T-WITHHOLD: withheld residual -> UNDETERMINED
    rd = level2_read(f, fr)
    lam2 = None
    for sd in rd.get('trace', []):
        if 'facs' in sd:
            lam2 = sd['lam2']
            break
    rd2 = level2_read(f, fr, withhold=lam2) if lam2 else {'status': 'n/a'}
    tooth('HE6R1-T-WITHHOLD', rd2['status'] == 'UNDETERMINED',
          'withheld lambda2 = %s -> %s' % (lam2, rd2['status']))


# =============================================================== LIFT2 leg
def lift2_leg():
    """P3: the d_r = 2 reachability tables, EXHAUSTIVELY enumerated."""
    print('\n== P3 (LIFT2 reachability at d_r = 2, K2 a PROPER extension) ==')
    for (p, u, c0, c1) in [(3, 3, 1, 0), (5, 3, 2, 0), (5, 3, 1, 1),
                           (7, 3, 3, 1), (5, 5, 2, 0)]:
        R = Zp(p)
        fr = L2Frame1(R, p, u, c0, c1)
        kmax = 2 * u + 4
        reach = lift2_reach(fr, kmax, hmax=kmax)
        full = p * p - 1
        onto = sorted(k for k in reach if len(reach[k]) == full)
        notonto = sorted(k for k in reach if len(reach[k]) < full)
        thr = (fr.dr - 1) * u + (DP - 1) * H        # (d_r-1)u + (D'-1)h
        pred_onto = sorted(k for k in reach if k >= u)
        rec = dict(p=p, lam=u, r=(c0, c1), thr_closed_form=thr,
                   onto=onto, not_onto=notonto,
                   predicted_onto_W2=pred_onto,
                   above_thr_all_onto=all(k in onto for k in reach
                                          if k >= thr),
                   below_lam_none_onto=all(k not in onto for k in reach
                                           if k < u))
        RES['lift2'].append(rec)
        note('HE6R1-LIFT2', len(reach))
        print('   p=%d lam=%d r=(%d,%d): thr=%d  onto=%s  not-onto=%s'
              % (p, u, c0, c1, thr, onto[:6], notonto[:8]))
        if pred_onto != onto:
            viol('HE6R1-LIFT2', 'W2 formula != enumeration',
                 dict(formula=pred_onto[:8], enum=onto[:8], p=p, lam=u))
        if not rec['above_thr_all_onto']:
            viol('HE6R1-LIFT2', 'a k above the closed-form threshold is NOT '
                 'onto', rec)
        if not rec['below_lam_none_onto']:
            viol('HE6R1-LIFT2', 'sharpness half failed', rec)


# ==================================================================== main
def smoke():
    print('SMOKE (p = 3, lambda = 3, r = Z^2 + 1)')
    R = Zp(3)
    fr = L2Frame1(R, 3, 3, 1, 0)
    # the UNPERTURBED member is exactly Psi^2 (disc = 0, excluded by the row
    # filter); the smoke member carries one deeper digit.
    A, f = instance1(3, 1, 0, R, {3: nrm(4, R)})
    rd = level2_read(f, fr)
    print('  Psi  =', polystr(fr.Psi))
    print('  f    =', polystr(f))
    print('  read =', rd.get('status'), rd.get('sigma'), 'mu2 =', rd.get('mu2'))
    leg_slot2(f, fr)
    leg_gen2(f, fr, grid2(fr) + grid2_labels(f, fr))
    print('  legs =', json.dumps(RES['legs']), ' viol =', len(RES['viol']))
    lift2_leg()
    teeth_run(3, 3, 1, 0)


def main():
    t0 = time.time()
    RES['pins'] = {q: md5(q) for q in PINS}
    print('HE6 r1 / RECONCILIATION battery — the ell = 1 branch of the '
          'WIDENED HE6-BOX-1')
    print('import pins:', json.dumps(RES['pins'], indent=None))
    full = '--full' in sys.argv
    if not full:
        smoke()
        return
    lift2_leg()
    ROWS = [(Zp(3), 3, 3, 1, 0, 'r inert, c1=0'),
            (Zp(5), 5, 3, 2, 0, 'r inert, c1=0'),
            (Zp(5), 5, 3, 1, 1, 'r inert, c1 LIVE'),
            (Zp(7), 7, 3, 3, 1, 'r inert, c1 LIVE'),
            (Zp(5), 5, 5, 2, 0, 'lambda = 5'),
            (FpTring(3), 3, 3, 1, 0, 'char p, identities only'),
            (FpTring(5), 5, 3, 2, 0, 'char p, identities only')]
    for (R, p, u, c0, c1, tag) in ROWS:
        run_row(R, p, u, c0, c1, W=2, cap=140, oracle=R.char0, tag=tag)
    teeth_run(5, 3, 2, 0)
    teeth_run(3, 3, 1, 0)
    RES['secs'] = round(time.time() - t0, 1)
    RES['violations'] = len(RES['viol'])
    print('\n===================== SUMMARY =====================')
    print('legs      :', json.dumps(RES['legs'], indent=None))
    print('teeth     :', json.dumps({k: v['fired'] for k, v in
                                     RES['teeth'].items()}))
    print('violations:', len(RES['viol']))
    print('seconds   :', RES['secs'])
    with open(os.path.join(HERE, 'he6r1_checks_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, default=str)


if __name__ == '__main__':
    main()
