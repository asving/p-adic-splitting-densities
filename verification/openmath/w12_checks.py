#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
w12_checks.py -- SEALED BATTERY for W12_PROOF_2026-08-08.md
(W-12, the general-n assembly: THEOREM W-12.A order-1 shape-generic
count laws checked at SEVEN new cubic triple-center families + the
quartic g = 2 families -- beyond (2,1,1) and beyond the n = 2 menu;
LEMMA W12-L0 history-resolved n = 2 laws; LEMMA W12-L1 block transfer
(Hensel product + direct-read vs sealed-W11-block-read pointwise);
THEOREM W-12.C's exact DBL drainage term (q-1)q^(2N-1); the S3.2
constructed ambiguous species; U3^TRP measured EXPLORATORY under the
disclosed conservative convention; PARI/GP independent sigma-multiset
oracle + species ambiguity witnesses.)

TWO-COMMIT SEAL.  Commit 1 = this runner + the note with its
preregistered predictions (S7), battery UNRUN on the full roster;
commit 2 = the verdict appended to the note FROM the committed
artifacts (w12_checks_output.txt / w12_checks_results.json).
PRE-SEAL SMOKE DISCLOSED: developed and debugged with `--smoke`
(cubic rows (Zp,2,3),(Zp,2,4),(Zp,3,2),(Fqt,2,3),(Fqt,4,2); quartic
rows (Zp,2,3),(Zp,3,3); L0HIST rows (Zp,2,5),(Fqt,3,3); oracle cubic
(2,3),(3,2) with species witnesses; quartic oracle (2,3)); observed at
smoke: all violation families 0, all four teeth firing (5,884 checks,
0.9 s).  COST PROBE DISCLOSED: one additional row, cubic (Fqt,2,6),
run once pre-seal to price the (2,7) rows (18.9 s, 0 violations,
dblU = 2048 = the law, 1,248 deep-decided TRP members realized).  An
independent throwaway brute-force (pre-runner, /tmp, disclosed in the
note S2.4) confirmed the seven TRP closed forms at 9 (p,N) rows and
the QRT laws at 4 rows BEFORE this runner was written.  gp
availability probed (PARI 2.17.4).  No full run before the seal.

DISCLOSED CONVENTIONS:
 * The TRP reader certifies NO tail sigma: any read state with
   v(b0) >= N (current recentered constant term = 0 in the window)
   exits UNDECIDED (note W12-BOX-3/BOX-7).  Its measured U3^TRP is an
   UPPER count for the sigma-convention residue -- EXPLORATORY, no
   closed form preregistered.
 * The DBL side inherits W-11's proved convention exactly (incl.
   SPLIT-TAIL certification), via the SEALED w11 classifier on the
   Hensel block and a FRESH direct cubic reader demanded to agree
   pointwise (W12-L1X).
 * Quartic rows enumerate the quadruple-center stratum only (the QRT
   laws are stratum laws; no quartic partition/drainage claim exists).
 * Oracle legs are mixed-characteristic only (PARI factorpadic);
   eq-char rows are SAME-class evidence (W10-BOX-4/W11-BOX-4).

FAMILIES (evidence class in brackets):
  W12-PIN    [NONE] md5 pins of the frozen imports (violation if moved)
  W12-LVL0   [SAME] level-0 pattern censuses C0(q) (5 cubic classes)
  W12-SHAPE  [SAME] every depth-0 decided TRP key == its S2.4 closed
             form, BOTH directions (unpredicted decided key or missing
             predicted key = violation), exact zeros included
  W12-QRT    [SAME] QRT-G2(h;(1,1)), (h;(2)) laws + the (1^2)
             composite-frontier volume, both directions
  W12-L0HIST [SAME] every history-resolved n=2 key (kind,params,hist)
             == the W12-L0 closed form; Sigma_H == the SEALED W-11
             aggregate predictor, key by key
  W12-BLOCK  [SAME] Hensel product identity g*l == f coefficient-exact
             per DBL member + fiber bijection (distinct (g,l) pairs,
             cardinality = the stratum)
  W12-L1X    [SAME] direct cubic read (FRESH arithmetic) == SEALED w11
             classifier on the Hensel block: (kind, params, hist)
             pointwise on every DBL member
  W12-DRAIN3 [SAME] partition Sigma == q^(3N); DBL-undecided ==
             (q-1)q^(2N-1) EXACTLY (the THEOREM leg); DBL per-pattern
             per-key counts == q^(N-1) x W12-L0 (letter-uniform across
             patterns); species members all undecided, count == q^N;
             U3^TRP reported (EXPLORATORY)
  W12-ORACLE [IND]  PARI/GP sigma MULTISET per decided cubic on the Zp
             oracle rows; exact integer disc == 0 ==> undecided
             (Python-exact disc; mixed bracket); species ambiguity
             witnesses sigma_A != sigma_B (constructed lifts of S3.2);
             quartic QRT decided members' sigma
  TEETH (each must fire >= 1 or the battery is RED):
  W12-T-SHAPE   RAM3 law corrupted to (q-1)q^(3N-2h-1) must mismatch
                on every cubic row (RAM3(1) always visible at N >= 2)
  W12-T-DRAIN   DBL drainage corrupted to (q-1)q^(2N-2) must mismatch
                on every cubic row
  W12-T-CENSUS4 S_(2) corrupted to q(q-1) must break QRT-G2(1,(2)) on
                every quartic row
  W12-T-SIGMA   QRT-G2(h,(2)) sigma mis-keyed to {(4,1)} must be
                caught by PARI on every decided (2)-member of every
                quartic oracle row

CUBIC CENSUS ROWS (23).  Zp: (p,N) in {(2,3),(2,4),(2,5),(2,6),(2,7),
(3,2),(3,3),(3,4),(5,2),(7,2)}; Fqt: (q,N) in {(2,3),(2,4),(2,5),
(2,6),(2,7),(3,2),(3,3),(3,4),(4,2),(4,3),(5,2),(8,2),(9,2)}.
7,105,774 monic cubics covered (unit: polynomials; separable-pattern
lifts counted analytically after level-0 classification, per LEMMA
W12-S2.1); 2,946,008 DBL/TRP lifts read INDIVIDUALLY (unit: lifts).
The (2,7) rows exist to realize TRP-3LIN (minimal visibility
u0 = 6 <= N-1).  QUARTIC ROWS (8, quadruple-center stratum).  Zp:
(2,3),(2,4),(2,5),(3,3); Fqt: (2,4),(2,5),(3,3),(4,3) -- 580,550
stratum members read.  L0HIST ROWS (11).  Zp: (2,5),(2,7),(3,3),
(5,3),(7,2); Fqt: (2,5),(2,7),(3,3),(4,3),(8,2),(9,2) -- 69,053
quadratics read (depth-3 histories realized at N = 7).  ORACLE ROWS.
Cubic Zp: (2,3),(2,4),(3,2),(3,3),(5,2) -- 40,645 cubics, every
decided member scored; species witnesses 85 pairs; quartic Zp: (2,3),
(2,4),(3,3) -- every QRT-decided member scored (1,516 members).

FROZEN-IMPORT PINS (W12-PIN; violation if a pinned file's md5 moved):
  w11_checks.py          500aae152bb5b5e9df3712904a6d73a6
  w10_checks.py          a9c34244a3af19f5fa864375b494380b
  iterlawn_pe_reimpl.py  cae45db2318b89520dd5484466ef3604
  grt_jc_probe.py        03811b695cf7aa1bd5b52d5b0cd8bcd6
  jd0_checks.py          d3a5e13df97d3768573800960a0ec509

Exact arithmetic throughout; deterministic; oracle = PARI/GP
subprocess.
"""

import sys, os, json, time, hashlib, subprocess, itertools
from math import gcd
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import w10_checks as W10
import w11_checks as W11

PINS = {
    'w11_checks.py':         '500aae152bb5b5e9df3712904a6d73a6',
    'w10_checks.py':         'a9c34244a3af19f5fa864375b494380b',
    'iterlawn_pe_reimpl.py': 'cae45db2318b89520dd5484466ef3604',
    'grt_jc_probe.py':       '03811b695cf7aa1bd5b52d5b0cd8bcd6',
    'jd0_checks.py':         'd3a5e13df97d3768573800960a0ec509',
}

FAMILIES = ['W12-PIN', 'W12-LVL0', 'W12-SHAPE', 'W12-QRT', 'W12-L0HIST',
            'W12-BLOCK', 'W12-L1X', 'W12-DRAIN3', 'W12-ORACLE']
TEETH = ['W12-T-SHAPE', 'W12-T-DRAIN', 'W12-T-CENSUS4', 'W12-T-SIGMA']

VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
LOG = []


def say(msg):
    print(msg)
    LOG.append(msg)


def note(fam, n=1):
    NCHK[fam] += n


def viol(fam, tag, detail):
    VIOL[fam].append((tag, detail))
    say('  VIOLATION [%s] %s: %s' % (fam, tag, detail))


# ------------------------------------------------------------ ring helpers
def rzero(R):
    return 0 if R.kind == 'Zp' else tuple([R.K.zero()] * R.N)


def is_rzero(R, a):
    return (a % R.M == 0) if R.kind == 'Zp' else all(R.K.is_zero(x)
                                                     for x in a)


def rneg(R, a):
    if R.kind == 'Zp':
        return (-a) % R.M
    return tuple(R.K.neg(x) for x in a)


def rsub(R, a, b):
    return R.add(a, rneg(R, b))


def rint(R, m):
    """the ring element m*1 (m a small nonneg int)."""
    one = 1 if R.kind == 'Zp' else R.lift(R.K.one())
    out = rzero(R)
    for _ in range(m):
        out = R.add(out, one)
    return out


def rinv(R, u):
    """inverse of a unit u in O/pi^N (Newton x <- x(2 - ux))."""
    x = R.lift(R.K.inv(R.res(u, 0)))
    two = rint(R, 2)
    it = 0
    while True:
        e = rsub(R, two, R.mul(u, x))
        x2 = R.mul(x, e)
        it += 1
        if x2 == x or it > R.N + 4:
            break
        x = x2
    assert is_rzero(R, rsub(R, R.mul(u, x), rint(R, 1))), 'rinv failed'
    return x


def pipow(R, m):
    out = rint(R, 1)
    for _ in range(m):
        out = R.mul(out, R.pi())
    return out


def shift3(R, a2, a1, a0, s):
    """coefficients of f(x+s) for f = x^3 + a2 x^2 + a1 x + a0."""
    s2 = R.mul(s, s)
    s3 = R.mul(s2, s)
    b2 = R.add(a2, R.mul(rint(R, 3), s))
    b1 = R.add(R.add(a1, R.mul(R.mul(rint(R, 2), a2), s)),
               R.mul(rint(R, 3), s2))
    b0 = R.add(R.add(R.add(a0, R.mul(a1, s)), R.mul(a2, s2)), s3)
    return b2, b1, b0


def shift4(R, a3, a2, a1, a0, s):
    """coefficients of f(x+s) for monic quartic."""
    s2 = R.mul(s, s)
    s3 = R.mul(s2, s)
    s4 = R.mul(s3, s)
    c = lambda m: rint(R, m)
    b3 = R.add(a3, R.mul(c(4), s))
    b2 = R.add(R.add(a2, R.mul(R.mul(c(3), a3), s)), R.mul(c(6), s2))
    b1 = R.add(R.add(R.add(a1, R.mul(R.mul(c(2), a2), s)),
                     R.mul(R.mul(c(3), a3), s2)), R.mul(c(4), s3))
    b0 = R.add(R.add(R.add(R.add(a0, R.mul(a1, s)), R.mul(a2, s2)),
                     R.mul(a3, s3)), s4)
    return b3, b2, b1, b0


# ------------------------------------------------------- residue-field poly
def kroots_mult(K, coeffs):
    """coeffs = [c0, c1, ..., 1] monic over K (deg = len-1 <= 3).
    Returns list of (root, mult) and the degree of the rootless
    cofactor."""
    deg = len(coeffs) - 1
    out = []
    poly = list(coeffs)
    for z in K.elems():
        m = 0
        while len(poly) > 1:
            # synthetic division of poly by (y - z); poly ascending
            dsc = list(poly)
            n = len(dsc) - 1
            quot = [K.zero()] * n
            acc = dsc[n]
            for i in range(n - 1, -1, -1):
                quot[i] = acc
                acc = K.add(dsc[i], K.mul(acc, z))
            if K.is_zero(acc):
                m += 1
                poly = quot
            else:
                break
        if m:
            out.append((z, m))
    return out, len(poly) - 1


def quad_type(K, c1, c0):
    """monic y^2 + c1 y + c0 over K: '11' | '2' | ('1sq', root)."""
    roots, cof = kroots_mult(K, [c0, c1, K.one()])
    tot = sum(m for _, m in roots)
    if tot == 2:
        if len(roots) == 2:
            return '11', None
        return '1sq', roots[0][0]
    if tot == 0:
        return '2', None
    raise AssertionError('quad with one simple root only')


def cubic_res_type(K, c2, c1, c0):
    """monic cubic residual: '111'|'12'|'3'|('11sq',z)|('1cube',z)."""
    roots, cof = kroots_mult(K, [c0, c1, c2, K.one()])
    tot = sum(m for _, m in roots)
    if tot == 3:
        ms = sorted((m for _, m in roots), reverse=True)
        if ms == [1, 1, 1]:
            return '111', None
        if ms == [2, 1]:
            z = next(z for z, m in roots if m == 2)
            return '11sq', z
        return '1cube', roots[0][0]
    if tot == 1:
        return '12', None
    if tot == 0:
        return '3', None
    raise AssertionError('cubic residual mult census broken')


# ------------------------------------------------------------ lower hull
def hull(points):
    pts = sorted((x, y) for (x, y) in points if y is not None)
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


# ------------------------------------------- FRESH direct cubic DBL reader
def read_dbl(R, q, a2, a1, a0, cb):
    """Direct read of the cubic x^3+a2x^2+a1x+a0 at the DOUBLE center
    cbar (fresh arithmetic; W-11 vocabulary exits).  Returns
    (kind, params, hist, sigma)."""
    K = R.K
    c = R.lift(cb)
    A2, A1, A0 = shift3(R, a2, a1, a0, c)
    assert R.val(A2) == 0, 'DBL center: A2 must be a unit'
    hist = []
    it = 0
    while True:
        it += 1
        assert it <= 3 * R.N + 8, 'read_dbl loop cap'
        u, w = R.val(A0), R.val(A1)
        H = tuple(hist)
        if u is not None:
            if u % 2 == 1 and (w is None or 2 * w >= u + 1):
                return ('RAM', (u,), H, ((1, 1), (2, 1)))
            if w is not None and 2 * w < u:
                return ('2SIDED', (w, u - w), H, ((1, 1),) * 3)
            kk = u // 2
            invA2 = K.inv(R.res(A2, 0))
            c1 = K.mul(R.res(A1, kk), invA2) if (w is not None and
                                                 w == kk) else K.zero()
            c0 = K.mul(R.res(A0, u), invA2)
            assert not K.is_zero(c0)
            t, z = quad_type(K, c1, c0)
            if t == '11':
                return ('SPLITEQ', (kk,), H, ((1, 1),) * 3)
            if t == '2':
                return ('INERTDEEP', (kk,), H, ((1, 1), (1, 2)))
            s = R.mul(R.lift(z), pipow(R, kk))
            A2, A1, A0 = shift3(R, A2, A1, A0, s)
            # shift3 on the DEPRESSED cubic state: state is monic cubic
            hist.append(kk)
            continue
        if w is not None and 2 * w + 1 <= R.N:
            return ('SPLIT-TAIL', (w,), H, ((1, 1),) * 3)
        return ('UNDECIDED', (), H, None)


# ----------------------------------------------------- Hensel block split
def hensel_split_dbl(R, q, a2, a1, a0, db):
    """f = x^3+a2x^2+a1x+a0, fbar = (x-cb)^2 (x-db): return
    (g0, g1, r) with f = (x^2 + g1 x + g0)(x - r), r == db mod pi."""
    r = R.lift(db)
    it = 0
    while True:
        fr = R.add(R.mul(R.add(R.mul(R.add(r, a2), r), a1), r), a0)
        if is_rzero(R, fr):
            break
        it += 1
        assert it <= R.N + 4, 'Newton did not converge'
        dfr = R.add(R.mul(R.add(R.mul(rint(R, 3), r),
                                R.mul(rint(R, 2), a2)), r), a1)
        r = rsub(R, r, R.mul(fr, rinv(R, dfr)))
    g1 = R.add(a2, r)
    g0 = R.add(a1, R.mul(r, g1))
    # remainder a0 + r*g0 == f(r) == 0 by loop exit
    return g0, g1, r


# --------------------------------------------------- recursive TRP reader
def sides_of(pts):
    """pts = hull vertices; yield (j0,y0,j1,y1) per side."""
    return [(pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1])
            for i in range(len(pts) - 1)]


def read_trp(R, q, a2, a1, a0, cb):
    """Recursive TRP read at the triple center cbar.  CONSERVATIVE TAIL
    CONVENTION (disclosed): v(b0) >= N ==> UNDECIDED.  Returns dict:
    decided, sigma (sorted tuple of (e,f)), depth0 (family key at the
    first read if it decided, else None), hist, species (b1=b0=0)."""
    K = R.K
    c = R.lift(cb)
    B2, B1, B0 = shift3(R, a2, a1, a0, c)
    assert R.val(B2) is None or R.val(B2) >= 1
    species = is_rzero(R, B1) and is_rzero(R, B0)
    hist = []
    depth0 = None
    first = True
    it = 0
    while True:
        it += 1
        assert it <= 3 * R.N + 8, 'read_trp loop cap'
        u0 = R.val(B0)
        if u0 is None:
            return {'decided': False, 'sigma': None, 'depth0': depth0,
                    'hist': tuple(hist), 'species': species}
        coeff = {0: B0, 1: B1, 2: B2}
        pts = [(0, u0), (1, R.val(B1)), (2, R.val(B2)), (3, 0)]
        hv = hull(pts)
        pieces = []
        refine = None          # (zbar, k)
        d0key = None
        S = sides_of(hv)
        for (j0, y0, j1, y1) in S:
            dx, dy = j1 - j0, y0 - y1
            g = gcd(dx, dy) if dy else dx
            if dy == 0:
                g = dx        # slope-0 side: e = 1, res degree dx
            e = dx // g
            hstep = dy // g
            # residual coefficients over K at the lattice points
            rc = []
            for i in range(g + 1):
                j = j0 + i * e
                h = y0 - i * hstep
                rc.append(K.one() if j == 3 else R.res(coeff[j], h))
            lead = rc[-1]
            invl = K.inv(lead)
            rcm = [K.mul(x, invl) for x in rc]
            if g == 1:
                pieces.append((e, 1))
                continue
            roots, cofdeg = kroots_mult(K, rcm)
            for (z, m) in roots:
                if m == 1:
                    pieces.append((e, 1))
                else:
                    assert refine is None, 'two repeated roots?'
                    assert e == 1, 'repeated root on e>1 side at n=3?'
                    refine = (z, hstep)
            if cofdeg:
                pieces.append((e, cofdeg))
        if first:
            first = False
            if refine is None:
                d0key = trp_depth0_key(hv, K, coeff, R)
                depth0 = d0key
        if refine is None:
            return {'decided': True,
                    'sigma': tuple(sorted(pieces)),
                    'depth0': depth0, 'hist': tuple(hist),
                    'species': species}
        z, k = refine
        s = R.mul(R.lift(z), pipow(R, k))
        B2, B1, B0 = shift3(R, B2, B1, B0, s)
        hist.append(k)


def trp_depth0_key(hv, K, coeff, R):
    """(family, params) for a DECIDED first read (S2.4 vocabulary)."""
    S = sides_of(hv)
    u0 = hv[0][1]
    if len(S) == 1:
        dx, dy = 3, u0
        if dy % 3 != 0:
            return ('RAM3', (u0,))
        k = dy // 3
        c2, c1, c0 = R.res(coeff[2], k), R.res(coeff[1], 2 * k), \
            R.res(coeff[0], 3 * k)
        t, _ = cubic_res_type(K, c2, c1, c0)
        return ('FULL', (k, t))
    if len(S) == 3:
        m1 = hv[0][1] - hv[1][1]
        m2 = hv[1][1] - hv[2][1]
        m3 = hv[2][1]
        return ('3LIN', (m1, m2, m3))
    # two sides: vertex at 1 or 2
    vx, vy = hv[1]
    if vx == 1:
        if vy % 2 == 1:
            return ('LINRAM2', (u0, vy))
        k = vy // 2
        invl = K.one()          # right side leading coeff = monic j=3
        c1 = R.res(coeff[2], k)
        c0 = R.res(coeff[1], vy)
        t, _ = quad_type(K, c1, c0)
        return ('VERT1', (u0, k, t))
    else:
        t0 = vy
        lead = R.res(coeff[2], t0)
        invl = K.inv(lead)
        mid = K.mul(R.res(coeff[1], (u0 + t0) // 2), invl)
        cst = K.mul(R.res(coeff[0], u0), invl)
        if (u0 - t0) % 2 == 1:
            return ('RAM2LIN', (u0, t0))
        t, _ = quad_type(K, mid, cst)
        return ('VERT2', (u0, t0, t))


# ------------------------------------------------------------ closed forms
def s_lam(q):
    return {'1': q - 1,
            '11': (q - 1) * (q - 2) // 2, '2': q * (q - 1) // 2,
            '1sq': q - 1,
            '111': (q - 1) * (q - 2) * (q - 3) // 6,
            '12': (q - 1) * q * (q - 1) // 2, '3': (q ** 3 - q) // 3,
            '11sq': (q - 1) * (q - 2), '1cube': q - 1}


def trp_expected(q, N):
    """whole-space (x q centers) depth-0 decided TRP counts."""
    S = s_lam(q)
    exp = {}

    def put(k, v):
        if v > 0:
            exp[k] = v * q          # q centers

    for h in range(1, N):
        if h % 3:
            put(('RAM3', (h,)), (q - 1) * q ** (3 * N - 2 * h - 2))
    for m1 in range(1, N):
        for m2 in range(1, m1):
            for m3 in range(1, m2):
                if m1 + m2 + m3 <= N - 1:
                    put(('3LIN', (m1, m2, m3)),
                        (q - 1) ** 3 * q ** (3 * N - 3 - m1 - 2 * m2
                                             - 3 * m3))
    for u0 in range(1, N):
        for u1 in range(1, u0):
            if u1 % 2 == 1 and 2 * u0 > 3 * u1:
                put(('LINRAM2', (u0, u1)),
                    (q - 1) ** 2 * q ** (3 * N - 2 - u0 - u1
                                         - (u1 + 1) // 2))
        for k in range(1, N):
            if u0 > 3 * k:
                for lam in ('11', '2'):
                    put(('VERT1', (u0, k, lam)),
                        (q - 1) * S[lam] * q ** (3 * N - 3 - u0 - 3 * k))
        for t in range(1, u0):
            if u0 > 3 * t:
                if (u0 - t) % 2 == 1:
                    put(('RAM2LIN', (u0, t)),
                        (q - 1) ** 2 * q ** (3 * N - 2 - u0 - t
                                             - (u0 + t + 1) // 2))
                else:
                    for lam in ('11', '2'):
                        put(('VERT2', (u0, t, lam)),
                            (q - 1) * S[lam]
                            * q ** (3 * N - 3 - u0 - t - (u0 + t) // 2))
    for k in range(1, N):
        if 3 * k <= N - 1:
            for lam in ('111', '12', '3'):
                put(('FULL', (k, lam)), S[lam] * q ** (3 * N - 6 * k - 3))
    return exp


def qrt_expected(q, N):
    """whole-stratum (x q centers) QRT-G2 keys incl. the (1^2) volume."""
    S = s_lam(q)
    exp = {}
    for h in range(1, N, 2):
        if 2 * h <= N - 1:
            for lam in ('11', '2', '1sq'):
                v = S[lam] * q ** (4 * N - 5 * h - 3) * q
                if v:
                    exp[('QRT-G2', (h, lam))] = v
    return exp


def l0hist_expected(q, N):
    """PER-CENTER history-resolved n=2 counts (LEMMA W12-L0)."""
    M = (N - 1) // 2
    out = {}

    def put(k, v):
        if v > 0:
            out[k] = out.get(k, 0) + v

    hists = []
    for r in range(M + 1):
        for tup in itertools.combinations(range(1, M + 1), r):
            hists.append(tup)
    for H in hists:
        s = max(H) if H else 0
        wt = (q - 1) ** len(H)
        for u in range(2 * s + 1, N):
            if u % 2 == 1:
                put(('RAM', (u,), H),
                    wt * (q - 1) * q ** (N - 1 - u)
                    * q ** (N - (u + 1) // 2))
            for w in range(s + 1, (u + 1) // 2):
                if 2 * w < u:
                    put(('2SIDED', (w, u - w), H),
                        wt * (q - 1) ** 2 * q ** (2 * N - 2 - u - w))
        for k in range(s + 1, M + 1):
            put(('SPLITEQ', (k,), H),
                wt * ((q - 1) * (q - 2) // 2) * q ** (2 * N - 3 * k - 2))
            put(('INERTDEEP', (k,), H),
                wt * (q * (q - 1) // 2) * q ** (2 * N - 3 * k - 2))
        for w in range(s + 1, M + 1):
            put(('SPLIT-TAIL', (w,), H), wt * (q - 1) * q ** (N - 1 - w))
        put(('UNDECIDED', (), H), wt * q ** (N - 1 - M))
    return out


# --------------------------------------------------------- level-0 helpers
def cubic_pattern(K, q, a2b, a1b, a0b):
    """pattern of xbar^3 + a2b x^2 + a1b x + a0b: returns
    ('SEP3'|'SEP12'|'IRR3', sigma) or ('DBL', cb, db) or ('TRP', cb)."""
    roots, cofdeg = kroots_mult(K, [a0b, a1b, a2b, K.one()])
    tot = sum(m for _, m in roots)
    if tot == 3:
        ms = sorted((m for _, m in roots), reverse=True)
        if ms == [1, 1, 1]:
            return ('SEP3', ((1, 1), (1, 1), (1, 1)))
        if ms == [2, 1]:
            cb = next(z for z, m in roots if m == 2)
            db = next(z for z, m in roots if m == 1)
            return ('DBL', cb, db)
        return ('TRP', roots[0][0])
    if tot == 1:
        return ('SEP12', ((1, 1), (1, 2)))
    return ('IRR3', ((1, 3),))


def lifts_of(R, abar):
    """all elements of O/pi^N with residue abar (q^(N-1) of them)."""
    if R.kind == 'Zp':
        base = abar % R.p
        return [base + R.p * t for t in range(R.p ** (R.N - 1))]
    K = R.K
    els = list(K.elems())
    return [(abar,) + rest
            for rest in itertools.product(els, repeat=R.N - 1)]


# =================================================== census row (cubic)
def run_cubic_row(kind, q, N, oracle_sink=None):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    lift_count = q ** (N - 1)
    # level-0 pattern census
    pat_count = {'SEP3': 0, 'SEP12': 0, 'IRR3': 0, 'DBL': 0, 'TRP': 0}
    kelems = list(K.elems())
    patterns = {}
    for a2b in kelems:
        for a1b in kelems:
            for a0b in kelems:
                pat = cubic_pattern(K, q, a2b, a1b, a0b)
                pat_count[pat[0]] += 1
                patterns[(a2b, a1b, a0b)] = pat
    c0exp = {'SEP3': q * (q - 1) * (q - 2) // 6,
             'SEP12': q * (q * q - q) // 2,
             'IRR3': (q ** 3 - q) // 3,
             'DBL': q * (q - 1), 'TRP': q}
    note('W12-LVL0', len(c0exp) + 1)
    for k2, v in c0exp.items():
        if pat_count[k2] != v:
            viol('W12-LVL0', 'census', '%s q=%d N=%d %s: obs %d exp %d'
                 % (kind, q, N, k2, pat_count[k2], v))
    if sum(pat_count.values()) != q ** 3:
        viol('W12-LVL0', 'sum', '%s q=%d N=%d' % (kind, q, N))
    sep_total = (pat_count['SEP3'] + pat_count['SEP12']
                 + pat_count['IRR3']) * q ** (3 * (N - 1))
    # ---- DBL stratum
    l0h = l0hist_expected(q, N)
    dbl_total = 0
    dbl_undec = 0
    l1x_bad = 0
    block_bad = 0
    dbl_keys_global = {}
    pat_uniform_bad = 0
    for (red, pat) in patterns.items():
        if pat[0] != 'DBL':
            continue
        cb, db = pat[1], pat[2]
        pairs = set()
        keys_here = {}
        for a2 in lifts_of(R, red[0]):
            for a1 in lifts_of(R, red[1]):
                for a0 in lifts_of(R, red[2]):
                    dbl_total += 1
                    g0, g1, r = hensel_split_dbl(R, q, a2, a1, a0, db)
                    # W12-BLOCK: explicit product identity
                    p2 = rsub(R, g1, r)
                    p1 = rsub(R, g0, R.mul(g1, r))
                    p0 = rneg(R, R.mul(g0, r))
                    if p2 != a2 or p1 != a1 or p0 != a0:
                        block_bad += 1
                    pairs.add((g0, g1, r))
                    rb = W11.classify_full(R, q, g0, g1)
                    kb = (rb['kind'], rb['params'], rb['hist'])
                    kd, pr, hs, sig = read_dbl(R, q, a2, a1, a0, cb)
                    if (kd, pr, hs) != kb:
                        l1x_bad += 1
                        if l1x_bad < 4:
                            viol('W12-L1X', 'read', '%s q=%d N=%d f=%s: '
                                 'direct %s block %s'
                                 % (kind, q, N, red, (kd, pr, hs), kb))
                    keys_here[kb] = keys_here.get(kb, 0) + 1
                    if kb[0] == 'UNDECIDED':
                        dbl_undec += 1
                    if oracle_sink is not None:
                        if kd == 'UNDECIDED':
                            oracle_sink.append((a2, a1, a0, None))
                        else:
                            full = tuple(sorted(sig))
                            oracle_sink.append((a2, a1, a0, full))
        note('W12-BLOCK', 2)
        if len(pairs) != q ** (3 * (N - 1)):
            viol('W12-BLOCK', 'bijection', '%s q=%d N=%d pat %s: %d pairs'
                 % (kind, q, N, red, len(pairs)))
        # per-pattern transported law: q^(N-1) x W12-L0 per key
        note('W12-DRAIN3', len(l0h))
        for kk, vv in ((k3, v3 * lift_count) for k3, v3 in l0h.items()):
            if keys_here.get(kk, 0) != vv:
                pat_uniform_bad += 1
                if pat_uniform_bad < 4:
                    viol('W12-DRAIN3', 'per-pattern', '%s q=%d N=%d pat '
                         '%s key %s: obs %d exp %d'
                         % (kind, q, N, red, kk, keys_here.get(kk, 0), vv))
        for kk in keys_here:
            if kk not in l0h and keys_here[kk]:
                pat_uniform_bad += 1
                viol('W12-DRAIN3', 'unpredicted-dbl-key',
                     '%s q=%d N=%d %s: %d' % (kind, q, N, kk,
                                              keys_here[kk]))
            dbl_keys_global[kk] = dbl_keys_global.get(kk, 0) \
                + keys_here[kk]
    note('W12-BLOCK', dbl_total)
    if block_bad:
        viol('W12-BLOCK', 'product', '%s q=%d N=%d: %d bad'
             % (kind, q, N, block_bad))
    note('W12-L1X', dbl_total)
    if l1x_bad:
        viol('W12-L1X', 'total', '%s q=%d N=%d: %d mismatches of %d'
             % (kind, q, N, l1x_bad, dbl_total))
    # ---- W12-L0HIST consistency: Sigma_H mine == sealed W-11 predictor
    agg = {}
    for (kd, pr, hs), v in l0hist_expected(q, N).items():
        agg[(kd, pr)] = agg.get((kd, pr), 0) + v
    w11p = W11.predict(q, N)
    note('W12-L0HIST', len(set(agg) | set(w11p)))
    for kk in set(agg) | set(w11p):
        if agg.get(kk, 0) != w11p.get(kk, 0):
            viol('W12-L0HIST', 'w11-aggregate', '%s q=%d N=%d %s: '
                 'mine %d w11 %d' % (kind, q, N, kk, agg.get(kk, 0),
                                     w11p.get(kk, 0)))
    # ---- TRP stratum
    trp_total = 0
    trp_undec = 0
    species_n = 0
    species_bad = 0
    depth0 = {}
    trp_deep_decided = 0
    for (red, pat) in patterns.items():
        if pat[0] != 'TRP':
            continue
        cb = pat[1]
        for a2 in lifts_of(R, red[0]):
            for a1 in lifts_of(R, red[1]):
                for a0 in lifts_of(R, red[2]):
                    trp_total += 1
                    rec = read_trp(R, q, a2, a1, a0, cb)
                    if rec['species']:
                        species_n += 1
                        if rec['decided']:
                            species_bad += 1
                    if not rec['decided']:
                        trp_undec += 1
                        if oracle_sink is not None:
                            oracle_sink.append((a2, a1, a0, None))
                        continue
                    if rec['depth0'] is not None:
                        depth0[rec['depth0']] = \
                            depth0.get(rec['depth0'], 0) + 1
                    else:
                        trp_deep_decided += 1
                    if oracle_sink is not None:
                        oracle_sink.append((a2, a1, a0, rec['sigma']))
    texp = trp_expected(q, N)
    note('W12-SHAPE', len(set(texp) | set(depth0)))
    for kk in sorted(set(texp) | set(depth0), key=repr):
        if texp.get(kk, 0) != depth0.get(kk, 0):
            viol('W12-SHAPE', 'law', '%s q=%d N=%d %s: obs %d exp %d'
                 % (kind, q, N, kk, depth0.get(kk, 0), texp.get(kk, 0)))
    # ---- drainage / partition
    note('W12-DRAIN3', 4)
    if sep_total + dbl_total + trp_total != q ** (3 * N):
        viol('W12-DRAIN3', 'partition', '%s q=%d N=%d' % (kind, q, N))
    dbl_law = (q - 1) * q ** (2 * N - 1)
    if dbl_undec != dbl_law:
        viol('W12-DRAIN3', 'dbl-drain', '%s q=%d N=%d: obs %d law %d'
             % (kind, q, N, dbl_undec, dbl_law))
    if species_bad or species_n != q ** N:
        viol('W12-DRAIN3', 'species', '%s q=%d N=%d: n=%d (exp %d) '
             'decided=%d' % (kind, q, N, species_n, q ** N, species_bad))
    # ---- teeth
    ram31 = depth0.get(('RAM3', (1,)), 0)
    corrupt = (q - 1) * q ** (3 * N - 2 - 1) * q      # exponent off by q
    note('W12-SHAPE', 1)
    if ram31 > 0 and ram31 != corrupt:
        FIRE['W12-T-SHAPE'] += 1
    else:
        viol('W12-SHAPE', 'tooth-shape-dead', '%s q=%d N=%d'
             % (kind, q, N))
    note('W12-DRAIN3', 1)
    if dbl_undec != (q - 1) * q ** (2 * N - 2):
        FIRE['W12-T-DRAIN'] += 1
    else:
        viol('W12-DRAIN3', 'tooth-drain-dead', '%s q=%d N=%d'
             % (kind, q, N))
    rec = {'kind': kind, 'q': q, 'N': N,
           'patterns': pat_count, 'sep_total': sep_total,
           'dbl_total': dbl_total, 'trp_total': trp_total,
           'dbl_undecided': dbl_undec,
           'U3TRP_measured_conservative': trp_undec,
           'species': species_n, 'trp_deep_decided': trp_deep_decided,
           'depth0_keys': {repr(k2): v for k2, v in sorted(
               depth0.items(), key=lambda kv: repr(kv[0]))},
           'dbl_keys': {repr(k2): v for k2, v in sorted(
               dbl_keys_global.items(), key=lambda kv: repr(kv[0]))},
           'elapsed_s': round(time.time() - t1, 1)}
    say('  [cubic %s q=%d N=%d] dbl=%d trp=%d dblU=%d U3TRP=%d '
        'depth0keys=%d deep=%d (%.1fs)'
        % (kind, q, N, dbl_total, trp_total, dbl_undec, trp_undec,
           len(depth0), trp_deep_decided, rec['elapsed_s']))
    return rec


# =================================================== quartic stratum row
def run_qrt_row(kind, q, N, oracle_sink=None):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    total = 0
    if kind == 'Zp':
        pivals = [y for y in range(R.M) if y % R.p == 0]
    else:
        pivals = [t for t in R.elems()
                  if R.val(t) is None or R.val(t) >= 1]
    for cb in K.elems():
        c = R.lift(cb)
        for B3 in pivals:
            for B2 in pivals:
                for B1 in pivals:
                    for B0 in pivals:
                        total += 1
                        key = classify_qrt(R, K, B3, B2, B1, B0)
                        if key is not None:
                            obs[key] = obs.get(key, 0) + 1
                            if oracle_sink is not None and \
                                    key[1][1] in ('11', '2'):
                                a3, a2, a1, a0 = shift4(
                                    R, B3, B2, B1, B0, rneg(R, c))
                                sig = (((2, 1), (2, 1))
                                       if key[1][1] == '11'
                                       else ((2, 2),))
                                oracle_sink.append(
                                    (a3, a2, a1, a0, sig, key))
    exp = qrt_expected(q, N)
    note('W12-QRT', len(set(exp) | set(obs)))
    for kk in sorted(set(exp) | set(obs), key=repr):
        if exp.get(kk, 0) != obs.get(kk, 0):
            viol('W12-QRT', 'law', '%s q=%d N=%d %s: obs %d exp %d'
                 % (kind, q, N, kk, obs.get(kk, 0), exp.get(kk, 0)))
    # tooth CENSUS4: S_(2) corrupted to q(q-1)
    note('W12-QRT', 1)
    o = obs.get(('QRT-G2', (1, '2')), 0)
    if o > 0 and o != q * (q - 1) * q ** (4 * N - 5 - 3) * q:
        FIRE['W12-T-CENSUS4'] += 1
    else:
        viol('W12-QRT', 'tooth-census4-dead', '%s q=%d N=%d'
             % (kind, q, N))
    rec = {'kind': kind, 'q': q, 'N': N, 'stratum_members': total,
           'keys': {repr(k2): v for k2, v in sorted(
               obs.items(), key=lambda kv: repr(kv[0]))},
           'elapsed_s': round(time.time() - t1, 1)}
    say('  [qrt %s q=%d N=%d] %d members, keys=%s (%.1fs)'
        % (kind, q, N, total, rec['keys'], rec['elapsed_s']))
    return rec


def classify_qrt(R, K, B3, B2, B1, B0):
    u0 = R.val(B0)
    if u0 is None:
        return None
    pts = [(0, u0), (1, R.val(B1)), (2, R.val(B2)), (3, R.val(B3)),
           (4, 0)]
    hv = hull(pts)
    if len(hv) != 2:
        return None
    if u0 % 4 != 2:
        return None
    h = u0 // 2                      # h odd
    r2 = R.res(B2, h)
    r0 = R.res(B0, u0)
    t, _ = quad_type(K, r2, r0)
    return ('QRT-G2', (h, t))


# =================================================== L0HIST row (quadratic)
def run_l0hist_row(kind, q, N):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    t1 = time.time()
    obs = {}
    total = 0
    for a0 in R.elems():
        for a1 in R.elems():
            total += 1
            rec = W11.classify_full(R, q, a0, a1)
            key = (rec['kind'], rec['params'], rec['hist'])
            obs[key] = obs.get(key, 0) + 1
    exp = {}
    for kk, v in l0hist_expected(q, N).items():
        exp[kk] = v * q                       # q centers
    nsep = (q * q - q) // 2 * q ** (2 * N - 2)
    exp[('SEP-SPLIT', (), ())] = nsep
    exp[('SEP-INERT', (), ())] = nsep
    note('W12-L0HIST', len(set(exp) | set(obs)))
    bad = 0
    for kk in sorted(set(exp) | set(obs), key=repr):
        if exp.get(kk, 0) != obs.get(kk, 0):
            bad += 1
            if bad < 6:
                viol('W12-L0HIST', 'hist-law', '%s q=%d N=%d %s: obs %d '
                     'exp %d' % (kind, q, N, kk, obs.get(kk, 0),
                                 exp.get(kk, 0)))
    if bad >= 6:
        viol('W12-L0HIST', 'hist-law-more', '%s q=%d N=%d: %d bad keys'
             % (kind, q, N, bad))
    maxd = max(len(kk[2]) for kk in obs)
    note('W12-L0HIST', 1)
    if maxd != (N - 1) // 2:
        viol('W12-L0HIST', 'depth', '%s q=%d N=%d: %d != %d'
             % (kind, q, N, maxd, (N - 1) // 2))
    rec = {'kind': kind, 'q': q, 'N': N, 'total': total,
           'hist_keys': len(obs), 'max_depth': maxd,
           'elapsed_s': round(time.time() - t1, 1)}
    say('  [l0hist %s q=%d N=%d] %d quadratics, %d keys, maxdepth %d '
        '(%.1fs)' % (kind, q, N, total, len(obs), maxd,
                     rec['elapsed_s']))
    return rec


# ====================================================== PARI oracle legs
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
sig3(a2, a1, a0, p) = sig(x^3 + a2*x^2 + a1*x + a0, p)
sig4(a3, a2, a1, a0, p) = sig(x^4 + a3*x^3 + a2*x^2 + a1*x + a0, p)
"""


def parse_sig(txt):
    """'[[1,1],[2,1]]' -> ((1,1),(2,1)) sorted."""
    nums = [int(x) for x in
            txt.replace('[', ' ').replace(']', ' ').replace(',', ' ')
            .split()]
    pairs = tuple(sorted(zip(nums[0::2], nums[1::2])))
    return pairs


def cubic_disc(a2, a1, a0):
    return (18 * a2 * a1 * a0 - 4 * a2 ** 3 * a0 + a2 ** 2 * a1 ** 2
            - 4 * a1 ** 3 - 27 * a0 ** 2)


def oracle_cubic(p, N):
    """full row: every decided cubic's sigma vs PARI; exact disc == 0
    ==> undecided (Python-exact integer disc); species witnesses."""
    t1 = time.time()
    sink = []
    rec_row = run_cubic_row('Zp', p, N, oracle_sink=sink)
    # sink: (a2, a1, a0, sigma or None); plus separable patterns are NOT
    # in the sink -- enumerate them here (small rows only)
    R = W10.ZpWin(p, N)
    K = R.K
    dec = []
    for (a2, a1, a0, sg) in sink:
        if sg is not None:
            dec.append((a2, a1, a0, sg))
    for a2b in K.elems():
        for a1b in K.elems():
            for a0b in K.elems():
                pat = cubic_pattern(K, p, a2b, a1b, a0b)
                if pat[0] in ('SEP3', 'SEP12', 'IRR3'):
                    for a2 in lifts_of(R, a2b):
                        for a1 in lifts_of(R, a1b):
                            for a0 in lifts_of(R, a0b):
                                dec.append((a2, a1, a0,
                                            tuple(sorted(pat[1]))))
    # disc == 0 bracket (exact integers, canonical lifts)
    note('W12-ORACLE', 1)
    d0_bad = 0
    for (a2, a1, a0, sg) in dec:
        if cubic_disc(a2, a1, a0) == 0:
            d0_bad += 1
            viol('W12-ORACLE', 'disc0-decided',
                 'p=%d N=%d f=(%d,%d,%d) decided %s but disc=0'
                 % (p, N, a2, a1, a0, sg))
    # PARI sigma per decided member
    lines = [GP_FUN]
    for i, (a2, a1, a0, sg) in enumerate(dec):
        lines.append('print("R %d ", sig3(%d,%d,%d,%d))'
                     % (i, a2, a1, a0, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = parse_sig(rest)
    nbad = 0
    note('W12-ORACLE', len(dec))
    if len(got) != len(dec):
        viol('W12-ORACLE', 'truncated', 'p=%d N=%d: %d of %d'
             % (p, N, len(got), len(dec)))
    for i, (a2, a1, a0, sg) in enumerate(dec):
        g = got.get(i)
        if g != sg:
            nbad += 1
            if nbad < 6:
                viol('W12-ORACLE', 'sigma', 'p=%d N=%d f=(%d,%d,%d): '
                     'oracle %s expect %s' % (p, N, a2, a1, a0, g, sg))
    if nbad >= 6:
        viol('W12-ORACLE', 'sigma-more', 'p=%d N=%d: %d bad'
             % (p, N, nbad))
    # ---- species ambiguity witnesses
    wit_lines = [GP_FUN]
    wits = []
    M = p ** N
    for cbar in range(p):
        c = cbar
        for tdig in range(p ** (N - 1)):
            b2 = p * tdig
            B = b2                       # canonical integer lift
            if B != 0:
                t = 0
                bb = B
                while bb % p == 0:
                    bb //= p
                    t += 1
                twoK1 = max(N, 2 * t + 2)
                if twoK1 % 2 == 0:
                    twoK1 += 1
                predA = ((1, 1), (1, 1), (1, 1))
                L = 3 * N
                if (L - t) % 2 == 0:
                    L += 1
                predB = ((1, 1), (2, 1))
                fa = expand_shift3(B, p ** twoK1, 0, c)
                fb = expand_shift3(B, 0, p ** L, c)
            else:
                twoK1 = N if N % 2 == 1 else N + 1
                predA = ((1, 1), (2, 1))
                L = 3 * N
                while L % 3 == 0:
                    L += 1
                predB = ((3, 1),)
                fa = expand_shift3(0, p ** twoK1, 0, c)
                fb = expand_shift3(0, 0, p ** L, c)
            i = len(wits)
            wits.append((predA, predB))
            wit_lines.append('print("A %d ", sig3(%d,%d,%d,%d))'
                             % (i, fa[0], fa[1], fa[2], p))
            wit_lines.append('print("B %d ", sig3(%d,%d,%d,%d))'
                             % (i, fb[0], fb[1], fb[2], p))
    wit_lines.append('quit')
    out = W10.gp_run('\n'.join(wit_lines) + '\n')
    gotA, gotB = {}, {}
    for line in out.splitlines():
        if line.startswith('A ') or line.startswith('B '):
            tag = line[0]
            idx, rest = line[2:].split(' ', 1)
            (gotA if tag == 'A' else gotB)[int(idx)] = parse_sig(rest)
    note('W12-ORACLE', 3 * len(wits))
    for i, (pa, pb) in enumerate(wits):
        ga, gb = gotA.get(i), gotB.get(i)
        if ga != pa:
            viol('W12-ORACLE', 'witnessA', 'p=%d N=%d i=%d: %s != %s'
                 % (p, N, i, ga, pa))
        if gb != pb:
            viol('W12-ORACLE', 'witnessB', 'p=%d N=%d i=%d: %s != %s'
                 % (p, N, i, gb, pb))
        if ga == gb:
            viol('W12-ORACLE', 'ambiguity', 'p=%d N=%d i=%d: sigma_A =='
                 ' sigma_B == %s' % (p, N, i, ga))
    say('  [oracle3 p=%d N=%d] %d decided scored, %d witnesses '
        '(%.1fs total incl. census)' % (p, N, len(dec), len(wits),
                                        time.time() - t1))
    return rec_row, {'p': p, 'N': N, 'decided_scored': len(dec),
                     'bad': nbad, 'witness_pairs': len(wits),
                     'disc0_bad': d0_bad}


def expand_shift3(B2, B1, B0, c):
    """integer coefficients of (x-c)^3 + B2 (x-c)^2 + B1 (x-c) + B0."""
    a2 = -3 * c + B2
    a1 = 3 * c * c - 2 * B2 * c + B1
    a0 = -c ** 3 + B2 * c * c - B1 * c + B0
    return (a2, a1, a0)


def oracle_qrt(p, N):
    t1 = time.time()
    sink = []
    rec_row = run_qrt_row('Zp', p, N, oracle_sink=sink)
    lines = [GP_FUN]
    for i, (a3, a2, a1, a0, sg, key) in enumerate(sink):
        lines.append('print("R %d ", sig4(%d,%d,%d,%d,%d))'
                     % (i, a3, a2, a1, a0, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = parse_sig(rest)
    nbad = 0
    note('W12-ORACLE', len(sink))
    for i, (a3, a2, a1, a0, sg, key) in enumerate(sink):
        g = got.get(i)
        if g != sg:
            nbad += 1
            if nbad < 6:
                viol('W12-ORACLE', 'qrt-sigma', 'p=%d N=%d %s: oracle %s'
                     ' expect %s' % (p, N, key, g, sg))
        # TOOTH T-SIGMA on the (2)-members: mis-keyed {(4,1)} must fail
        if key[1][1] == '2':
            note('W12-ORACLE', 1)
            if g is not None and g != ((4, 1),):
                FIRE['W12-T-SIGMA'] += 1
            else:
                viol('W12-ORACLE', 'tooth-sigma-dead', 'p=%d N=%d %s'
                     % (p, N, key))
    say('  [oracle4 p=%d N=%d] %d QRT members scored (%.1fs incl. '
        'stratum)' % (p, N, len(sink), time.time() - t1))
    return rec_row, {'p': p, 'N': N, 'qrt_scored': len(sink),
                     'bad': nbad}


# ------------------------------------------------------------- row lists
CUBIC_ROWS = [('Zp', 2, 3), ('Zp', 2, 4), ('Zp', 2, 5), ('Zp', 2, 6),
              ('Zp', 2, 7), ('Zp', 3, 2), ('Zp', 3, 3), ('Zp', 3, 4),
              ('Zp', 5, 2), ('Zp', 7, 2),
              ('Fqt', 2, 3), ('Fqt', 2, 4), ('Fqt', 2, 5), ('Fqt', 2, 6),
              ('Fqt', 2, 7), ('Fqt', 3, 2), ('Fqt', 3, 3), ('Fqt', 3, 4),
              ('Fqt', 4, 2), ('Fqt', 4, 3), ('Fqt', 5, 2), ('Fqt', 8, 2),
              ('Fqt', 9, 2)]
QRT_ROWS = [('Zp', 2, 3), ('Zp', 2, 4), ('Zp', 2, 5), ('Zp', 3, 3),
            ('Fqt', 2, 4), ('Fqt', 2, 5), ('Fqt', 3, 3), ('Fqt', 4, 3)]
L0HIST_ROWS = [('Zp', 2, 5), ('Zp', 2, 7), ('Zp', 3, 3), ('Zp', 5, 3),
               ('Zp', 7, 2),
               ('Fqt', 2, 5), ('Fqt', 2, 7), ('Fqt', 3, 3), ('Fqt', 4, 3),
               ('Fqt', 8, 2), ('Fqt', 9, 2)]
ORACLE3_ROWS = [(2, 3), (2, 4), (3, 2), (3, 3), (5, 2)]
ORACLE4_ROWS = [(2, 3), (2, 4), (3, 3)]

SMOKE_CUBIC = [('Zp', 2, 3), ('Zp', 2, 4), ('Zp', 3, 2), ('Fqt', 2, 3),
               ('Fqt', 4, 2)]
SMOKE_QRT = [('Zp', 2, 3), ('Zp', 3, 3)]
SMOKE_L0HIST = [('Zp', 2, 5), ('Fqt', 3, 3)]
SMOKE_ORACLE3 = [(2, 3), (3, 2)]
SMOKE_ORACLE4 = [(2, 3)]


def main(smoke=False):
    t0 = time.time()
    say('W12 SEALED BATTERY %s' % ('(SMOKE)' if smoke else '(FULL)'))
    # ---- pins
    for fn, md5 in PINS.items():
        note('W12-PIN')
        with open(os.path.join(HERE, fn), 'rb') as fh:
            h = hashlib.md5(fh.read()).hexdigest()
        if h != md5:
            viol('W12-PIN', 'moved', '%s: %s != %s' % (fn, h, md5))
    cubic_rows = SMOKE_CUBIC if smoke else CUBIC_ROWS
    qrt_rows = SMOKE_QRT if smoke else QRT_ROWS
    l0_rows = SMOKE_L0HIST if smoke else L0HIST_ROWS
    o3_rows = SMOKE_ORACLE3 if smoke else ORACLE3_ROWS
    o4_rows = SMOKE_ORACLE4 if smoke else ORACLE4_ROWS
    results = {'smoke': smoke, 'cubic': [], 'qrt': [], 'l0hist': [],
               'oracle3': [], 'oracle4': []}
    # oracle rows run the census WITH a sink (also produces census rec)
    oracle_cubic_set = {('Zp', p, N) for (p, N) in o3_rows}
    oracle_qrt_set = {('Zp', p, N) for (p, N) in o4_rows}
    say('== cubic census rows ==')
    for (kind, q, N) in cubic_rows:
        if (kind, q, N) in oracle_cubic_set:
            continue                       # run inside the oracle leg
        results['cubic'].append(run_cubic_row(kind, q, N))
    say('== quartic stratum rows ==')
    for (kind, q, N) in qrt_rows:
        if (kind, q, N) in oracle_qrt_set:
            continue
        results['qrt'].append(run_qrt_row(kind, q, N))
    say('== L0HIST rows ==')
    for (kind, q, N) in l0_rows:
        results['l0hist'].append(run_l0hist_row(kind, q, N))
    say('== oracle rows (cubic, with census) ==')
    for (p, N) in o3_rows:
        crec, orec = oracle_cubic(p, N)
        results['cubic'].append(crec)
        results['oracle3'].append(orec)
    say('== oracle rows (quartic, with stratum) ==')
    for (p, N) in o4_rows:
        qrec, orec = oracle_qrt(p, N)
        results['qrt'].append(qrec)
        results['oracle4'].append(orec)
    # ---- verdict
    say('== verdict ==')
    total_checks = sum(NCHK.values())
    nviol = sum(len(v) for v in VIOL.values())
    for f in FAMILIES:
        say('  %-12s checks=%-8d violations=%d'
            % (f, NCHK[f], len(VIOL[f])))
    red = nviol > 0
    for t in TEETH:
        say('  %-14s fired=%d' % (t, FIRE[t]))
        if FIRE[t] < 1:
            red = True
            say('  TOOTH DEAD: %s' % t)
    say('TOTAL: %d checks, %d violations, teeth %s -- %s (%.1fs)'
        % (total_checks, nviol,
           '/'.join(str(FIRE[t]) for t in TEETH),
           'RED' if red else 'GREEN', time.time() - t0))
    results['families'] = {f: {'checks': NCHK[f],
                               'violations': VIOL[f]} for f in FAMILIES}
    results['teeth'] = dict(FIRE)
    results['verdict'] = 'RED' if red else 'GREEN'
    results['elapsed_s'] = round(time.time() - t0, 1)
    if not smoke:
        with open(os.path.join(HERE, 'w12_checks_results.json'),
                  'w') as fh:
            json.dump(results, fh, indent=1, default=repr)
        with open(os.path.join(HERE, 'w12_checks_output.txt'),
                  'w') as fh:
            fh.write('\n'.join(LOG) + '\n')
    return 0 if not red else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
