#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
qscout22_checks.py -- SEALED BATTERY for QSCOUT22_2026-08-08.md
(the quartic (2,2) composite-stage scout: the two order-2 genres at the
quadruple center -- GENRE E (e-first: QRT-G2(h,(1sq)), key phi2 = x^2 -
z*pi^h, value-group index 2, half-integer slot lattice) and GENRE F
(f-first: FULL(k, psi^2), key phi2 = lift of psi, residue field F_{q^2})
-- read to full order-2 refinement history by an independent
division-based reader, tabulated, and compared BOTH DIRECTIONS against
the preregistered four-slot model predictor (the (2,2)-BRACKET model),
plus order-1 one-side laws (RAM4/G2/FULL/SUB incl. prehistory chains =
new W-12.A instances), J-D0 letter-uniformity, mixed-vs-eq-char
identity, and a PARI/GP sigma oracle.)

TWO-COMMIT SEAL.  Commit 1 = this runner + the note with S1/S2
preregistered (taxonomy, four-slot model, P-A..P-D, teeth), battery
UNRUN on the full roster; commit 2 = verdict appended to the note FROM
the committed artifacts (qscout22_output.txt / qscout22_results.json).
PRE-SEAL SMOKE DISCLOSED in the note S2 and below (main --smoke).

DISCLOSED CONVENTIONS (note S2/S7):
 * conservative tails: L1TAIL (v(B0) >= N at level 1), E/F 'UND'
   (hidden A0 beyond the SPLTAIL certification bound dv(A1) < N in
   doubled units resp. 2*v1(A1) < N), and the genre-F boundary band
   (an even dv0 >= N needs an out-of-window residual component) all
   exit UNDECIDED; no sigma is certified there.
 * canonical digit-lift letters in phi2 (lift-convention-keyed
   histories; the W-2/LIFTCORNER seam is NOT consumed).
 * VTX (vertex level-1 polygons) and L1TAIL are partition-checked
   buckets only (order-1 territory, no law claimed here).
 * genre F needs F_{q^2} arithmetic: prime q only in this kit; the
   roster never realizes genre F at q = 4 (4k <= N-1 fails there).
 * oracle legs mixed-characteristic (PARI factorpadic) only; eq-char
   rows are SAME-class evidence.

FAMILIES:
  Q22-PIN    [NONE] md5 pins of frozen imports (w10_checks, w12_checks)
  Q22-SUM    [SAME] full-row key partition Sigma == q^{4(N-1)} (B-space)
  Q22-W12TIE [SAME] order-1 one-side decided laws (G2 = the SEALED W-12
             law; RAM4/FULL/SUB = fresh W-12.A instances) both
             directions, prehistory chains included
  Q22-E      [SAME] every genre-E composite key == the four-slot model,
             BOTH directions (missing or unpredicted key = violation)
  Q22-F      [SAME] genre-F keys == the F_{q^2}-slot model, both dirs
  Q22-PRE    [SAME] prehistory rows == (q-1)^r x floored fresh law
  Q22-CONS   [SAME] constructive enumeration == full-sweep restriction
  Q22-JD0    [SAME] letter-resolved counts uniform per composite key
             (entry letter x first refinement letter)
  Q22-XCHAR  [SAME] Zp vs Fqt composite key tables identical at (q,N)
  Q22-ORACLE [IND]  PARI sigma multiset == reader sigma per decided
             composite member (sampled where large; disc != 0 lifts)
TEETH (each must fire >= 1 or the battery is RED):
  Q22-T-LAT  genre-E predictor collapsed to the INTEGER dv lattice
             (W-11 transported naively, no E=2 densification) must
             mismatch on every E row
  Q22-T-CEN  E-INERT census q(q-1)/2 -> q(q-1) must mismatch on every
             row realizing an INERT key
  Q22-T-ALPH genre-F census field q^2 -> q must mismatch on every F row
  Q22-T-SIG  F-RAM sigma {(2,2)} -> {(1,4)} must be caught by PARI on
             every F-RAM oracle member

Exact arithmetic; deterministic; PARI/GP subprocess.
"""

import sys, os, json, time, hashlib, itertools
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import w10_checks as W10
import w12_checks as W12

PINS = {
    'w10_checks.py': 'a9c34244a3af19f5fa864375b494380b',
    'w12_checks.py': '7dc040d94fbbb1e8d20ac817b665d418',
}

FAMILIES = ['Q22-PIN', 'Q22-SUM', 'Q22-W12TIE', 'Q22-E', 'Q22-F',
            'Q22-PRE', 'Q22-CONS', 'Q22-JD0', 'Q22-XCHAR', 'Q22-ORACLE']
TEETH = ['Q22-T-LAT', 'Q22-T-CEN', 'Q22-T-ALPH', 'Q22-T-SIG']

VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
LOG = []


def say(msg):
    print(msg)
    sys.stdout.flush()
    LOG.append(msg)


def note(fam, n=1):
    NCHK[fam] += n


def viol(fam, tag, detail):
    VIOL[fam].append((tag, detail))
    say('  VIOLATION [%s] %s: %s' % (fam, tag, detail))


# ring helpers from the sealed w12 (frozen import)
rzero, is_rzero = W12.rzero, W12.is_rzero
rneg, rsub, rint, rinv, pipow = (W12.rneg, W12.rsub, W12.rint,
                                 W12.rinv, W12.pipow)
shift4, hull, quad_type, kroots_mult, s_lam = (
    W12.shift4, W12.hull, W12.quad_type, W12.kroots_mult, W12.s_lam)


def elems_with_floor(R, m):
    """all elements of O/pi^N with v >= m (q^(N-m) of them; m >= 1)."""
    if m >= R.N:
        return [rzero(R)]
    if R.kind == 'Zp':
        return [R.p ** m * t for t in range(R.p ** (R.N - m))]
    els = list(R.K.elems())
    z = R.K.zero()
    return [(z,) * m + rest
            for rest in itertools.product(els, repeat=R.N - m)]


def relem(R, digits):
    """ring element with the given {height: K-digit} dict."""
    out = rzero(R)
    for h, d in digits.items():
        out = R.add(out, R.mul(R.lift(d), pipow(R, h)))
    return out


# ------------------------------------------------------- F_{q^2} field
class FExt(object):
    """F_{q^2} = K[y]/(y^2 + c1 y + c0), elements (a, b) = a*y + b."""

    def __init__(self, K, c1, c0):
        self.K, self.c1, self.c0 = K, c1, c0

    def elems(self):
        for a in self.K.elems():
            for b in self.K.elems():
                yield (a, b)

    def zero(self):
        return (self.K.zero(), self.K.zero())

    def one(self):
        return (self.K.zero(), self.K.one())

    def is_zero(self, x):
        return self.K.is_zero(x[0]) and self.K.is_zero(x[1])

    def add(self, x, y):
        return (self.K.add(x[0], y[0]), self.K.add(x[1], y[1]))

    def neg(self, x):
        return (self.K.neg(x[0]), self.K.neg(x[1]))

    def mul(self, x, y):
        K = self.K
        ac = K.mul(x[0], y[0])
        ad_bc = K.add(K.mul(x[0], y[1]), K.mul(x[1], y[0]))
        bd = K.mul(x[1], y[1])
        # y^2 = -c1 y - c0
        return (K.add(ad_bc, K.neg(K.mul(ac, self.c1))),
                K.add(bd, K.neg(K.mul(ac, self.c0))))


def irred_quads(K):
    """all (c1, c0) with y^2 + c1 y + c0 irreducible over K."""
    out = []
    for c1 in K.elems():
        for c0 in K.elems():
            roots, _ = kroots_mult(K, [c0, c1, K.one()])
            if not roots:
                out.append((c1, c0))
    return out


def quartic_res_type(K, r3, r2, r1, r0):
    """monic quartic residual y^4+r3y^3+r2y^2+r1y+r0 (r0 != 0):
    ('1111'|'112'|'22'|'13'|'4', None) separable decided;
    ('D211'|'D2Q'|'D22'|'D31', None) order-1 subsystems;
    ('D4', z) quadruple root; ('F', (c1,c0)) = psi^2, psi irreducible."""
    roots, cofdeg = kroots_mult(K, [r0, r1, r2, r3, K.one()])
    tot = sum(m for _, m in roots)
    if tot == 4:
        ms = sorted((m for _, m in roots), reverse=True)
        if ms == [1, 1, 1, 1]:
            return ('1111', None)
        if ms == [2, 1, 1]:
            return ('D211', None)
        if ms == [2, 2]:
            return ('D22', None)
        if ms == [3, 1]:
            return ('D31', None)
        return ('D4', roots[0][0])
    if tot == 2:
        if len(roots) == 2:
            return ('112', None)
        return ('D2Q', None)
    if tot == 1:
        return ('13', None)
    # tot == 0: cofactor degree 4: '4' | '22' | psi^2
    for (c1, c0) in irred_quads(K):
        # psi^2 = y^4 + 2c1 y^3 + (c1^2+2c0) y^2 + 2c1c0 y + c0^2
        two = K.add(K.one(), K.one())
        e3 = K.mul(two, c1)
        e2 = K.add(K.mul(c1, c1), K.mul(two, c0))
        e1 = K.mul(K.mul(two, c1), c0)
        e0 = K.mul(c0, c0)
        if (K.is_zero(K.add(r3, K.neg(e3)))
                and K.is_zero(K.add(r2, K.neg(e2)))
                and K.is_zero(K.add(r1, K.neg(e1)))
                and K.is_zero(K.add(r0, K.neg(e0)))):
            return ('F', (c1, c0))
    # divisible by two distinct irreducible quadratics, or irreducible
    for (c1, c0) in irred_quads(K):
        # divide by y^2+c1y+c0: remainder of the quartic
        q1 = K.add(r3, K.neg(c1))
        q0 = K.add(r2, K.neg(K.add(c0, K.mul(q1, c1))))
        rr1 = K.add(r1, K.neg(K.add(K.mul(q1, c0), K.mul(q0, c1))))
        rr0 = K.add(r0, K.neg(K.mul(q0, c0)))
        if K.is_zero(rr1) and K.is_zero(rr0):
            return ('22', None)
    return ('4', None)


# ------------------------------------------------------------ the reader
def divide_by_quad(R, B3, B2, B1, B0, p1, p0):
    """f = x^4+B3x^3+B2x^2+B1x+B0 = phi2^2 + A1 phi2 + A0,
    phi2 = x^2+p1x+p0.  Returns (a1, a0, b1, b0) with A1 = a1 x + a0,
    A0 = b1 x + b0."""
    q1 = rsub(R, B3, p1)
    q0 = rsub(R, rsub(R, B2, p0), R.mul(q1, p1))
    r1 = rsub(R, rsub(R, B1, R.mul(q1, p0)), R.mul(q0, p1))
    r0 = rsub(R, B0, R.mul(q0, p0))
    return rsub(R, q1, p1), rsub(R, q0, p0), r1, r0


def dv_E(R, h, a1, a0):
    """doubled v1-value of A = a1 x + a0 in genre E (v1(x) = h/2):
    (dv, slot) with slot in {'x','c'}; (None, None) if window-zero."""
    v1 = R.val(a1)
    v0 = R.val(a0)
    c1 = 2 * v1 + h if v1 is not None else None
    c0 = 2 * v0 if v0 is not None else None
    if c1 is None and c0 is None:
        return None, None
    if c0 is None or (c1 is not None and c1 < c0):
        return c1, 'x'
    return c0, 'c'


def dv_F(R, k, a1, a0):
    """v1-value of A = a1 x + a0 in genre F (v1(x) = k): integer."""
    v1 = R.val(a1)
    v0 = R.val(a0)
    c1 = v1 + k if v1 is not None else None
    c0 = v0
    if c1 is None and c0 is None:
        return None
    if c0 is None:
        return c1
    if c1 is None:
        return c0
    return min(c1, c0)


SIG_E = {'RAM': ((4, 1),), 'INERT': ((2, 2),),
         'SPLITEQ': ((2, 1), (2, 1)), '2SIDED': ((2, 1), (2, 1)),
         'SPLTAIL': ((2, 1), (2, 1)), 'UND': None}
SIG_F = {'RAM': ((2, 2),), 'INERT': ((1, 4),),
         'SPLITEQ': ((1, 2), (1, 2)), '2SIDED': ((1, 2), (1, 2)),
         'SPLTAIL': ((1, 2), (1, 2)), 'UND': None}


def read_E(R, K, q, h, z, B3, B2, B1, B0):
    """order-2 read, genre E at level-1 slope h/2 with residual double
    root z != 0.  Returns (H2, leaf, params, letters2)."""
    N = R.N
    p1 = rzero(R)
    p0 = rneg(R, R.mul(R.lift(z), pipow(R, h)))  # phi2 = x^2 - z*pi^h
    zinv = K.inv(z)
    H2, letters2 = [], []
    floor0 = 4 * h
    while True:
        a1, a0, b1, b0 = divide_by_quad(R, B3, B2, B1, B0, p1, p0)
        dv1, _s1 = dv_E(R, h, a1, a0)
        dv0, _s0 = dv_E(R, h, b1, b0)
        # lift-stability caps: a doubled value >= 2N can be undercut
        # by an out-of-window beta0/alpha0 digit of a lift -> hidden
        if dv1 is not None and dv1 >= 2 * N:
            dv1 = None
        if dv0 is not None and dv0 >= 2 * N:
            dv0 = None
        assert dv1 is None or dv1 > 2 * h, 'E: dv1 floor broken'
        if dv0 is not None and dv0 <= floor0:
            viol('Q22-E', 'floor', 'refined dv0 %d <= %d (h=%d H2=%s)'
                 % (dv0, floor0, h, H2))
        if dv0 is None:
            if dv1 is not None and dv1 < N:
                return tuple(H2), 'SPLTAIL', (dv1,), letters2
            return tuple(H2), 'UND', (), letters2
        if dv1 is not None and dv0 > 2 * dv1:
            return tuple(H2), '2SIDED', (dv1, dv0 - dv1), letters2
        if dv0 % 2 == 1:
            return tuple(H2), 'RAM', (dv0,), letters2
        dmu = dv0 // 2
        # S1 = A1's residual digit at doubled height dmu
        if dmu % 2 == 1:
            S1 = R.res(a1, (dmu - h) // 2)
        else:
            S1 = R.res(a0, dmu // 2)
        S0 = R.res(b0, dv0 // 2)                 # dv0 even => c-slot
        S0eff = K.mul(zinv, S0) if dmu % 2 == 1 else S0
        t, root = quad_type(K, S1, S0eff)
        if t == '11':
            return tuple(H2), 'SPLITEQ', (dmu,), letters2
        if t == '2':
            return tuple(H2), 'INERT', (dmu,), letters2
        s = root                                  # refine phi2 by s
        assert not K.is_zero(s)
        if dmu % 2 == 1:
            p1 = rsub(R, p1, R.mul(R.lift(s), pipow(R, (dmu - h) // 2)))
        else:
            p0 = rsub(R, p0, R.mul(R.lift(s), pipow(R, dmu // 2)))
        H2.append(dmu)
        letters2.append(repr(s))
        floor0 = dv0
        assert len(H2) < 4 * N, 'E: refinement runaway'


def read_F(R, K, q, k, psi, B3, B2, B1, B0):
    """order-2 read, genre F at integer slope k with residual psi^2."""
    N = R.N
    c1, c0 = psi
    F2 = FExt(K, c1, c0)
    p1 = R.mul(R.lift(c1), pipow(R, k))
    p0 = R.mul(R.lift(c0), pipow(R, 2 * k))
    H2, letters2 = [], []
    floor0 = 4 * k
    while True:
        a1, a0, b1, b0 = divide_by_quad(R, B3, B2, B1, B0, p1, p0)
        dv1 = dv_F(R, k, a1, a0)
        dv0 = dv_F(R, k, b1, b0)
        # lift-stability caps (integer units; bound N)
        if dv1 is not None and dv1 > N:
            dv1 = None
        if dv0 is not None and dv0 > N:
            dv0 = None
        assert dv1 is None or dv1 > 2 * k, 'F: dv1 floor broken'
        if dv0 is not None and dv0 <= floor0:
            viol('Q22-F', 'floor', 'refined dv0 %d <= %d (k=%d H2=%s)'
                 % (dv0, floor0, k, H2))
        if dv0 is None:
            if dv1 is not None and 2 * dv1 < N:
                return tuple(H2), 'SPLTAIL', (dv1,), letters2
            return tuple(H2), 'UND', (), letters2
        if dv1 is not None and dv0 > 2 * dv1:
            return tuple(H2), '2SIDED', (dv1, dv0 - dv1), letters2
        if dv0 % 2 == 1:
            return tuple(H2), 'RAM', (dv0,), letters2
        if dv0 == N:      # value stable but the S0 beta0-component is
            return tuple(H2), 'UND', (), letters2    # out of window
        dmu = dv0 // 2
        S1 = (R.res(a1, dmu - k), R.res(a0, dmu))
        S0 = (R.res(b1, dv0 - k), R.res(b0, dv0))
        t, root = quad_type(F2, S1, S0)
        if t == '11':
            return tuple(H2), 'SPLITEQ', (dmu,), letters2
        if t == '2':
            return tuple(H2), 'INERT', (dmu,), letters2
        sa, sb = root
        p1 = rsub(R, p1, R.mul(R.lift(sa), pipow(R, dmu - k)))
        p0 = rsub(R, p0, R.mul(R.lift(sb), pipow(R, dmu)))
        H2.append(dmu)
        letters2.append(repr(root))
        floor0 = dv0
        assert len(H2) < 4 * N, 'F: refinement runaway'


def read22(R, K, q, B3, B2, B1, B0):
    """the full quadruple-center read.  Returns (key, letters) with
    key one of:
      ('L1TAIL', pre) | ('VTX', pre, hullpts) | ('RAM4', pre, (u0,))
      ('G2', pre, (h, lam)) | ('FULL', pre, (k, lam))
      ('SUB', pre, (k, tag))
      ('E', pre, h, H2, leaf, params) | ('F', pre, k, H2, leaf, params)
    letters = (entry_letter_repr, first_refinement_letter_repr) for
    composite keys, else None."""
    pre = []
    preletters = []
    while True:
        u = [R.val(B0), R.val(B1), R.val(B2), R.val(B3)]
        if u[0] is None:
            return ('L1TAIL', tuple(pre)), None
        pts = [(0, u[0]), (1, u[1]), (2, u[2]), (3, u[3]), (4, 0)]
        hv = hull(pts)
        if len(hv) != 2:
            return ('VTX', tuple(pre), tuple(hv)), None
        u0 = u[0]
        g = gcd(u0, 4)
        if g == 1:
            return ('RAM4', tuple(pre), (u0,)), None
        if g == 2:
            h = u0 // 2
            r2 = R.res(B2, h)
            r0 = R.res(B0, u0)
            t, z = quad_type(K, r2, r0)
            if t != '1sq':
                return ('G2', tuple(pre), (h, t)), None
            H2, leaf, params, l2 = read_E(R, K, q, h, z, B3, B2, B1, B0)
            letters = (repr(('z', z, tuple(preletters))),
                       l2[0] if l2 else '-')
            return ('E', tuple(pre), h, H2, leaf, params), letters
        k = u0 // 4
        r3, r2, r1 = R.res(B3, k), R.res(B2, 2 * k), R.res(B1, 3 * k)
        r0 = R.res(B0, 4 * k)
        tag, data = quartic_res_type(K, r3, r2, r1, r0)
        if tag in ('1111', '112', '22', '13', '4'):
            return ('FULL', tuple(pre), (k, tag)), None
        if tag in ('D211', 'D2Q', 'D22', 'D31'):
            return ('SUB', tuple(pre), (k, tag)), None
        if tag == 'D4':
            z = data
            s = R.mul(R.lift(z), pipow(R, k))
            B3, B2, B1, B0 = shift4(R, B3, B2, B1, B0, s)
            pre.append(k)
            preletters.append(repr(z))
            assert len(pre) < R.N, 'prehistory runaway'
            continue
        # tag == 'F'
        H2, leaf, params, l2 = read_F(R, K, q, k, data, B3, B2, B1, B0)
        letters = (repr(('psi', data, tuple(preletters))),
                   l2[0] if l2 else '-')
        return ('F', tuple(pre), k, H2, leaf, params), letters


# ------------------------------------------------- the slot-model laws
def model_E(q, N, h, integer_lattice_only=False, inert_census=None):
    """genre-E composite keys per (center, entry letter):
    dict (H2, leaf, params) -> count.  The (2,2)-BRACKET model.
    integer_lattice_only / inert_census: tooth corruptions."""
    S1all = [s for s in range(2 * h + 1, 2 * (N - 1) + h + 1)
             if (s % 2 == 1 and (s - h) // 2 <= N - 1
                 and (s - h) // 2 >= (h + 1) // 2)
             or (s % 2 == 0 and s // 2 <= N - 1 and s // 2 >= h + 1)]
    S0all = [s for s in range(4 * h + 1, 2 * (N - 1) + h + 1)
             if (s % 2 == 1 and (s - h) // 2 <= N - 1
                 and (s - h) // 2 >= (3 * h + 1) // 2)
             or (s % 2 == 0 and s // 2 <= N - 1 and s // 2 >= 2 * h + 1)]
    if integer_lattice_only:
        S1all = [s for s in S1all if s % 2 == 0]
        S0all = [s for s in S0all if s % 2 == 0]
    c_11 = (q - 1) * (q - 2) // 2
    c_2 = q * (q - 1) // 2 if inert_census is None else inert_census
    c_sq = q - 1
    out = {}

    def put(key, v):
        if v:
            out[key] = out.get(key, 0) + v

    def rec(f1, f0, wt, H2):
        A1 = [s for s in S1all if s > f1]
        A0 = [s for s in S0all if s > f0]
        # slots at/above the lift-stability cap 2N are hidden-class
        deep0 = len([s for s in A0 if s >= 2 * N])
        for dv1 in A1:
            if dv1 < N:
                put((H2, 'SPLTAIL', (dv1,)),
                    wt * (q - 1) * q ** deep0
                    * q ** len([s for s in A1 if s > dv1]))
        put((H2, 'UND', ()), wt * q ** deep0
            * q ** len([s for s in A1 if s >= N]))
        for dv0 in A0:
            if dv0 >= 2 * N:
                continue                       # hidden-class slot
            nz0 = len([s for s in A0 if s > dv0])
            if dv0 % 2 == 1:
                free1 = len([s for s in A1 if 2 * s > dv0])
                put((H2, 'RAM', (dv0,)),
                    wt * (q - 1) * q ** (nz0 + free1))
            for dv1 in A1:
                if 2 * dv1 < dv0:
                    put((H2, '2SIDED', (dv1, dv0 - dv1)),
                        wt * (q - 1) ** 2
                        * q ** (nz0 + len([s for s in A1 if s > dv1])))
            if dv0 % 2 == 0:
                dmu = dv0 // 2
                free1 = len([s for s in A1 if s > dmu])
                base = wt * q ** (free1 + nz0)
                put((H2, 'SPLITEQ', (dmu,)), base * c_11)
                put((H2, 'INERT', (dmu,)), base * c_2)
                rec(dmu, dv0, wt * c_sq, H2 + (dmu,))

    rec(2 * h, 4 * h, 1, ())
    if not integer_lattice_only and inert_census is None:
        total = sum(out.values())
        want = q ** (len(S1all) + len(S0all))
        assert total == want, ('model_E partition %d != %d '
                               '(q=%d N=%d h=%d)' % (total, want,
                                                     q, N, h))
    return out


def model_F(q, N, k, alphabet_q=False):
    """genre-F composite keys per (center, psi): dict as model_E.
    alphabet_q: tooth corruption (censuses over F_q instead F_{q^2})."""
    Q = q if alphabet_q else q * q
    S1all = list(range(2 * k + 1, N + k))
    S0all = list(range(4 * k + 1, N + k))

    def comp(m):        # digit components at integer height m
        return 2 if m <= N - 1 else 1

    c_11 = (Q - 1) * (Q - 2) // 2
    c_2 = Q * (Q - 1) // 2
    c_sq = Q - 1
    out = {}

    def put(key, v):
        if v:
            out[key] = out.get(key, 0) + v

    def wfree(av, lo):
        e = sum(comp(s) for s in av if s > lo)
        return q ** e

    def rec(f1, f0, wt, H2):
        A1 = [s for s in S1all if s > f1]
        A0 = [s for s in S0all if s > f0]
        # slots above the lift-stability cap N are hidden-class
        deep0 = q ** sum(comp(s) for s in A0 if s > N)
        for dv1 in A1:
            if 2 * dv1 < N:
                put((H2, 'SPLTAIL', (dv1,)),
                    wt * (q ** comp(dv1) - 1) * wfree(A1, dv1) * deep0)
        put((H2, 'UND', ()),
            wt * deep0 * q ** sum(comp(s) for s in A1 if 2 * s >= N))
        for dv0 in A0:
            if dv0 > N:
                continue                       # hidden-class slot
            nz0 = wfree(A0, dv0)
            exact0 = q ** comp(dv0) - 1
            if dv0 % 2 == 1:
                free1 = q ** sum(comp(s) for s in A1 if 2 * s > dv0)
                put((H2, 'RAM', (dv0,)), wt * exact0 * nz0 * free1)
            for dv1 in A1:
                if 2 * dv1 < dv0:
                    put((H2, '2SIDED', (dv1, dv0 - dv1)),
                        wt * (q ** comp(dv1) - 1) * exact0
                        * wfree(A1, dv1) * nz0)
            if dv0 % 2 == 0:
                dmu = dv0 // 2
                onside1 = q ** sum(comp(s) for s in A1 if s > dmu)
                if dv0 == N:    # stable value, unreadable residual
                    put((H2, 'UND', ()),
                        wt * q ** comp(dmu) * exact0 * onside1 * nz0)
                else:
                    base = wt * onside1 * nz0
                    put((H2, 'SPLITEQ', (dmu,)), base * c_11)
                    put((H2, 'INERT', (dmu,)), base * c_2)
                    rec(dmu, dv0, wt * c_sq, H2 + (dmu,))

    rec(2 * k, 4 * k, 1, ())
    if not alphabet_q:
        total = sum(out.values())
        want = q ** sum(comp(s) for s in S1all + S0all)
        assert total == want, ('model_F partition %d != %d '
                               '(q=%d N=%d k=%d)' % (total, want,
                                                     q, N, k))
    return out


def s4_lam(q):
    """quartic residual censuses (nonzero constant term), incl. the
    repeated tags; row sum q^3(q-1)."""
    nq2 = (q * q - q) // 2
    d = {'1111': (q - 1) * (q - 2) * (q - 3) * (q - 4) // 24,
         '112': (q - 1) * (q - 2) // 2 * nq2,
         '22': nq2 * (nq2 - 1) // 2,
         '13': (q - 1) * (q ** 3 - q) // 3,
         '4': (q ** 4 - q * q) // 4,
         'D211': (q - 1) * (q - 2) * (q - 3) // 2,
         'D2Q': (q - 1) * nq2,
         'D22': (q - 1) * (q - 2) // 2,
         'D31': (q - 1) * (q - 2),
         'D4': q - 1,
         'F': nq2}
    assert sum(d.values()) == q ** 3 * (q - 1)
    return d


def ram4_exponent(N, u0):
    """B-space exponent of the RAM4(u0) law (q-1)q^e."""
    s = sum(-(-u0 * (4 - j) // 4) for j in range(4))    # ceil sum
    return 4 * N - s - 1


def pre_chains(N):
    """prehistory chains (k1<k2<...), each 4k_i <= N-1."""
    ks = [k for k in range(1, N) if 4 * k <= N - 1]
    chains = [()]
    for r in (1, 2, 3):
        for tup in itertools.combinations(ks, r):
            chains.append(tup)
    return chains


def expected_full(q, N, teeth=None):
    """B-space expected counts for every LAW key (order-1 one-side +
    SUB + composite E/F), prehistory chains included.  teeth: None or
    one of 'LAT','CEN','ALPH' (corrupted predictor for tooth checks)."""
    S4 = s4_lam(q)
    exp = {}

    def put(k, v):
        if v:
            exp[k] = exp.get(k, 0) + v

    for pre in pre_chains(N):
        wt = (q - 1) ** len(pre)
        kr = pre[-1] if pre else 0
        # RAM4
        for u0 in range(4 * kr + 1, N):
            if gcd(u0, 4) == 1:
                put(('RAM4', pre, (u0,)),
                    wt * (q - 1) * q ** ram4_exponent(N, u0))
        # G2 (h odd) + genre E
        h = 2 * kr + 1
        while 2 * h <= N - 1:
            vol = q ** (4 * N - 5 * h - 3)
            put(('G2', pre, (h, '11')), wt * (q - 1) * (q - 2) // 2 * vol)
            put(('G2', pre, (h, '2')), wt * q * (q - 1) // 2 * vol)
            mE = model_E(q, N, h,
                         integer_lattice_only=(teeth == 'LAT'),
                         inert_census=(q * (q - 1) if teeth == 'CEN'
                                       else None))
            for (H2, leaf, params), c in mE.items():
                put(('E', pre, h, H2, leaf, params), wt * (q - 1) * c)
            h += 2
        # FULL (integer slope) + SUB + genre F
        for k in range(kr + 1, N):
            if 4 * k > N - 1:
                break
            vol = q ** (4 * N - 10 * k - 4)
            for tag in ('1111', '112', '22', '13', '4'):
                put(('FULL', pre, (k, tag)), wt * S4[tag] * vol)
            for tag in ('D211', 'D2Q', 'D22', 'D31'):
                put(('SUB', pre, (k, tag)), wt * S4[tag] * vol)
            mF = model_F(q, N, k, alphabet_q=(teeth == 'ALPH'))
            for (H2, leaf, params), c in mF.items():
                put(('F', pre, k, H2, leaf, params), wt * S4['F'] * c)
    return exp


# --------------------------------------------------------- row runners
LAW_KINDS = ('RAM4', 'G2', 'FULL', 'SUB', 'E', 'F')


def key_str(k):
    return repr(k)


def compare_tables(fam, rowid, obs, exp, kinds=LAW_KINDS):
    n = 0
    for kk in sorted(set(list(obs) + list(exp)), key=repr):
        if kk[0] not in kinds:
            continue
        n += 1
        if obs.get(kk, 0) != exp.get(kk, 0):
            viol(fam, 'law', '%s %s: obs %d exp %d'
                 % (rowid, kk, obs.get(kk, 0), exp.get(kk, 0)))
    note(fam, n)
    return n


def tooth_check(tooth, q, N, obs, rowid, has):
    """corrupted predictor must MISmatch somewhere on this row."""
    exp_bad = expected_full(q, N, teeth={'Q22-T-LAT': 'LAT',
                                         'Q22-T-CEN': 'CEN',
                                         'Q22-T-ALPH': 'ALPH'}[tooth])
    kinds = ('E',) if tooth in ('Q22-T-LAT', 'Q22-T-CEN') else ('F',)
    mism = False
    for kk in set(list(obs) + list(exp_bad)):
        if kk[0] in kinds and obs.get(kk, 0) != exp_bad.get(kk, 0):
            mism = True
            break
    if has and mism:
        FIRE[tooth] += 1
    elif has and not mism:
        viol('Q22-E' if kinds == ('E',) else 'Q22-F',
             'tooth-dead', '%s on %s' % (tooth, rowid))


def jd0_check(rowid, letters_tab):
    """per composite key: counts uniform in entry letter, and in first
    refinement letter (where a refinement happened)."""
    for kk, sub in sorted(letters_tab.items(), key=lambda x: repr(x[0])):
        ent = {}
        refl = {}
        for (e, l2), c in sub.items():
            ent[e] = ent.get(e, 0) + c
            if l2 != '-':
                refl[l2] = refl.get(l2, 0) + c
        note('Q22-JD0', 2)
        if len(set(ent.values())) > 1:
            viol('Q22-JD0', 'entry-letter', '%s %s: %s'
                 % (rowid, kk, sorted(ent.values())))
        if refl and len(set(refl.values())) > 1:
            viol('Q22-JD0', 'refine-letter', '%s %s: %s'
                 % (rowid, kk, sorted(refl.values())))


def run_full_row(kind, q, N, oracle_sink=None, oracle_step=1):
    """sweep the whole B-space (pi O/pi^N)^4: q^{4(N-1)} members."""
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs, letters_tab = {}, {}
    tot = 0
    piv = elems_with_floor(R, 1)
    for B3 in piv:
        for B2 in piv:
            for B1 in piv:
                for B0 in piv:
                    key, letters = read22(R, K, q, B3, B2, B1, B0)
                    obs[key] = obs.get(key, 0) + 1
                    if letters is not None:
                        sub = letters_tab.setdefault(key, {})
                        sub[letters] = sub.get(letters, 0) + 1
                        if (oracle_sink is not None
                                and SIG_KEY(key) is not None
                                and tot % oracle_step == 0):
                            oracle_sink.append(
                                (B3, B2, B1, B0, SIG_KEY(key), key))
                    tot += 1
    rowid = 'full %s q=%d N=%d' % (kind, q, N)
    note('Q22-SUM', 1)
    if tot != q ** (4 * (N - 1)) or sum(obs.values()) != tot:
        viol('Q22-SUM', 'partition', '%s: %d vs %d'
             % (rowid, sum(obs.values()), tot))
    exp = expected_full(q, N)
    compare_tables_split(rowid, obs, exp)
    hasE = any(kk[0] == 'E' for kk in obs)
    hasFdeep = any(kk[0] == 'F' and (kk[4] in ('SPLITEQ', 'INERT')
                                     or kk[3]) for kk in obs)
    tooth_check('Q22-T-LAT', q, N, obs, rowid, hasE)
    tooth_check('Q22-T-CEN', q, N, obs, rowid,
                any(kk[0] == 'E' and kk[4] == 'INERT' for kk in obs))
    tooth_check('Q22-T-ALPH', q, N, obs, rowid, hasFdeep)
    jd0_check(rowid, letters_tab)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {key_str(k): v for k, v in sorted(
                obs.items(), key=lambda x: repr(x[0]))},
            'elapsed_s': round(time.time() - t1, 1)}, obs


def compare_tables_split(rowid, obs, exp):
    compare_tables('Q22-W12TIE', rowid, obs, exp,
                   kinds=('RAM4', 'G2', 'FULL', 'SUB'))
    compare_tables('Q22-E', rowid,
                   {k: v for k, v in obs.items() if k[0] == 'E'},
                   {k: v for k, v in exp.items() if k[0] == 'E'},
                   kinds=('E',))
    compare_tables('Q22-F', rowid,
                   {k: v for k, v in obs.items() if k[0] == 'F'},
                   {k: v for k, v in exp.items() if k[0] == 'F'},
                   kinds=('F',))
    pre_obs = {k: v for k, v in obs.items()
               if k[0] in LAW_KINDS and len(k[1]) > 0}
    pre_exp = {k: v for k, v in exp.items()
               if k[0] in LAW_KINDS and len(k[1]) > 0}
    compare_tables('Q22-PRE', rowid, pre_obs, pre_exp)


def SIG_KEY(key):
    if key[0] == 'E':
        return SIG_E[key[4]]
    if key[0] == 'F':
        return SIG_F[key[4]]
    return None


def cons_E_members(R, K, q, N, h):
    """constructive genre-E entry stratum: z in K^*, four free strings."""
    for z in K.elems():
        if K.is_zero(z):
            continue
        w = R.mul(R.lift(z), pipow(R, h))
        two = rint(R, 2)
        for a1 in elems_with_floor(R, (h + 1) // 2):
            B3 = a1
            for a0 in elems_with_floor(R, h + 1):
                B2 = rsub(R, a0, R.mul(two, w))
                B3w = R.mul(B3, w)
                for b1 in elems_with_floor(R, (3 * h + 1) // 2):
                    B1 = rsub(R, b1, B3w)
                    base0 = R.add(R.mul(B2, w), R.mul(w, w))
                    for b0 in elems_with_floor(R, 2 * h + 1):
                        B0 = rsub(R, b0, base0)
                        yield z, B3, B2, B1, B0


def run_cons_E(kind, q, N, h, full_obs=None, oracle_sink=None,
               oracle_step=1):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs, letters_tab = {}, {}
    tot = 0
    for z, B3, B2, B1, B0 in cons_E_members(R, K, q, N, h):
        key, letters = read22(R, K, q, B3, B2, B1, B0)
        if not (key[0] == 'E' and key[1] == () and key[2] == h):
            viol('Q22-CONS', 'escape', 'consE %s q=%d N=%d h=%d -> %s'
                 % (kind, q, N, h, key))
            continue
        obs[key] = obs.get(key, 0) + 1
        sub = letters_tab.setdefault(key, {})
        sub[letters] = sub.get(letters, 0) + 1
        if oracle_sink is not None and SIG_KEY(key) is not None \
                and tot % oracle_step == 0:
            oracle_sink.append((B3, B2, B1, B0, SIG_KEY(key), key))
        tot += 1
    rowid = 'consE %s q=%d N=%d h=%d' % (kind, q, N, h)
    exp = {('E', (), h, H2, leaf, params): (q - 1) * c
           for (H2, leaf, params), c in model_E(q, N, h).items()}
    compare_tables('Q22-E', rowid, obs, exp, kinds=('E',))
    for tooth, kw in (('Q22-T-LAT', {'integer_lattice_only': True}),
                      ('Q22-T-CEN', {'inert_census': q * (q - 1)})):
        bad = {('E', (), h, H2, leaf, params): (q - 1) * c
               for (H2, leaf, params), c
               in model_E(q, N, h, **kw).items()}
        armed = (tooth == 'Q22-T-LAT'
                 or any(kk[4] == 'INERT' for kk in obs))
        if armed:
            if bad != obs:
                FIRE[tooth] += 1
            else:
                viol('Q22-E', 'tooth-dead', '%s on %s' % (tooth, rowid))
    note('Q22-SUM', 1)
    if tot != (q - 1) * q ** (4 * N - 5 * h - 3):
        viol('Q22-SUM', 'entry-volume', '%s: %d != %d'
             % (rowid, tot, (q - 1) * q ** (4 * N - 5 * h - 3)))
    if full_obs is not None:
        note('Q22-CONS', 1)
        fr = {k: v for k, v in full_obs.items()
              if k[0] == 'E' and k[1] == () and k[2] == h}
        if fr != obs:
            viol('Q22-CONS', 'mismatch', rowid)
    jd0_check(rowid, letters_tab)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {key_str(k): v for k, v in sorted(
                obs.items(), key=lambda x: repr(x[0]))},
            'elapsed_s': round(time.time() - t1, 1)}, obs


def cons_F_members(R, K, q, N, k):
    two = rint(R, 2)
    for (c1, c0) in irred_quads(K):
        # residual pins: r3 = 2c1, r2 = c1^2+2c0, r1 = 2c1c0, r0 = c0^2
        pins = {3: K.mul(K.add(c1, c1), K.one()),
                2: K.add(K.mul(c1, c1), K.add(c0, c0)),
                1: K.mul(K.add(c1, c1), c0),
                0: K.mul(c0, c0)}
        Bs = []
        for j in (3, 2, 1, 0):
            ht = (4 - j) * k
            base = R.mul(R.lift(pins[j]), pipow(R, ht))
            Bs.append((base, ht))
        for t3 in elems_with_floor(R, k + 1):
            B3 = R.add(Bs[0][0], t3)
            for t2 in elems_with_floor(R, 2 * k + 1):
                B2 = R.add(Bs[1][0], t2)
                for t1v in elems_with_floor(R, 3 * k + 1):
                    B1 = R.add(Bs[2][0], t1v)
                    for t0 in elems_with_floor(R, 4 * k + 1):
                        B0 = R.add(Bs[3][0], t0)
                        yield (c1, c0), B3, B2, B1, B0


def run_cons_F(kind, q, N, k, full_obs=None, oracle_sink=None,
               oracle_step=1):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs, letters_tab = {}, {}
    tot = 0
    for psi, B3, B2, B1, B0 in cons_F_members(R, K, q, N, k):
        key, letters = read22(R, K, q, B3, B2, B1, B0)
        if not (key[0] == 'F' and key[1] == () and key[2] == k):
            viol('Q22-CONS', 'escape', 'consF %s q=%d N=%d k=%d -> %s'
                 % (kind, q, N, k, key))
            continue
        obs[key] = obs.get(key, 0) + 1
        sub = letters_tab.setdefault(key, {})
        sub[letters] = sub.get(letters, 0) + 1
        if oracle_sink is not None and SIG_KEY(key) is not None \
                and tot % oracle_step == 0:
            oracle_sink.append((B3, B2, B1, B0, SIG_KEY(key), key))
        tot += 1
    rowid = 'consF %s q=%d N=%d k=%d' % (kind, q, N, k)
    npsi = (q * q - q) // 2
    exp = {('F', (), k, H2, leaf, params): npsi * c
           for (H2, leaf, params), c in model_F(q, N, k).items()}
    compare_tables('Q22-F', rowid, obs, exp, kinds=('F',))
    if any(kk[4] in ('SPLITEQ', 'INERT') or kk[3] for kk in obs):
        bad = {('F', (), k, H2, leaf, params): npsi * c
               for (H2, leaf, params), c
               in model_F(q, N, k, alphabet_q=True).items()}
        if bad != obs:
            FIRE['Q22-T-ALPH'] += 1
        else:
            viol('Q22-F', 'tooth-dead', 'Q22-T-ALPH on %s' % rowid)
    note('Q22-SUM', 1)
    if tot != npsi * q ** (4 * N - 10 * k - 4):
        viol('Q22-SUM', 'entry-volume', '%s: %d != %d'
             % (rowid, tot, npsi * q ** (4 * N - 10 * k - 4)))
    if full_obs is not None:
        note('Q22-CONS', 1)
        fr = {kk: v for kk, v in full_obs.items()
              if kk[0] == 'F' and kk[1] == () and kk[2] == k}
        if fr != obs:
            viol('Q22-CONS', 'mismatch', rowid)
    jd0_check(rowid, letters_tab)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {key_str(kk): v for kk, v in sorted(
                obs.items(), key=lambda x: repr(x[0]))},
            'elapsed_s': round(time.time() - t1, 1)}, obs


def run_cons_pre(kind, q, N, k1, oracle_sink=None, oracle_step=1):
    """(1^4)@k1 prehistory row: enumerate the floor set + letter, map
    back through the inverse recentering, feed the reader."""
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    for z in K.elems():
        if K.is_zero(z):
            continue
        s = R.mul(R.lift(z), pipow(R, k1))
        ns = rneg(R, s)
        for B3p in elems_with_floor(R, k1 + 1):
            for B2p in elems_with_floor(R, 2 * k1 + 1):
                for B1p in elems_with_floor(R, 3 * k1 + 1):
                    for B0p in elems_with_floor(R, 4 * k1 + 1):
                        B3, B2, B1, B0 = shift4(R, B3p, B2p, B1p,
                                                B0p, ns)
                        key, letters = read22(R, K, q, B3, B2, B1, B0)
                        if not key[1] or key[1][0] != k1:
                            viol('Q22-PRE', 'not-pre',
                                 'pre %s q=%d N=%d k1=%d -> %s'
                                 % (kind, q, N, k1, key))
                            continue
                        obs[key] = obs.get(key, 0) + 1
                        if oracle_sink is not None \
                                and SIG_KEY(key) is not None \
                                and tot % oracle_step == 0:
                            oracle_sink.append((B3, B2, B1, B0,
                                                SIG_KEY(key), key))
                        tot += 1
    rowid = 'pre %s q=%d N=%d k1=%d' % (kind, q, N, k1)
    exp = {kk: v for kk, v in expected_full(q, N).items()
           if kk[1] and kk[1][0] == k1}
    obs_law = {kk: v for kk, v in obs.items() if kk[0] in LAW_KINDS}
    compare_tables('Q22-PRE', rowid, obs_law, exp)
    note('Q22-SUM', 1)
    if tot != (q - 1) * q ** (4 * N - 10 * k1 - 4):
        viol('Q22-SUM', 'pre-volume', '%s: %d != %d'
             % (rowid, tot, (q - 1) * q ** (4 * N - 10 * k1 - 4)))
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {key_str(kk): v for kk, v in sorted(
                obs.items(), key=lambda x: repr(x[0]))},
            'elapsed_s': round(time.time() - t1, 1)}, obs


# ------------------------------------------------------------- oracle
def quartic_disc(a3, a2, a1, a0):
    """exact integer disc of x^4+a3x^3+a2x^2+a1x+a0 (Sylvester 7x7)."""
    f = [1, a3, a2, a1, a0]
    fp = [4, 3 * a3, 2 * a2, a1]
    M = []
    for i in range(3):
        M.append([0] * i + f + [0] * (2 - i))
    for i in range(4):
        M.append([0] * i + fp + [0] * (3 - i))
    n = 7
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for c in range(n):
        pr = None
        for r in range(c, n):
            if A[r][c] != 0:
                pr = r
                break
        if pr is None:
            return 0
        if pr != c:
            A[c], A[pr] = A[pr], A[c]
            det = -det
        det *= A[c][c]
        inv = 1 / A[c][c]
        for r in range(c + 1, n):
            if A[r][c] != 0:
                fac = A[r][c] * inv
                for cc in range(c, n):
                    A[r][cc] -= fac * A[c][cc]
    assert det.denominator == 1
    return int(det)


def oracle_leg(p, N, sink, rowid, flip_fram=False):
    """PARI sigma per decided composite member.  flip_fram: tooth
    Q22-T-SIG (F-RAM predictions corrupted to ((1,4),))."""
    t1 = time.time()
    M = p ** N
    jobs = []
    for (B3, B2, B1, B0, sg, key) in sink:
        a3, a2, a1, a0 = B3 % M, B2 % M, B1 % M, B0 % M
        j = 0
        while quartic_disc(a3, a2, a1, a0 + j * M) == 0 and j < 6:
            j += 1
        jobs.append((a3, a2, a1, a0 + j * M, sg, key))
    lines = [W12.GP_FUN]
    for i, (a3, a2, a1, a0, sg, key) in enumerate(jobs):
        lines.append('print("R %d ", sig4(%d,%d,%d,%d,%d))'
                     % (i, a3, a2, a1, a0, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = W12.parse_sig(rest)
    note('Q22-ORACLE', len(jobs))
    if len(got) != len(jobs):
        viol('Q22-ORACLE', 'truncated', '%s: %d of %d'
             % (rowid, len(got), len(jobs)))
    nbad = 0
    fram_caught, fram_all = 0, 0
    for i, (a3, a2, a1, a0, sg, key) in enumerate(jobs):
        g = got.get(i)
        want = tuple(sorted(sg))
        if g != want:
            nbad += 1
            if nbad < 6:
                viol('Q22-ORACLE', 'sigma',
                     '%s f=(%d,%d,%d,%d) key=%s: oracle %s expect %s'
                     % (rowid, a3, a2, a1, a0, key, g, want))
        if key[0] == 'F' and key[4] == 'RAM':
            fram_all += 1
            if g != ((1, 4),):
                fram_caught += 1
    if nbad >= 6:
        viol('Q22-ORACLE', 'sigma-more', '%s: %d bad' % (rowid, nbad))
    if flip_fram and fram_all:
        if fram_caught == fram_all:
            FIRE['Q22-T-SIG'] += 1
        else:
            viol('Q22-ORACLE', 'tooth-sig-dead', '%s: %d/%d'
                 % (rowid, fram_caught, fram_all))
    say('  [oracle %s] %d scored, %d bad, F-RAM tooth %d/%d (%.1fs)'
        % (rowid, len(jobs), nbad, fram_caught, fram_all,
           time.time() - t1))
    return {'row': rowid, 'scored': len(jobs), 'bad': nbad,
            'fram': [fram_caught, fram_all],
            'elapsed_s': round(time.time() - t1, 1)}


def xchar_check(tag, obsA, obsB):
    """Zp vs Fqt composite tables identical (composite keys only)."""
    a = {k: v for k, v in obsA.items() if k[0] in ('E', 'F')}
    b = {k: v for k, v in obsB.items() if k[0] in ('E', 'F')}
    note('Q22-XCHAR', len(set(list(a) + list(b))))
    for kk in sorted(set(list(a) + list(b)), key=repr):
        if a.get(kk, 0) != b.get(kk, 0):
            viol('Q22-XCHAR', 'diff', '%s %s: Zp %d Fqt %d'
                 % (tag, kk, a.get(kk, 0), b.get(kk, 0)))


# ---------------------------------------------------------------- main
def main(smoke=False):
    t0 = time.time()
    say('QSCOUT22 battery -- %s' % ('SMOKE' if smoke else 'FULL ROSTER'))
    # pins
    for fn, want in PINS.items():
        with open(os.path.join(HERE, fn), 'rb') as fh:
            md5 = hashlib.md5(fh.read()).hexdigest()
        note('Q22-PIN')
        if want is not None and md5 != want:
            viol('Q22-PIN', 'moved', '%s md5 %s != %s' % (fn, md5, want))
        say('  pin %s = %s' % (fn, md5))

    results = {'rows': [], 'oracle': [], 'smoke': smoke}
    full_tabs = {}

    if smoke:
        FULL = [('Zp', 2, 4), ('Zp', 2, 5), ('Zp', 3, 4), ('Fqt', 2, 5)]
        CONSE = [('Zp', 2, 6, 1), ('Fqt', 2, 6, 1)]
        CONSF = [('Zp', 2, 7, 1)]
        CONSP = [('Zp', 2, 7, 1)]
        ORACLE_FULL = [('Zp', 2, 5, 1), ('Zp', 3, 4, 1)]
    else:
        FULL = [('Zp', 2, 4), ('Zp', 2, 5), ('Zp', 2, 6), ('Zp', 3, 4),
                ('Zp', 5, 3), ('Fqt', 2, 5), ('Fqt', 3, 4),
                ('Fqt', 4, 3)]
        CONSE = [('Zp', 2, 6, 1), ('Zp', 2, 7, 1), ('Zp', 2, 7, 3),
                 ('Zp', 3, 5, 1), ('Zp', 5, 4, 1), ('Fqt', 2, 6, 1),
                 ('Fqt', 4, 4, 1)]
        CONSF = [('Zp', 2, 7, 1), ('Zp', 2, 8, 1), ('Zp', 3, 6, 1),
                 ('Zp', 5, 5, 1), ('Fqt', 2, 7, 1), ('Fqt', 3, 5, 1)]
        CONSP = [('Zp', 2, 7, 1), ('Zp', 2, 8, 1)]
        ORACLE_FULL = [('Zp', 2, 5, 1), ('Zp', 2, 6, 4), ('Zp', 3, 4, 1),
                       ('Zp', 5, 3, 1)]

    oracle_sinks = {}
    for (kind, q, N) in FULL:
        step = dict((('Zp', a, b), c) for (x, a, b, c) in ORACLE_FULL
                    if x == 'Zp').get((kind, q, N))
        sink = [] if (kind == 'Zp' and step) else None
        rec, obs = run_full_row(kind, q, N, oracle_sink=sink,
                                oracle_step=step or 1)
        results['rows'].append(rec)
        full_tabs[(kind, q, N)] = obs
        if sink:
            oracle_sinks['full Zp q=%d N=%d' % (q, N)] = (q, N, sink)

    for (kind, q, N, h) in CONSE:
        fo = full_tabs.get((kind, q, N))
        st = {(2, 6, 1): 64, (2, 7, 1): 512, (2, 7, 3): 8,
              (3, 5, 1): 1024, (5, 4, 1): 1024}.get((q, N, h), 64)
        sink = [] if kind == 'Zp' and not smoke else None
        rec, obs = run_cons_E(kind, q, N, h, full_obs=fo,
                              oracle_sink=sink, oracle_step=st)
        results['rows'].append(rec)
        full_tabs[('consE', kind, q, N, h)] = obs
        if sink:
            oracle_sinks[rec['row']] = (q, N, sink)

    for (kind, q, N, k) in CONSF:
        fo = full_tabs.get((kind, q, N))
        st = {(2, 7): 8, (2, 8): 64, (3, 6): 64, (5, 5): 64}.get(
            (q, N), 8)
        sink = [] if kind == 'Zp' and not smoke else None
        rec, obs = run_cons_F(kind, q, N, k, full_obs=fo,
                              oracle_sink=sink, oracle_step=st)
        results['rows'].append(rec)
        full_tabs[('consF', kind, q, N, k)] = obs
        if sink:
            oracle_sinks[rec['row']] = (q, N, sink)

    for (kind, q, N, k1) in CONSP:
        sink = [] if kind == 'Zp' and not smoke else None
        rec, obs = run_cons_pre(kind, q, N, k1, oracle_sink=sink,
                                oracle_step=16)
        results['rows'].append(rec)
        if sink:
            oracle_sinks[rec['row']] = (q, N, sink)

    # cross-characteristic identity
    pairs = []
    seen = [key for key in full_tabs
            if len(key) == 3 and key[0] in ('Zp', 'Fqt')]
    for key in seen:
        if key[0] == 'Zp' and ('Fqt', key[1], key[2]) in full_tabs:
            pairs.append((key[1], key[2]))
    for (q, N) in pairs:
        xchar_check('full q=%d N=%d' % (q, N),
                    full_tabs[('Zp', q, N)], full_tabs[('Fqt', q, N)])
    for tag in [('consE', 2, 6, 1), ('consF', 2, 7, 1)]:
        a = full_tabs.get((tag[0], 'Zp', tag[1], tag[2], tag[3]))
        b = full_tabs.get((tag[0], 'Fqt', tag[1], tag[2], tag[3]))
        if a is not None and b is not None:
            xchar_check('%s q=%d N=%d p=%d' % tag, a, b)

    # oracle legs (mixed characteristic only); T-SIG on every F leg
    for rowid, (q, N, sink) in sorted(oracle_sinks.items()):
        if not sink:
            continue
        hasF = any(key[0] == 'F' and key[4] == 'RAM'
                   for (_, _, _, _, _, key) in sink)
        results['oracle'].append(
            oracle_leg(q, N, sink, rowid, flip_fram=hasF))

    # ---- verdict
    say('')
    say('== FAMILY TOTALS ==')
    red = False
    for f in FAMILIES:
        say('  %-11s checks %-8d violations %d'
            % (f, NCHK[f], len(VIOL[f])))
        if VIOL[f]:
            red = True
    say('== TEETH ==')
    for t in TEETH:
        say('  %-11s fired %d' % (t, FIRE[t]))
        if FIRE[t] == 0:
            red = True
            say('  RED: tooth %s never fired' % t)
    say('== %s (%.1fs) ==' % ('RED' if red else 'GREEN',
                              time.time() - t0))
    results['families'] = {f: [NCHK[f], len(VIOL[f]),
                               VIOL[f][:20]] for f in FAMILIES}
    results['teeth'] = dict(FIRE)
    results['verdict'] = 'RED' if red else 'GREEN'
    results['elapsed_s'] = round(time.time() - t0, 1)
    suff = '_smoke' if smoke else ''
    with open(os.path.join(HERE, 'qscout22_results%s.json' % suff),
              'w') as fh:
        json.dump(results, fh, indent=1, default=repr)
    with open(os.path.join(HERE, 'qscout22_output%s.txt' % suff),
              'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    return 0 if not red else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
