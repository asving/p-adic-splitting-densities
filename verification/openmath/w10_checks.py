#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
w10_checks.py -- SEALED BATTERY for W10_PROOF_2026-08-08.md
(W-10 at the (2,1,1) shape: the stratum-count equality -- classifier
stratum count = model-side count L3 x q^B assembled from the shape data
(d0=1; one read (e,h,g)=(2,1,1)) -- at every tested prime power q, BOTH
residue characteristics, wild p=2 included).

TWO-COMMIT SEAL.  Commit 1 = this runner + the note with its preregistered
predictions, battery UNRUN on the full roster; commit 2 = the verdict
appended to the note FROM the committed artifacts (w10_checks_output.txt /
w10_checks_results.json).  PRE-SEAL SMOKE DISCLOSED: developed and debugged
with `--smoke` (census rows (Zp,2,2),(Zp,3,2),(Fqt,4,2); towers C2A,C2C;
oracle rows p=2,N=3 impl + p=3,N=2 conv); observed on the smoke rows: all
violation families 0, all teeth firing.  No full run happened before the
seal.
DEVICE PROBES DISCLOSED (pre-seal): the tower polygon-record probe on
C2A/C2C/J7A (records [[0,gam],[eg,0]]; gam = e*wPhi+h observed) and the
`gp` availability probe (factorpadic(x^2+2x+2,2,10) irreducible) ran
before composition; both are quoted in the note's S5.

THE COUNT UNDER TEST (note S0/S2).  Fix the decided order-1 shape
T(2,1,1): d0 = 1 (level-0 factor of degree 1) and ONE read
(e,h,g) = (2,1,1).  Over a local ring O with residue field F_q and
uniformizer pi, at truncation window N >= 2 (coefficients in O/pi^N):

  CLASSIFIER side: enumerate ALL monic quadratics f = x^2 + a1 x + a0
    over O/pi^N; run the classifier read on each: reduction fbar; level-0
    factorization (double root cbar or separable); recenter g = f(x+c),
    c a lift of cbar; Newton polygon of g by LOWER-HULL COMPUTATION on
    {(0,v(a0')), (1,v(a1')), (2,0)}; f is in the stratum iff the polygon
    is ONE side from (0,1) to (2,0) (interior point strictly above),
    i.e. side data (e,h,g) = (2,1,1), residual degree 1 (decided), letter
    = res(a0'/pi) != 0.
  MODEL side (the shape-only assembly J-D0 licenses):
    L3(level 0) x L3(level 1) x q^B
    = [# monic degree-1 residual polys over F_q = q  (the center menu)]
    x [# monic degree-1 residual polys with nonzero constant = q-1
       (the letter menu, psi(0) != 0)]
    x q^(2N-3)  (B = 2N - 3: of the 2N digit positions, a0' digit 0 and
       a1' digit 0 are pinned to 0 by the side, a0' digit 1 is the letter
       slot priced in L3; the rest are free).
  EQUALITY UNDER TEST (exact integers, per row):
    census == q * (q-1) * q^(2N-3);  density census/q^(2N) == (q-1)/q^2
    (full stratum) and (q-1)/q^3 per center (the WELD_SYNTHESIS 3.1 row).

WHAT IS KEYED (note section in brackets):

  W10-PIN     md5 pins of the frozen imports (violation if moved).
  W10-CENSUS  [S2]  the count equality, exact, on every census row; PLUS
              the product-form refinement: the per-(center,letter) cell
              counts are ALL equal to q^(2N-3) (the L3 x L4 factorization
              of the count, cell by cell).
  W10-RECENTER[S2.1] per-center counts all equal (q-1)q^(2N-3) with
              exactly q centers realized; lift-independence on sampled
              members (recenter with c and c+pi: same verdict, same
              letter -- the representative-independence face at the
              instance).
  W10-TOWER   [S2.3] the frozen-roster realization leg: on the named
              tower subset, every realized (2,1,1) level's polygon record
              has endpoints (0, gam_{j+1}), (2, 0) with gam_{j+1} odd,
              any interior point strictly above the side, and the grid
              tie gam_{j+1} == e_j * wPhi_j + h_j; at least one WILD
              realization (char | e) must appear.
  W10-ORACLE  [S2.4] the INDEPENDENT engine (PARI/GP, subprocess `gp`):
              (a) IMPLICATION leg -- every centered stratum member at the
              Zp oracle rows, lifted to Z[x]: nfinit/idealprimedec gives
              ONE prime, e = 2, f = 1, and v_p(disc) == 1 at p odd /
              in {2,3} at p = 2 by the v(a1') rule (=2 iff v(a1')==1);
              (b) CONVERSE leg (p odd, N=2, ALL q^(2N) polynomials):
              oracle membership {irreducible over Q_p, e=2, f=1,
              v_p(disc)=1} == classifier membership, PER POLYNOMIAL (set
              equality, not just count equality).

  INTERIOR-FREE (scored, W10-CENSUS): at THIS shape the polygon's
  interior pin v(a1') >= 1 is IMPLIED by the level-0 double-root
  condition (a1'bar = fbar'(cbar) = 0), so the endpoint-only hull agrees
  with the full hull POINTWISE; scored per polynomial.  DISCLOSED: the
  originally drafted blind-hull tooth is structurally dead at (2,1,1)
  quadratics for exactly this reason (found at smoke) and was REPLACED
  pre-seal by W10-T-VEXACT / W10-T-CENTER0 below; at deeper shapes the
  interior points are genuine pins.

  TEETH (each must fire >= 1 GLOBALLY or the battery is RED):
  W10-T-VEXACT   the classifier corrupted to accept v(a0') >= 1 (instead
                 of == 1; exactness of the letter valuation = decidedness
                 forgotten) must OVERCOUNT on every census row.
  W10-T-CENTER0  the classifier corrupted to recenter at cbar = 0 only
                 (the level-0 factor menu forgotten) must UNDERCOUNT on
                 every census row.
  W10-T-LETTER0  the model with the letter 0 admitted (L3 = q instead of
                 q-1, i.e. psi(0) != 0 forgotten) must mismatch the
                 census on every row (decidedness is load-bearing).
  W10-T-TAMEDISC the tame discriminant prediction v(disc) = e-1 = 1 must
                 FAIL on EVERY p = 2 stratum member (the wild rows are
                 genuinely wild; the count equality holds there anyway --
                 J-D0 S3 made concrete).

CENSUS ROWS.  Zp (mixed char, q = p): (p,N) in {2,3,5,7} x {2,3} and
(2,4).  Fq[[t]] (equal char, prime-power q): q in {2,3,4,5,7,8,9},
N in {2,3}; F4 = F2[y]/(y^2+y+1), F8 = F2[y]/(y^3+y+1),
F9 = F3[y]/(y^2+1) built on the frozen GFp/Ext classes.  23 rows,
~1.08M polynomials, exact arithmetic, no floats.  Wild realizations:
every p = 2 / char-2 row (char divides e = 2).  DISCLOSED LIMIT: no
mixed-characteristic prime-power rows (no frozen unramified-base ring);
prime-power q is carried by the eq-char rows; the oracle leg is
mixed-char only (PARI factorpadic is Q_p-only).

TOWER SUBSET (frozen roster by md5-pinned import): C2A, C2C, C2E, C2F,
P3A from grt_jc_probe.ROSTER / jd0_checks.PAIR_MEMBERS + J7A, P1B from
jd0_checks (P7_GENRE / PAIR_MEMBERS).  Wild (2,1,1) levels: C2A (both,
p=2), C2E (eq-char 2), P1B (p=2), P3A level 0 is (3,1,1) at p=3 -- its
(2,1,1) levels are tame; J7A/C2C/C2F tame (2,1,1) levels.

FROZEN-IMPORT PINS (W10-PIN; violation if a pinned file's md5 moved):
  iterlawn_pe_reimpl.py  cae45db2318b89520dd5484466ef3604
  grt_jc_probe.py        03811b695cf7aa1bd5b52d5b0cd8bcd6
  jd0_checks.py          d3a5e13df97d3768573800960a0ec509

Exact arithmetic throughout; deterministic; oracle = PARI/GP subprocess.
"""

import sys, os, json, time, hashlib, subprocess, itertools
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import iterlawn_pe_reimpl as ITL
import grt_jc_probe as JCP
import jd0_checks as JD0

PINS = {
    'iterlawn_pe_reimpl.py': 'cae45db2318b89520dd5484466ef3604',
    'grt_jc_probe.py':       '03811b695cf7aa1bd5b52d5b0cd8bcd6',
    'jd0_checks.py':         'd3a5e13df97d3768573800960a0ec509',
}

FAMILIES = ['W10-PIN', 'W10-CENSUS', 'W10-RECENTER', 'W10-TOWER',
            'W10-ORACLE']
TEETH = ['W10-T-VEXACT', 'W10-T-CENTER0', 'W10-T-LETTER0',
         'W10-T-TAMEDISC']

VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}


def note(fam, n=1):
    NCHK[fam] += n


def viol(fam, tag, detail):
    VIOL[fam].append((tag, detail))
    print('  VIOLATION [%s] %s: %s' % (fam, tag, detail))


# ------------------------------------------------------------ residue fields
def GF(q):
    """residue field F_q on the frozen GFp/Ext classes; returns (K, p, k)."""
    if q in (2, 3, 5, 7, 11):
        return ITL.GFp(q), q, 1
    if q == 4:
        return ITL.Ext(ITL.GFp(2), (1, 1, 1)), 2, 2          # y^2+y+1
    if q == 8:
        return ITL.Ext(ITL.GFp(2), (1, 1, 0, 1)), 2, 3       # y^3+y+1
    if q == 9:
        return ITL.Ext(ITL.GFp(3), (1, 0, 1)), 3, 2          # y^2+1
    raise ValueError(q)


def kpow(K, z, n):
    r = K.one()
    for _ in range(n):
        r = K.mul(r, z)
    return r


def sqrt_char2(K, a, k):
    """unique square root in F_{2^k}: a^(2^(k-1))."""
    return kpow(K, a, 2 ** (k - 1))


# ------------------------------------------------------------ census rings
class ZpWin(object):
    """Z_p truncated at pi^N: elements = ints in [0, p^N)."""
    kind = 'Zp'

    def __init__(self, p, N):
        self.p, self.N, self.M = p, N, p ** N
        self.K = ITL.GFp(p)
        self.k = 1

    def elems(self):
        return range(self.M)

    def add(self, a, b):
        return (a + b) % self.M

    def mul(self, a, b):
        return (a * b) % self.M

    def val(self, a):
        if a % self.M == 0:
            return None                      # >= N at this window
        a, v = a % self.M, 0
        while a % self.p == 0:
            a //= self.p
            v += 1
        return v

    def res(self, a, w):
        return ((a % self.M) // self.p ** w) % self.p

    def lift(self, c):
        return c % self.p

    def pi(self):
        return self.p


class FqtWin(object):
    """F_q[[t]] truncated at t^N: elements = tuples of K-elems, len N."""
    kind = 'Fqt'

    def __init__(self, q, N):
        self.q, self.N = q, N
        self.K, self.p, self.k = GF(q)

    def elems(self):
        els = list(self.K.elems())
        return itertools.product(els, repeat=self.N)

    def add(self, a, b):
        return tuple(self.K.add(x, y) for x, y in zip(a, b))

    def mul(self, a, b):
        K, N = self.K, self.N
        out = [K.zero()] * N
        for i, x in enumerate(a):
            if K.is_zero(x):
                continue
            for j, y in enumerate(b):
                if i + j >= N:
                    break
                out[i + j] = K.add(out[i + j], K.mul(x, y))
        return tuple(out)

    def val(self, a):
        for i, c in enumerate(a):
            if not self.K.is_zero(c):
                return i
        return None

    def res(self, a, w):
        return a[w] if w < len(a) else self.K.zero()

    def lift(self, c):
        return (c,) + (self.K.zero(),) * (self.N - 1)

    def pi(self):
        K = self.K
        return (K.zero(), K.one()) + (K.zero(),) * (self.N - 2)


# ------------------------------------------------------------ the classifier
def lower_hull(pts):
    """lower convex hull of [(i, v)] with v = None meaning +infinity;
    returns the list of hull vertices (i, v), left to right."""
    fin = [(i, v) for (i, v) in pts if v is not None]
    hull = []
    for pt in fin:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # drop (x2,y2) if not strictly below the chord (x1,y1)-(pt)
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


def classify(R, a0, a1, lift_shift=0):
    """the classifier read of f = x^2 + a1 x + a0 over R = O/pi^N.
    Returns (bucket, center, letter):
      bucket in {'sep','211','vertex','side-e1','side-2h','deep'};
      center = cbar (residue-field elem) when the reduction has a double
      root, else None; letter = res(a0'/pi) for '211' members."""
    K, k = R.K, R.k
    a0b, a1b = R.res(a0, 0), R.res(a1, 0)
    # level-0: double root of fbar = x^2 + a1b x + a0b over K?
    if R.p == 2:
        if not K.is_zero(a1b):
            return 'sep', None, None         # disc = a1b^2 != 0
        cb = sqrt_char2(K, a0b, k)
    else:
        four = K.add(K.add(K.one(), K.one()), K.add(K.one(), K.one()))
        disc = K.add(K.mul(a1b, a1b), K.neg(K.mul(four, a0b)))
        if not K.is_zero(disc):
            return 'sep', None, None
        inv2 = K.inv(K.add(K.one(), K.one()))
        cb = K.neg(K.mul(a1b, inv2))
    # recenter: g = f(x + c), c a lift of cb (optionally shifted by pi)
    c = R.lift(cb)
    if lift_shift:
        c = R.add(c, R.pi())
    two_c = R.add(c, c)
    a1p = R.add(a1, two_c)
    a0p = R.add(R.add(R.mul(c, c), R.mul(a1, c)), a0)
    v0, v1 = R.val(a0p), R.val(a1p)
    if v0 is None:
        return 'deep', cb, None
    hull = lower_hull([(0, v0), (1, v1), (2, 0)])
    if len(hull) == 3:
        return 'vertex', cb, None            # two sides: split stratum
    (x0, y0), (x1, y1) = hull
    assert (x0, x1) == (0, 2) and y1 == 0 and y0 == v0
    if v0 == 1:
        letter = R.res(a0p, 1)
        assert not K.is_zero(letter)
        return '211', cb, letter
    if v0 % 2 == 0:
        return 'side-e1', cb, None           # slope integer: e = 1 side
    return 'side-2h', cb, None               # (2,h,1) with h = v0 >= 3


def classify_blind(R, a0, a1):
    """TOOTH classifier: hull of the ENDPOINTS only (interior dropped)."""
    K, k = R.K, R.k
    a0b, a1b = R.res(a0, 0), R.res(a1, 0)
    if R.p == 2:
        if not K.is_zero(a1b):
            return False
        cb = sqrt_char2(K, a0b, k)
    else:
        four = K.add(K.add(K.one(), K.one()), K.add(K.one(), K.one()))
        disc = K.add(K.mul(a1b, a1b), K.neg(K.mul(four, a0b)))
        if not K.is_zero(disc):
            return False
        cb = K.neg(K.mul(a1b, K.inv(K.add(K.one(), K.one()))))
    c = R.lift(cb)
    a0p = R.add(R.add(R.mul(c, c), R.mul(a1, c)), a0)   # c^2 + a1*c + a0
    return R.val(a0p) == 1                   # v(a1') never consulted


# ------------------------------------------------------------ census rows
CENSUS_ROWS = [('Zp', 2, 2), ('Zp', 2, 3), ('Zp', 2, 4),
               ('Zp', 3, 2), ('Zp', 3, 3),
               ('Zp', 5, 2), ('Zp', 5, 3),
               ('Zp', 7, 2), ('Zp', 7, 3),
               ('Fqt', 2, 2), ('Fqt', 2, 3),
               ('Fqt', 3, 2), ('Fqt', 3, 3),
               ('Fqt', 4, 2), ('Fqt', 4, 3),
               ('Fqt', 5, 2), ('Fqt', 5, 3),
               ('Fqt', 7, 2), ('Fqt', 7, 3),
               ('Fqt', 8, 2), ('Fqt', 8, 3),
               ('Fqt', 9, 2), ('Fqt', 9, 3)]

SMOKE_CENSUS = [('Zp', 2, 2), ('Zp', 3, 2), ('Fqt', 4, 2)]


def model_side(K, q, N):
    """the shape-only assembly: L3(level0) x L3(level1) x q^B, each leg
    ENUMERATED (not formula-substituted)."""
    els = list(K.elems())
    L3_0 = len(els)                              # monic deg-1: y - c, any c
    L3_1 = len([z for z in els if not K.is_zero(z)])   # psi(0) != 0
    B = 2 * N - 3                                # digit bookkeeping (S2.2)
    return L3_0, L3_1, B, L3_0 * L3_1 * q ** B


def run_census_row(kind, q, N):
    R = ZpWin(q, N) if kind == 'Zp' else FqtWin(q, N)
    K = R.K
    t1 = time.time()
    total = 0
    buckets = {}
    per_center = {}
    per_cell = {}                                # (center, letter) -> count
    center0_count = 0
    interior_mismatch = 0
    members = []
    zero = K.zero()
    for a0 in R.elems():
        for a1 in (R.elems() if kind == 'Zp' else
                   itertools.product(list(K.elems()), repeat=N)):
            total += 1
            bucket, cb, letter = classify(R, a0, a1)
            buckets[bucket] = buckets.get(bucket, 0) + 1
            if bucket == '211':
                per_center[repr(cb)] = per_center.get(repr(cb), 0) + 1
                cell = (repr(cb), repr(letter))
                per_cell[cell] = per_cell.get(cell, 0) + 1
                if cb == zero:
                    center0_count += 1
                if len(members) < 200:
                    members.append((a0, a1))
            # INTERIOR-FREE: endpoint-only hull == full hull, pointwise
            if classify_blind(R, a0, a1) != (bucket == '211'):
                interior_mismatch += 1
    census = buckets.get('211', 0)
    vexact_count = total - buckets.get('sep', 0)
    L3_0, L3_1, B, model = model_side(K, q, N)
    rec = {'kind': kind, 'q': q, 'N': N, 'total': total,
           'census': census, 'model': model,
           'L3_level0': L3_0, 'L3_level1': L3_1, 'B': B,
           'buckets': buckets, 'vexact_count': vexact_count,
           'center0_count': center0_count,
           'interior_mismatch': interior_mismatch,
           'per_center_counts': sorted(per_center.values()),
           'n_centers': len(per_center),
           'elapsed_s': round(time.time() - t1, 1)}
    # THE COUNT EQUALITY (exact)
    note('W10-CENSUS')
    if census != model:
        viol('W10-CENSUS', 'count', '%s q=%d N=%d: census %d != model %d'
             % (kind, q, N, census, model))
    # density forms (exact rationals)
    note('W10-CENSUS', 2)
    if Fraction(census, total) != Fraction(q - 1, q ** 2):
        viol('W10-CENSUS', 'density-full', '%s q=%d N=%d' % (kind, q, N))
    if Fraction(census, total * q) != Fraction(q - 1, q ** 3):
        viol('W10-CENSUS', 'density-center', '%s q=%d N=%d' % (kind, q, N))
    # product form: every (center, letter) cell == q^B
    cellB = q ** B
    note('W10-CENSUS', len(per_cell) + 1)
    if len(per_cell) != q * (q - 1):
        viol('W10-CENSUS', 'cells', '%s q=%d N=%d: %d cells != q(q-1)'
             % (kind, q, N, len(per_cell)))
    for cell, cnt in per_cell.items():
        if cnt != cellB:
            viol('W10-CENSUS', 'cell-count', '%s q=%d N=%d %s: %d != %d'
                 % (kind, q, N, cell, cnt, cellB))
    # recenter family: per-center equality + exactly q centers
    note('W10-RECENTER', 2)
    if len(per_center) != q:
        viol('W10-RECENTER', 'centers', '%s q=%d N=%d: %d centers'
             % (kind, q, N, len(per_center)))
    if any(v != (q - 1) * q ** B for v in per_center.values()):
        viol('W10-RECENTER', 'per-center', '%s q=%d N=%d: %s'
             % (kind, q, N, sorted(per_center.values())))
    # lift-independence on sampled members: c vs c + pi
    for (a0, a1) in members:
        note('W10-RECENTER')
        b1, c1, l1 = classify(R, a0, a1)
        b2, c2, l2 = classify(R, a0, a1, lift_shift=1)
        if (b1, c1, l1) != (b2, c2, l2):
            viol('W10-RECENTER', 'lift', '%s q=%d N=%d f=(%s,%s)'
                 % (kind, q, N, a0, a1))
    # INTERIOR-FREE: endpoint-only hull agrees pointwise (scored per poly)
    note('W10-CENSUS', total)
    if interior_mismatch:
        viol('W10-CENSUS', 'interior-free', '%s q=%d N=%d: %d mismatches'
             % (kind, q, N, interior_mismatch))
    # TOOTH: v(a0') >= 1 corruption (exactness forgotten) must overcount
    note('W10-CENSUS')
    if vexact_count != census:
        FIRE['W10-T-VEXACT'] += 1
    else:
        viol('W10-CENSUS', 'tooth-vexact-dead', '%s q=%d N=%d: %d'
             % (kind, q, N, vexact_count))
    # TOOTH: center-0-only corruption (level-0 menu forgotten) undercounts
    note('W10-CENSUS')
    if center0_count != census:
        FIRE['W10-T-CENTER0'] += 1
    else:
        viol('W10-CENSUS', 'tooth-center0-dead', '%s q=%d N=%d'
             % (kind, q, N))
    # TOOTH: letter-0 model must mismatch
    note('W10-CENSUS')
    model_l0 = L3_0 * L3_0 * q ** B              # letter menu q, not q-1
    if model_l0 != census:
        FIRE['W10-T-LETTER0'] += 1
    else:
        viol('W10-CENSUS', 'tooth-letter0-dead', '%s q=%d N=%d'
             % (kind, q, N))
    print('  [census %s q=%d N=%d] census=%d model=%d (%.1fs)'
          % (kind, q, N, census, model, rec['elapsed_s']))
    return rec


# ------------------------------------------------------------ tower leg
TOWER_IDS = ['C2A', 'C2C', 'C2E', 'C2F', 'P3A', 'J7A', 'P1B']
SMOKE_TOWER_IDS = ['C2A', 'C2C']


def tower_specs(ids):
    pool = {s['id']: dict(s) for s in JCP.ROSTER}
    pool.update({s['id']: dict(s) for s in JD0.P7_GENRE})
    pool.update({s['id']: dict(s) for s in JD0.PAIR_MEMBERS})
    return [pool[i] for i in ids]


def run_towers(ids):
    out = []
    wild_hits = 0
    for spec in tower_specs(ids):
        tid = spec['id']
        T = ITL.build_tower(spec)
        p = spec['p']
        for j in range(T.NR):
            e, h, g = spec['reads'][j]
            if (e, h, g) != (2, 1, 1):
                continue
            Phi_next = T.Phi[j + 1] if j + 1 <= T.n else T._build_lift(T.n)
            dv = T.P.dev(Phi_next, T.Phi[j])
            pts = [[i, T.wlev(j, A)] for i, A in enumerate(dv) if A]
            gam = T.gam[j + 1]
            wild = (p % e == 0)
            wild_hits += 1 if wild else 0
            rec = {'id': tid, 'level': j, 'p': p, 'ring': spec['ring'],
                   'pts': pts, 'gam': gam, 'wPhi_j': T.wPhi[j],
                   'wild': wild}
            out.append(rec)
            note('W10-TOWER', 4)
            if pts[0] != [0, gam] or pts[-1] != [2, 0]:
                viol('W10-TOWER', 'endpoints', '%s level %d: %s'
                     % (tid, j, pts))
            if gam % 2 != 1:
                viol('W10-TOWER', 'slope-denom', '%s level %d: gam=%d even'
                     % (tid, j, gam))
            if len(pts) == 3 and 2 * pts[1][1] <= gam:
                viol('W10-TOWER', 'interior', '%s level %d: %s'
                     % (tid, j, pts))
            if gam != e * T.wPhi[j] + h:
                viol('W10-TOWER', 'grid-tie', '%s level %d: gam=%d != '
                     'e*wPhi+h=%d' % (tid, j, gam, e * T.wPhi[j] + h))
    note('W10-TOWER')
    if wild_hits < 1:
        viol('W10-TOWER', 'no-wild', 'no wild (2,1,1) realization')
    print('  [towers] %d (2,1,1) levels checked, %d wild'
          % (len(out), wild_hits))
    return out, wild_hits


# ------------------------------------------------------------ oracle leg
ORACLE_IMPL_ROWS = [(2, 3), (2, 4), (3, 3), (5, 3), (7, 3)]
ORACLE_CONV_ROWS = [(3, 2), (5, 2)]
SMOKE_ORACLE = ([(2, 3)], [(3, 2)])


def gp_run(script):
    r = subprocess.run(['gp', '-q'], input=script.encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=1800)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:500])
    return r.stdout.decode()


GP_FUN = r"""
t(a1,a0,p) = {
  my(f = x^2+a1*x+a0, d = poldisc(f), vd, F, nf, dec);
  vd = if (d == 0, -1, valuation(d, p));
  F = factorpadic(f, p, 40);
  if (matsize(F)[1] > 1 || poldegree(F[1,1]) < 2 || F[1,2] > 1,
      return([0, 0, 0, vd]));
  nf = nfinit([f, [p]]); dec = idealprimedec(nf, p);
  [length(dec), dec[1].e, dec[1].f, vd]
}
"""


def oracle_leg(impl_rows, conv_rows):
    recs = {'impl': [], 'conv': []}
    # (a) implication: all centered members, lifted to Z[x]
    for (p, N) in impl_rows:
        M = p ** N
        queries = []
        for a0 in range(M):
            v0 = None if a0 == 0 else ZpWin(p, N).val(a0)
            if v0 != 1:
                continue
            for a1 in range(0, M, p):           # v(a1) >= 1
                queries.append((a1, a0))
        script = GP_FUN + '\n'.join(
            'print("R ",%d," ",%d," ",t(%d,%d,%d))' % (a1, a0, a1, a0, p)
            for (a1, a0) in queries) + '\nquit\n'
        outp = gp_run(script)
        nbad = 0
        nparsed = 0
        for line in outp.splitlines():
            if not line.startswith('R '):
                continue
            nparsed += 1
            parts = line[2:].replace('[', '').replace(']', '') \
                            .replace(',', ' ').split()
            a1, a0, nd, e, f, vd = [int(x) for x in parts]
            note('W10-ORACLE')
            v1 = ZpWin(p, N).val(a1) if a1 else None
            want_vd = 1 if p != 2 else (2 if v1 == 1 else 3)
            if not (nd == 1 and e == 2 and f == 1 and vd == want_vd):
                nbad += 1
                viol('W10-ORACLE', 'impl', 'p=%d N=%d f=(%d,%d): '
                     '(%d,%d,%d,%d)' % (p, N, a1, a0, nd, e, f, vd))
            if p == 2:
                note('W10-ORACLE')
                if vd != 1:
                    FIRE['W10-T-TAMEDISC'] += 1
                else:
                    viol('W10-ORACLE', 'tooth-tamedisc-dead',
                         'p=2 N=%d f=(%d,%d): vd==1' % (N, a1, a0))
        note('W10-ORACLE')
        if nparsed != len(queries):
            viol('W10-ORACLE', 'impl-truncated', 'p=%d N=%d: %d of %d'
                 % (p, N, nparsed, len(queries)))
        recs['impl'].append({'p': p, 'N': N, 'members': len(queries),
                             'parsed': nparsed, 'bad': nbad})
        print('  [oracle-impl p=%d N=%d] %d members, %d bad'
              % (p, N, len(queries), nbad))
    # (b) converse: ALL polynomials at (p, N), per-f set equality
    for (p, N) in conv_rows:
        R = ZpWin(p, N)
        M = p ** N
        allf = [(a1, a0) for a0 in range(M) for a1 in range(M)]
        script = GP_FUN + '\n'.join(
            'print("R ",%d," ",%d," ",t(%d,%d,%d))' % (a1, a0, a1, a0, p)
            for (a1, a0) in allf) + '\nquit\n'
        outp = gp_run(script)
        got = {}
        for line in outp.splitlines():
            if not line.startswith('R '):
                continue
            parts = line[2:].replace('[', '').replace(']', '') \
                            .replace(',', ' ').split()
            a1, a0, nd, e, f, vd = [int(x) for x in parts]
            got[(a1, a0)] = (nd == 1 and e == 2 and f == 1 and vd == 1)
        nbad = 0
        for (a1, a0) in allf:
            note('W10-ORACLE')
            cls = classify(R, a0, a1)[0] == '211'
            if got.get((a1, a0)) != cls:
                nbad += 1
                viol('W10-ORACLE', 'conv', 'p=%d N=%d f=(%d,%d): oracle %s'
                     ' classifier %s' % (p, N, a1, a0, got.get((a1, a0)),
                                         cls))
        note('W10-ORACLE')
        if len(got) != len(allf):
            viol('W10-ORACLE', 'conv-truncated', 'p=%d N=%d: %d of %d'
                 % (p, N, len(got), len(allf)))
        recs['conv'].append({'p': p, 'N': N, 'polys': len(allf),
                             'parsed': len(got), 'bad': nbad})
        print('  [oracle-conv p=%d N=%d] %d polynomials, %d bad'
              % (p, N, len(allf), nbad))
    return recs


# ------------------------------------------------------------ main
def main(smoke=False):
    t0 = time.time()
    print('W10 SEALED BATTERY -- %s mode' % ('SMOKE' if smoke else 'FULL'))
    for fn, want in PINS.items():
        note('W10-PIN')
        got = hashlib.md5(open(os.path.join(HERE, fn), 'rb').read()
                          ).hexdigest()
        if got != want:
            viol('W10-PIN', fn, '%s != %s' % (got, want))
    census_rows = SMOKE_CENSUS if smoke else CENSUS_ROWS
    census_recs = [run_census_row(*row) for row in census_rows]
    tower_recs, wild_hits = run_towers(
        SMOKE_TOWER_IDS if smoke else TOWER_IDS)
    impl_rows, conv_rows = SMOKE_ORACLE if smoke else (ORACLE_IMPL_ROWS,
                                                       ORACLE_CONV_ROWS)
    try:
        oracle_recs = oracle_leg(impl_rows, conv_rows)
    except Exception as ex:
        viol('W10-ORACLE', 'gp', '%s: %s' % (type(ex).__name__, ex))
        oracle_recs = {'impl': [], 'conv': [], 'error': repr(ex)}

    nviol = sum(len(v) for v in VIOL.values())
    teeth_ok = all(FIRE[t] >= 1 for t in TEETH)
    verdict = 'GREEN' if (nviol == 0 and teeth_ok) else 'RED'
    summary = {
        'mode': 'smoke' if smoke else 'full',
        'verdict': verdict,
        'census_rows': len(census_recs),
        'checks': NCHK, 'violations': {f: len(VIOL[f]) for f in FAMILIES},
        'violation_detail': {f: VIOL[f][:50] for f in FAMILIES},
        'teeth_fires': FIRE,
        'census': census_recs,
        'towers': {'levels': tower_recs, 'wild_hits': wild_hits},
        'oracle': oracle_recs,
        'elapsed_s': round(time.time() - t0, 1),
    }
    tag = '_smoke' if smoke else ''
    with open(os.path.join(HERE, 'w10_checks_results%s.json' % tag),
              'w') as fh:
        json.dump(summary, fh, indent=1, default=repr)
    lines = ['W10 BATTERY VERDICT: %s' % verdict,
             'census rows: %d   tower (2,1,1) levels: %d (wild %d)   '
             'checks: %d' % (len(census_recs), len(tower_recs), wild_hits,
                             sum(NCHK.values())),
             'violations: ' + ' '.join('%s=%d' % (f, len(VIOL[f]))
                                       for f in FAMILIES),
             'teeth: ' + ' '.join('%s=%d' % (t, FIRE[t]) for t in TEETH),
             'oracle: impl rows %s   conv rows %s' % (
                 [(r['p'], r['N'], r['members'], r['bad'])
                  for r in oracle_recs.get('impl', [])],
                 [(r['p'], r['N'], r['polys'], r['bad'])
                  for r in oracle_recs.get('conv', [])]),
             'elapsed: %.1fs' % (time.time() - t0)]
    print('\n'.join(lines))
    if not smoke:
        with open(os.path.join(HERE, 'w10_checks_output.txt'), 'w') as fh:
            fh.write('\n'.join(lines) + '\n')
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
