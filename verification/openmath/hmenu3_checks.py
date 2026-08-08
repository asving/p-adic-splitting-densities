"""HMENU3 — the (hMenu-3) battery: the COMPLETE n = 3 core menu
(HMENU3 unit; consumes W-12 BOX-2; companion note
lean/notes/openmath/HMENU3_PROOF_2026-08-08.md).

THE LAW UNDER TEST (preregistered; per prime power q, window N >= 2,
both characteristics; the conservative read convention of the sealed
w12 TRP reader, W12-BOX-3/BOX-7):  the TRP (triple-center) per-center
state space partitions EXACTLY into HISTORY-RESOLVED menu keys
key = (step_1, ..., step_r, leaf), where each step is a refine event
classified at its own frame

    ('ALPHA', d)         FULL side, residual (y-z)^3      [d = raw depth]
    ('FULL11SQ', d)      FULL side, residual (y-z)^2(y-z')
    ('VERT1', u0, k)     vertex at 1, right side residual (y-z)^2
    ('VERT2', u0, t)     vertex at 2, left side residual (y-z)^2

and the leaf is a decided depth-0-shape key ('RAM3',h) / ('3LIN',...)
/ ('LINRAM2',u0,u1) / ('RAM2LIN',u0,t) / ('VERT1',u0,k,lam) /
('VERT2',u0,t,lam) / ('FULL',k,lam) or ('DRAIN',), with the count of
every key given by the RECURSIVE PREDICTOR pred3 below (the note's
THEOREM HM3.A): depth-0 laws (W-12.A instances) + alpha-transport
(q-1)q^{3k} x window-(N-3k) self-similarity + three beta-routes into
the W12-L0 history-resolved n=2 block system with fibers
  beta1 (FULL11SQ):   (q-1)(q-2) q^{3k+M-1}          x L0(M)
  beta2 (VERT1,w):    (q-1)^2    q^{3k+M-1-w}        x L0(M)
  beta3 (VERT2,t,j):  (q-1)      q^{3t+M-1}          x L0(M | k1 = j)
(M = reduced window, raw-key translation by the shear dictionary).
AGGREGATED (A1) LAYER (THEOREM HM3.B): the alpha-prefix bracket
Sum over compositions of m of prod (q-1)q^{3k_i} = (q-1)q^{4m-1}, the
W-11 aggregated block laws A_L(M), the j-entry laws A_L^{(j)}(M), and
the finite aggregate family list agg_laws == sums of raw keys, both
directions.  COROLLARY (HM3.D): R_tau(q) for the five cubic splitting
types, verified symbolically (sum = 1; == the monic level-0 assembly
of om_density_engine's beta(2)/beta(3) cluster laws; series-tied to
the aggregate menu by exact partial sums with vanishing tails).

EVIDENCE CLASSES: fresh reader + predictor = SAME (this runner's own
arithmetic); XREAD tie to the SEALED w12 read_trp = SEAL-TIE; ties to
COMMITTED w12/hex3 JSONs = NONE (bookkeeping vs frozen artifacts);
PARI sigma leg = IND (independent engine, cypari2); sympy leg = SYM.

FAMILIES:
  HM3-PIN     [NONE] md5 pins (7 files, values below).
  HM3-MENU    [SAME] per-row per-key count == pred3, BOTH directions.
  HM3-DRAIN   [SAME] partition sum == q^{3(N-1)} and drain-key sum ==
              u(q,N) (THEOREM HEX3.A re-derived at key granularity).
  HM3-AGG     [SAME] aggregate famlies == sums of measured raw keys,
              BOTH directions (the bracket + aggregation lemmas).
  HM3-XREAD   [SEAL-TIE] pointwise vs sealed w12 read_trp on every row
              with <= 65536 states: decided verdict, depth-0 key
              identity, and sigma of decided members vs my leaf table.
  HM3-HEX3TIE [NONE] first-step species (locus, drained) == committed
              hex3 species_tally on shared rows.
  HM3-W12TIE  [NONE] committed w12 depth0_keys == q x Group-I laws
              (both directions), trp_deep_decided == q x my deep sum,
              U3TRP == q x u_law, at all 23 committed w12 cubic rows.
  HM3-DBLTIE  [NONE] committed w12 dbl_keys summed over histories ==
              the four whole-space DBL aggregate laws
              q(q-1) q^{N-1} A_L(N), both directions, all 23 rows.
  HM3-ORACLE  [IND] PARI/GP (cypari2) sigma multiset of EVERY
              deep-decided (history length >= 1) per-center member on
              the four oracle rows == the leaf sigma table.
  HM3-RTAU    [SYM] sympy: Sum_tau R_tau = 1; R_tau == monic assembly
              from om_density_engine beta(2)/beta(3) (md5-pinned);
              exact partial sums of the aggregate menu converge to
              R_tau (positive remainder < q^{-(N-4)}); per-center
              partial-sum identity Sum_tau D_tau(N) == q^{3(N-1)} -
              u(q,N) exactly.

TEETH (preregistered EXACT fire counts; wrong count = RED):
  HM3-T-BRACKET  alpha-transport factor (q-1)q^{3k} -> (q-1)q^{3k+1}:
                 must mismatch HM3-MENU on exactly the 21 rows with
                 N >= 4.
  HM3-T-SHEAR    beta RAM2LIN raw translation 3m+u -> 3m+u+1: must
                 mismatch on exactly the 15 rows with N >= 5.
  HM3-T-L0BRK    block INERTDEEP law q(q-1)/2 -> q(q-1): must
                 mismatch on exactly the 10 rows with N >= 6.
  HM3-T-SIGMA    leaf sigma table RAM3 -> {(1,1),(2,1)}: must be
                 caught by PARI on exactly the 4 oracle rows.

ROSTER (41 rows, 94,824,902 per-center states read; per-center
enumeration at the recentered origin — exact for the whole space by
the translation bijection):
  Zp  (2,3..9), (3,2..6), (5,2..4), (7,2..3), (13,3)      [18 rows]
  Fqt (2,3..9), (3,2..6), (4,2..5), (5,2..3), (7,3),
      (8,3), (9,3), (11,3), (27,2)                        [23 rows]
NEVER-MEASURED rows (in no committed battery): (Fqt,2,9), (Fqt,3,6),
(Fqt,27,2) — preregistered per-key predictions in the note S7 (spot:
(Fqt,2,9) deep-decided 523,008/center, (('ALPHA',1),('RAM3',4)) =
131,072; (Fqt,3,6) deep-decided 95,580/center,
(('FULL11SQ',1),('RAM2LIN',4,1)) = 26,244; (Fqt,27,2) single decided
key ('RAM3',1) = 18,954/center, drain 729).  F27 = F3[y]/(y^3+2y+1)
built on the frozen Ext class (disclosed local construction; GF(27)
is not in the frozen w10 GF map).
ORACLE ROWS (Zp, per-center): (2,5) 48 members, (2,6) 624, (2,7)
6,688, (3,5) 2,592 — every deep-decided member sigma-scored
(9,952 total; deep TRP sigma was never independently oracled before
this unit: the w12 oracle rows had no deep-decided TRP members).

PRE-SEAL SMOKE DISCLOSED: reader + predictor + aggregate layer
developed as a /tmp prototype (examples-first); confirmed pre-seal on
16 enumeration rows (Zp (2,4..8),(3,4..6),(5,3),(5,4); Fqt (2,5),
(2,7),(3,4),(3,5),(4,4),(4,5)) with 0 violations after ONE repair
(the block-2SIDED raw translation m1 = m+w+d -> m+d, caught by the
(2,7) prototype row); aggregate layer confirmed closed-form-vs-raw at
17 (q,N) incl. (2,10),(3,7) beyond the roster; oracle leg confirmed
on (2,5),(3,4),(3,5) = 2,640 members 0 mismatches; the R_tau forms
verified against beta(3) and the monic assembly BEFORE composing the
note.  This runner's --smoke was run THREE times pre-seal: runs 1-2
RED on two INSTRUMENT defects (the DBLTIE want-map omitted the
committed SPLIT-TAIL/UNDECIDED boundary keys — their aggregated laws
q(q-1)q^{N-1}(q-1)q^{N-2} per w and q(q-1)q^{2N-2} were added; the
L0BRK tooth could not fire on an N <= 5 smoke roster — (Zp,2,6)
added to SMOKE_ZP); zero math-side changes; run 3 GREEN: PIN 7,
MENU 101, DRAIN 18, AGG 75, XREAD 116,146, HEX3TIE 8, W12TIE 69,
DBLTIE 23, ORACLE 49, RTAU 30, all 0 violations, teeth 7/3/1/1,
7.4 s.  No full run before the seal.

Exact integer arithmetic in all counting legs; deterministic; sympy
(exact rationals) only in HM3-RTAU; cypari2 only in HM3-ORACLE.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
# user site-packages (sympy 1.14.0 / cypari2 2.2.0 live there; the
# system python 3.10 on this box does not enable the user site)
sys.path.append(os.path.expanduser(
    '~/.local/lib/python3.10/site-packages'))

import w10_checks as W10
import w12_checks as W12
import iterlawn_pe_reimpl as ITL

PINS = {
    'w10_checks.py':            'a9c34244a3af19f5fa864375b494380b',
    'w11_checks.py':            '500aae152bb5b5e9df3712904a6d73a6',
    'w12_checks.py':            '7dc040d94fbbb1e8d20ac817b665d418',
    'hex3_checks.py':           '83faf7edb554811cd657691d7ea256cc',
    'w12_checks_results.json':  '05776c9e00071c5d7524abdfbe894442',
    'hex3_checks_results.json': 'ce6f41162a22b0bd66a641e98cb4d56e',
    '../om_density_engine.py':  '7240a916060c360d4433ca8a802d315d',
}

FAMILIES = ['HM3-PIN', 'HM3-MENU', 'HM3-DRAIN', 'HM3-AGG', 'HM3-XREAD',
            'HM3-HEX3TIE', 'HM3-W12TIE', 'HM3-DBLTIE', 'HM3-ORACLE',
            'HM3-RTAU']
TEETH = ['HM3-T-BRACKET', 'HM3-T-SHEAR', 'HM3-T-L0BRK', 'HM3-T-SIGMA']
TEETH_EXPECT = {'HM3-T-BRACKET': 21, 'HM3-T-SHEAR': 15,
                'HM3-T-L0BRK': 10, 'HM3-T-SIGMA': 4}

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
    VIOL[fam].append((tag, str(detail)))
    say('  VIOLATION [%s] %s: %s' % (fam, tag, detail))


# ------------------------------------------------------------- ring helpers
def GFq(q):
    """residue field, extending the frozen w10 GF map by F27 (disclosed)."""
    if q == 27:
        return ITL.Ext(ITL.GFp(3), (1, 2, 0, 1))     # y^3 + 2y + 1
    if q in (2, 3, 5, 7, 11, 13):
        return ITL.GFp(q)
    return W10.GF(q)[0]


class Fqt27(W10.FqtWin):
    """FqtWin with the local F27 field (same frozen mechanics)."""
    def __init__(self, q, N):
        self.q, self.N = q, N
        self.K, self.p, self.k = GFq(q), 3, 3


def mkring(kind, q, N):
    if kind == 'Zp':
        return W10.ZpWin(q, N)
    if q == 27:
        return Fqt27(q, N)
    return W10.FqtWin(q, N)


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


def kroots_mult(K, coeffs):
    out = []
    poly = list(coeffs)
    for z in K.elems():
        m = 0
        while len(poly) > 1:
            n = len(poly) - 1
            quot = [K.zero()] * n
            acc = poly[n]
            for i in range(n - 1, -1, -1):
                quot[i] = acc
                acc = K.add(poly[i], K.mul(acc, z))
            if K.is_zero(acc):
                m += 1
                poly = quot
            else:
                break
        if m:
            out.append((z, m))
    return out, len(poly) - 1


def rint(R, m):
    one = 1 if R.kind == 'Zp' else R.lift(R.K.one())
    out = 0 if R.kind == 'Zp' else tuple([R.K.zero()] * R.N)
    for _ in range(m):
        out = R.add(out, one)
    return out


def pipow(R, m):
    out = rint(R, 1)
    for _ in range(m):
        out = R.mul(out, R.pi())
    return out


def shift3(R, a2, a1, a0, s):
    s2 = R.mul(s, s)
    s3 = R.mul(s2, s)
    b2 = R.add(a2, R.mul(rint(R, 3), s))
    b1 = R.add(R.add(a1, R.mul(R.mul(rint(R, 2), a2), s)),
               R.mul(rint(R, 3), s2))
    b0 = R.add(R.add(R.add(a0, R.mul(a1, s)), R.mul(a2, s2)), s3)
    return b2, b1, b0


# --------------------------------------------------------- the fresh reader
def _restype(roots, deg):
    nr = len(roots)
    if deg == 2:
        return '11' if nr == 2 else '2'
    if nr == 3:
        return '111'
    if nr == 1:
        return '12'
    return '3'


def read_menu(R, q, B2, B1, B0):
    """full conservative chain of a per-center TRP state; returns the
    history-resolved menu key (step, ..., leaf)."""
    K = R.K
    key = []
    last_depth = -1
    it = 0
    while True:
        it += 1
        assert it <= 3 * R.N + 8, 'read_menu loop cap'
        u0 = R.val(B0)
        if u0 is None:
            key.append(('DRAIN',))
            return tuple(key)
        pts = [(0, u0), (1, R.val(B1)), (2, R.val(B2)), (3, 0)]
        hv = hull(pts)
        refine = None
        leaf = None
        if len(hv) == 2:
            if u0 % 3:
                leaf = ('RAM3', u0)
            else:
                k = u0 // 3
                rc = [R.res(B0, 3 * k), R.res(B1, 2 * k), R.res(B2, k),
                      K.one()]
                roots, _ = kroots_mult(K, rc)
                rep = [(z, m) for (z, m) in roots if m > 1]
                if rep:
                    key.append(('ALPHA', k) if rep[0][1] == 3
                               else ('FULL11SQ', k))
                    refine = (rep[0][0], k)
                else:
                    leaf = ('FULL', k, _restype(roots, 3))
        elif len(hv) == 3 and hv[1][0] == 1:
            u1 = hv[1][1]
            if u1 % 2:
                leaf = ('LINRAM2', u0, u1)
            else:
                k = u1 // 2
                rc = [R.res(B1, u1), R.res(B2, k), K.one()]
                roots, _ = kroots_mult(K, rc)
                rep = [(z, m) for (z, m) in roots if m > 1]
                if rep:
                    key.append(('VERT1', u0, k))
                    refine = (rep[0][0], k)
                else:
                    leaf = ('VERT1', u0, k, _restype(roots, 2))
        elif len(hv) == 3 and hv[1][0] == 2:
            t = hv[1][1]
            if (u0 - t) % 2:
                leaf = ('RAM2LIN', u0, t)
            else:
                kk = (u0 + t) // 2
                lam = R.res(B2, t)
                invl = K.inv(lam)
                rc = [K.mul(R.res(B0, u0), invl),
                      K.mul(R.res(B1, kk), invl), K.one()]
                roots, _ = kroots_mult(K, rc)
                rep = [(z, m) for (z, m) in roots if m > 1]
                if rep:
                    key.append(('VERT2', u0, t))
                    refine = (rep[0][0], (u0 - t) // 2)
                else:
                    leaf = ('VERT2', u0, t, _restype(roots, 2))
        else:
            m3 = hv[2][1]
            m2 = hv[1][1] - hv[2][1]
            m1 = hv[0][1] - hv[1][1]
            leaf = ('3LIN', m1, m2, m3)
        if leaf is not None:
            key.append(leaf)
            return tuple(key)
        z, dep = refine
        assert dep > last_depth, 'refine depths must strictly increase'
        last_depth = dep
        s = R.mul(R.lift(z), pipow(R, dep))
        B2, B1, B0 = shift3(R, B2, B1, B0, s)


# leaf sigma table (Ore at the terminal frame; W-12 S2.3 / S2.4)
def leaf_sigma(leaf, sigma_bad=False):
    fam = leaf[0]
    if fam == 'RAM3':
        return (((1, 1), (2, 1)) if sigma_bad else ((3, 1),))
    if fam == '3LIN':
        return ((1, 1), (1, 1), (1, 1))
    if fam in ('LINRAM2', 'RAM2LIN'):
        return ((1, 1), (2, 1))
    if fam in ('VERT1', 'VERT2'):
        return (((1, 1), (1, 1), (1, 1)) if leaf[-1] == '11'
                else ((1, 1), (1, 2)))
    if fam == 'FULL':
        return {'111': ((1, 1), (1, 1), (1, 1)),
                '12': ((1, 1), (1, 2)), '3': ((1, 3),)}[leaf[-1]]
    raise ValueError(leaf)


# ------------------------------------------------------------ the predictor
def u_law(N, q):
    def Rr(M):
        return q ** (M - 1) + (((M - 1) // 2) * (q - 1) * q ** (M - 2)
                               if M >= 2 else 0)
    tot = q ** (2 * N - 2)
    for k in range(1, (N - 1) // 3 + 1):
        M = N - 3 * k
        tot += (q - 1) * q ** (4 * k - 1) * (q ** M - 1) * Rr(M)
    return tot


def S_lam(q):
    return {'11': (q - 1) * (q - 2) // 2, '2': q * (q - 1) // 2,
            '111': (q - 1) * (q - 2) * (q - 3) // 6,
            '12': q * (q - 1) ** 2 // 2, '3': (q ** 3 - q) // 3}


def predL0(q, M, l0brk_bad=False):
    """W12-L0 history-resolved n=2 block system, window M, per center."""
    Mf = (M - 1) // 2
    for r in range(Mf + 1):
        for hist in itertools.combinations(range(1, Mf + 1), r):
            s = hist[-1] if hist else 0
            base = (q - 1) ** len(hist)
            for u in range(2 * s + 1, M, 2):
                yield hist, ('RAM', u), base * (q - 1) * q ** (M - 1 - u) \
                    * q ** (M - (u + 1) // 2)
            for w in range(s + 1, Mf + 1):
                for u in range(2 * w + 1, M):
                    yield hist, ('2SIDED', w, u - w), \
                        base * (q - 1) ** 2 * q ** (2 * M - 2 - u - w)
            for k2 in range(s + 1, Mf + 1):
                c = base * (q - 1) * (q - 2) // 2 * q ** (2 * M - 3 * k2 - 2)
                if c:
                    yield hist, ('SPLITEQ', k2), c
                cid = base * q * (q - 1) // 2 * q ** (2 * M - 3 * k2 - 2)
                yield hist, ('INERTDEEP', k2), (2 * cid if l0brk_bad
                                                else cid)
            for w in range(s + 1, Mf + 1):
                yield hist, ('TAIL', w), base * (q - 1) * q ** (M - 1 - w)
            yield hist, ('UNDEC',), base * q ** (M - 1 - Mf)


def rawblock(hist, leaf, m, shear_bad=False):
    """translate an n=2 block (hist, leaf) at split depth m to raw keys."""
    steps = tuple(('VERT2', 3 * m + 2 * ki, m) for ki in hist)
    if leaf[0] == 'RAM':
        u0 = 3 * m + leaf[1] + (1 if shear_bad else 0)
        return steps + (('RAM2LIN', u0, m),)
    if leaf[0] == '2SIDED':
        return steps + (('3LIN', m + leaf[2], m + leaf[1], m),)
    if leaf[0] == 'SPLITEQ':
        return steps + (('VERT2', 3 * m + 2 * leaf[1], m, '11'),)
    if leaf[0] == 'INERTDEEP':
        return steps + (('VERT2', 3 * m + 2 * leaf[1], m, '2'),)
    return steps + (('DRAIN',),)


def pred_depth0(q, Ne, s):
    """Group-I (depth-0 decided) keys of the window-Ne frame at shear s."""
    S = S_lam(q)
    out = {}
    for u0 in range(1, Ne):
        if u0 % 3:
            out[(('RAM3', u0 + 3 * s),)] = \
                (q - 1) * q ** (3 * Ne - 2 * u0 - 2)
        else:
            k = u0 // 3
            for lam in ('111', '12', '3'):
                c = S[lam] * q ** (3 * Ne - 6 * k - 3)
                if c:
                    out[(('FULL', k + s, lam),)] = c
    for m3 in range(1, Ne):
        for m2 in range(m3 + 1, Ne):
            for m1 in range(m2 + 1, Ne):
                if m1 + m2 + m3 <= Ne - 1:
                    out[(('3LIN', m1 + s, m2 + s, m3 + s),)] = \
                        (q - 1) ** 3 * q ** (3 * Ne - 3 - m1 - 2 * m2 - 3 * m3)
    for u1 in range(1, Ne, 2):
        for u0 in range(u1 + 1, Ne):
            if 2 * u0 > 3 * u1:
                out[(('LINRAM2', u0 + 3 * s, u1 + 2 * s),)] = \
                    (q - 1) ** 2 * q ** (3 * Ne - 2 - u0 - u1 - (u1 + 1) // 2)
    for t in range(1, Ne):
        for u0 in range(3 * t + 1, Ne):
            if (u0 - t) % 2:
                out[(('RAM2LIN', u0 + 3 * s, t + s),)] = \
                    (q - 1) ** 2 * q ** (3 * Ne - 2 - u0 - t - (u0 + t + 1) // 2)
    for k in range(1, Ne):
        for u0 in range(3 * k + 1, Ne):
            for lam in ('11', '2'):
                c = (q - 1) * S[lam] * q ** (3 * Ne - 3 - u0 - 3 * k)
                if c:
                    out[(('VERT1', u0 + 3 * s, k + s, lam),)] = c
    for t in range(1, Ne):
        for u0 in range(3 * t + 2, Ne):
            if (u0 - t) % 2 == 0:
                for lam in ('11', '2'):
                    c = (q - 1) * S[lam] * \
                        q ** (3 * Ne - 3 - u0 - t - (u0 + t) // 2)
                    if c:
                        out[(('VERT2', u0 + 3 * s, t + s, lam),)] = c
    return out


def pred3(q, Ne, s=0, bracket_bad=False, shear_bad=False, l0brk_bad=False):
    """THEOREM HM3.A: the full history-resolved menu of the window-Ne
    TRP frame at raw shear s (drain keys included), per center."""
    out = dict(pred_depth0(q, Ne, s))
    out[(('DRAIN',),)] = q ** (2 * (Ne - 1)) if Ne >= 1 else 0
    for k in range(1, (Ne - 1) // 3 + 1):
        M = Ne - 3 * k
        m = s + k
        sub = pred3(q, M, m, bracket_bad, shear_bad, l0brk_bad)
        fac = (q - 1) * q ** (3 * k + (1 if bracket_bad else 0))
        for kk, c in sub.items():
            key = (('ALPHA', m),) + kk
            out[key] = out.get(key, 0) + fac * c
        if q > 2:
            for hist, leaf, c in predL0(q, M, l0brk_bad):
                key = (('FULL11SQ', m),) + rawblock(hist, leaf, m, shear_bad)
                out[key] = out.get(key, 0) + \
                    (q - 1) * (q - 2) * q ** (3 * k + M - 1) * c
        for w in range(1, M):
            fk = ('VERT1', 3 * k + w + 3 * s, m)
            for hist, leaf, c in predL0(q, M, l0brk_bad):
                key = (fk,) + rawblock(hist, leaf, m, shear_bad)
                out[key] = out.get(key, 0) + \
                    (q - 1) ** 2 * q ** (3 * k + M - 1 - w) * c
    for t in range(1, Ne):
        M = Ne - 3 * t
        m = s + t
        for j in range(1, Ne):
            u0 = 3 * t + 2 * j
            if u0 > Ne - 1:
                break
            fk = ('VERT2', u0 + 3 * s, t + s)
            for hist, leaf, c in predL0(q, M, l0brk_bad):
                if not hist or hist[0] != j:
                    continue
                key = (fk,) + rawblock(hist[1:], leaf, m, shear_bad)
                out[key] = out.get(key, 0) + \
                    (q - 1) * q ** (3 * t + M - 1) * c
    return {k: v for k, v in out.items() if v}


# --------------------------------------------------- the aggregate layer
def bracket(q, m):
    return 1 if m == 0 else (q - 1) * q ** (4 * m - 1)


def A_L(q, M):
    """W-11 aggregated block laws at window M (depth-0 entry)."""
    out = {}
    Mf = (M - 1) // 2
    for u in range(1, M, 2):
        out[('RAM', u)] = (q - 1) * q ** (2 * M - u - 2)
    for w1 in range(1, Mf + 1):
        for u in range(2 * w1 + 1, M):
            out[('2SIDED', w1, u - w1)] = (q - 1) ** 2 * q ** (2 * M - u - 3)
    for k in range(1, Mf + 1):
        c = (q - 1) * (q - 2) // 2 * q ** (2 * M - 2 * k - 3)
        if c:
            out[('SPLITEQ', k)] = c
        out[('INERTDEEP', k)] = q * (q - 1) // 2 * q ** (2 * M - 2 * k - 3)
    return {k: v for k, v in out.items() if v}


def A_L_entry(q, M, j):
    """block laws with forced first refine at depth j (beta3 entry)."""
    out = {}
    Mf = (M - 1) // 2
    if j > Mf:
        return out
    for u in range(2 * j + 1, M, 2):
        out[('RAM', u)] = (q - 1) ** 2 * q ** (2 * M - u - 2 - j)
    for w1 in range(j + 1, Mf + 1):
        for u in range(2 * w1 + 1, M):
            out[('2SIDED', w1, u - w1)] = \
                (q - 1) ** 3 * q ** (2 * M - 3 - u - j)
    for k in range(j + 1, Mf + 1):
        c = (q - 1) ** 2 * (q - 2) // 2 * q ** (2 * M - 2 * k - 3 - j)
        if c:
            out[('SPLITEQ', k)] = c
        out[('INERTDEEP', k)] = \
            q * (q - 1) ** 2 // 2 * q ** (2 * M - 2 * k - 3 - j)
    return {k: v for k, v in out.items() if v}


def agg_laws(q, N):
    """THEOREM HM3.B: the finite aggregate (A1) menu at window N."""
    out = {}
    for fam, c in _d0laws(q, N).items():
        out[('I',) + fam] = c
    for m in range(1, (N - 1) // 3 + 1):
        for fam, c in _d0laws(q, N - 3 * m).items():
            out[('II', m) + fam] = bracket(q, m) * c
    for m in range(0, N // 3 + 1):
        b = bracket(q, m)
        Nm = N - 3 * m
        for k in range(1, (Nm - 1) // 3 + 1):
            M = Nm - 3 * k
            for (L, cL) in A_L(q, M).items():
                c = b * (q - 1) * (q - 2) * q ** (3 * k + M - 1) * cL
                if c:
                    out[('B1', m, k) + L] = c
                for w in range(1, M):
                    out[('B2', m, k, w) + L] = \
                        b * (q - 1) ** 2 * q ** (3 * k + M - 1 - w) * cL
        for t in range(1, (Nm - 1) // 3 + 1):
            M = Nm - 3 * t
            for j in range(1, Nm):
                if 3 * t + 2 * j > Nm - 1:
                    break
                for (L, cL) in A_L_entry(q, M, j).items():
                    out[('B3', m, t, j) + L] = \
                        b * (q - 1) * q ** (3 * t + M - 1) * cL
    return {k: v for k, v in out.items() if v}


def _d0laws(q, Ne):
    return {k[0]: v for k, v in pred_depth0(q, Ne, 0).items()}


def unshift_leaf(leaf, s):
    f = leaf[0]
    if f == 'RAM3':
        return ('RAM3', leaf[1] - 3 * s)
    if f == 'FULL':
        return ('FULL', leaf[1] - s, leaf[2])
    if f == '3LIN':
        return ('3LIN', leaf[1] - s, leaf[2] - s, leaf[3] - s)
    if f == 'LINRAM2':
        return ('LINRAM2', leaf[1] - 3 * s, leaf[2] - 2 * s)
    if f == 'RAM2LIN':
        return ('RAM2LIN', leaf[1] - 3 * s, leaf[2] - s)
    if f == 'VERT1':
        return ('VERT1', leaf[1] - 3 * s, leaf[2] - s, leaf[3])
    if f == 'VERT2':
        return ('VERT2', leaf[1] - 3 * s, leaf[2] - s, leaf[3])
    raise ValueError(leaf)


def block_of_leaf(leaf, ms):
    f = leaf[0]
    if f == 'RAM2LIN':
        return ('RAM', leaf[1] - 3 * ms)
    if f == '3LIN':
        return ('2SIDED', leaf[2] - ms, leaf[1] - ms)
    if f == 'VERT2' and len(leaf) == 4:
        k = (leaf[1] - 3 * ms) // 2
        return (('SPLITEQ' if leaf[3] == '11' else 'INERTDEEP'), k)
    raise ValueError(leaf)


def agg_of_raw(rawkey):
    if rawkey[-1] == ('DRAIN',):
        return None
    i, m = 0, 0
    while rawkey[i][0] == 'ALPHA':
        m = rawkey[i][1]
        i += 1
    rest = rawkey[i:]
    if len(rest) == 1:
        fam = unshift_leaf(rest[0], m)
        return ('I',) + fam if m == 0 else ('II', m) + fam
    first = rest[0]
    leaf = rest[-1]
    if first[0] == 'FULL11SQ':
        ms = first[1]
        return ('B1', m, ms - m) + block_of_leaf(leaf, ms)
    if first[0] == 'VERT1':
        ms = first[2]
        k = ms - m
        w = (first[1] - 3 * m) - 3 * k
        return ('B2', m, k, w) + block_of_leaf(leaf, ms)
    if first[0] == 'VERT2' and len(first) == 3:
        ms = first[2]
        t = ms - m
        j = ((first[1] - 3 * m) - 3 * t) // 2
        return ('B3', m, t, j) + block_of_leaf(leaf, ms)
    raise ValueError(rawkey)


# ------------------------------------------------------------- row runner
XREAD_CAP = 65536


def w12_depth0_key(leaf):
    """my leaf key -> the sealed w12 depth0 key format."""
    return (leaf[0], tuple(leaf[1:]))


def enum_row(kind, q, N, do_xread):
    R = mkring(kind, q, N)
    K = R.K
    if kind == 'Zp':
        elems1 = [q * b for b in range(q ** (N - 1))]
        zero_res = 0
    else:
        els = list(K.elems())
        elems1 = [(K.zero(),) + rest
                  for rest in itertools.product(els, repeat=N - 1)]
        zero_res = K.zero()
    tally = {}
    xdiv = 0
    t0 = time.time()
    for B2 in elems1:
        for B1 in elems1:
            for B0 in elems1:
                key = read_menu(R, q, B2, B1, B0)
                tally[key] = tally.get(key, 0) + 1
                if do_xread:
                    rec = W12.read_trp(R, q, B2, B1, B0, zero_res)
                    dec = key[-1] != ('DRAIN',)
                    if rec['decided'] != dec:
                        xdiv += 1
                    if rec['depth0'] is not None:
                        if len(key) != 1 or \
                                w12_depth0_key(key[0]) != rec['depth0']:
                            xdiv += 1
                    elif len(key) == 1 and dec:
                        xdiv += 1
                    if dec and rec['sigma'] != \
                            tuple(sorted(leaf_sigma(key[-1]))):
                        xdiv += 1
    return tally, xdiv, time.time() - t0


def check_row(kind, q, N):
    states = q ** (3 * (N - 1))
    do_x = states <= XREAD_CAP
    tally, xdiv, el = enum_row(kind, q, N, do_x)
    pred = pred3(q, N)

    # HM3-MENU both directions
    menu_bad = 0
    for k in sorted(set(tally) | set(pred)):
        note('HM3-MENU')
        if tally.get(k, 0) != pred.get(k, 0):
            menu_bad += 1
            viol('HM3-MENU', '%s q=%d N=%d %s' % (kind, q, N, k),
                 'measured %d != pred %d'
                 % (tally.get(k, 0), pred.get(k, 0)))

    # HM3-DRAIN: partition + drain == u_law
    note('HM3-DRAIN', 2)
    if sum(tally.values()) != states:
        viol('HM3-DRAIN', 'partition %s q=%d N=%d' % (kind, q, N),
             'sum != q^(3N-3)')
    drain = sum(c for k, c in tally.items() if k[-1] == ('DRAIN',))
    if drain != u_law(N, q):
        viol('HM3-DRAIN', 'ulaw %s q=%d N=%d' % (kind, q, N),
             'drain %d != u_law %d' % (drain, u_law(N, q)))

    # HM3-AGG both directions (aggregate the MEASURED tally)
    got = {}
    for k, c in tally.items():
        ak = agg_of_raw(k)
        if ak is not None:
            got[ak] = got.get(ak, 0) + c
    want = agg_laws(q, N)
    for k in sorted(set(got) | set(want)):
        note('HM3-AGG')
        if got.get(k, 0) != want.get(k, 0):
            viol('HM3-AGG', '%s q=%d N=%d %s' % (kind, q, N, k),
                 'raw-sum %d != law %d' % (got.get(k, 0), want.get(k, 0)))

    # HM3-XREAD
    if do_x:
        note('HM3-XREAD', states)
        if xdiv:
            viol('HM3-XREAD', '%s q=%d N=%d' % (kind, q, N),
                 '%d divergences vs sealed read_trp' % xdiv)

    # teeth (corrupted predictors must mismatch the measurement)
    for tooth, kw in (('HM3-T-BRACKET', 'bracket_bad'),
                      ('HM3-T-SHEAR', 'shear_bad'),
                      ('HM3-T-L0BRK', 'l0brk_bad')):
        bad = pred3(q, N, **{kw: True})
        if bad != pred:
            if any(bad.get(k, 0) != tally.get(k, 0)
                   for k in set(bad) | set(tally)):
                FIRE[tooth] += 1
            else:
                viol('HM3-MENU', 'tooth %s %s q=%d N=%d'
                     % (tooth, kind, q, N),
                     'corrupted prediction matched measurement')

    deep = sum(c for k, c in tally.items()
               if len(k) >= 2 and k[-1] != ('DRAIN',))
    say('  [%s q=%d N=%d] states=%d keys=%d menu-bad=%d deep=%d drain=%d '
        'xread=%s %.1fs'
        % (kind, q, N, states, len(tally), menu_bad, deep, drain,
           ('%d-div' % xdiv) if do_x else 'skip', el))
    return tally


# --------------------------------------------------------------- rosters
ROWS_ZP = ([(2, N) for N in range(3, 10)] + [(3, N) for N in range(2, 7)]
           + [(5, 2), (5, 3), (5, 4), (7, 2), (7, 3), (13, 3)])
ROWS_FQT = ([(2, N) for N in range(3, 10)] + [(3, N) for N in range(2, 7)]
            + [(4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (7, 3),
               (8, 3), (9, 3), (11, 3), (27, 2)])
ORACLE_ROWS = [(2, 5), (2, 6), (2, 7), (3, 5)]
ORACLE_EXPECT = {(2, 5): 48, (2, 6): 624, (2, 7): 6688, (3, 5): 2592}

SMOKE_ZP = [(2, 4), (2, 5), (2, 6), (3, 4), (5, 3)]
SMOKE_FQT = [(2, 5), (3, 4), (4, 4), (27, 2)]
SMOKE_ORACLE = [(2, 5)]


# --------------------------------------------------------------- ties
def hex3_tie(tallies, smoke):
    with open(os.path.join(HERE, 'hex3_checks_results.json')) as f:
        hx = json.load(f)
    n = 0
    for r in hx['rows']:
        key = (r['kind'], r['q'], r['N'])
        if key not in tallies:
            continue
        n += 1
        # my first-step species map
        mine = {}
        for k, c in tallies[key].items():
            if k == (('DRAIN',),):
                sp = ('B0ZERO',)
            elif len(k) == 1:
                sp = ('DECIDED',)
            else:
                sp = k[0]
            loc, dr = mine.get(sp, (0, 0))
            mine[sp] = (loc + c, dr + (c if k[-1] == ('DRAIN',) else 0))
        theirs = {eval(kk): tuple(v) for kk, v in r['species_tally'].items()}
        note('HM3-HEX3TIE')
        if mine != theirs:
            viol('HM3-HEX3TIE', str(key), 'species maps differ: %s vs %s'
                 % (mine, theirs))
    say('HM3-HEX3TIE: %d committed hex3 rows tied' % n)


def w12_ties(tallies, smoke):
    with open(os.path.join(HERE, 'w12_checks_results.json')) as f:
        w12res = json.load(f)
    n0 = nd = 0
    for r in w12res['cubic']:
        kind, q, N = r['kind'], r['q'], r['N']
        # depth0_keys tie (JSON vs q x Group-I laws; no enumeration needed)
        mine0 = {}
        for k, c in pred_depth0(q, N, 0).items():
            mine0[w12_depth0_key(k[0])] = q * c
        theirs0 = {eval(kk): v for kk, v in r['depth0_keys'].items()}
        note('HM3-W12TIE')
        n0 += 1
        if mine0 != theirs0:
            viol('HM3-W12TIE', 'depth0 %s q=%d N=%d' % (kind, q, N),
                 'depth0_keys differ')
        # U3TRP + deep-decided ties
        note('HM3-W12TIE', 2)
        if r['U3TRP_measured_conservative'] != q * u_law(N, q):
            viol('HM3-W12TIE', 'U3 %s q=%d N=%d' % (kind, q, N),
                 'committed U3TRP != q*u_law')
        deep_pred = q * sum(c for k, c in pred3(q, N).items()
                            if len(k) >= 2 and k[-1] != ('DRAIN',))
        if r['trp_deep_decided'] != deep_pred:
            viol('HM3-W12TIE', 'deep %s q=%d N=%d' % (kind, q, N),
                 'committed deep %d != q*pred %d'
                 % (r['trp_deep_decided'], deep_pred))
        # DBL tie: dbl_keys summed over histories == whole-space DBL laws
        agg = {}
        for kk, v in r['dbl_keys'].items():
            fam, params, hist = eval(kk)
            k2 = (fam,) + params
            agg[k2] = agg.get(k2, 0) + v
        mineD = {L: q * (q - 1) * q ** (N - 1) * c
                 for L, c in A_L(q, N).items()}
        # the (A2)-routed DBL boundary masses (aggregated over histories:
        # TAIL(w): (q-1) q^{N-2} each, w = 1..(N-1)//2; UNDEC: q^{N-1})
        for w in range(1, (N - 1) // 2 + 1):
            mineD[('SPLIT-TAIL', w)] = \
                q * (q - 1) * q ** (N - 1) * (q - 1) * q ** (N - 2)
        mineD[('UNDECIDED',)] = q * (q - 1) * q ** (N - 1) * q ** (N - 1)
        note('HM3-DBLTIE')
        nd += 1
        if agg != mineD:
            viol('HM3-DBLTIE', '%s q=%d N=%d' % (kind, q, N),
                 'dbl aggregate differs: %s vs %s' % (agg, mineD))
    say('HM3-W12TIE: %d rows tied; HM3-DBLTIE: %d rows tied' % (n0, nd))


# --------------------------------------------------------------- oracle
def run_oracle(rows):
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(256 * 1024 * 1024)

    def pari_sigma(p, N, B2, B1, B0):
        f = pari('x^3 + %d*x^2 + %d*x + %d' % (B2, B1, B0))
        fp = pari.factorpadic(f, p, N + 15)
        out = []
        for i in range(len(fp[0])):
            g = pari.liftall(fp[0][i])
            assert int(fp[1][i]) == 1
            d = int(pari.poldegree(g))
            if d == 1:
                out.append((1, 1))
            else:
                L = pari.nfinit(g)
                dec = pari.idealprimedec(L, p)
                assert len(dec) == 1
                e, ff = int(dec[0][2]), int(dec[0][3])
                assert e * ff == d
                out.append((e, ff))
        return tuple(sorted(out))

    for (p, N) in rows:
        R = W10.ZpWin(p, N)
        elems1 = [p * b for b in range(p ** (N - 1))]
        n_deep = bad = 0
        bad_tooth_caught = False
        t0 = time.time()
        for B2 in elems1:
            for B1 in elems1:
                for B0 in elems1:
                    key = read_menu(R, p, B2, B1, B0)
                    if len(key) < 2 or key[-1] == ('DRAIN',):
                        continue
                    n_deep += 1
                    got = pari_sigma(p, N, B2, B1, B0)
                    note('HM3-ORACLE')
                    if got != tuple(sorted(leaf_sigma(key[-1]))):
                        bad += 1
                        if bad <= 5:
                            viol('HM3-ORACLE', '(Zp,%d,%d) %s'
                                 % (p, N, key), 'PARI %s' % (got,))
                    if got != tuple(sorted(leaf_sigma(key[-1],
                                                      sigma_bad=True))):
                        bad_tooth_caught = True
        note('HM3-ORACLE')
        exp = ORACLE_EXPECT.get((p, N))
        if exp is not None and n_deep != exp:
            viol('HM3-ORACLE', 'count (Zp,%d,%d)' % (p, N),
                 'deep members %d != preregistered %d' % (n_deep, exp))
        if bad_tooth_caught:
            FIRE['HM3-T-SIGMA'] += 1
        else:
            viol('HM3-ORACLE', 'tooth (Zp,%d,%d)' % (p, N),
                 'corrupted sigma table not caught')
        say('  ORACLE [Zp q=%d N=%d] deep=%d bad=%d %.1fs'
            % (p, N, n_deep, bad, time.time() - t0))


# --------------------------------------------------------------- R_tau leg
def rtau_leg():
    import sympy as sp
    q = sp.symbols('q', positive=True)
    Phi5 = q ** 4 + q ** 3 + q ** 2 + q + 1
    R = {                                    # COROLLARY HM3.D display
        '111':   q ** 3 * (q ** 2 - q + 1) / (6 * (q + 1) * Phi5),
        '12_11': q ** 3 * (q ** 2 + q + 1) / (2 * (q + 1) * Phi5),
        '3':     q ** 3 * (q + 1) / (3 * Phi5),
        '21_11': q * (q ** 3 + q + 1) / ((q + 1) * Phi5),
        '31':    (q ** 2 + 1) / Phi5,
    }
    note('HM3-RTAU')
    if sp.simplify(sum(R.values()) - 1) != 0:
        viol('HM3-RTAU', 'sum', 'Sum R_tau != 1')

    # tie to om_density_engine's cluster laws (monic level-0 assembly)
    import om_density_engine as E
    qe = E.q
    b2, b3 = E.beta(2), E.beta(3)
    from collections import defaultdict

    def uni(*ts):
        out = []
        for t in ts:
            out += list(t)
        return tuple(sorted(out))
    acc = defaultdict(lambda: sp.Integer(0))
    pats = [
        (qe * (qe - 1) * (qe - 2) / 6,
         [{((1, 1),): 1}, {((1, 1),): 1}, {((1, 1),): 1}]),
        (qe * (qe ** 2 - qe) / 2, [{((1, 1),): 1}, {((1, 2),): 1}]),
        ((qe ** 3 - qe) / 3, [{((1, 3),): 1}]),
        (qe * (qe - 1), [b2, {((1, 1),): 1}]),
        (qe, [b3]),
    ]
    for C0, dists in pats:
        agg = {(): sp.Integer(1)}
        for dist in dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[uni(t0, t1)] += p0 * p1
            agg = dict(new)
        for t, p in agg.items():
            acc[t] += C0 / qe ** 3 * p
    TYP = {'111': ((1, 1), (1, 1), (1, 1)), '12_11': ((1, 1), (1, 2)),
           '3': ((1, 3),), '21_11': ((1, 1), (2, 1)), '31': ((3, 1),)}
    for tt, tau in TYP.items():
        note('HM3-RTAU')
        d = sp.simplify(R[tt].subs(q, qe) - acc[tuple(sorted(tau))])
        if d != 0:
            viol('HM3-RTAU', 'engine-tie %s' % tt, sp.factor(d))

    # exact partial sums of the aggregate menu -> R_tau; and the exact
    # per-center identity Sum_tau D_tau(N) == q^{3(N-1)} - u(q,N)
    def sig_of_agg(k):
        if k[0] in ('I', 'II'):
            leaf = k[2:] if k[0] == 'II' else k[1:]
            fam = leaf[0]
            if fam == 'RAM3':
                return '31'
            if fam == '3LIN':
                return '111'
            if fam in ('LINRAM2', 'RAM2LIN'):
                return '21_11'
            if fam in ('VERT1', 'VERT2'):
                return '111' if leaf[-1] == '11' else '12_11'
            return {'111': '111', '12': '12_11', '3': '3'}[leaf[-1]]
        L = {'RAM': '21_11', '2SIDED': '111', 'SPLITEQ': '111',
             'INERTDEEP': '12_11'}
        blk = k[3] if k[0] in ('B1',) else k[4] if k[0] == 'B2' else k[4]
        # block type name position: B1: k[3], B2: k[4], B3: k[4]
        return L[blk]

    for qq in (2, 3, 4, 5):
        Nbig = 24
        D = {tt: 0 for tt in R}
        for k, c in agg_laws(qq, Nbig).items():
            D[sig_of_agg(k)] += c
        # TRP identity
        note('HM3-RTAU')
        if sum(D.values()) != qq ** (3 * (Nbig - 1)) - u_law(Nbig, qq):
            viol('HM3-RTAU', 'identity q=%d' % qq,
                 'Sum_tau D_tau != q^(3N-3) - u')
        # whole-space partial (SEP + DBL + q*TRP) -> R_tau
        SEP = {'111': Fraction(qq * (qq - 1) * (qq - 2), 6),
               '12_11': Fraction(qq ** 2 * (qq - 1), 2),
               '3': Fraction(qq ** 3 - qq, 3)}
        DBLs = {'21_11': 0, '111': 0, '12_11': 0}
        for L, c in A_L(qq, Nbig).items():
            key = {'RAM': '21_11', '2SIDED': '111', 'SPLITEQ': '111',
                   'INERTDEEP': '12_11'}[L[0]]
            DBLs[key] += c
        for tt in R:
            # whole-space density partial sum: SEP + DBL + q x TRP
            dens = Fraction(SEP.get(tt, 0), qq ** 3) \
                + Fraction(qq * (qq - 1) * qq ** (Nbig - 1)
                           * DBLs.get(tt, 0), qq ** (3 * Nbig)) \
                + Fraction(qq * D[tt], qq ** (3 * Nbig))
            Rv = sp.nsimplify(R[tt].subs(q, qq))
            Rv = Fraction(int(Rv.p), int(Rv.q))
            rem = Rv - dens
            note('HM3-RTAU')
            if not (0 < rem < Fraction(1, qq ** (Nbig - 4))):
                viol('HM3-RTAU', 'series q=%d tau=%s' % (qq, tt),
                     'remainder %s out of (0, q^-(N-4))' % rem)
    say('HM3-RTAU: symbolic + series checks done')


# ------------------------------------------------------------------ main
def main(smoke=False):
    t0 = time.time()
    say('HMENU3 battery %s' % ('SMOKE' if smoke else 'FULL'))

    for fn, md5 in PINS.items():
        note('HM3-PIN')
        with open(os.path.join(HERE, fn), 'rb') as f:
            got = hashlib.md5(f.read()).hexdigest()
        if got != md5:
            viol('HM3-PIN', fn, 'md5 %s != pinned %s' % (got, md5))

    rows_zp = SMOKE_ZP if smoke else ROWS_ZP
    rows_fqt = SMOKE_FQT if smoke else ROWS_FQT
    tallies = {}
    results = []
    for kind, roster in (('Zp', rows_zp), ('Fqt', rows_fqt)):
        for (qq, N) in roster:
            tly = check_row(kind, qq, N)
            tallies[(kind, qq, N)] = tly
            results.append({
                'kind': kind, 'q': qq, 'N': N,
                'states': qq ** (3 * (N - 1)),
                'n_keys': len(tly),
                'deep_decided': sum(c for k, c in tly.items()
                                    if len(k) >= 2 and k[-1] != ('DRAIN',)),
                'drain': sum(c for k, c in tly.items()
                             if k[-1] == ('DRAIN',)),
                'menu_tally': {repr(k): v for k, v in sorted(tly.items())},
            })

    hex3_tie(tallies, smoke)
    w12_ties(tallies, smoke)
    run_oracle(SMOKE_ORACLE if smoke else ORACLE_ROWS)
    rtau_leg()

    elapsed = time.time() - t0
    say('')
    say('==== SUMMARY ====')
    red = False
    for f in FAMILIES:
        say('%-12s checks=%-9d violations=%d' % (f, NCHK[f], len(VIOL[f])))
        if VIOL[f]:
            red = True
    for t in TEETH:
        exp = TEETH_EXPECT[t] if not smoke else None
        ok = (FIRE[t] == exp) if exp is not None else (FIRE[t] >= 1)
        say('%-14s fired=%d expected=%s %s'
            % (t, FIRE[t], exp if exp is not None else '>=1',
               'OK' if ok else 'RED'))
        if not ok:
            red = True
    verdict = 'RED' if red else 'GREEN'
    say('VERDICT: %s (%.1fs)' % (verdict, elapsed))

    out = {'smoke': smoke, 'rows': results,
           'families': {f: {'checks': NCHK[f], 'violations': VIOL[f]}
                        for f in FAMILIES},
           'teeth': {t: FIRE[t] for t in TEETH},
           'teeth_expected': TEETH_EXPECT,
           'verdict': verdict, 'elapsed_s': round(elapsed, 1)}
    if not smoke:
        with open(os.path.join(HERE, 'hmenu3_checks_results.json'),
                  'w') as f:
            json.dump(out, f, indent=1)
        with open(os.path.join(HERE, 'hmenu3_checks_output.txt'),
                  'w') as f:
            f.write('\n'.join(LOG) + '\n')
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
