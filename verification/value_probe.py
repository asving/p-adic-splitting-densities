#!/usr/bin/env python3
"""value_probe.py — R1 wall probe: are VALUE-linked stratum counts universal in q?

EXPLORATION-CLASS (no seal).  Spec: ASSEMBLY_PLAN_2026-07-26.md §2v NOTE [1v]
(VALUE-Fq gate geometry) + §8 R1 (the wall experiment).  The retired torus lemma
(D4R.3, counterexample on record) claimed uniform vtx-fibers; this probe measures
the STRATIFIED fiber calculus (VAL.1/VAL.2) and the aggregate fallback (VAL.3)
by EXACT exhaustive enumeration over F_q — no sampling anywhere.

FAMILY FAM-L (the plan's sealed counterexample family).  Parent node: residual
shape psi^2 * (A z + B), psi monic irreducible quadratic over F_q, A, B in F_q*
(nonzero-endpoint convention), mu = 2.  Value assignments = (psi, A, B).
Transported vertex value per C.0:  vtx = alpha^aeff * (A alpha + B) in F_{q^2}*,
alpha = class of z in F' := F_q[z]/psi; aeff := a - mu*mhat probed in {0,1,2}
(the plan's a in {0,1} plus one more alpha-twist).
Child node at the deg-2 key over F': (HV) pins the child's vertex pattern digit
t = vtx(parent); child residual shapes (deg <= 2 menu, both endpoints nonzero):
  lin   : d1*w + t, d1 != 0                       (linear side, e'=1)
  e2    : d2*w + t in the e'=2 compressed variable (same count, separate leg)
  irr   : d2*w^2 + d1*w + t irreducible over F'
  split : d2*w^2 + d1*w + t = d2(w-r)(w-s), r != s in F'* (distinct nonzero roots)
  dbl   : d2*(w-r)^2, r in F'*, const = t          (mu'=2 continuation)
LINKED COUNT C_{S}(q) = #{(psi,A,B, child digits) : shapes + endpoints + (HV)}.

STRATIFICATIONS measured (VAL.1/VAL.2): targets t in F'* classified in
  FIXED cells   : FS = F_q* (x=0), FL = F_q*.alpha (y=0), FG = both coords != 0
                  (coords in basis {alpha, 1}: t = x*alpha + y)
  TWISTED cells : same cells applied to alpha^{-aeff} * t (anchor-aligned).
Per-cell parent counts, per-cell fiber constancy (max=min), 3x3 joint matrix.

FAMILY FAM-Q (EXTRA, exploration): parent cofactor quadratic A z^2 + B z + D,
A, D != 0, coprime to psi; vtx = alpha^aeff*(A alpha^2 + B alpha + D); fibers
genuinely non-constant sizes (q-1 / q-2 / q-3) — VAL.1 refinement stress test.
Run at small q only (parent-side series, degree <= 5).

Q POINTS.  Sealed by the plan: q in {2,3,4,5,7,8,9,11,13}.  EXTRA consistency
points (exploration-class; needed because linked totals have degree up to 12
in q, unresolvable on 9 points): primes to 43 (+49) and powers 16,25,27,32,49.

POLYNOMIALITY VERDICT (defined here, before any enumeration ran):
  exact Newton interpolation over Fractions through ALL points of a series;
  UNIVERSAL(d)  iff interpolant degree d <= (#points - 1) - 3  (>= 3 excess);
  else CHAR-SPLIT if the odd-char subseries interpolates with >= 2 excess and
  char-2 points deviate from the odd interpolant (per-class forms reported);
  else FINE-SPLIT if the classes by (char = 2, q mod 3) each fit with >= 2
  excess (total excess >= 3; thin classes < 4 pts listed unfitted);
  else IRREGULAR.  Reported per series.
AGGREGATE / WILD-p TEST (plan §8 R1(2),(3), charge part 2): aggregate series
  AGG_s(q) = sum over aeff in {0,1} of linked totals (per child type s), plus
  the sum over cells of every char-split per-cell series; fit each aggregate on
  TAME points (char not in {2,3}); PASS iff the wild-char values (q = 2,4,8,16,
  32 for p=2; q = 3,9,27 for p=3) match the tame interpolant EXACTLY.
R1 READING (plan's own criterion): linked C_S(q) universal at every S =>
  NO-WALL; non-universal but aggregates match at wild p => VAL.3 route
  (needs-refinement); aggregates provably off the tame interpolation at wild
  p => WALL.  Per-cell non-universality with universal linked totals is a
  recorded VAL.2-stratification refinement instruction, not a wall.

In-script predicted closed forms (derivation-grade, same-context — adjudication
aid only, NOT a seal): see PRED table below the enumeration code.

Run:  python3 value_probe.py
      full tables -> results/value_probe_output.txt
      all series  -> results/value_probe_series.json ; summary on stdout
"""
import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
OUTTXT = os.path.join(HERE, 'results', 'value_probe_output.txt')
OUTJSON = os.path.join(HERE, 'results', 'value_probe_series.json')

QS_SEALED = [2, 3, 4, 5, 7, 8, 9, 11, 13]
QS_EXTRA = [16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 49, 53, 59]
QS_ALL = sorted(QS_SEALED + QS_EXTRA)
QS_FAMQ = sorted(QS_SEALED + [16, 17, 19])      # FAM-Q small-q run
CHAR2 = {2, 4, 8, 16, 32}
CHAR3 = {3, 9, 27}
AEFFS = (0, 1, 2)
CHILD_TYPES = ('lin', 'e2', 'irr', 'split', 'dbl')

# base fields F_{p^k}: q -> (p, defining poly low->high, monic)
IRRED = {4: (2, [1, 1, 1]), 8: (2, [1, 1, 0, 1]), 9: (3, [1, 0, 1]),
         16: (2, [1, 1, 0, 0, 1]), 25: (5, [1, 1, 1]), 27: (3, [1, 2, 0, 1]),
         32: (2, [1, 0, 1, 0, 0, 1]), 49: (7, [3, 1, 1])}


class GF:
    """F_q as ints 0..q-1 (base-p digit encoding); exhaustive add/mul tables."""

    def __init__(self, q):
        self.q = q
        if q in IRRED:
            p, poly = IRRED[q]
            k = len(poly) - 1
        else:
            p, poly, k = q, None, 1
        self.p, self.k = p, k

        def digs(e):
            return [(e // p**i) % p for i in range(k)]

        def undigs(d):
            return sum(c * p**i for i, c in enumerate(d))

        def polymulmod(a, b):
            r = [0] * (2 * k - 1)
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    r[i + j] = (r[i + j] + x * y) % p
            for i in range(2 * k - 2, k - 1, -1):     # reduce by monic poly
                c = r[i]
                if c:
                    for j in range(k + 1):
                        r[i - k + j] = (r[i - k + j] - c * poly[j]) % p
            return r[:k]

        self.add = [[undigs([(x + y) % p for x, y in zip(digs(a), digs(b))])
                     for b in range(q)] for a in range(q)]
        if k == 1:
            self.mul = [[(a * b) % p for b in range(q)] for a in range(q)]
        else:
            self.mul = [[undigs(polymulmod(digs(a), digs(b)))
                         for b in range(q)] for a in range(q)]
        self.neg = [self.add[a].index(0) for a in range(q)]
        self.inv = [0] * q
        for a in range(1, q):
            self.inv[a] = self.mul[a].index(1)
        # sanity: field axioms spot-grid (exhaustive assoc for q <= 9)
        if q <= 9:
            for a in range(q):
                for b in range(q):
                    for c in range(q):
                        assert self.mul[a][self.mul[b][c]] == \
                            self.mul[self.mul[a][b]][c]
        assert all(self.mul[1][a] == a for a in range(q))

    def sub(self, a, b):
        return self.add[a][self.neg[b]]


def irreducible_quadratics(F):
    """All (c1, c0) with z^2 + c1 z + c0 irreducible over F (no root, exhaustive)."""
    out = []
    for c1 in range(F.q):
        for c0 in range(F.q):
            if all(F.add[F.mul[z][F.add[z][c1]]][c0] != 0 for z in range(F.q)):
                out.append((c1, c0))
    return out



# ---------------------------------------------------------------- extension F'
# F' = F_q[z]/(z^2 + c1 z + c0); elements (x, y) = x*alpha + y.

def emul(F, c1, c0, u, v):
    """(x1 a + y1)(x2 a + y2) with a^2 = -c1 a - c0."""
    (x1, y1), (x2, y2) = u, v
    M, A, S = F.mul, F.add, F.sub
    xx = M[x1][x2]
    return (S(A[M[x1][y2]][M[y1][x2]], M[c1][xx]),
            S(M[y1][y2], M[c0][xx]))


def cell_of(t):
    """FIXED cell of t = (x, y) in F'*: FS (x=0), FL (y=0), FG (both nonzero)."""
    x, y = t
    if x == 0:
        return 'FS'
    return 'FL' if y == 0 else 'FG'


def parent_census_L(F, quads):
    """FAM-L exhaustive parent census.  Returns per aeff:
    total, fixed-cell counts, twisted-cell counts, 3x3 joint (fixed,twisted),
    per-cell fiber constancy data (min/max fiber over targets IN each cell,
    twisted cells; fibers counted per psi — targets live in psi's own F').
    Also #psi and #psi with c1 = 0 (the char-split generator)."""
    q = F.q
    cells = ('FG', 'FS', 'FL')
    res = {a: {'total': 0,
               'fixed': dict.fromkeys(cells, 0),
               'twist': dict.fromkeys(cells, 0),
               'joint': {(f, t): 0 for f in cells for t in cells},
               'fib': {c: [None, 0] for c in cells}}   # [min, max] per twisted cell
           for a in AEFFS}
    units = [(x, y) for x in range(q) for y in range(q) if (x, y) != (0, 0)]
    for c1, c0 in quads:
        # alpha powers and inverse of alpha: a^-1 = -(a + c1)/c0  (a(a+c1) = -c0)
        alpha = (1, 0)
        ic0 = F.inv[c0]
        ainv = (F.neg[ic0], F.neg[F.mul[c1][ic0]])
        apow = {0: (0, 1), 1: alpha, 2: emul(F, c1, c0, alpha, alpha)}
        ainvpow = {0: (0, 1), 1: ainv, 2: emul(F, c1, c0, ainv, ainv)}
        for a in AEFFS:
            fib = {}
            for A in range(1, q):
                for B in range(1, q):
                    t = emul(F, c1, c0, apow[a], (A, B))    # alpha^a (A alpha + B)
                    fib[t] = fib.get(t, 0) + 1
                    r = res[a]
                    r['total'] += 1
                    fc = cell_of(t)
                    tc = cell_of(emul(F, c1, c0, ainvpow[a], t))
                    r['fixed'][fc] += 1
                    r['twist'][tc] += 1
                    r['joint'][(fc, tc)] += 1
            # fiber constancy per TWISTED cell: every target of F'* scanned
            for t in units:
                tc = cell_of(emul(F, c1, c0, ainvpow[a], t))
                f = fib.get(t, 0)
                mm = res[a]['fib'][tc]
                mm[0] = f if mm[0] is None else min(mm[0], f)
                mm[1] = max(mm[1], f)
    n0 = sum(1 for c1, c0 in quads if c1 == 0)
    return res, len(quads), n0


def parent_census_Q(F, quads, aeffs=(0, 1)):
    """FAM-Q (EXTRA): cofactor A z^2 + B z + D, A,D != 0, coprime to psi.
    vtx = alpha^aeff * (A alpha^2 + B alpha + D).  Fixed/twisted cell counts +
    global fiber-size histogram per (aeff) (sizes pooled over psi)."""
    q = F.q
    cells = ('FG', 'FS', 'FL')
    res = {a: {'total': 0, 'fixed': dict.fromkeys(cells, 0),
               'twist': dict.fromkeys(cells, 0), 'fibhist': {}} for a in aeffs}
    for c1, c0 in quads:
        alpha = (1, 0)
        ic0 = F.inv[c0]
        ainv = (F.neg[ic0], F.neg[F.mul[c1][ic0]])
        a2 = emul(F, c1, c0, alpha, alpha)
        apow = {0: (0, 1), 1: alpha, 2: a2}
        ainvpow = {0: (0, 1), 1: ainv, 2: emul(F, c1, c0, ainv, ainv)}
        for a in aeffs:
            fib = {}
            for A in range(1, q):
                Aa2 = emul(F, c1, c0, (0, A), a2)
                for B in range(q):
                    ABa = (F.add[Aa2[0]][B], Aa2[1])      # A a^2 + B a
                    for D in range(1, q):
                        s = (ABa[0], F.add[ABa[1]][D])
                        if s == (0, 0):
                            continue                       # psi | cofactor: mu jumps
                        t = emul(F, c1, c0, apow[a], s)
                        fib[t] = fib.get(t, 0) + 1
                        r = res[a]
                        r['total'] += 1
                        r['fixed'][cell_of(t)] += 1
                        r['twist'][cell_of(emul(F, c1, c0, ainvpow[a], t))] += 1
            h = res[a]['fibhist']
            for f in fib.values():
                h[f] = h.get(f, 0) + 1
    return res


# ------------------------------------------------------------------ child side
# Child of type X given pinned vertex digit t (constant term, C.0 anchoring):
# residual d2 w^2 + d1 w + t, d2 != 0 (free endpoint).  Writing it as
# d2*(w^2 + b w + c) with b = d1/d2 (bijection) and c = t/d2 (as d2 ranges over
# units, c ranges over ALL units bijectively), the count per t is
# sum_{c != 0} NX(c) with NX(c) = #{b : w^2 + b w + c has type X} — the same
# for EVERY t (t-independence is exact, not assumed; literal per-t enumeration
# is additionally run at q = 2).  Nonzero roots are automatic (root product =
# c != 0).  Exactly one distinct root <=> double root (deg-2 cofactor is linear).

def child_counts_monic(F, c1, c0):
    """Exhaustive: classify every monic w^2 + b w + c (c != 0) over F' by a
    genuine root loop; return {type: sum_c NX(c)} plus per-c table for 'irr'
    (the fixed-const character structure exhibit)."""
    q = F.q
    Fp = [(x, y) for x in range(q) for y in range(q)]
    units = [t for t in Fp if t != (0, 0)]
    sq = {w: emul(F, c1, c0, w, w) for w in Fp}
    cnt = dict.fromkeys(CHILD_TYPES, 0)
    cnt['lin'] = cnt['e2'] = len(units)
    irr_per_c = {}
    for c in units:
        nirr = 0
        for b in Fp:
            nroots = 0
            for w in Fp:
                bw = emul(F, c1, c0, b, w)
                v = (F.add[F.add[sq[w][0]][bw[0]]][c[0]],
                     F.add[F.add[sq[w][1]][bw[1]]][c[1]])
                if v == (0, 0):
                    nroots += 1
            if nroots == 0:
                cnt['irr'] += 1
                nirr += 1
            elif nroots == 2:
                cnt['split'] += 1
            else:
                assert nroots == 1
                cnt['dbl'] += 1
        irr_per_c[c] = nirr
    return cnt, irr_per_c


def child_counts_literal_q2(F, c1, c0):
    """Literal per-t enumeration at q = 2 ONLY (Q = 16): loop t, d2, d1 with
    genuine root loops; returns {t: counts} to check exact t-independence."""
    q = F.q
    assert q == 2
    Fp = [(x, y) for x in range(q) for y in range(q)]
    units = [t for t in Fp if t != (0, 0)]
    perT = {}
    for t in units:
        cnt = dict.fromkeys(CHILD_TYPES, 0)
        cnt['lin'] = cnt['e2'] = len(units)
        for d2 in units:
            for d1 in Fp:
                nroots = 0
                for w in Fp:
                    w2 = emul(F, c1, c0, w, w)
                    v = emul(F, c1, c0, d2, w2)
                    bw = emul(F, c1, c0, d1, w)
                    v = (F.add[F.add[v[0]][bw[0]]][t[0]],
                         F.add[F.add[v[1]][bw[1]]][t[1]])
                    if v == (0, 0):
                        nroots += 1
                cnt[{0: 'irr', 1: 'dbl', 2: 'split'}[nroots]] += 1
        perT[t] = cnt
    return perT


def child_counts_formula(q):
    """Root-parametrized exact counts over F' (|F'| = Q = q^2), const term t
    pinned nonzero, lead endpoint free nonzero:
      lin/e2: Q-1;  split: (Q-1)(Q-2)/2;  dbl: Q-1;  irr: (Q^2-Q)/2."""
    Q = q * q
    return {'lin': Q - 1, 'e2': Q - 1, 'split': (Q - 1) * (Q - 2) // 2,
            'dbl': Q - 1, 'irr': (Q * Q - Q) // 2}



# ------------------------------------------------- exact polynomial machinery
def newton_interp(pts):
    """Exact Newton interpolation through pts = [(q, v)]; returns (degree,
    coeffs in the standard basis as Fractions, callable eval)."""
    xs = [Fraction(x) for x, _ in pts]
    coef = [Fraction(v) for _, v in pts]
    for j in range(1, len(pts)):
        for i in range(len(pts) - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    # expand to standard basis
    poly = [Fraction(0)] * len(pts)
    acc = [Fraction(1)]                       # prod (x - xs[k]), k < j
    for j, c in enumerate(coef):
        for i, a in enumerate(acc):
            poly[i] += c * a
        na = [Fraction(0)] * (len(acc) + 1)
        for i, a in enumerate(acc):
            na[i] -= a * xs[j]
            na[i + 1] += a
        acc = na
    deg = max((i for i, c in enumerate(poly) if c != 0), default=0)
    poly = poly[:deg + 1]

    def ev(x):
        x = Fraction(x)
        s = Fraction(0)
        for c in reversed(poly):
            s = s * x + c
        return s
    return deg, poly, ev


def polystr(poly):
    return ' + '.join('%s q^%d' % (c, i) if i else str(c)
                      for i, c in enumerate(poly) if c != 0) or '0'


def verdict(name, data, out):
    """data: {q: int}.  Verdict per the docstring rule.  Returns tag string."""
    pts = sorted(data.items())
    deg, poly, _ = newton_interp(pts)
    excess = len(pts) - 1 - deg
    if excess >= 3:
        out.append('  %-46s UNIVERSAL deg %d (excess %d): %s'
                   % (name, deg, excess, polystr(poly)))
        return 'UNIVERSAL'
    odd = [(q, v) for q, v in pts if q not in CHAR2]
    ch2 = [(q, v) for q, v in pts if q in CHAR2]
    if len(odd) >= 3:
        dodd, podd, evodd = newton_interp(odd)
        exodd = len(odd) - 1 - dodd
        dev2 = [(q, v) for q, v in ch2 if evodd(q) != v]
        if exodd >= 2 and dev2:
            d2s = ''
            if len(ch2) >= 2:
                dch2, pch2, _ = newton_interp(ch2)
                d2s = '; char2 (%d pts, deg %d): %s' % (len(ch2), dch2,
                                                        polystr(pch2))
            out.append('  %-46s CHAR-SPLIT: odd deg %d (excess %d): %s%s'
                       % (name, dodd, exodd, polystr(podd), d2s))
            # sub-split within odd (e.g. q mod 3)?
            do3 = [(q, v) for q, v in odd if evodd(q) != v]
            if do3:
                out.append('      [odd-fit deviants: %s]' % do3)
            return 'CHAR-SPLIT'
    # finest preregistered layer: classes by (char == 2, q mod 3)
    classes = {}
    for q, v in pts:
        classes.setdefault(('char2' if q in CHAR2 else 'odd', q % 3),
                           []).append((q, v))
    big = {k: c for k, c in classes.items() if len(c) >= 4}
    if big:
        fits, totex, okc = [], 0, True
        for k in sorted(big):
            d, p, _ = newton_interp(big[k])
            ex = len(big[k]) - 1 - d
            totex += ex
            okc &= ex >= 2
            fits.append('%s: deg %d (excess %d): %s' % (k, d, ex, polystr(p)))
        if okc and totex >= 3:
            out.append('  %-46s FINE-SPLIT(char,mod3):' % name)
            for f in fits:
                out.append('      %s' % f)
            small = {k: c for k, c in classes.items() if k not in big}
            if small:
                out.append('      [thin classes, no fit attempted: %s]'
                           % {k: c for k, c in sorted(small.items())})
            return 'FINE-SPLIT'
    out.append('  %-46s IRREGULAR (all-pts deg %d, excess %d)'
               % (name, deg, excess))
    return 'IRREGULAR'


def wild_test(name, data, out):
    """Aggregate/wild test: fit on tame (char not in {2,3}), evaluate at the
    wild-char points.  PASS iff every wild point matches exactly AND the tame
    fit has >= 3 excess.  Returns (p2ok, p3ok) or None if underdetermined."""
    pts = sorted(data.items())
    tame = [(q, v) for q, v in pts if q not in CHAR2 and q not in CHAR3]
    dt, pt_, evt = newton_interp(tame)
    ext = len(tame) - 1 - dt
    p2 = [(q, v, evt(q)) for q, v in pts if q in CHAR2]
    p3 = [(q, v, evt(q)) for q, v in pts if q in CHAR3]
    p2ok = all(v == e for _, v, e in p2)
    p3ok = all(v == e for _, v, e in p3)
    out.append('  %-46s tame fit deg %d (excess %d) -> p=2 pts %s | p=3 pts %s'
               % (name, dt, ext,
                  'MATCH' if p2ok else 'DEVIATE %s' % [(q, v - e) for q, v, e
                                                       in p2 if v != e],
                  'MATCH' if p3ok else 'DEVIATE %s' % [(q, v - e) for q, v, e
                                                       in p3 if v != e]))
    return (p2ok and ext >= 3, p3ok and ext >= 3)


# ------------------------- predicted closed forms (adjudication aid, no seal)
def npsi(q):
    return (q * q - q) // 2


def pred_FAML(q):
    """{series: value} predictions derived in-context (see analysis note):
    nz1 := #psi with c1 != 0 (char2: all; odd: (q-1)^2/2);
    n_eq := #psi of form z^2+cz+c^2, c != 0 (irreducible iff -3 nonsquare:
    odd q: q = 3: 0; q = 1 mod 3: 0; q = 2 mod 3: q-1 | char2: q-1 if k odd
    else 0)."""
    tot = npsi(q) * (q - 1) ** 2
    if q in CHAR2:
        nz1 = npsi(q)
        k = {2: 1, 4: 2, 8: 3, 16: 4, 32: 5}[q]
        n_eq = (q - 1) if k % 2 == 1 else 0
    else:
        nz1 = (q - 1) ** 2 // 2
        p = 3 if q in CHAR3 else q
        n_eq = 0 if (q % 3 != 2) else (q - 1)
    pr = {'aeff0/fixed/FG': tot, 'aeff0/fixed/FS': 0, 'aeff0/fixed/FL': 0,
          'aeff1/fixed/FS': (q - 1) * nz1, 'aeff1/fixed/FL': 0,
          'aeff1/fixed/FG': tot - (q - 1) * nz1,
          'aeff2/fixed/FL': (q - 1) * nz1,
          'aeff2/fixed/FS': (q - 1) * (nz1 - n_eq),
          'aeff2/fixed/FG': tot - (q - 1) * (2 * nz1 - n_eq)}
    for a in AEFFS:
        pr['aeff%d/total' % a] = tot
        pr['aeff%d/twist/FG' % a] = tot
        pr['aeff%d/twist/FS' % a] = 0
        pr['aeff%d/twist/FL' % a] = 0
    return pr


def run_census(out, series):
    """Stage 1: exhaustive FAM-L census at every q; child counts; FAM-Q.
    Returns (fiber_violations, pred_mismatches, child_verify_log)."""
    fibviol, predmis = [], []
    cells = ('FG', 'FS', 'FL')
    for q in QS_ALL:
        t1 = time.time()
        F = GF(q)
        quads = irreducible_quadratics(F)
        res, npsi_ct, n0 = parent_census_L(F, quads)
        series.setdefault('NPSI', {})[q] = npsi_ct
        series.setdefault('NPSI_c1eq0', {})[q] = n0
        pr = pred_FAML(q)
        for a in AEFFS:
            r = res[a]
            got = {'aeff%d/total' % a: r['total']}
            for c in cells:
                got['aeff%d/fixed/%s' % (a, c)] = r['fixed'][c]
                got['aeff%d/twist/%s' % (a, c)] = r['twist'][c]
            for k, v in got.items():
                series.setdefault('FAML/' + k, {})[q] = v
                if pr.get(k) is not None and pr[k] != v:
                    predmis.append((q, k, pr[k], v))
            for f in cells:                       # joint matrix (txt + series)
                for tc in cells:
                    series.setdefault('FAML/aeff%d/joint/%s_%s'
                                      % (a, f, tc), {})[q] = r['joint'][(f, tc)]
            # fiber constancy per twisted cell (expected: TG-cell fibers all 1,
            # TS/TL-cell fibers all 0 — the anchor-twisted VAL.1 claim)
            for c in cells:
                mn, mx = r['fib'][c]
                exp = (1, 1) if c == 'FG' else (0, 0)
                if (mn, mx) != exp:
                    fibviol.append((q, a, c, mn, mx))
        out.append('q=%-3d #psi=%-4d #psi[c1=0]=%-3d  parent totals %s  '
                   '(%.1fs)' % (q, npsi_ct, n0,
                                [res[a]['total'] for a in AEFFS],
                                time.time() - t1))
        out.append('   joint (fixed x twisted) aeff=1: %s'
                   % {k: v for k, v in res[1]['joint'].items() if v})
        out.append('   joint (fixed x twisted) aeff=2: %s'
                   % {k: v for k, v in res[2]['joint'].items() if v})
    # ---- child counts: formula everywhere; exhaustive monic check q <= 13;
    # ---- psi-independence at q <= 9; literal per-t at q = 2
    chlog = []
    for q in QS_ALL:
        cf = child_counts_formula(q)
        for ty in CHILD_TYPES:
            series.setdefault('CHILD/' + ty, {})[q] = cf[ty]
    for q in [qq for qq in QS_ALL if qq <= 13]:
        F = GF(q)
        quads = irreducible_quadratics(F)
        cm, irr_per_c = child_counts_monic(F, *quads[0])
        ok = cm == child_counts_formula(q)
        chlog.append('  q=%-2d monic-exhaustive vs formula: %s  %s'
                     % (q, 'MATCH' if ok else 'MISMATCH %s vs %s'
                        % (cm, child_counts_formula(q)), ''))
        if q <= 9 and len(quads) > 1:
            cm2, _ = child_counts_monic(F, *quads[-1])
            chlog.append('  q=%-2d second psi %s: %s' %
                         (q, quads[-1], 'MATCH' if cm2 == cm else 'MISMATCH'))
        hist = {}
        for v in irr_per_c.values():
            hist[v] = hist.get(v, 0) + 1
        if q <= 5:
            chlog.append('    irr-count per fixed const c (exhibit; char-'
                         'structure lives here, cancelled by the free '
                         'endpoint): %s' % hist)
    F2 = GF(2)
    q2 = irreducible_quadratics(F2)
    perT = child_counts_literal_q2(F2, *q2[0])
    vals = list(perT.values())
    chlog.append('  q=2 LITERAL per-t (all 15 t in F_4[w]-coeff field F_16*): '
                 't-independent: %s; counts %s'
                 % (all(v == vals[0] for v in vals), vals[0]))
    # ---- FAM-Q (EXTRA)
    for q in QS_FAMQ:
        F = GF(q)
        quads = irreducible_quadratics(F)
        resq = parent_census_Q(F, quads)
        for a in (0, 1):
            series.setdefault('FAMQ/aeff%d/total' % a, {})[q] = resq[a]['total']
            for c in cells:
                series.setdefault('FAMQ/aeff%d/fixed/%s' % (a, c),
                                  {})[q] = resq[a]['fixed'][c]
                series.setdefault('FAMQ/aeff%d/twist/%s' % (a, c),
                                  {})[q] = resq[a]['twist'][c]
            series.setdefault('FAMQ/aeff%d/fibhist' % a, {})[q] = \
                sorted(resq[a]['fibhist'].items())
    return fibviol, predmis, chlog


def build_linked_and_agg(series):
    """Stage 2a: LINKED counts (per-t child counts are exact and t-independent
    — verified above — so the linked sum over targets factorizes LITERALLY as
    N_child(q) * parent-count; computed per q from the enumerated factors) and
    the sigma-aggregates over aeff in {0,1} (the plan's a-range)."""
    cells = ('FG', 'FS', 'FL')
    for ty in CHILD_TYPES:
        for a in AEFFS:
            for tag in ['total'] + ['fixed/%s' % c for c in cells]:
                src = series['FAML/aeff%d/%s' % (a, tag)]
                series['LINKED/aeff%d/%s/%s' % (a, ty, tag)] = \
                    {q: series['CHILD/' + ty][q] * v for q, v in src.items()}
        series['AGG/%s' % ty] = \
            {q: series['LINKED/aeff0/%s/total' % ty][q]
             + series['LINKED/aeff1/%s/total' % ty][q] for q in QS_ALL}
        for c in cells:                    # aggregate over aeff at FIXED cell
            series['AGG_CELL/%s/%s' % (ty, c)] = \
                {q: series['LINKED/aeff0/%s/fixed/%s' % (ty, c)][q]
                 + series['LINKED/aeff1/%s/fixed/%s' % (ty, c)][q]
                 for q in QS_ALL}
    series['AGG_PARENT'] = {q: series['FAML/aeff0/total'][q]
                            + series['FAML/aeff1/total'][q] for q in QS_ALL}


def stage2(out, series):
    """Stage 2b: polynomiality verdicts on every series; wild-p tests on the
    aggregates; the R1 reading per the plan's own criterion."""
    tags = {}
    out.append('\n== STAGE 2: polynomiality verdicts (exact interpolation; '
               'rule in docstring) ==')
    groups = [('parent structure', ['NPSI', 'NPSI_c1eq0']),
              ('FAM-L parent totals + twisted cells',
               [k for k in series if k.startswith('FAML/') and
                ('total' in k or 'twist' in k)]),
              ('FAM-L parent FIXED cells (frame NOT anchor-aligned)',
               [k for k in series if k.startswith('FAML/') and 'fixed' in k]),
              ('FAM-L joint matrix (nonzero entries)',
               [k for k in series if k.startswith('FAML/') and 'joint' in k
                and any(series[k].values())]),
              ('child counts', ['CHILD/' + t for t in CHILD_TYPES]),
              ('LINKED totals (the C_S(q) of the plan)',
               [k for k in series if k.startswith('LINKED/')
                and k.endswith('/total')]),
              ('LINKED per fixed cell (stress exhibit)',
               [k for k in series if k.startswith('LINKED/') and 'fixed' in k
                and any(series[k].values())]),
              ('FAM-Q (EXTRA) parent series',
               [k for k in series if k.startswith('FAMQ/')
                and 'fibhist' not in k]),
              ('sigma-aggregates', [k for k in series if
                                    k.startswith(('AGG/', 'AGG_'))])]
    for gname, keys in groups:
        out.append('\n-- %s --' % gname)
        for k in sorted(keys):
            tags[k] = verdict(k, series[k], out)
    out.append('\n== STAGE 3: aggregate-cancellation / wild-p test '
               '(plan §8 R1(2),(3)) ==')
    out.append('tame points (char not in {2,3}): %s'
               % [q for q in QS_ALL if q not in CHAR2 and q not in CHAR3])
    wild = {}
    for k in (['AGG_PARENT'] + ['AGG/%s' % t for t in CHILD_TYPES]
              + sorted(k for k in series if k.startswith('AGG_CELL/')
                       and any(series[k].values()))):
        wild[k] = wild_test(k, series[k], out)
    return tags, wild


def r1_reading(tags, wild, fibviol, predmis, out):
    per_stratum = {k: t for k, t in tags.items()
                   if k.startswith('LINKED/') and k.endswith('/total')}
    strata_ok = all(t == 'UNIVERSAL' for t in per_stratum.values())
    agg_keys = ['AGG_PARENT'] + ['AGG/%s' % t for t in CHILD_TYPES]
    agg_ok = all(tags[k] == 'UNIVERSAL' for k in agg_keys)
    wild_ok = all(all(wild[k]) for k in agg_keys)
    cellsplit = sorted(k for k, t in tags.items()
                       if 'fixed' in k and t != 'UNIVERSAL')
    out.append('\n' + '=' * 72)
    out.append('R1 READING (per ASSEMBLY_PLAN_2026-07-26.md §8 R1):')
    out.append('  per-stratum linked counts C_S(q) universal: %s (%d series)'
               % (strata_ok, len(per_stratum)))
    out.append('  sigma-aggregates universal: %s; wild-p (2 and 3) on tame '
               'interpolation: %s' % (agg_ok, wild_ok))
    out.append('  fiber constancy on ANCHOR-TWISTED cells: %s'
               % ('EXACT (all q, all aeff)' if not fibviol else fibviol))
    out.append('  in-context closed-form predictions: %s'
               % ('all match' if not predmis else predmis))
    out.append('  NON-universal series (all in the fixed, non-anchor-aligned '
               'frame): %d' % len(cellsplit))
    if strata_ok and wild_ok:
        v = ('NO-WALL: linked counts universal in q; aggregates match at '
             'wild p. CAVEAT for [1v]: VAL.2 must use the ANCHOR-TWISTED '
             'stratification — fixed-frame cell counts are provably '
             'char-dependent (and q mod 3-dependent at aeff=2).')
    elif wild_ok or all(all(w) for w in wild.values() if w):
        v = 'NEEDS-REFINEMENT: per-stratum failure but aggregates cancel (VAL.3).'
    else:
        v = 'WALL: aggregate deviates at wild p — the R1 obstruction.'
    out.append('  VERDICT: ' + v)
    out.append('=' * 72)
    return v


def main():
    t0 = time.time()
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    out, series = [], {}
    out.append('R1 VALUE PROBE (exploration-class, no seal) — spec: '
               'ASSEMBLY_PLAN_2026-07-26.md §2v + §8 R1')
    out.append('q sealed: %s   extra: %s' % (QS_SEALED, QS_EXTRA))
    out.append('\n== STAGE 1: exhaustive parent census (FAM-L all q; FAM-Q '
               'small q), child counts ==')
    fibviol, predmis, chlog = run_census(out, series)
    out.append('\n== child-count verification ==')
    out.extend(chlog)
    out.append('\nfiber-constancy violations on TWISTED cells (expect none): '
               '%s' % (fibviol or 'NONE'))
    out.append('closed-form prediction mismatches (expect none): %s'
               % (predmis or 'NONE'))
    build_linked_and_agg(series)
    tags, wild = stage2(out, series)
    v = r1_reading(tags, wild, fibviol, predmis, out)
    out.append('wall time %.0fs' % (time.time() - t0))
    with open(OUTTXT, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    with open(OUTJSON, 'w') as fh:
        json.dump({k: {str(q): val for q, val in sv.items()}
                   for k, sv in series.items()}, fh, indent=1, default=str)
    taghist = {}
    for t in tags.values():
        taghist[t] = taghist.get(t, 0) + 1
    print('verdid %d series: %s' % (len(tags), taghist))
    print(v)
    print('full tables: %s' % OUTTXT)
    return 0


if __name__ == '__main__':
    sys.exit(main())
