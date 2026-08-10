#!/usr/bin/env python3
"""GENTOW6-BOXES passPE3 FRESH LEG (hostile verifier's own instrument).

INDEPENDENT implementation: no import of any sealed runner and no code
copied from one; the engine below represents two-variable objects as
Y-lists of x-coefficient lists (the committed engines use dict-of-dict
grids) and was written from the note's definitions alone.

ROUTE (disjoint from every prior frame: X3/X4/A53/B3/P33-P36/FR5X/F6/
F7/Q54-Q57/CE3-CE5/BP3/R3F/R3G/RES-M2 and r2's W/E rows):
a THIRD-PRIME (p = 5) replication of the r2 F-1 construction pattern
at a NEW genre, plus a 6.6/6.7 JOINT face at the same odd-p frame.

FRAMES.
  R5F = the R3F genre SHAPE at Q5 (a new genre: new p, new base):
        Phi' = x^3 - 5 (e1 = D' = 3, f1 = 1, h = 1), e2 = 1, f2 = 3,
        u2 = 7, lifts t=2:(i,a)=(1,2), t=1:(2,4), t=0:(0,7), chats 1,
        mu2 = 2.  E2 = 21, delta = 4, THETA = [46, 25], ee = 3,
        w(a,b) = a + 7b.  Regime 3: s* = 3 (pair {1,2}, I = 3),
        a(s*,3) = (7*3-3)/3 = 6, chi = 2*1*1 = 2 != 0 mod 5 -> 6.7(b1)
        predicts the graded digit 2*5^6 at slot (0,1) of ShC_1, height
        25 = THETA_1.  Budget floors (GENTOW-1(b)): floor(1,2,1) = 6,
        floor(1,1,2) = 4 (p-independent arithmetic).
  R5E = the FAM-E genre SHAPE at Q5: same Phi', e2 = 2, f2 = 1,
        u2 = 7, lift t=0:(1,2), mu2 = 2.  delta = 1, E2 = 14, THETA =
        [29, 15], ee = 6, w(a,b) = 2a + 7b.  2*max i = 2 < 3 = D':
        6.5(d) predicts the self-shadow IDENTICALLY ZERO.
  G8  = the distinct-slope sibling key at the R5F level-1 data:
        g = Phi'^3 - 5^8 (deg 9; its side has slope 8/3 > 7/3, so at
        every root x0 of an R5F-box member v(g(x0)) = min(3*(7/3), 8)
        = 7 exactly - the ultrametric min is strict).

PREREGISTERED WANTS (hand ledgers derived BEFORE this file first ran;
the R5F integer slot coefficients are p-generic ledger multiplicities,
pinned by the committed p = 2 and p = 3 rows and re-derived from the
branch census: s*-pair 2, {1,1}-direct 1 + stepped 2 = 3 at ShC_1;
(5, 5, 3) at ShC_0):
  SELF-R5F: ShC_1 = {(0,1): 2*5^6 = 31250, (1,0): 3*5^8 = 1171875};
    ShC_0 = {(2,2): 5^11, (0,1): 5^14, (1,0): 3*5^15}; mindiff =
    (46, 25).  NEW-PRIME TWIST (preregistered): at p = 5 the j0 slots
    (2,2)/(0,1) carry coefficient 5 and get PROMOTED one grade (5*5^10
    = 5^11: height 49), so the j0 floor is attained through (1,0)
    (coefficient 3, a 5-unit, height 46) - unlike p = 2, 3 where
    (2,2)/(0,1) attain it.
  SELF-R5E: diff == 0, mindiff (None, None)  [6.5(d) at p = 5].
  ROW-V2 (R5F below-floor single entry (jp,a,b,c) = (1,2,1,5^4)):
    emission integers are p-generic (-1, -2 at ShC_1; -3, -3, -2 at
    ShC_0 per unit of c/5^4): diff_1 = {(0,1): 5^6, (1,0): 5^8},
    diff_0 = {(2,2): 2*5^10, (0,1): 2*5^13, (1,0): 5^15},
    mindiff (46, 25) - one below-floor entry cannot defeat.
  ROW-V3 (below-floor pair c = 5^4 at (2,1), c' = 5^2 at (1,2)):
    the p = 5 graded system (2 - eps - eps', 3 - 2eps - eps') mod 5
    solves at (eps, eps') = (1, 1), and the INTEGER system (2-1-1,
    3-2-1; 5-3-2, 5-3-2, 3-2-1) is exactly zero: diff == 0 at BOTH
    coordinates - shadow-EXACT (the W3 pattern at a third prime).
  ROW-V4 (c = -4*5^4 = -2500, c' = 5^2): eps = -4 == 1 mod 5:
    graded kill without integer cancellation: diff_1 = {(0,1): 5^7,
    (1,0): 2*5^9}, diff_0 = {(2,2): 3*5^11, (0,1): 3*5^14,
    (1,0): 2*5^16}, mindiff (49, 28) - THE CONTRAST MEMBER at p = 5
    (same numbers (49, 28) as r2's W4 at p = 3: the heights are
    p-generic).  With SELF-R5F this replicates the r2 construction:
    exactly-THETA vs strictly-above, same genre GEOMETRY, the
    defeating member below the budget floors.
  ROW-U21 (R5E in-budget entry (1,2,1,5), floor v = 1): the entry-
    pair ledger digit -c*chat*pi^{a_0} at Y = b + e2 t + (jp-1)e2f2
    + 1 = 2: diff_1 = {(0,0): -5^3}, cascade diff_0 = {(1,0): -5^5},
    mindiff (32, 18) = (THETA_0 + r + delta, THETA_1 + r + delta)
    with r = 2 - LEMMA 6.7E's gap live at delta = 1, p = 5.
  ROW-UNOFLOW (R5E entry (1,1,0,5): a + i_0 = 2 < 3, no overflow):
    diff == 0 - with ROW-U21 the diverge-vs-not pair inside one
    genre at p = 5.
  SWEEP (law-keyed): every in-budget single-entry R5F member at the
    overflow-capable slots (a,b) in {1,2}x{0,1,2}, eps in 1..4,
    k in {0,1} above floor (48 rows): mindiff == (46, 25) EXACTLY
    (LEMMA 6.7E genre-uniformity at the third prime), and the graded
    height-25 digit at (0,1) of ShC_1 stays NONZERO on every row.
  6.6 JOINT FACES (same frame, exact):
    RES-63: v_5(Res(Phi2_R5F, G8)) = 63 (= 9 roots x v(g(x0)) = 7),
      and CONSTANT at 63 on 8 in-budget perturbed pairs (u', g')
      (u' = Phi2 + eps*5^(floor+k)*x^a*Phi'^b at the mu2 = 1 box
      floors ceil((25 - w)/3); g' = G8 + eps*5^7*Phi' at its box
      floor ceil((29 - 8)/3) = 7) - the (H2) separation face.
    RES-SAME: v_5(Res(Phi2, Phi2 + 5^6*Phi')) = 75 = 9*(pin 25)/3 -
      the same-class jump (no single (H2) constant inside one class;
      the root-evaluation pricing read exactly).
    SYL: det(Sylvester) == +-Res on the bare pair and every sampled
      pair, via TWO in-file algorithms (Bareiss integer determinant
      vs Fraction-exact Euclidean resultant) + gp polresultant.
    SMITH: Z_5-elementary divisors of Syl(Phi2, G8): sum = 63, each
      divisor <= 63 (6.6(a)'s lattice clause dm(O^d) >= pi^c O^d).
  GP rows: polresultant on 3 pairs; factorpadic(Phi2_R5F, 5) carrier
    one factor (e f) = (3, 3); poldisc(Phi2_R5F) != 0.

TEETH (mutants that must die; kills asserted):
  T-OBSTR5 (1): the withdrawn S8.1 sentence at p = 5 - predicts an
    in-budget sweep defector; the sweep must measure NONE.
  T-GRDK (1): mutant "some in-budget entry kills the graded (0,1)@j1
    digit" (the slot-level face of the withdrawn display): none may.
  T-BELOW5 (2): budget fence dropped from LEMMA 6.7E: predicts V4
    mindiff_1 = 25 (measured 28) and V3 mindiff_1 = 25 (None).
  T-NODELTA5 (2): the lemma priced without +delta at R5E: predicts
    U21 pins (31, 17); measured (32, 18).
  T-CHI5 (1): mutant "chi == 0 at p = 5" (b2-misfire): predicts the
    s*-slot graded digit zero; measured NONZERO (2*5^6).
  T-CJ8 (1): mutant slope-8 pricing v(Res(Phi2, G8)) = 72: dies at 63.
  T-SAME (1): mutant "(H2)'s constant 63 holds on same-class pairs":
    dies at RES-SAME = 75.
PRE-RUN DISCLOSURE: no part of this file ran before the wants above
were fixed; the committed r2/PE2 outputs were READ (they are the
p = 2, 3 coefficient pins) but no p = 5 object was computed anywhere
before this file's first execution.
"""
import subprocess, sys
from fractions import Fraction

P = 5

# ---------------- one-variable exact helpers (own code) ----------------
def strip(f):
    while f and f[-1] == 0: f.pop()
    return f

def padd(f, g):
    n = max(len(f), len(g))
    return strip([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
                  for i in range(n)])

def pmul(f, g):
    if not f or not g: return []
    o = [0]*(len(f)+len(g)-1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                o[i+j] += a*b
    return strip(o)

def pdivmod(f, g):
    """f, g integer coeff lists, g monic. Returns (q, r)."""
    f = list(f); assert g and g[-1] == 1
    q = [0]*max(1, len(f)-len(g)+1)
    while strip(f) and len(f) >= len(g):
        c, d = f[-1], len(f)-len(g)
        q[d] += c
        for k, gc in enumerate(g):
            f[d+k] -= c*gc
    return strip(q), strip(f)

def val(n):
    n = abs(n); assert n
    v = 0
    while n % P == 0: n //= P; v += 1
    return v

# ---------------- frames ----------------------------------------------
class Frame:
    """Two-variable rep: a Y-poly is a list (index = Y-degree) of
    x-coefficient lists."""
    def __init__(self, name, e2, f2, u2, lifts):
        self.name, self.e2, self.f2, self.u2 = name, e2, f2, u2
        self.PHI1 = [-P, 0, 0, 1]          # x^3 - 5
        self.Dp, self.h = 3, 1
        self.E2 = e2*f2*u2
        self.delta = u2 - e2*self.Dp*self.h
        self.ee = self.Dp*e2
        self.n = e2*f2
        self.lifts = lifts                  # t -> (i, a)  (chats all 1)
        for t, (i, a) in lifts.items():
            assert self.Dp*a + i*self.h == u2*(f2-t) and 0 <= i < self.Dp
        # K2 lift table keyed by Y-degree e2*t
        self.KL = {e2*t: strip([0]*i + [P**a]) for t, (i, a) in lifts.items()}
        # Phi2 = K2(x, Phi') one-variable
        ppow = [[1]]
        for _ in range(self.n): ppow.append(pmul(ppow[-1], self.PHI1))
        f = list(ppow[self.n])
        for yd, lx in self.KL.items():
            f = padd(f, [-c for c in pmul(lx, ppow[yd])])
        self.PHI2 = f
        assert f[-1] == 1 and len(f)-1 == self.n*self.Dp

    def theta(self, j): return (2-j)*self.E2 + self.delta
    def w(self, a, b):  return a*self.e2*self.h + b*self.u2
    def floorv(self, j, a, b):
        d = self.theta(j) - self.w(a, b)
        return max(0, -((-d)//self.ee))

    def dev(self, f):
        """one-variable f -> Y-list of x-lists (divmod chain by Phi')."""
        out, r = [], list(f)
        while strip(list(r)):
            r, rem = pdivmod(r, self.PHI1)
            out.append(rem)
        return out

    def divK2(self, F, reduce_each):
        """iterated exact division of Y-rep F by K2 = Y^n - lifts.
        Returns ([G_0, ..., G_{m-1}], top_quotient). m = 2."""
        A = [list(c) for c in F]
        coords = []
        for _ in range(2):
            Q = []
            while len(A) > self.n:
                yd = len(A)-1
                c = A.pop()
                while len(Q) <= yd - self.n: Q.append([])
                Q[yd-self.n] = padd(Q[yd-self.n], c)
                for k, lx in self.KL.items():
                    tgt = yd - self.n + k
                    while len(A) <= tgt: A.append([])
                    t = padd(A[tgt], pmul(c, lx))
                    if reduce_each: t = pdivmod(t, self.PHI1)[1]
                    A[tgt] = t
                while A and not strip(list(A[-1])): A.pop()
            coords.append(A)
            A = Q
        return coords, A

    def slots(self, coord, terminal_reduce):
        d = {}
        for b, xl in enumerate(coord):
            r = pdivmod(list(xl), self.PHI1)[1] if terminal_reduce else list(xl)
            for a, c in enumerate(r):
                if c: d[(a, b)] = c
        return d

    def pin(self, sd):
        h = [self.ee*val(c) + self.w(a, b) for (a, b), c in sd.items()]
        return min(h) if h else None

    def graded_nonzero(self, sd, a, b, H):
        c = sd.get((a, b), 0)
        if c == 0: return False
        r = H - self.w(a, b)
        return r >= 0 and r % self.ee == 0 and val(c) == r//self.ee

    def member(self, entries):
        """entries: (jp, a, b, c) -> f = Phi2^2 + sum c x^a Phi'^b Phi2^jp."""
        f = pmul(self.PHI2, self.PHI2)
        for (jp, a, b, c) in entries:
            t = [0]*a + [c]
            for _ in range(b):  t = pmul(t, self.PHI1)
            for _ in range(jp): t = pmul(t, self.PHI2)
            f = padd(f, t)
        return f

    def read(self, f):
        """returns (shadow slot dicts, honest slot dicts, oracle flags)."""
        F = self.dev(f)
        cR, qR = self.divK2(F, True)
        cE, qE = self.divK2(F, False)
        sR = [self.slots(c, False) for c in cR]   # R-route already reduced
        sE = [self.slots(c, True) for c in cE]    # terminal reduction
        dual = (sR == sE)
        topok = all(len(q) == 1 and strip(list(q[0])) == [1] for q in (qR, qE))
        # substitution oracle on the EXACT route: sum_j G_j(x,Phi')Phi2^j
        s, p2 = [], [1]
        for c in cE:
            gj = []
            for b, xl in enumerate(c):
                t = list(xl)
                for _ in range(b): t = pmul(t, self.PHI1)
                gj = padd(gj, t)
            s = padd(s, pmul(gj, p2))
            p2 = pmul(p2, self.PHI2)
        subst = (s == padd(list(f), [-x for x in pmul(self.PHI2, self.PHI2)]))
        # honest one-variable coordinates
        g, Cs = list(f), []
        for _ in range(2):
            g, r = pdivmod(g, self.PHI2)
            Cs.append(r)
        hon = (g == [1])
        hd = [self.slots(self.dev(C), False) for C in Cs]
        return sR, hd, dual, topok, subst, hon

NCHK = NVIO = 0
def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

KILLS = {}
def tooth(name, killed, msg):
    KILLS[name] = KILLS.get(name, 0) + (1 if killed else 0)
    chk('TOOTH', killed, 'tooth %s NOT killed: %s' % (name, msg))

def dsub(a, b):
    o = dict(a)
    for k, v in b.items():
        o[k] = o.get(k, 0) - v
        if o[k] == 0: del o[k]
    return o

def member_row(F, tag, entries, want_diffs=None, want_md=None, law=None):
    f = F.member(entries)
    sR, hd, dual, topok, subst, hon = F.read(f)
    chk('DUAL', dual, '%s R != E' % tag)
    chk('TOPQ', topok, '%s top quotient != 1' % tag)
    chk('SUBST', subst, '%s substitution oracle' % tag)
    chk('HON', hon, '%s honest top != 1' % tag)
    diffs = [dsub(sR[j], hd[j]) for j in range(2)]
    mds = tuple(F.pin(d) for d in diffs)
    for j in range(2):
        chk('FLOOR', mds[j] is None or mds[j] >= F.theta(j),
            '%s mindiff_%d %s < %d' % (tag, j, mds[j], F.theta(j)))
    if want_md is not None:
        chk('MD', mds == want_md, '%s mindiff %s want %s' % (tag, mds, want_md))
    if want_diffs is not None:
        for j, wd in want_diffs.items():
            chk('DIFFD', diffs[j] == wd,
                '%s diff_%d %s want %s' % (tag, j, diffs[j], wd))
    if law == 'UNIFORM':
        chk('LAW-U', mds == (F.theta(0), F.theta(1)),
            '%s mindiff %s != THETA (uniformity)' % (tag, mds))
    if law == 'GAP':
        for j in range(2):
            chk('LAW-G', mds[j] is None or mds[j] >= F.theta(j)+F.delta,
                '%s mindiff_%d %s < THETA+delta' % (tag, j, mds[j]))
    print('  %s: mindiff %s diffs %s' % (tag, mds, diffs))
    return mds, diffs, sR

# ---------------- resultant / Sylvester / Smith machinery --------------
def sylvester(f, g):
    """f, g coefficient lists (ascending). Matrix rows: x^i*g, x^j*f
    (the classical layout; det = +-Res)."""
    m, n = len(f)-1, len(g)-1
    N = m+n
    M = []
    for i in range(m):        # rows of g shifted
        row = [0]*N
        for k, c in enumerate(g): row[i+k] = c
        M.append(row)
    for j in range(n):        # rows of f shifted
        row = [0]*N
        for k, c in enumerate(f): row[j+k] = c
        M.append(row)
    return M

def bareiss_det(M):
    M = [row[:] for row in M]
    n = len(M); sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            for i in range(k+1, n):
                if M[i][k]:
                    M[k], M[i] = M[i], M[k]; sign = -sign; break
            else: return 0
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
            M[i][k] = 0
        prev = M[k][k]
    return sign*M[n-1][n-1]

def euclid_res(f, g):
    """exact resultant over Q by the Euclidean recursion."""
    f = [Fraction(c) for c in f]; g = [Fraction(c) for c in g]
    res = Fraction(1)
    while True:
        m, n = len(f)-1, len(g)-1
        if n == 0: return res*g[0]**m
        # r = f mod g
        r = f[:]
        while len(r)-1 >= n and any(r):
            d = len(r)-1-n; c = r[-1]/g[-1]
            for k in range(len(g)): r[d+k] -= c*g[k]
            while r and r[-1] == 0: r.pop()
            if not r: break
        if not r: return Fraction(0)
        d = len(r)-1
        res *= (-1)**(m*n)*g[-1]**(m-d)
        f, g = g, r

def smith_vals(M):
    """elementary divisor valuations over Z_(5) by DVR pivoting."""
    A = [[Fraction(c) for c in row] for row in M]
    def fv(q):
        if q == 0: return None
        v = 0; a, b = q.numerator, q.denominator
        while a % P == 0: a //= P; v += 1
        while b % P == 0: b //= P; v -= 1
        return v
    n = len(A); vals = []
    rows, cols = list(range(n)), list(range(n))
    while rows:
        best = None
        for i in rows:
            for j in cols:
                v = fv(A[i][j])
                if v is not None and (best is None or v < best[0]):
                    best = (v, i, j)
        assert best is not None, 'singular over Q?'
        v, pi, pj = best
        vals.append(v)
        for i in rows:
            if i == pi: continue
            c = A[i][pj]/A[pi][pj]
            for j in cols: A[i][j] -= c*A[pi][j]
        rows.remove(pi); cols.remove(pj)
    return sorted(vals)

def gp(expr):
    s = subprocess.run(['gp', '-q'], input=expr+'\n', capture_output=True,
                       text=True, timeout=120)
    return s.stdout.strip()

def gp_pol(f):
    return 'Pol(%s)' % list(reversed(f))

# ======================= RUN =========================================
R5F = Frame('R5F', 1, 3, 7, {2: (1, 2), 1: (2, 4), 0: (0, 7)})
R5E = Frame('R5E', 2, 1, 7, {0: (1, 2)})
chk('CONST', [R5F.theta(j) for j in (0, 1)] == [46, 25] and R5F.delta == 4,
    'R5F constants')
chk('CONST', [R5E.theta(j) for j in (0, 1)] == [29, 15] and R5E.delta == 1,
    'R5E constants')
chk('CONST', R5F.floorv(1, 2, 1) == 6 and R5F.floorv(1, 1, 2) == 4,
    'R5F floors')
chk('CONST', R5E.floorv(1, 2, 1) == 1, 'R5E floor')

print('== SELF rows (p = 5) ==')
_, _, sF = member_row(R5F, 'SELF-R5F', [], want_md=(46, 25))
chk('SLOT', sF[1] == {(0, 1): 31250, (1, 0): 1171875},
    'R5F ShC_1 %s' % sF[1])
chk('SLOT', sF[0] == {(2, 2): 5**11, (0, 1): 5**14, (1, 0): 3*5**15},
    'R5F ShC_0 %s' % sF[0])
chk('THY', R5F.graded_nonzero(sF[1], 0, 1, 25),
    '6.7(b1) graded digit at (0,1)@j1')
chk('THY', val(sF[1][(0, 1)]) == 6 and sF[1][(0, 1)]//5**6 == 2,
    'chi = 2 residue at the s*-slot')
chk('TWIST', R5F.ee*val(sF[0][(2, 2)]) + R5F.w(2, 2) == 49 and
             R5F.ee*val(sF[0][(0, 1)]) + R5F.w(0, 1) == 49 and
             R5F.ee*val(sF[0][(1, 0)]) + R5F.w(1, 0) == 46,
    'the p = 5 promotion twist at j0')
tooth('T-CHI5', R5F.graded_nonzero(sF[1], 0, 1, 25),
      'chi==0 mutant predicts graded zero at the s*-slot')
member_row(R5E, 'SELF-R5E', [], want_diffs={0: {}, 1: {}},
           want_md=(None, None))

print('== construction pattern at the third prime ==')
member_row(R5F, 'ROW-V2', [(1, 2, 1, 5**4)],
           want_diffs={1: {(0, 1): 5**6, (1, 0): 5**8},
                       0: {(2, 2): 2*5**10, (0, 1): 2*5**13,
                           (1, 0): 5**15}},
           want_md=(46, 25))
mV3, _, _ = member_row(R5F, 'ROW-V3 (below-floor exact solve)',
           [(1, 2, 1, 5**4), (1, 1, 2, 5**2)],
           want_diffs={1: {}, 0: {}}, want_md=(None, None))
mV4, _, _ = member_row(R5F, 'ROW-V4 (THE p=5 CONTRAST MEMBER)',
           [(1, 2, 1, -4*5**4), (1, 1, 2, 5**2)],
           want_diffs={1: {(0, 1): 5**7, (1, 0): 2*5**9},
                       0: {(2, 2): 3*5**11, (0, 1): 3*5**14,
                           (1, 0): 2*5**16}},
           want_md=(49, 28))
mU21, _, _ = member_row(R5E, 'ROW-U21', [(1, 2, 1, 5)],
           want_diffs={1: {(0, 0): -5**3}, 0: {(1, 0): -5**5}},
           want_md=(32, 18), law='GAP')
member_row(R5E, 'ROW-UNOFLOW', [(1, 1, 0, 5)],
           want_diffs={0: {}, 1: {}}, want_md=(None, None))

print('== in-budget sweep at p = 5 (LEMMA 6.7E uniformity) ==')
nsw = defect = gkill = 0
for a in (1, 2):
    for b in (0, 1, 2):
        fl = R5F.floorv(1, a, b)
        for eps in range(1, 5):
            for k in (0, 1):
                c = eps*5**(fl+k)
                mds, diffs, _ = member_row(
                    R5F, 'SW(%d,%d)c=%d' % (a, b, c), [(1, a, b, c)],
                    law='UNIFORM')
                nsw += 1
                if mds != (46, 25): defect += 1
                if not R5F.graded_nonzero(diffs[1], 0, 1, 25): gkill += 1
print('  sweep rows %d, defectors %d, graded kills %d' % (nsw, defect, gkill))
tooth('T-OBSTR5', defect == 0, 'in-budget defector at p = 5')
tooth('T-GRDK', gkill == 0, 'in-budget graded (0,1)@j1 kill at p = 5')
tooth('T-BELOW5', mV4 == (49, 28), 'V4 off-floor contrast')
tooth('T-BELOW5', mV3 == (None, None), 'V3 shadow-exact')
tooth('T-NODELTA5', mU21 == (32, 18) and mU21[1] != 17,
      'U21 pins with +delta')
tooth('T-NODELTA5', mU21[0] != 31, 'U21 j0 pin with +delta')

print('== 6.6 joint faces at p = 5 ==')
A = R5F.PHI2
G8 = padd(pmul(pmul(R5F.PHI1, R5F.PHI1), R5F.PHI1), [-5**8])
assert len(G8)-1 == 9 and G8[-1] == 1

def res_row(tag, u, w2, want_v=None):
    r1 = bareiss_det(sylvester(u, w2))
    r2 = euclid_res(u, w2)
    chk('SYL', abs(r1) == abs(r2.numerator) and r2.denominator == 1,
        '%s Bareiss %s vs Euclid %s' % (tag, r1, r2))
    v = val(int(r2)) if r2 else None
    if want_v is not None:
        chk('RESV', v == want_v, '%s v(Res) = %s want %s' % (tag, v, want_v))
    return v, r1

v0, det0 = res_row('RES-63-bare', A, G8, want_v=63)
print('  v(Res(Phi2, G8)) = %s' % v0)
tooth('T-CJ8', v0 == 63 and v0 != 72, 'slope-8 mutant predicts 72')
gpres = gp('polresultant(%s, %s)' % (gp_pol(A), gp_pol(G8)))
chk('GP', gpres.lstrip('-') == str(abs(det0)), 'gp polresultant bare pair')

def phib(b):
    t = [1]
    for _ in range(b): t = pmul(t, R5F.PHI1)
    return t

pert = [(0, 1, 1, 0), (0, 1, 2, 0), (2, 1, 1, 0), (1, 0, 3, 1),
        (2, 0, 2, 0), (0, 0, 4, 0), (1, 1, 1, 1), (2, 2, 3, 0)]
for idx, (a, b, eps, k) in enumerate(pert):
    fl = max(0, -((-(25 - R5F.w(a, b)))//3))   # mu2 = 1 box floor
    u2p = padd(list(A), pmul([0]*a + [eps*5**(fl+k)], phib(b)))
    g2p = padd(list(G8), [x*((idx % 3)+1)*5**7 for x in R5F.PHI1])
    v, d = res_row('RES-63-p%d' % idx, u2p, g2p, want_v=63)
sameu = padd(list(A), [x*5**6 for x in R5F.PHI1])
vs, ds = res_row('RES-SAME', A, sameu, want_v=75)
tooth('T-SAME', vs == 75 and vs != 63, 'same-class pair jumps to 75')
gpres2 = gp('polresultant(%s, %s)' % (gp_pol(A), gp_pol(sameu)))
chk('GP', gpres2.lstrip('-') == str(abs(ds)), 'gp polresultant same-class')

sv = smith_vals(sylvester(A, G8))
chk('SMITH', sum(sv) == 63 and max(sv) <= 63,
    'Smith profile sum %s max %s' % (sum(sv), max(sv)))
print('  Smith profile (18 divisors): %s' % sv)

fp = gp('F = factorpadic(%s, 5, 30); [matsize(F)[1], poldegree(F[1,1])]'
        % gp_pol(A))
chk('GP', fp.replace(' ', '') == '[1,9]',
    'factorpadic one deg-9 factor: %s' % fp)
pd = gp('poldisc(%s) == 0' % gp_pol(A))
chk('GP', pd == '0', 'poldisc nonzero')
print('  gp: factorpadic %s ; poldisc==0 -> %s' % (fp, pd))

print('TEETH kills: %s' % dict(sorted(KILLS.items())))
print('RESULT: %d checks, %d violations' % (NCHK, NVIO))
sys.exit(0 if NVIO == 0 else 1)
