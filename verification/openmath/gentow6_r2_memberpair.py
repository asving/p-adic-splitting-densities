#!/usr/bin/env python3
"""GENTOW6-BOXES r2 REPAIR machine leg (passPE2 F-1): the same-genre
exactly-THETA contrast pair — CONSTRUCTED, and PROVED impossible
IN-GENRE (LEMMA GENTOW-6.7E, the entry-branch floor gap).

CHARGE. passPE2 F-1: S8.1/S10 cited a same-genre "both behaviors"
witness pair that is cross-genre. PROVE-FIRST outcome delivered
here: (1) LEMMA 6.7E, re-derived from the note's own weight ledger
(the lift identity e1 a_t + i_t h = u2(f2 - t) is a dv2-weight tie,
so division emissions are weight-exact; each x-overflow extraction
costs +delta = u2 - e2 D' h > 0): for a member f = Phi2^2 + C_1
Phi2 + C_0 with digits ON/ABOVE the GENTOW-1(b) budget floors
(= in the genre locus), every entry-driven discrepancy branch reads
at dv2-height >= THETA_j + delta > THETA_j at every coordinate j.
COROLLARY (genre-uniformity): the member's height-THETA_j graded
discrepancy layer EQUALS the key power's, so "shadow diverges at
EXACTLY THETA_j" is genre-constant on the locus — the S8.1
obstruction display is overturned, and the exactly-THETA contrast
pair provably does NOT exist inside one genre. (2) The pair IS
constructed — BELOW the budget floors (outside the locus), where
the branch valuation can reach the graded layer: the simultaneous-
defeat system over the two live slots of R3F's ShC_1 is infeasible
in-budget (needs v(c) <= 4 < 6 = floor) and solvable at depth 4.

ENGINE: Fr2 two-variable division engine copied from the committed
gentow6_boxes_pe2_fresh.py (md5 asserted against the committed
file), extended with member reads: honest one-variable Phi2-divmod
coordinates C_j, diff_j := ShC_j - dev(C_j), mindiff_j :=
pin(diff_j).  Oracles per row: (R) reduce-each-step vs (E) exact
division, slot-identical; (S) substitution identity
sum_j GhatE_j(x, Phi') Phi2^j == f - Phi2^m in ONE variable;
(H) honest reconstruction sum_j C_j Phi2^j + Phi2^m == f.
PRE-SEAL SMOKE (disclosed): the copied engine reran the committed
CE4 self-shadow row only (dict + pins reproduced bit-identically);
no member row, no new frame ran before the seal.

FRAMES (all committed): R3F (Q3, Phi' = x^3-3, e2 = 1, f2 = 3,
u2 = 7, lifts t2:(1,2) t1:(2,4) t0:(0,7), chats 1, mu2 = 2; THETA =
[46, 25], delta = 4, chi = 2 != 0 mod 3: 6.7(b1) attains);
R3G (same shape at Q2: chi = 0 mod 2, attains through the lower-s
(1,0) slot); FAM-E ((3,1,4;1)/Q2: Phi' = x^3-2, e2 = 2, f2 = 1,
u2 = 7, lift (1,2), mu2 = 2; THETA = [29, 15], delta = 1; regime 4:
self-shadow == 0). Budget floors floor(j,a,b) =
max(0, ceil((THETA_j - w(a,b)) / (D' e2))).

PREREGISTERED WANTS (hand ledgers fully derived before this file
ran; M-part linear contributions traced by hand at both R3F and
R3G):
  SELF rows: R3F ShC_1 = {(0,1): 1458, (1,0): 19683}, ShC_0 =
    {(2,2): 295245, (0,1): 7971615, (1,0): 43046721}, mindiff =
    (46, 25) — the EXACTLY-THETA member (both coords ON the floor);
    R3G ShC_1 = {(0,1): 128, (1,0): 768}, ShC_0 = {(2,2): 5120,
    (0,1): 40960, (1,0): 98304}, mindiff (46, 25); FAM-E self
    diff == 0 (mindiff None, None).
  ROW-A (R3F in-budget floor entry (2,1), c = 3^6 = 729):
    diff_1 = {(0,1): -5103, (1,0): -98415} [-7*3^6 v6 ht 25;
    -5*3^9 v9 ht 28], diff_0 = {(2,2): -1299078, (0,1): -35075106,
    (1,0): -215233605} [-22*3^10, -22*3^13, -5*3^16], mindiff
    (46, 25) — graded residue -7 == 2 mod 3 UNCHANGED.
  ROW-B (R3G in-budget floor entry (2,1), c = 2^6 = 64): diff_1 =
    {(0,1): -128, (1,0): -1280}, diff_0 = {(2,2): -7168,
    (0,1): -57344, (1,0): -163840}, mindiff (46, 25).
  COMBO-R3F (in-budget (2,1) c = 729 + (1,2) c' = 81): diff_1 =
    {(0,1): -11664, (1,0): -157464} mindiff (46, 25); COMBO-R3G
    ((2,1) c = 64 + (1,2) c' = 16): diff_1 = {(0,1): -384,
    (1,0): -2304} mindiff (46, 25) — the in-budget two-slot kill
    attempt FAILS (LEMMA 6.7E's infeasibility).
  ROW-W2 (BELOW-FLOOR display, R3F (2,1) c = 81, v = 4 < 6):
    diff_1 = {(0,1): 729, (1,0): 6561} mindiff_1 = 25, diff_0 =
    {(2,2): 118098, (0,1): 4782969*2/3 -- exactly 2*3^13 =
    3188646, (1,0): 14348907} mindiff_0 = 46: ONE below-floor
    entry still cannot defeat (residues land (1,1) at the two
    slots — the 2x2 system needs the second slot).
  ROW-W3 (BELOW-FLOOR pair c = 81 at (2,1) + c' = 9 at (1,2)):
    diff == 0 at BOTH coordinates — a SHADOW-EXACT member (the
    solved system (eps, eps') = (1,1) cancels every slot exactly).
  ROW-W4 (BELOW-FLOOR pair c = -162, c' = 9): THE CONTRAST MEMBER:
    diff_1 = {(0,1): 2187, (1,0): 39366} mindiff_1 = 28 > 25 =
    THETA_1, diff_0 = {(2,2): 531441, (0,1): 14348907,
    (1,0): 86093442} mindiff_0 = 49 > 46: diverges STRICTLY ABOVE
    the floor at BOTH coordinates — with SELF-R3F (25/46 exactly)
    this is the exactly-THETA contrast pair, and it lives ONLY
    below the budget floors (v(c) = 4 < 6, v(c') = 2 < 4).
  ROW-EENTRY (FAM-E, f_E = Phi2^2 + 4x^2 Phi2 + 16 Phi'): diff_0 =
    {(0,1): -16} mindiff_0 = 31 = THETA_0 + r + delta (r = 1),
    diff_1 = None; shadow ShC_0 slot (0,1) == 0 (the committed
    drain flip) — reproduced on the fresh member engine.
  ROW-E21 (FAM-E in-budget (2,1), c = 2): diff_1 = {(0,0): -8}
    mindiff_1 = 18 = THETA_1 + 2 + 1, diff_0 = {(1,0): -32}
    mindiff_0 = 32 (the dropped carry CASCADES, each leg at
    THETA_j + r + delta).
  ROW-E20 (FAM-E in-budget (2,0), c in {4, 8, 16}): diff_0 =
    {(0,1): -4c}, pins 31 / 37 / 43 (the branch height moves
    linearly with v(c) — ABOVE the floor: the honest content of
    the withdrawn S8.1 sentence), diff_1 = None.
  ROW-NOFLOW (FAM-E, c = 4 at slot (1,0): a + i_0 = 2 < 3 = D',
    no overflow): diff == 0 — with ROW-EENTRY the diverge-vs-not
    pair INSIDE one genre, both measured.
  SWEEP (law-keyed, no per-row dicts): every in-budget single-
    entry member at R3F/R3G (overflow-capable slots (1,b)/(2,b),
    b in {0,1,2}, eps in units, k in {0,1} above floor):
    mindiff == (46, 25) EXACTLY on every row (genre-uniformity);
    every in-budget FAM-E row: mindiff_j == None or >= THETA_j +
    delta (>= 30 / >= 16).  Floors mindiff_j >= THETA_j hold on
    every row incl. the below-floor displays (measured, displayed).

TEETH (mutants that must die; kill counts asserted):
  T-OBSTR the withdrawn S8.1 obstruction sentence ("exactly-THETA
    membership is cut by per-member congruences INSIDE the genre"):
    predicts >= 1 in-budget R3F/R3G sweep row with mindiff_1 != 25:
    the sweep measures NONE — 1 kill (menu-exhaustive, no
    universal claim).
  T-NODELTA the lemma priced without the +delta extraction cost:
    predicts ROW-EENTRY pin 30 (measured 31) and ROW-E21 diff_1
    pin 17 (measured 18): 2 kills.
  T-BELOW the budget fence dropped from LEMMA 6.7E (mutant: the
    uniformity law holds for ALL members): predicts ROW-W4
    mindiff_1 = 25 (measured 28) and ROW-W3 mindiff_1 = 25
    (measured None): 2 kills.
"""
import hashlib, sys
from fractions import Fraction

# ---- engine copied from committed gentow6_boxes_pe2_fresh.py ----
# (md5 of the source of the copy asserted below; no import — that
# file runs its battery at module level)
PE2_FRESH_MD5 = 'd05ec293853becb79e9be4bdf205677f'

def st(f):
    while f and f[-1] == 0:
        f.pop()
    return f

def ad(f, g):
    return st([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
               for i in range(max(len(f), len(g)))])

def ml(f, g):
    if not f or not g:
        return []
    o = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            o[i + j] += a * b
    return st(o)

def dm(f, g):
    f = list(f)
    assert g[-1] == 1
    q = [0] * max(1, len(f) - len(g) + 1)
    while st(f) and len(f) >= len(g):
        c, d = f[-1], len(f) - len(g)
        q[d] += c
        for k, gc in enumerate(g):
            f[d + k] -= c * gc
        st(f)
    return st(q), st(f)

def vp(n, p):
    n = abs(n)
    assert n
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def xd_add(a, b):
    o = dict(a)
    for k, v in b.items():
        o[k] = o.get(k, 0) + v
        if o[k] == 0:
            del o[k]
    return o

def xd_scale_list(xp):
    return {i: c for i, c in enumerate(xp) if c}

def xd_mul(a, b):
    o = {}
    for i, c in a.items():
        for j, d in b.items():
            o[i + j] = o.get(i + j, 0) + c * d
    return {k: v for k, v in o.items() if v}

def xd_red(a, PHI1):
    lst = [0] * (max(a) + 1) if a else []
    for i, c in a.items():
        lst[i] = c
    return xd_scale_list(dm(lst, PHI1)[1])

class Fr2:
    def __init__(self, name, p, PHI1, h, e2, f2, u2, lifts, m):
        self.name, self.p, self.PHI1, self.h = name, p, PHI1, h
        self.e2, self.f2, self.u2, self.m = e2, f2, u2, m
        self.Dp = len(PHI1) - 1
        self.E2 = e2 * f2 * u2
        self.delta = u2 - e2 * self.Dp * h
        self.ee = self.Dp * e2
        self.n = e2 * f2
        for t, (i, a, c) in lifts.items():
            assert self.Dp * a + i * h == u2 * (f2 - t) and 0 <= i < self.Dp
        self.lifts = lifts
        self.K2lift = {}
        for t, (i, a, c) in lifts.items():
            self.K2lift[e2 * t] = xd_add(self.K2lift.get(e2 * t, {}),
                                         {i: c * p ** a})
        pw = [[1]]
        for _ in range(self.n):
            pw.append(ml(pw[-1], PHI1))
        f = list(pw[self.n])
        for yd, xdct in self.K2lift.items():
            xp = [0] * (max(xdct) + 1)
            for i, c in xdct.items():
                xp[i] = c
            f = ad(f, [-c for c in ml(xp, pw[yd])])
        self.PHI2 = f
        assert f[-1] == 1 and len(f) - 1 == self.n * self.Dp

    def theta(self, j):
        return (self.m - j) * self.E2 + self.delta

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def dev(self, f):
        out, r, yd = {}, list(f), 0
        while st(list(r)):
            r, rem = dm(r, self.PHI1)
            if rem:
                out[yd] = xd_scale_list(rem)
            yd += 1
        return out

    def phi2pow(self):
        f = [1]
        for _ in range(self.m):
            f = ml(f, self.PHI2)
        return f

    def divide(self, F, red_each):
        A = {yd: dict(xd) for yd, xd in F.items()}
        coords = []
        for _ in range(self.m):
            q = {}
            top = max(A) if A else 0
            for yd in range(top, self.n - 1, -1):
                c = A.pop(yd, None)
                if not c:
                    continue
                q[yd - self.n] = xd_add(q.get(yd - self.n, {}), c)
                for k, lx in self.K2lift.items():
                    t = xd_add(A.get(yd - self.n + k, {}), xd_mul(c, lx))
                    if red_each:
                        t = xd_red(t, self.PHI1)
                    A[yd - self.n + k] = t
            coords.append({b: A.get(b, {}) for b in range(self.n)})
            A = q
        return coords, A

    def slotd(self, coord):
        d = {}
        for b, xdct in coord.items():
            for a, c in xdct.items():
                if c:
                    d[(a, b)] = c
        return d

    def pin(self, coord):
        best = None
        for (a, b), c in self.slotd(coord).items():
            ht = self.ee * vp(c, self.p) + self.w(a, b)
            best = ht if best is None else min(best, ht)
        return best

    def graded(self, coord, a, b, H):
        c = self.slotd(coord).get((a, b), 0)
        if c == 0:
            return False
        r = H - self.w(a, b)
        return r >= 0 and r % self.ee == 0 and vp(c, self.p) == r // self.ee

    # ---- member extensions (this unit's own code) ----------------
    def floorv(self, j, a, b):
        d = self.theta(j) - self.w(a, b)
        return max(0, -((-d) // self.ee))

    def entry(self, a, b):
        t = [0] * a + [1]
        for _ in range(b):
            t = ml(t, self.PHI1)
        return t

    def member(self, entries):
        """entries: list of (jprime, a, b, c)."""
        f = self.phi2pow()
        for (jp, a, b, c) in entries:
            t = [x * c for x in self.entry(a, b)]
            for _ in range(jp):
                t = ml(t, self.PHI2)
            f = ad(f, t)
        return f

    def honest(self, f):
        g, Cs = list(f), []
        for _ in range(self.m):
            g, r = dm(g, self.PHI2)
            Cs.append(r)
        assert g == [1], 'honest divmod top != 1'
        return Cs

    def member_read(self, f):
        F = self.dev(f)
        R, qR = self.divide(F, True)
        Eraw, qE = self.divide(F, False)
        okq = all(set(q) <= {0} and q.get(0, {}) == {0: 1}
                  for q in (qR, qE))
        # substitution oracle on the exact read
        s = []
        p2 = [1]
        for j in range(self.m):
            gj = []
            for b, xdct in Eraw[j].items():
                xp = [0] * (max(xdct) + 1) if xdct else []
                for i, c in xdct.items():
                    xp[i] = c
                t = xp
                for _ in range(b):
                    t = ml(t, self.PHI1)
                gj = ad(gj, t)
            s = ad(s, ml(gj, p2))
            p2 = ml(p2, self.PHI2)
        want_s = ad(list(f), [-x for x in self.phi2pow()])
        subst_ok = (s == want_s)
        E = [{b: xd_red(xdct, self.PHI1) for b, xdct in coord.items()}
             for coord in Eraw]
        Cs = self.honest(f)
        hon_ok = True
        g, p2 = [], [1]
        for C in Cs:
            g = ad(g, ml(list(C), p2))
            p2 = ml(p2, self.PHI2)
        hon_ok = (ad(g, p2) == st(list(f)))
        diffs = []
        for j in range(self.m):
            dv = self.dev(Cs[j]) if Cs[j] else {}
            dcoord = {b: xd_add(R[j].get(b, {}),
                                {a: -c for a, c in dv.get(b, {}).items()})
                      for b in range(self.n)}
            diffs.append(dcoord)
        dualok = all(self.slotd(R[j]) == self.slotd(E[j])
                     for j in range(self.m))
        return R, diffs, okq, subst_ok, hon_ok, dualok

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
    chk('TOOTH', killed, 'tooth %s not killed: %s' % (name, msg))

def run_member(F, tag, entries, want_diffs=None, want_md=None,
               law=None):
    f = F.member(entries)
    R, diffs, okq, sok, hok, dok = F.member_read(f)
    chk('TOPQ', okq, '%s top quotient != 1' % tag)
    chk('SUBST', sok, '%s substitution oracle failed' % tag)
    chk('HONEST', hok, '%s honest reconstruction failed' % tag)
    chk('DUAL', dok, '%s R != E' % tag)
    mds = []
    for j in range(F.m):
        md = F.pin(diffs[j])
        mds.append(md)
        chk('FLOOR', md is None or md >= F.theta(j),
            '%s mindiff_%d = %s < THETA %d' % (tag, j, md, F.theta(j)))
    if want_md is not None:
        chk('MD', tuple(mds) == want_md,
            '%s mindiff %s want %s' % (tag, tuple(mds), want_md))
    if want_diffs is not None:
        for j, wd in want_diffs.items():
            got = F.slotd(diffs[j])
            chk('DIFFD', got == wd,
                '%s diff_%d = %s want %s' % (tag, j, got, wd))
    if law == 'UNIFORM':
        chk('LAW-U', tuple(mds) == (F.theta(0), F.theta(1)),
            '%s mindiff %s != THETA exactly (uniformity)'
            % (tag, tuple(mds)))
    if law == 'GAP':
        for j in range(F.m):
            chk('LAW-G', mds[j] is None or
                mds[j] >= F.theta(j) + F.delta,
                '%s mindiff_%d = %s < THETA+delta %d'
                % (tag, j, mds[j], F.theta(j) + F.delta))
    print('  %s: mindiff %s  diff slots %s' %
          (tag, tuple(mds), [F.slotd(d) for d in diffs]))
    return mds, diffs, R

# ---------------- engine copy integrity + frames ----------------------
import os
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, 'gentow6_boxes_pe2_fresh.py'), 'rb').read()
assert hashlib.md5(src).hexdigest()[:32] == PE2_FRESH_MD5, \
    'committed pe2_fresh source drifted'

R3F = Fr2('R3F', 3, [-3, 0, 0, 1], 1, 1, 3, 7,
          {2: (1, 2, 1), 1: (2, 4, 1), 0: (0, 7, 1)}, 2)
R3G = Fr2('R3G', 2, [-2, 0, 0, 1], 1, 1, 3, 7,
          {2: (1, 2, 1), 1: (2, 4, 1), 0: (0, 7, 1)}, 2)
FAME = Fr2('FAM-E', 2, [-2, 0, 0, 1], 1, 2, 1, 7, {0: (1, 2, 1)}, 2)
assert [R3F.theta(j) for j in range(2)] == [46, 25]
assert [R3G.theta(j) for j in range(2)] == [46, 25]
assert [FAME.theta(j) for j in range(2)] == [29, 15]
assert (R3F.delta, R3G.delta, FAME.delta) == (4, 4, 1)
assert R3F.floorv(1, 2, 1) == 6 and R3F.floorv(1, 1, 2) == 4
assert FAME.floorv(1, 2, 0) == 2 and FAME.floorv(1, 2, 1) == 1

# ---------------- SELF rows (the exactly-THETA members) ---------------
print('== SELF rows ==')
_, dF, RF = run_member(R3F, 'SELF-R3F', [], want_md=(46, 25))
chk('SLOT', R3F.slotd(RF[1]) == {(0, 1): 1458, (1, 0): 19683},
    'R3F self ShC_1 %s' % R3F.slotd(RF[1]))
chk('SLOT', R3F.slotd(RF[0]) == {(2, 2): 295245, (0, 1): 7971615,
                                 (1, 0): 43046721},
    'R3F self ShC_0 %s' % R3F.slotd(RF[0]))
chk('GRD', R3F.graded(RF[1], 0, 1, 25) is True, 'R3F s*-slot graded')
_, dG, RG = run_member(R3G, 'SELF-R3G', [], want_md=(46, 25))
chk('SLOT', R3G.slotd(RG[1]) == {(0, 1): 128, (1, 0): 768},
    'R3G self ShC_1 %s' % R3G.slotd(RG[1]))
chk('SLOT', R3G.slotd(RG[0]) == {(2, 2): 5120, (0, 1): 40960,
                                 (1, 0): 98304},
    'R3G self ShC_0 %s' % R3G.slotd(RG[0]))
run_member(FAME, 'SELF-FAME', [], want_md=(None, None))

# ---------------- preregistered exact-dict member rows ----------------
print('== preregistered member rows ==')
run_member(R3F, 'ROW-A', [(1, 2, 1, 729)],
           want_diffs={1: {(0, 1): -5103, (1, 0): -98415},
                       0: {(2, 2): -1299078, (0, 1): -35075106,
                           (1, 0): -215233605}},
           want_md=(46, 25), law='UNIFORM')
run_member(R3G, 'ROW-B', [(1, 2, 1, 64)],
           want_diffs={1: {(0, 1): -128, (1, 0): -1280},
                       0: {(2, 2): -7168, (0, 1): -57344,
                           (1, 0): -163840}},
           want_md=(46, 25), law='UNIFORM')
run_member(R3F, 'COMBO-R3F', [(1, 2, 1, 729), (1, 1, 2, 81)],
           want_diffs={1: {(0, 1): -11664, (1, 0): -157464}},
           want_md=(46, 25), law='UNIFORM')
run_member(R3G, 'COMBO-R3G', [(1, 2, 1, 64), (1, 1, 2, 16)],
           want_diffs={1: {(0, 1): -384, (1, 0): -2304}},
           want_md=(46, 25), law='UNIFORM')
mW2, _, _ = run_member(R3F, 'ROW-W2 (below-floor)', [(1, 2, 1, 81)],
           want_diffs={1: {(0, 1): 729, (1, 0): 6561},
                       0: {(2, 2): 118098, (0, 1): 3188646,
                           (1, 0): 14348907}},
           want_md=(46, 25))
mW3, _, _ = run_member(R3F, 'ROW-W3 (below-floor pair)',
           [(1, 2, 1, 81), (1, 1, 2, 9)],
           want_diffs={1: {}, 0: {}}, want_md=(None, None))
mW4, _, _ = run_member(R3F, 'ROW-W4 (THE CONTRAST MEMBER)',
           [(1, 2, 1, -162), (1, 1, 2, 9)],
           want_diffs={1: {(0, 1): 2187, (1, 0): 39366},
                       0: {(2, 2): 531441, (0, 1): 14348907,
                           (1, 0): 86093442}},
           want_md=(49, 28))
mEE, dEE, REE = run_member(FAME, 'ROW-EENTRY',
           [(1, 2, 0, 4), (0, 0, 1, 16)],
           want_diffs={0: {(0, 1): -16}, 1: {}},
           want_md=(31, None), law='GAP')
chk('FLIP', FAME.slotd(REE[0]).get((0, 1), 0) == 0,
    'E-ENTRY shadow (0,1) not drained: %s' % FAME.slotd(REE[0]))
mE21, _, _ = run_member(FAME, 'ROW-E21', [(1, 2, 1, 2)],
           want_diffs={1: {(0, 0): -8}, 0: {(1, 0): -32}},
           want_md=(32, 18), law='GAP')
e20pins = []
for k in range(3):
    c = 4 * 2 ** k
    md, _, _ = run_member(FAME, 'ROW-E20 c=%d' % c, [(1, 2, 0, c)],
               want_diffs={0: {(0, 1): -4 * c}, 1: {}}, law='GAP')
    e20pins.append(md[0])
chk('LIN', e20pins == [31, 37, 43],
    'E20 pins %s want [31,37,43]' % e20pins)
run_member(FAME, 'ROW-NOFLOW', [(1, 1, 0, 4)], want_md=(None, None))

# ---------------- the in-budget LAW sweep ------------------------------
print('== in-budget sweep (LEMMA 6.7E / genre-uniformity) ==')
nsw, defectors = 0, 0
for F in (R3F, R3G):
    for a in (1, 2):
        for b in (0, 1, 2):
            fl = F.floorv(1, a, b)
            for eps in range(1, F.p):
                for k in (0, 1):
                    c = eps * F.p ** (fl + k)
                    mds, _, _ = run_member(
                        F, 'SW-%s(%d,%d)c=%d' % (F.name, a, b, c),
                        [(1, a, b, c)], law='UNIFORM')
                    if tuple(mds) != (46, 25):
                        defectors += 1
                    nsw += 1
for a, b in ((2, 0), (2, 1)):
    fl = FAME.floorv(1, a, b)
    for k in (0, 1):
        c = 2 ** (fl + k)
        run_member(FAME, 'SW-FAME(%d,%d)c=%d' % (a, b, c),
                   [(1, a, b, c)], law='GAP')
        nsw += 1
print('  sweep rows: %d (R3F/R3G defectors: %d)' % (nsw, defectors))

# ---------------- teeth -----------------------------------------------
# T-OBSTR: the withdrawn S8.1 sentence predicts an in-budget R3F/R3G
# row off the (46, 25) floor pair; the sweep found none.
tooth('T-OBSTR', defectors == 0,
      'in-budget sweep uniformity (mutant predicts a defector)')
tooth('T-NODELTA', mEE[0] != 30 and mEE[0] == 31,
      'E-ENTRY pin 31 != 30 (mutant drops +delta)')
tooth('T-NODELTA', mE21[1] != 17 and mE21[1] == 18,
      'E21 diff_1 pin 18 != 17 (mutant drops +delta)')
tooth('T-BELOW', mW4[1] == 28 and mW4[1] != 25,
      'W4 mindiff_1 = 28 != 25 (mutant: budget fence dropped)')
tooth('T-BELOW', mW3[1] is None,
      'W3 mindiff_1 = None != 25 (mutant: budget fence dropped)')

print('TEETH kills: %s' % KILLS)
print('RESULT: %d checks, %d violations' % (NCHK, NVIO))
sys.exit(0 if NVIO == 0 else 1)

