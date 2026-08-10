#!/usr/bin/env python3
"""GENTOW6-BOXES passPE2 FRESH-ROUTE verifier leg (hostile pass 2).

Independent implementation: no import of any sealed runner, own
two-variable division engine (dict-of-Y-bands of x-coefficient
dicts — different data layout and authorship from pe1_fresh's
list-of-lists). Exact integer arithmetic. Oracles per frame:
(R) reduce-mod-Phi'-each-step division vs (E) exact two-variable
division with one terminal reduction (slot-dict equality); (S) the
substitution identity sum_j GhatE_j(x, Phi'(x)) * Phi2(x)^j == 0 in
ONE variable (a non-division-shaped exact oracle: the division
identity F = sum Ghat_j K2^j + K2^m evaluated at Y = Phi', where
F(x, Phi') = Phi2^m and K2(x, Phi') = Phi2); honest read DRAIN;
per-coordinate floors. 6.6 leg: two in-file resultant routes
(Sylvester/Bareiss vs Fraction-exact Euclidean) + gp polresultant.

FRAMES (disjoint from PE1's eight and the units' batteries):
  CE4  Q2, Phi' = x^4-2 (e1 = D' = 4, h = 1), e2 = 1, f2 = 2,
       u2 = 7, T = {0,1}: (i_1,a_1) = (3,1), (i_0,a_0) = (2,3),
       chats 1; delta = 3, E2 = 14; Phi2 = Phi'^2 - 2x^3 Phi'
       - 8x^2; m = 3. The verifier's own SECOND e2(f2-t*) = 1
       frame at CE3's axis: the k = 3 exception is LIVE with SLACK
       budget (3 i_{t*} = 9 > 2D' = 8; CE3 was tight at 6 = 6),
       so the exception's x-slot is 1 = 9-8 (CE3's was 0) — still
       < a* = 2. B*+1 = 5, j* = 2, (a*,b*) = (2,1), THETA =
       [45, 31, 17].
  CE5  same geometry, m = 4: the FIRST frame anywhere with TWO
       live exception ks (k = 3: 9 >= 8; k = 4: 12 >= 12 tight)
       AND p | binom(m,2) (= 6): the (b2) kill and the corrected
       (a) census interact. B*+1 = 7, j* = 3, (a*,b*) = (2,1),
       THETA = [59, 45, 31, 17].
  Q54  Q5, Phi' = x^2-5, e2 = 2, f2 = 1, u2 = 7, (i_0,a_0) =
       (1,3), chat = 1, delta = 3, E2 = 14; Phi2 = Phi'^2 - 125x;
       m = 4. 6.7C' at p = 5, both units: binom(4,2) = 6 and
       2 binom(4,3) = 8 are 5-units — top AND j*-1 attain.
  Q56  same geometry, m = 6: p = 5 | binom(6,2) = 15 AND
       p = 5 | 2 binom(6,3) = 40 — the FIRST p | 2 binom(m,3)
       j*-1 kill anywhere (box3's P-frames tested p = 3 only;
       PE1's Q55/Q57 tested the top slot only).
  R3F  Q3, Phi' = x^3-3 (e1 = 3), e2 = 1, f2 = 3, u2 = 7,
       T = {0,1,2}: (i_2,a_2) = (1,2), (i_1,a_1) = (2,4),
       (i_0,a_0) = (0,7), chats 1; delta = 4, E2 = 21; mu2 = 2.
       NEW regime-3 genre (2 i_{t*} = 2 < 3; overflowing pairs
       {1,1} s=2 and {1,2} s=3): s* = 3 via the SINGLETON mixed
       pair, I(s*) = {3}, chi = 2 c-bar_1 c-bar_2 = 2 != 0 mod 3:
       6.7(b1) attain. j*3 = 1, b*3 = 1, THETA = [46, 25].
  R3G  same shape at Q2 (Phi' = x^3-2): chi = 2 = 0 mod 2:
       6.7(b2) fires at the s*-slot — while the LOWER-s pair
       {1,1} carries a graded floor digit at (1,0): pin(ShC_1) =
       THETA_1 = 25 ON the floor. The BP3-shaped honesty stress
       INSIDE regime 3: (b2) must claim only the s*-slots.
  RES-M2  6.6(d) separation at m' = 2 (box2's T1 ran m' = 1
       only): FAM-P5 geography Q3, Phi' = x^2-3, Phi2 =
       Phi'^2-18x (psi2-block, mu2* = 2), Phi2' = Phi'^2-9x
       (r-class, m' = 2): c_J = mu2*·m'·D2·E2/(e1e2) =
       2·2·4·10/4 = 40; GENTOW-1(a) floors [6,5,4,4|3,3,2,1]
       (ceil((THETA_j - w)/4), THETA = [21,11], w = 2a+5b).

PREREGISTERED WANTS (hand ledgers fully derived BEFORE this file
ran; the CE4/Q54/Q56/R3F/R3G full-coordinate dicts are complete
hand divisions kept in the pass notes):
  CE4: ShC_2 = {(2,1): 12, (1,1): -8, (1,0): 160, (0,0): -160}
       [(2,1) = binom(3,2) chat^2 pi^{2a_1}: graded TRUE at
       THETA_2 = 17 — 6.5(b1) survives the exception; (1,1) = -8
       = the k = 3 exception branch at x-slot 1 < a* = 2, v = 3,
       height 20 = THETA_2 + delta: graded FALSE];
       ShC_1 = {(0,1): 1280, (3,1): -704, (3,0): 2688,
       (2,0): -3584}; ShC_0 = {(2,1): 8704, (1,1): -14336,
       (1,0): 22528, (0,0): -36864}; pins [45, 31, 17] = THETA.
  CE5: ShC_3 b=1 band EXACTLY {(2,1): 24, (1,1): -32, (0,1): 16}
       [cert 24 = binom(4,2)·4: v = 3, height 21 = THETA_3 + ee:
       graded FALSE — the (b2) kill; k = 3 exception -32 at
       x-slot 1, v = 5, height 28: FALSE; k = 4 exception +16 at
       x-slot 0, v = 4, height 23 = THETA_3 + 2delta: FALSE];
       floors at every j; b=0 bands recorded, not want-checked.
  Q54: ShC_3 = {}; ShC_2 = {(0,1): 93750 = 6·5^6} graded TRUE at
       THETA_2 = 31 (6.5(b1) at p = 5); ShC_1 = {(1,1): 15625000
       = 8·5^9, (0,0): 244140625 = 5^12} — the 6.7C' value
       2 binom(4,3)·5^9 with graded TRUE at THETA_1 = 45 (j*-1
       attains); ShC_0 = {(0,1): 4·5^13, (1,0): 5^15} pin 59.
  Q56: ShC_5 = {}; ShC_4 = {(0,1): 234375 = 15·5^6} v = 7 graded
       FALSE at THETA_4 = 31, pin 35 (top-slot p = 5 kill);
       ShC_3 = {(1,1): 78125000 = 40·5^9, (0,0): 3662109375 =
       15·5^12} v = 10/13, both graded FALSE at THETA_3 = 45,
       pin 49 — the FIRST p | 2 binom(m,3) kill; ShC_2 =
       {(0,1): 12·5^14, (1,0): 39·5^15} pin 62 (floor holds, not
       attained) [RUN-1 RED, disclosed: the sealed pin want was
       61 — the verifier's own hand slip w(1,0) = 1 instead of
       a·e2·h = 2 at this one line; every slot VALUE and
       valuation of the frame matched the sealed dict exactly;
       artifact gentow6_boxes_pe2_fresh_output_run1_RED.txt md5
       85293c70, sealed-run runner md5 3cb89803; the single
       repaired literal is this pin];
       ShC_1 = {(1,1): 48·5^16, (0,1): 5^18,
       (0,0): 36·5^19} pin 73 = THETA_1; ShC_0 = {(0,1): 16·5^20,
       (1,1): 5^21, (1,0): 12·5^22} pin 87 = THETA_0.
  R3F: ShC_1 = {(0,1): 1458 = 2·3^6, (1,0): 19683 = 3^9}:
       (0,1) = chi·pi^{a(s*,3)} graded TRUE at THETA_1 = 25, pin
       25 (6.7(b1)); (1,0) = 3^8 + 2·3^8 cascade-cancels in grade
       (v = 9 > 8). ShC_0 = {(2,2): 295245 = 5·3^10,
       (0,1): 7971615 = 5·3^13, (1,0): 43046721 = 3^16} pin 46.
  R3G: ShC_1 = {(0,1): 128 = 2·2^6, (1,0): 768 = 3·2^8}: (0,1)
       graded FALSE at THETA_1 = 25 (chi = 2 = 0 mod 2, the (b2)
       kill: v = 7, height 28); (1,0) graded TRUE: pin(ShC_1) =
       25 = THETA_1 — attainment ON the floor at the lower-s slot
       with every chi(s*,·) = 0. ShC_0 = {(2,2): 5120 = 5·2^10,
       (0,1): 40960 = 5·2^13, (1,0): 98304 = 3·2^15} pin 46.
  RES-M2: v_3(Res(f_S, g)) = 40 at the bare pair (Phi2^2, Phi2'^2)
       and at 12 random in-box pairs (digits to depth +3); the two
       in-file resultant routes agree exactly on every row; gp
       polresultant matches on 3 rows; v_3(Res(Phi2, Phi2')) = 10
       (the mu2* = m' = 1 sanity row); Smith divisors at one
       in-box pair: sum = 40, each <= 40.
  EVERY shadow frame: dual R/E slot equality per coordinate, the
       substitution identity (S), honest read DRAIN, floors
       (pin(ShC_j) >= THETA_j or None).

TEETH (mutants that must die; kill counts asserted):
  T-SEAL65A the sealed (pre-r1) 6.5(a) forcing "(2,{t*,t*},1,0)
       unconditionally" — predicts NO Y = B*+1 content off the
       cert slot: dies at CE4 ((1,1)@j2 = -8 present) and CE5
       ((1,1)@j3, (0,1)@j3 present): 3 kills.
  T-OLD67C the refuted 6.7C law (binom(m,2)-binom(m,3)): predicts
       2·5^9 at Q54-j1 (measured 8·5^9) and -5·5^9 at Q56-j3
       (measured 40·5^9): 2 kills.
  T-CJM1 c_J with m' read as 1 (= 20): dies at the bare-pair
       RES-M2 row (measured 40): 1 kill.
  T-CHINOW chi without the (2 - delta_{tt'}) weighting (all
       coefficients 1): predicts graded TRUE at R3G's s*-slot
       (measured FALSE): 1 kill; BLIND at R3F (1 != 0 and truth
       2 != 0 agree — disclosed).
"""
import subprocess, sys
from fractions import Fraction

# ---------- one-variable integer polys (lists, own code) -------------
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
    """divmod by monic g."""
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

# ---------- two-variable engine: dict Ydeg -> dict xdeg -> c ----------
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
        # lifts: {t: (i_t, a_t, chat_t)}
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
        # K2 slots: K2 = Y^n - sum_t chat p^a x^i Y^{e2 t};
        # slot k of the SUBTRACTED part (for division emissions)
        self.K2lift = {}
        for t, (i, a, c) in lifts.items():
            self.K2lift[e2 * t] = xd_add(self.K2lift.get(e2 * t, {}),
                                         {i: c * p ** a})
        # Phi2 = Phi'^n - sum lifts * Phi'^{e2 t} (one variable)
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
        """base-Phi' expansion of one-var poly -> {Ydeg: xdict}."""
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

    def drain(self):
        r = self.phi2pow()
        for _ in range(self.m):
            r, rem = dm(r, self.PHI2)
            if st(rem):
                return False
        return r == [1]

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

    def shadows(self):
        F = self.dev(self.phi2pow())
        R, qR = self.divide(F, True)
        Eraw, qE = self.divide(F, False)
        # non-vacuity: final quotient == 1 exactly (K2^m top)
        for qq in (qR, qE):
            assert set(qq) <= {0} and qq.get(0, {}) == {0: 1}, 'top != 1'
        # substitution oracle: sum_j GhatE_j(x, Phi') Phi2^j == 0
        pw2, acc = [1], []
        s = []
        p2 = [1]
        for j in range(self.m):
            gj = []
            for b, xdct in Eraw[j].items():
                xp = [0] * (max(xdct) + 1) if xdct else []
                for i, c in xdct.items():
                    xp[i] = c
                # times Phi'^b
                t = xp
                for _ in range(b):
                    t = ml(t, self.PHI1)
                gj = ad(gj, t)
            s = ad(s, ml(gj, p2))
            p2 = ml(p2, self.PHI2)
        subst_ok = (s == [])
        E = [{b: xd_red(xdct, self.PHI1) for b, xdct in coord.items()}
             for coord in Eraw]
        return R, E, subst_ok

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

def runfr(F, wants, pins, gflags):
    print('== %s (p=%d, m=%d) ==' % (F.name, F.p, F.m))
    chk('DRAIN', F.drain(), '%s not DRAIN' % F.name)
    R, E, sok = F.shadows()
    chk('SUBST', sok, '%s substitution identity failed' % F.name)
    for j in range(F.m):
        chk('DUAL', F.slotd(R[j]) == F.slotd(E[j]),
            '%s R != E at j=%d' % (F.name, j))
        pn = F.pin(R[j])
        chk('FLOOR', pn is None or pn >= F.theta(j),
            '%s pin_%d=%s < %d' % (F.name, j, pn, F.theta(j)))
        print('   ShC_%d = %s pin %s (THETA %d)' %
              (j, F.slotd(R[j]), pn, F.theta(j)))
    for j, dw in wants.items():
        chk('FULL', F.slotd(R[j]) == dw,
            '%s ShC_%d = %s want %s' % (F.name, j, F.slotd(R[j]), dw))
    for j, pw in pins.items():
        chk('PIN', F.pin(R[j]) == pw,
            '%s pin_%d = %s want %s' % (F.name, j, F.pin(R[j]), pw))
    for (j, a, b, g) in gflags:
        chk('GRADED', F.graded(R[j], a, b, F.theta(j)) == g,
            '%s graded j%d (%d,%d) want %s' % (F.name, j, a, b, g))
    return R

# ---------------- frames ---------------------------------------------
CE4 = Fr2('CE4', 2, [-2, 0, 0, 0, 1], 1, 1, 2, 7,
          {1: (3, 1, 1), 0: (2, 3, 1)}, 3)
CE5 = Fr2('CE5', 2, [-2, 0, 0, 0, 1], 1, 1, 2, 7,
          {1: (3, 1, 1), 0: (2, 3, 1)}, 4)
Q54 = Fr2('Q54', 5, [-5, 0, 1], 1, 2, 1, 7, {0: (1, 3, 1)}, 4)
Q56 = Fr2('Q56', 5, [-5, 0, 1], 1, 2, 1, 7, {0: (1, 3, 1)}, 6)
R3F = Fr2('R3F', 3, [-3, 0, 0, 1], 1, 1, 3, 7,
          {2: (1, 2, 1), 1: (2, 4, 1), 0: (0, 7, 1)}, 2)
R3G = Fr2('R3G', 2, [-2, 0, 0, 1], 1, 1, 3, 7,
          {2: (1, 2, 1), 1: (2, 4, 1), 0: (0, 7, 1)}, 2)

assert [CE4.theta(j) for j in range(3)] == [45, 31, 17]
assert [CE5.theta(j) for j in range(4)] == [59, 45, 31, 17]
assert [Q54.theta(j) for j in range(4)] == [59, 45, 31, 17]
assert [Q56.theta(j) for j in range(6)] == [87, 73, 59, 45, 31, 17]
assert [R3F.theta(j) for j in range(2)] == [46, 25]
assert [R3G.theta(j) for j in range(2)] == [46, 25]
assert (CE4.delta, Q54.delta, R3F.delta) == (3, 3, 4)

runfr(CE4,
      {2: {(2, 1): 12, (1, 1): -8, (1, 0): 160, (0, 0): -160},
       1: {(0, 1): 1280, (3, 1): -704, (3, 0): 2688, (2, 0): -3584},
       0: {(2, 1): 8704, (1, 1): -14336, (1, 0): 22528, (0, 0): -36864}},
      {0: 45, 1: 31, 2: 17},
      [(2, 2, 1, True), (2, 1, 1, False)])
R = runfr(CE5, {}, {}, [(3, 2, 1, False), (3, 1, 1, False),
                       (3, 0, 1, False)])
b1band = {s: c for s, c in CE5.slotd(R[3]).items() if s[1] == 1}
chk('CE5B1', b1band == {(2, 1): 24, (1, 1): -32, (0, 1): 16},
    'CE5 j3 b=1 band = %s' % b1band)
chk('CE5V', vp(CE5.slotd(R[3])[(1, 1)], 2) == 5 and
    vp(CE5.slotd(R[3])[(0, 1)], 2) == 4, 'CE5 exception valuations')
runfr(Q54,
      {3: {}, 2: {(0, 1): 93750},
       1: {(1, 1): 15625000, (0, 0): 244140625},
       0: {(0, 1): 4 * 5 ** 13, (1, 0): 5 ** 15}},
      {0: 59, 1: 45, 2: 31, 3: None},
      [(2, 0, 1, True), (1, 1, 1, True)])
runfr(Q56,
      {5: {}, 4: {(0, 1): 234375},
       3: {(1, 1): 78125000, (0, 0): 3662109375},
       2: {(0, 1): 12 * 5 ** 14, (1, 0): 39 * 5 ** 15},
       1: {(1, 1): 48 * 5 ** 16, (0, 1): 5 ** 18, (0, 0): 36 * 5 ** 19},
       0: {(0, 1): 16 * 5 ** 20, (1, 1): 5 ** 21, (1, 0): 12 * 5 ** 22}},
      {0: 87, 1: 73, 2: 62, 3: 49, 4: 35, 5: None},
      [(4, 0, 1, False), (3, 1, 1, False), (3, 0, 0, False)])
runfr(R3F,
      {1: {(0, 1): 1458, (1, 0): 19683},
       0: {(2, 2): 295245, (0, 1): 7971615, (1, 0): 43046721}},
      {0: 46, 1: 25},
      [(1, 0, 1, True), (1, 1, 0, False)])
runfr(R3G,
      {1: {(0, 1): 128, (1, 0): 768},
       0: {(2, 2): 5120, (0, 1): 40960, (1, 0): 98304}},
      {0: 46, 1: 25},
      [(1, 0, 1, False), (1, 1, 0, True)])

# ---------------- teeth on the shadow legs ---------------------------
d4 = CE4.slotd(CE4.shadows()[0][2])
d5 = CE5.slotd(CE5.shadows()[0][3])
tooth('T-SEAL65A', (1, 1) in d4, 'CE4 (1,1)@j2 present (mutant: absent)')
tooth('T-SEAL65A', (1, 1) in d5, 'CE5 (1,1)@j3 present')
tooth('T-SEAL65A', (0, 1) in d5, 'CE5 (0,1)@j3 present')
q1 = Q54.slotd(Q54.shadows()[0][1])
q3 = Q56.slotd(Q56.shadows()[0][3])
old4 = (6 - 4) * 5 ** 9      # binom(4,2)-binom(4,3) law
old6 = (15 - 20) * 5 ** 9    # binom(6,2)-binom(6,3) law
tooth('T-OLD67C', q1[(1, 1)] != old4,
      'Q54 j1 (1,1) = %d vs old law %d' % (q1[(1, 1)], old4))
tooth('T-OLD67C', q3[(1, 1)] != old6,
      'Q56 j3 (1,1) = %d vs old law %d' % (q3[(1, 1)], old6))
# T-CHINOW: chi with all integer weights 1 (drop the 2-delta) at R3G:
# predicts the s*-slot graded TRUE (1 != 0 mod 2); measured FALSE.
g_s = R3G.graded(R3G.shadows()[0][1], 0, 1, R3G.theta(1))
tooth('T-CHINOW', g_s is False, 'R3G s*-slot graded %s (mutant TRUE)'
      % g_s)
print('   [T-CHINOW blind at R3F: mutant chi = 1 != 0 and true chi = 2'
      ' != 0 agree — disclosed]')

# ---------------- RES-M2: THEOREM 6.6(d) at m-prime = 2 --------------
print('== RES-M2 (FAM-P5 geography, mu2* = 2, m\' = 2, c_J = 40) ==')
P, PHI1 = 3, [-3, 0, 1]
PHI2 = st(ad(ml([-3, 0, 1], [-3, 0, 1]), [0, -18]))   # x^4-6x^2-18x+9
PHI2p = st(ad(ml([-3, 0, 1], [-3, 0, 1]), [0, -9]))   # x^4-6x^2-9x+9

def sylv(u, w):
    du, dw = len(u) - 1, len(w) - 1
    d = du + dw
    M = [[0] * d for _ in range(d)]
    for i in range(dw):
        for k, c in enumerate(u):
            M[i + k][i] = c
    for j in range(du):
        for k, c in enumerate(w):
            M[j + k][dw + j] = c
    return M

def bdet(M):
    A = [r[:] for r in M]
    n, sgn, prev = len(A), 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k]:
                    A[k], A[r] = A[r], A[k]
                    sgn = -sgn
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sgn * A[-1][-1]

def eures(f, g):
    """resultant by Fraction-exact Euclidean recursion."""
    f = [Fraction(c) for c in f]
    g = [Fraction(c) for c in g]
    if len(g) == 1:
        return g[0] ** (len(f) - 1)
    df, dg, lg = len(f) - 1, len(g) - 1, g[-1]
    r = list(f)
    while len(r) - 1 >= dg and any(r):
        c, d = r[-1] / lg, len(r) - 1 - dg
        for k in range(len(g)):
            r[d + k] -= c * g[k]
        while r and r[-1] == 0:
            r.pop()
    if not r:
        return Fraction(0)
    dr = len(r) - 1
    return ((-1) ** (df * dg)) * lg ** (df - dr) * eures(g, r)

def member(key, seed):
    """key^2 + budget perturbations; seed drives a simple LCG."""
    THJ, W = [21, 11], lambda a, b: 2 * a + 5 * b
    f = ml(key, key)
    s = seed
    for j in range(2):
        for a in range(2):
            for b in range(2):
                s = (s * 1103515245 + 12345) % (2 ** 31)
                c = s % 3
                s = (s * 1103515245 + 12345) % (2 ** 31)
                extra = s % 3
                if c == 0:
                    continue
                fl = -((W(a, b) - THJ[j]) // 4)   # ceil((TH-w)/4)
                t = [0] * a + [1]
                for _ in range(b):
                    t = ml(t, PHI1)
                for _ in range(j):
                    t = ml(t, key)
                f = ad(f, [c * P ** (fl + extra) * x for x in t])
    return f

vres_rows = []
bare_f, bare_g = ml(PHI2, PHI2), ml(PHI2p, PHI2p)
pairs = [(bare_f, bare_g, 'bare')]
for i in range(12):
    pairs.append((member(PHI2, 1000 + i), member(PHI2p, 5000 + i),
                  'smp%d' % i))
for f, g, tag in pairs:
    r1 = bdet(sylv(f, g))
    r2 = eures(f, g)
    chk('RDUAL', Fraction(r1) == r2, 'RES-M2 %s routes differ' % tag)
    v = vp(r1, P)
    vres_rows.append(v)
    chk('CJ40', v == 40, 'RES-M2 %s v(Res) = %d want 40' % (tag, v))
print('   v(Res) rows: %s' % vres_rows)
tooth('T-CJM1', vres_rows[0] != 20, 'bare v(Res) = 40 != 20 (m\'=1 law)')
chk('SAN10', vp(bdet(sylv(PHI2, PHI2p)), P) == 10,
    'sanity v(Res(Phi2, Phi2\')) want 10')

def smith_divs(M, p):
    A = [[Fraction(x) for x in r] for r in M]
    divs = []
    def fv(x):
        if x == 0:
            return None
        return vp(x.numerator, p) - vp(x.denominator, p)
    while A and any(any(x != 0 for x in r) for r in A):
        best = None
        for i, r in enumerate(A):
            for j, x in enumerate(r):
                v = fv(x)
                if v is not None and (best is None or v < best[0]):
                    best = (v, i, j)
        v, bi, bj = best
        divs.append(v)
        piv = A[bi][bj]
        A = [[x - r[bj] / piv * A[bi][j2] for j2, x in enumerate(r)]
             for i, r in enumerate(A) if i != bi]
        A = [[x for j2, x in enumerate(r) if j2 != bj] for r in A]
    return sorted(divs)

sd = smith_divs(sylv(pairs[1][0], pairs[1][1]), P)
chk('SMITH', sum(sd) == 40 and max(sd) <= 40 and len(sd) == 16,
    'Smith divisors %s' % sd)
print('   Smith profile (in-box pair): %s' % sd)

gp_ok = 0
for f, g, tag in pairs[:3]:
    try:
        s = subprocess.run(
            ['gp', '-q'], input=('polresultant(Pol(%s), Pol(%s))'
            % (list(reversed(f)), list(reversed(g)))).encode(),
            capture_output=True, timeout=60)
        got = int(s.stdout.strip())
        chk('GP', got == bdet(sylv(f, g)), 'gp mismatch at %s' % tag)
        gp_ok += 1
    except Exception as e:
        chk('GP', False, 'gp row %s failed: %s' % (tag, e))
print('   gp rows OK: %d' % gp_ok)

print('TEETH kills: %s' % KILLS)
print('RESULT: %d checks, %d violations' % (NCHK, NVIO))
sys.exit(0 if NVIO == 0 else 1)
