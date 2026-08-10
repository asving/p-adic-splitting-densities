#!/usr/bin/env python3
"""GENTOW6-BOXES passPE1 FRESH-ROUTE verifier leg (hostile pass).

Independent implementation (no import of any sealed runner). Exact
integer arithmetic throughout. Dual routes: (R) reduce coefficients
mod Phi' at every division step vs (E) exact two-variable division
with one terminal reduction; plus a RECONSTRUCTION identity check on
route E's raw output (F == Sum_j Ghat_j * K2^j exactly, before any
reduction) as a third, non-division-shaped oracle.

PREREGISTERED WANTS (hand ledgers derived before this file ran;
verifier's own arithmetic, THEOREM GENTOW-6.5's displays):

  BRIDGE X3 = FR5X mu2=3 (committed PE5 vector, cross-pin):
    ShC = [{(1,1): 524288}, {(0,1): 12288}, {}], pins [91, 61, None].
  F6 = FR5X geometry m=6:  j*=4, ShC_4 = {(0,1): 61440 = 15*4096},
    v=12, graded THETA_4=61 NONZERO (p=2 does not divide 15);
    ShC_5 = {}.
  F7 = FR5X m=7: j*=5, ShC_5 = {(0,1): 86016 = 21*4096}, v=12,
    graded 61 NONZERO; ShC_6 = {}.
  P36 = GEN-P3 m=6 (p=3 | binom(6,2)=15): j*=4,
    ShC_4 = {(0,1): 4860 = 15*4*81}, v_3=5, graded THETA_4=21 ZERO,
    pin 25; ShC_5 = {}.
  Q55 = Q5 frame (Phi'=x^2-5, Phi2=Phi'^2-125x, u2=7) m=5
    (p=5 | binom(5,2)=10): j*=3, ShC_3 = {(0,1): 156250 = 10*5^6},
    v_5=7, graded THETA_3=31 ZERO, pin 35; ShC_4 = {}.
  Q57 = same geometry m=7 (binom(7,2)=21 a 5-unit): j*=5,
    ShC_5 = {(0,1): 328125 = 21*5^6}, v_5=6, graded 31 NONZERO;
    ShC_6 = {}.
  CE3 = COUNTER-FRAME to 6.5(a)'s equality-forcing sentence:
    Q2, Phi' = x^3-2 (e1=D'=3, h=1), e2=1, f2=2, u2=5, T={0,1},
    t*=1 (i_1=2, a_1=1, chat_1=1; i_0=1, a_0=3), delta=2, E2=10,
    Phi2 = Phi'^2 - 2x^2 Phi' - 8x. Here e2(f2-t*) = 1 and
    3 i_{t*} = 6 = 2D': the k=3 diagonal source -8x^6 Y^3 extracts
    TWICE to -8Y^5 with Y = 5 = B*+1 at x-slot 0 != a* = 1 —
    refuting (a)'s "Y = B*+1 forcing (2, {t*,t*}, 1, 0)".
    WANTS: m=3, j*=2, THETA=[32,22,12];
    ShC_2 = {(1,1): 12, (0,1): -8, (0,0): 160, (2,0): -32}
    (cert digit binom(3,2)*chat^2*pi^{2a_1} = 12 at (a*,b*)=(1,1),
    v=2, graded THETA_2=12 NONZERO — (b1) SURVIVES; the refuter
    (0,1) = -8 nonzero, v=3, height 14 > 12 — above the graded
    layer exactly as Step IV's weight fence says); pins [32,22,12].
  BP3 = iff-REFUTER for the two dated append summaries ("attainment
    on the floor iff p does not divide binom(mu2,2)") — NOT of the
    theorem, whose (b2) claims nothing: Q3, Phi' = x^2-3, e2=1,
    f2=2, u2=3, t*=1 (i_1=1, a_1=1), i_0=0, a_0=3, delta=1, E2=6,
    Phi2 = Phi'^2 - 3x Phi' - 27, m=3: p=3 | binom(3,2)=3.
    WANTS: j*=2, THETA_2=7; cert slot (0,1)@j2 = 27, v_3=3,
    graded-7 ZERO ((b2) kill: 2*3+3 = 9 > 7); BUT slot (1,0)@j2
    (the m=3 triple branch -27xY^4, e=1, weight mE2+delta) has
    v_3 = 3 and graded-7 digit NONZERO: pin(ShC_2) = 7 = THETA_2 —
    the shadow diverges from DRAIN exactly on the floor at
    coordinate j* even though p | binom(m,2).
  EVERY frame: dual R/E slot equality per coordinate,
    reconstruction identity, honest read DRAIN, floor pins
    (pin(ShC_j) >= THETA_j or None), above-top coords empty.
"""
import sys

# ---------- integer x-poly utilities (own code) -----------------------
def strip(f):
    while f and f[-1] == 0:
        f.pop()
    return f

def add(f, g):
    n = max(len(f), len(g))
    return strip([(f[i] if i < len(f) else 0) +
                  (g[i] if i < len(g) else 0) for i in range(n)])

def neg(f):
    return [-c for c in f]

def mul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return strip(out)

def divmod_monic(f, g):
    f = list(f)
    q = [0] * max(1, len(f) - len(g) + 1)
    while len(f) >= len(g):
        c, d = f[-1], len(f) - len(g)
        q[d] = c
        for i in range(len(g)):
            f[d + i] -= c * g[i]
        strip(f)
    return strip(q), strip(f)

def vp(n, p):
    n = abs(n)
    assert n
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

# ---------- frame ------------------------------------------------------
class Fr:
    def __init__(self, name, p, PHI1, h, e2, f2, u2, PHI2, m):
        self.name, self.p, self.PHI1, self.h = name, p, PHI1, h
        self.e2, self.f2, self.u2, self.m = e2, f2, u2, m
        self.Dp = len(PHI1) - 1
        self.e1 = self.Dp          # f1 = 1
        self.E2 = e2 * f2 * u2
        self.delta = u2 - e2 * self.Dp * h
        self.ee = self.e1 * e2
        self.PHI2 = PHI2
        self.n = e2 * f2           # deg_Y K2
        # base-Phi' expansion of PHI2 -> K2 coefficients
        self.K2 = self.dev(PHI2, self.n + 1)
        assert self.K2[self.n] == [1], 'K2 not monic'

    def dev(self, f, nslots):
        out, r = [], list(f)
        for _ in range(nslots):
            r, rem = divmod_monic(r, self.PHI1)
            out.append(rem)
        assert not strip(r), 'dev overflow'
        return out

    def theta(self, j):
        return (self.m - j) * self.E2 + self.delta

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def red(self, c):
        return divmod_monic(c, self.PHI1)[1]

    def phi2pow(self):
        f = [1]
        for _ in range(self.m):
            f = mul(f, self.PHI2)
        return f

    def honest_drain(self):
        r = self.phi2pow()
        for _ in range(self.m):
            r, rem = divmod_monic(r, self.PHI2)
            if strip(rem):
                return False
        return r == [1]

    def divide(self, A, red_each):
        out = []
        for _ in range(self.m):
            q = [[] for _ in range(max(1, len(A) - self.n))]
            for i in range(len(A) - 1, self.n - 1, -1):
                c = A[i]
                if strip(list(c)):
                    q[i - self.n] = add(q[i - self.n], c)
                    A[i] = []
                    for k in range(self.n):
                        t = add(A[i - self.n + k], neg(mul(c, self.K2[k])))
                        A[i - self.n + k] = self.red(t) if red_each else t
            out.append([list(A[b]) for b in range(self.n)])
            A = q
        assert strip(list(A[0])) == [1] and \
            all(not strip(list(x)) for x in A[1:]), 'top quotient != 1'
        return out

    def shadows(self):
        f = self.phi2pow()
        F = self.dev(f, self.n * self.m + 1)
        # route R
        R = self.divide([self.red(list(a)) for a in F], True)
        # route E, raw for reconstruction, then terminal reduction
        Eraw = self.divide([list(a) for a in F], False)
        # reconstruction: F == sum_j Ghat_j K2^j + K2^m  (exact)
        kp = [[1]]
        for _ in range(self.m):
            nk = [[] for _ in range(len(kp) + self.n)]
            for i, c in enumerate(kp):
                for k2i, k2c in enumerate(self.K2):
                    nk[i + k2i] = add(nk[i + k2i], mul(c, k2c))
            kp = [strip(x) for x in nk]
        acc = [list(x) for x in kp]      # K2^m * 1 (top coefficient)
        kpj = [[1]]
        for j in range(self.m):
            for i, c in enumerate(Eraw[j]):
                idx = i
                for ki, kc in enumerate(kpj):
                    pass
                # multiply Ghat_j (coeffs Eraw[j] at Y^0..Y^{n-1}) by K2^j
                # accumulate below
            kpj = kpj  # placeholder, replaced by direct method below
        # direct reconstruction
        recon = [list(x) for x in kp]
        kpow = [[[1]]]
        for j in range(1, self.m):
            prev = kpow[-1]
            nk = [[] for _ in range(len(prev) + self.n)]
            for i, c in enumerate(prev):
                for k2i in range(self.n + 1):
                    k2c = self.K2[k2i] if k2i < self.n else [1]
                    nk[i + k2i] = add(nk[i + k2i], mul(c, k2c))
            kpow.append([strip(x) for x in nk])
        for j in range(self.m):
            for gi, gc in enumerate(Eraw[j]):
                if not strip(list(gc)):
                    continue
                for ki, kc in enumerate(kpow[j]):
                    if strip(list(kc)):
                        idx = gi + ki
                        while len(recon) <= idx:
                            recon.append([])
                        recon[idx] = add(recon[idx], mul(gc, kc))
        ok_recon = len(strip([0])) == 0  # trivially true placeholder
        ok_recon = all(strip(list(a)) == strip(list(b)) for a, b in
                       zip(recon + [[]] * (len(F) - len(recon)),
                           F + [[]] * (len(recon) - len(F))))
        E = [[self.red(list(c)) for c in coord] for coord in Eraw]
        return R, E, ok_recon

    def slotdict(self, coord):
        d = {}
        for b, g in enumerate(coord):
            for a, c in enumerate(g):
                if c:
                    d[(a, b)] = c
        return d

    def pin(self, coord):
        best = None
        for (a, b), c in self.slotdict(coord).items():
            ht = self.ee * vp(c, self.p) + self.w(a, b)
            best = ht if best is None else min(best, ht)
        return best

    def graded(self, coord, a, b, H):
        c = self.slotdict(coord).get((a, b), 0)
        if c == 0:
            return False
        nn = H - self.w(a, b)
        return nn >= 0 and nn % self.ee == 0 and vp(c, self.p) == nn // self.ee

NCHK = NVIO = 0
def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

def run(F, jstar, topwant, vstar, gwant, pinw, extra, fulldicts=None,
        pins=None):
    print('== %s (p=%d m=%d j*=%d) ==' % (F.name, F.p, F.m, jstar))
    chk('DRAIN', F.honest_drain(), '%s honest read not DRAIN' % F.name)
    R, E, ok = F.shadows()
    chk('RECON', ok, '%s reconstruction identity failed' % F.name)
    for j in range(F.m):
        chk('DUAL', F.slotdict(R[j]) == F.slotdict(E[j]),
            '%s routes differ at j=%d' % (F.name, j))
    top = F.slotdict(R[jstar])
    print('   ShC_%d = %s  pin %s (THETA %d)' %
          (jstar, top, F.pin(R[jstar]), F.theta(jstar)))
    if topwant is not None:
        chk('TOPD', top == topwant, '%s ShC_%d = %s want %s'
            % (F.name, jstar, top, topwant))
    ab = [s for s in ([min(topwant)] if topwant else [])]
    for j in range(jstar + 1, F.m):
        chk('TOPZ', not F.slotdict(R[j]), '%s ShC_%d nonzero' % (F.name, j))
    for j in range(F.m):
        pn = F.pin(R[j])
        chk('FLOOR', pn is None or pn >= F.theta(j),
            '%s pin_%d = %s < THETA %d' % (F.name, j, pn, F.theta(j)))
    for (slot, vw, gw, tagmsg) in extra:
        c = F.slotdict(R[jstar]).get(slot, 0)
        chk('SLOT', c != 0 and vp(c, F.p) == vw, '%s %s slot %s v=%s want %d'
            % (F.name, tagmsg, slot, vp(c, F.p) if c else None, vw))
        chk('SLOT', F.graded(R[jstar], slot[0], slot[1],
                             F.theta(jstar)) == gw,
            '%s %s slot %s graded want %s' % (F.name, tagmsg, slot, gw))
    if pinw is not None:
        chk('PIN', F.pin(R[jstar]) == pinw, '%s pin_%d = %s want %d'
            % (F.name, jstar, F.pin(R[jstar]), pinw))
    if pins is not None:
        got = [F.pin(R[j]) for j in range(F.m)]
        chk('PINS', got == pins, '%s pins %s want %s' % (F.name, got, pins))
    if fulldicts is not None:
        for j, dw in fulldicts.items():
            chk('FULL', F.slotdict(R[j]) == dw, '%s ShC_%d = %s want %s'
                % (F.name, j, F.slotdict(R[j]), dw))

PX2, PX3 = [-2, 0, 1], [-3, 0, 1]
FRX = [4, -64, -4, 0, 1]                      # (x^2-2)^2 - 64x
FRP = [9, -18, -6, 0, 1]                      # (x^2-3)^2 - 18x
FRQ = [25, -125, -10, 0, 1]                   # (x^2-5)^2 - 125x
CE3PHI2 = [4, -8, 4, -4, 0, -2, 1]            # (x^3-2)^2 -2x^2(x^3-2) -8x
BP3PHI2 = [-18, 9, -6, -3, 1]                 # (x^2-3)^2 -3x(x^2-3) -27

X3 = Fr('X3-bridge', 2, PX2, 1, 2, 1, 13, FRX, 3)
F6 = Fr('F6', 2, PX2, 1, 2, 1, 13, FRX, 6)
F7 = Fr('F7', 2, PX2, 1, 2, 1, 13, FRX, 7)
P36 = Fr('P36', 3, PX3, 1, 2, 1, 5, FRP, 6)
Q55 = Fr('Q55', 5, [-5, 0, 1], 1, 2, 1, 7, FRQ, 5)
Q57 = Fr('Q57', 5, [-5, 0, 1], 1, 2, 1, 7, FRQ, 7)
CE3 = Fr('CE3', 2, [-2, 0, 0, 1], 1, 1, 2, 5, CE3PHI2, 3)
BP3 = Fr('BP3', 3, PX3, 1, 1, 2, 3, BP3PHI2, 3)

assert [X3.theta(j) for j in range(3)] == [87, 61, 35]
assert (F6.theta(4), F7.theta(5)) == (61, 61)
assert P36.theta(4) == 21 and Q55.theta(3) == 31 and Q57.theta(5) == 31
assert [CE3.theta(j) for j in range(3)] == [32, 22, 12]
assert BP3.theta(2) == 7
assert (CE3.delta, BP3.delta) == (2, 1)

run(X3, 1, {(0, 1): 12288}, 12, True, 61, [],
    fulldicts={0: {(1, 1): 524288}, 1: {(0, 1): 12288}, 2: {}},
    pins=[91, 61, None])
run(F6, 4, {(0, 1): 61440}, 12, True, 61,
    [((0, 1), 12, True, 'cert')])
run(F7, 5, {(0, 1): 86016}, 12, True, 61,
    [((0, 1), 12, True, 'cert')])
run(P36, 4, {(0, 1): 4860}, 5, False, 25,
    [((0, 1), 5, False, 'cert-cancel')])
run(Q55, 3, {(0, 1): 156250}, 7, False, 35,
    [((0, 1), 7, False, 'cert-cancel')])
run(Q57, 5, {(0, 1): 328125}, 6, True, 31,
    [((0, 1), 6, True, 'cert')])
run(CE3, 2, {(1, 1): 12, (0, 1): -8, (0, 0): 160, (2, 0): -32}, 2,
    True, 12,
    [((1, 1), 2, True, 'cert'), ((0, 1), 3, False, 'REFUTER-k3e2')],
    pins=[32, 22, 12])
# the refuter is load-bearing: (0,1)@j2 nonzero = Y-content at
# B*+1 = 5 at x-slot 0 != a* = 1, impossible under 6.5(a)'s
# equality-forcing sentence
c = CE3.slotdict(CE3.shadows()[0][2]).get((0, 1), 0)
chk('REFUTE-A', c != 0,
    'CE3 (0,1)@j2 empty: 6.5(a) equality-forcing NOT refuted')
run(BP3, 2, None, 3, False, 7,
    [((0, 1), 3, False, 'cert-cancel-p3'),
     ((1, 0), 3, True, 'triple-branch-floor')])
# the iff-refuter is load-bearing: pin = THETA with graded nonzero
# at (1,0) => attainment on the floor DESPITE p | binom(3,2)

print('RESULT: %d checks, %d violations' % (NCHK, NVIO))
sys.exit(0 if NVIO == 0 else 1)
