#!/usr/bin/env python3
"""GENTOW1 passPE1 FRESH ROUTE: frames disjoint from the note's five
battery families.  Written by the hostile verifier, independent
implementation (own poly engine, own gate, own gp text).

FRAME F1 (THE GAUGE FRAME -- first eta != 1 tower-entry contact):
  p = 3, Phi' = x^2 - 6 (e1 = 2, f1 = 1, h = 1; eta = res(6/3) = 2),
  inner (e2, f2) = (1, 2), u2 = 3 (kappa2 = 3 > D'h = 2), mu2 = 2,
  psi2 = Z^2 + Z + 2 over F3 (disc -7 = 2 nonsquare, irreducible).
  W(t) = floor((f2-t)i(u2)/e1), i(3) = 1: W(1) = 0, W(0) = 1.
  CORRECTED key (GENHN dated erratum 59c1966, c_t |-> c_t*eta^W(t)):
    PHI2C = Phi'^2 + 3x*Phi' + 108   (chat_1 = -1, chat_0 = -4 = 2 mod 3)
  NAIVE key (the T(b)' display GENTOW1 consumed at composition time):
    PHI2N = Phi'^2 + 3x*Phi' + 54    (chat_0 = -2 = 1 mod 3)
  Constants: D2 = 4, E2 = e2f2u2 = 6, m = e1e2 = 2, dv2 = 2v, n = 8,
  w(a,b) = a + 3b.  Floors (note display): j=0: 7*,6,5,5* ;
  j=1: 4*,3,2,2* (pins at (0,0),(1,1) -- f1f2 = 2 flavors).
  Twisted residual of the naive key vs coherent normalizers:
  psi~ = T^2 + T + 1 = (T-1)^2 over F3, psi~(eta2) = 2 != 0 (derived:
  eta2^2 = 2*eta2 + 1, so psi~(eta2) = 3*eta2 + 2 = 2).

FRAME F2 (e1e2 = 6 with e1 = 3 -- factorization new vs FAM-C's 2*3):
  p = 2, Phi' = x^3 - 2 (e1 = 3, f1 = 1, h = 1), inner (e2, f2) =
  (2, 1), u2 = 7 > e2D'h = 6, psi2 = Z + 1 over F2, mu2 = 2, mu1 = 4.
  PHI2 = Phi'^2 - 4x (n2hat(7) = 4x: 3a + i = 7, i = 1, a = 2).
  D2 = 6, E2 = 14, m = 6, n = 12, w(a,b) = 2a + 7b (classes
  0,2,4,1,3,5 -- all six residues, single slot each).  Floors:
  j=0: 5,5,5*,4,4,3 ; j=1: 3,3*,2,2,1,1.  Node floors [29, 15].

PREREGISTERED PREDICTIONS (sealed before the run):
 FR-P1 (erratum replication): ef(PHI2C) = {(2,2)}; ef(PHI2N) = {(4,1)}.
 FR-P2 (floors real at eta != 1): NODE-EQ anchor fC = PHI2C^2 + 729x
   reads (p0, p1) = (13, None) tRAM; 10 random in-budget corrected
   members + 3 deep (v = 40) perturbations pass the level-1 polygon
   gate (dv(A0) = 12 exact, pins weakly above side, monic) + strict-
   above (all Phi'-grid weights of f - PHI2C^2 >= 13) + composed
   floors on readback; node pins p_j >= (2-j)*6 + 1.
 FR-P3 (node oracle at eta != 1): every prime pr of every factor of
   every scored F1 member: 2*nfeltval(x) = pr.e; 2*nfeltval(Phi') =
   3*pr.e; nfeltval(PHI2C) > 3*pr.e STRICT; carrier divisibility
   2 | pr.e... e and 2 | pr.f.
 FR-P4 (THE GAUGE TOOTH -- naive key fails the field floor): at the
   same scored F1 members' primes, nfeltval(PHI2N) == 3*pr.e EXACTLY
   (psi~(eta2) = 2 != 0: no psi-cancellation at the naive key).
   PLUS: naive-key members fN = PHI2N^2 + 729x and PHI2N^2 + 729x +
   3^7: PARI sigma != {(4,2)} (the naive frame's tRAM prediction
   fails -- value-level seam, valuation-level tables identical).
 FR-P5 (sigma both routes): fC sigma = {(4,2)} route1 AND route2;
   SPLTAIL member fS = PHI2C^2 + 27x*PHI2C + 3^8 (pins (16, 7),
   p0 > 2p1) sigma = {(2,2),(2,2)} both routes.
 FR-P6 (refine transfer at eta != 1): Kp = PHI2C - 9*Phi' (what =
   -lift(s; 7), s the eta2-flavor: slot (0,1), v = 2); member
   f6 = Kp^2 + 3^5*x*Kp + 3^9*x (new pins (19, 11), above the
   lam = 7 node).  OLD-key read: pins (14, 7) BOTH alive (q = 3:
   the binomial char-sensitivity, tDBL); NEW-key read: (19, 11)
   tRAM, sigma {(4,2)} by PARI both routes; refined key keeps
   ef = {(2,2)} and level-1 A0-min = E2 = 6.  TEETH: wrong-flavor
   normalizer Kw1 = PHI2C - 27x (t = 0 flavor at height 7) and
   wrong-height Kw2 = PHI2C - 27*Phi' (height 9) both leave an
   event pin (p0 = 14 or p1 = 7) alive.
 FR-P7 (F2 frame): anchor f2a = PHI2^2 + 8x^2*Phi' reads (29, None)
   tRAM sigma {(12,1)} both routes; SPLTAIL f2s = PHI2^2 +
   8x^2*Phi'*PHI2 + 32x (pins (32, 15)) sigma {(6,1),(6,1)}
   route 1; 8 random in-budget members pass gate (dv(A0) = 28
   on dv = 3v ladder... dv(A0)*e2 = mu1*u2 = 28, i.e. 3v-ladder
   value 14 exact) + strict-above (>= 29) + floors readback + node
   pins; node oracle: 6*nfeltval(PHI2) > 14*pr.e STRICT,
   3*nfeltval(x) = pr.e, 6*nfeltval(Phi') = 7*pr.e.
VERDICT: GREEN iff 0 violations and both gauge teeth fire.
NOT RUN (disclosed): non-prime q (d = 2 ambient) -- rnf cost; the
mu2 >= 3 rows (GENTOW-BOX-1 scope, unchanged).
"""
import random
import subprocess
import sys
import time

random.seed(99080901)
T0 = time.time()
VIOL = []
NCHK = [0]
TEETH = {'GAUGE-NODE': 0, 'GAUGE-SIGMA': 0, 'REFWRONG': 0}


def chk(ok, msg):
    NCHK[0] += 1
    if not ok:
        VIOL.append(msg)
        print('  !! VIOLATION: %s' % msg)


def pstrip(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])


def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return pstrip(out)


def psca(c, f):
    return pstrip([c * a for a in f])


def pdivmod(f, g):
    f = list(f)
    dg = len(g) - 1
    assert g[-1] == 1
    q = [0] * max(1, len(f) - dg)
    for i in range(len(f) - 1, dg - 1, -1):
        c = f[i]
        if c:
            q[i - dg] += c
            for j, gj in enumerate(g):
                f[i - dg + j] -= c * gj
    return pstrip(q), pstrip(f[:dg])


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def pstr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'


class Frame(object):
    def __init__(self, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        self.p, self.PHI1, self.h = p, PHI1, h
        self.e1, self.e2, self.f2, self.mu2, self.u2 = e1, e2, f2, mu2, u2
        self.PHI2 = PHI2
        self.Dp = e1
        self.D2 = e1 * e2 * f2
        self.E2 = e2 * f2 * u2
        self.m = e1 * e2
        self.mu1 = e2 * f2 * mu2
        self.n = self.Dp * self.mu1

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def floor(self, j, a, b):
        num = (self.mu2 - j) * self.E2 - self.w(a, b)
        fl = -((-num) // self.m)
        if num % self.m == 0 and num > 0:
            fl += 1
        return max(fl, 0)

    def gate(self, f):
        """level-1 polygon gate on dv = e1*v: dv(A0)*e2 = mu1*u2 exact,
        every pin weakly above the side, monic dev."""
        g, A = list(f), []
        for _ in range(self.mu1):
            g, r = pdivmod(g, self.PHI1)
            A.append(r)
        if g != [1]:
            return 'dev not monic'
        dvs = []
        for c in A:
            vals = [self.e1 * vp(cc, self.p) + i * self.h
                    for i, cc in enumerate(c) if cc]
            dvs.append(min(vals) if vals else None)
        if dvs[0] is None or self.e2 * dvs[0] != self.mu1 * self.u2:
            return 'dv(A0) = %s want %s/e2' % (dvs[0], self.mu1 * self.u2)
        for J in range(1, self.mu1):
            if dvs[J] is not None and \
                    self.e2 * dvs[J] < (self.mu1 - J) * self.u2:
                return 'pin J=%d below side' % J
        return None

    def strictly_above(self, g, thr):
        gg, B = list(g), []
        for _ in range(self.mu1 + self.mu2 + 2):
            gg, r = pdivmod(gg, self.PHI1)
            B.append(r)
        if gg:
            return False
        for J, rb in enumerate(B):
            for a, c in enumerate(rb):
                if c and self.m * vp(c, self.p) + a * self.e2 * self.h \
                        + J * self.u2 <= thr:
                    return False
        return True

    def read_pins(self, f, key):
        g, Cs = list(f), []
        for _ in range(self.mu2):
            g, r = pdivmod(g, key)
            Cs.append(r)
        assert g == [1]
        pins, digs = [], {}
        for j, C in enumerate(Cs):
            gg, B = list(C), []
            for _ in range(self.e2 * self.f2):
                gg, r = pdivmod(gg, self.PHI1)
                B.append(r)
            assert not gg
            vals = []
            for b, rb in enumerate(B):
                for a, c in enumerate(rb):
                    if c:
                        vals.append(self.m * vp(c, self.p) + self.w(a, b))
                        digs[(j, a, b)] = c
            pins.append(min(vals) if vals else None)
        return pins, digs


GPH = r"""
default(parisizemax, 4000000000);
ef1(g, p) = {
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  vecsort(vector(#dec, j, [dec[j].e, dec[j].f]))
}
sig1(f, p) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1, listput(out, [1, 1]),
        my(v = ef1(g, p)); for (j = 1, #v, listput(out, v[j]))));
  vecsort(Vec(out))
}
sig2(f, p) = {
  my(F = factorpadic(f, p, 400), out = List());
  for (i = 1, matsize(F)[1],
    my(v = ef1(liftall(F[i, 1]), p));
    for (j = 1, #v, listput(out, v[j])));
  vecsort(Vec(out))
}
nodev(f, p, P2, P1, PN) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [dec[j].e, dec[j].f,
                      nfeltval(nf, Mod(x, g), dec[j]),
                      nfeltval(nf, Mod(P1, g), dec[j]),
                      nfeltval(nf, Mod(P2, g), dec[j]),
                      nfeltval(nf, Mod(PN, g), dec[j])]))));
  Vec(out)
}
"""
JOBS, META = [], {}


def gp_run():
    src = GPH + '\n' + '\n'.join(JOBS) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=3600)
    if out.stderr.strip():
        print('  gp stderr tail: %s' % out.stderr[-400:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    return res


def parse_pairs(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1]) for i in range(0, len(nums), 2))


def parse_rows(s, k):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return [nums[i:i + k] for i in range(0, len(nums), k)]


# ---------------- FRAME F1 ----------------
P1 = [-6, 0, 1]
F1 = Frame(3, P1, 1, 2, 1, 2, 2, 3,
           padd(padd(pmul(P1, P1), pmul([0, 3], P1)), [108]))
PHI2N = padd(padd(pmul(P1, P1), pmul([0, 3], P1)), [54])

FLOORS_F1 = {(0, 0, 0): 7, (0, 1, 0): 6, (0, 0, 1): 5, (0, 1, 1): 5,
             (1, 0, 0): 4, (1, 1, 0): 3, (1, 0, 1): 2, (1, 1, 1): 2}


def run_f1():
    print('== F1 (eta != 1 gauge frame) ==')
    for (j, a, b), want in FLOORS_F1.items():
        chk(F1.floor(j, a, b) == want,
            'F1 floor(%d,%d,%d) = %d want %d' %
            (j, a, b, F1.floor(j, a, b), want))
    JOBS.append('print("F1KC ", ef1(%s, 3))' % pstr(F1.PHI2))
    META['F1KC'] = ('pairs', [(2, 2)], 'FR-P1 corrected key ef')
    JOBS.append('print("F1KN ", ef1(%s, 3))' % pstr(PHI2N))
    META['F1KN'] = ('pairs', [(4, 1)], 'FR-P1 naive key ef')
    members = []
    anchor = padd(pmul(F1.PHI2, F1.PHI2), [0, 729])
    members.append(('F1-EQ', anchor))
    pins, _ = F1.read_pins(anchor, F1.PHI2)
    chk(pins[0] == 13 and pins[1] is None,
        'F1-EQ pins %s want (13, None)' % (pins,))
    for i in range(10):
        digs = {}
        for (j, a, b), fl in FLOORS_F1.items():
            if random.random() < 0.7:
                digs[(j, a, b)] = random.choice([1, 2, -1, -2, 4]) * \
                    3 ** (fl + random.choice([0, 0, 1, 2]))
        if not any(j == 0 for (j, a, b) in digs):
            digs[(0, 0, 0)] = 3 ** 7
        f = pmul(F1.PHI2, F1.PHI2)
        for (j, a, b), c in digs.items():
            mono = [0] * a + [c]
            for _ in range(b):
                mono = pmul(mono, P1)
            for _ in range(j):
                mono = pmul(mono, F1.PHI2)
            f = padd(f, mono)
        members.append(('F1-R%d' % i, f))
        if i < 3:
            pert = [random.randint(-2, 2) * 3 ** 40 for _ in range(8)]
            members.append(('F1-R%dp' % i, padd(list(f), pert)))
    for tag, f in members:
        err = F1.gate(f)
        chk(err is None, '%s gate: %s' % (tag, err))
        g = padd(list(f), psca(-1, pmul(F1.PHI2, F1.PHI2)))
        chk(F1.strictly_above(g, 12), '%s not strictly above 12' % tag)
        pins, digs = F1.read_pins(f, F1.PHI2)
        for (j, a, b), c in digs.items():
            chk(vp(c, 3) >= F1.floor(j, a, b),
                '%s digit (%d,%d,%d) v=%d < floor' %
                (tag, j, a, b, vp(c, 3)))
        for j, pj in enumerate(pins):
            chk(pj is None or pj >= (2 - j) * 6 + 1,
                '%s pin p%d = %s below node' % (tag, j, pj))
        JOBS.append('print("%s.nv ", nodev(%s, 3, %s, %s, %s))' %
                    (tag, pstr(f), pstr(F1.PHI2), pstr(P1), pstr(PHI2N)))
        META[tag + '.nv'] = ('node1', None, tag)
    JOBS.append('print("F1EQ.s1 ", sig1(%s, 3))' % pstr(anchor))
    META['F1EQ.s1'] = ('pairs', [(4, 2)], 'FR-P5 anchor route1')
    JOBS.append('print("F1EQ.s2 ", sig2(%s, 3))' % pstr(anchor))
    META['F1EQ.s2'] = ('pairs', [(4, 2)], 'FR-P5 anchor route2')
    fS = padd(padd(pmul(F1.PHI2, F1.PHI2), pmul([0, 27], F1.PHI2)),
              [3 ** 8])
    pins, _ = F1.read_pins(fS, F1.PHI2)
    chk(pins == [16, 7], 'F1 SPLTAIL pins %s want [16, 7]' % (pins,))
    JOBS.append('print("F1SP.s1 ", sig1(%s, 3))' % pstr(fS))
    META['F1SP.s1'] = ('pairs', [(2, 2), (2, 2)], 'FR-P5 spltail r1')
    JOBS.append('print("F1SP.s2 ", sig2(%s, 3))' % pstr(fS))
    META['F1SP.s2'] = ('pairs', [(2, 2), (2, 2)], 'FR-P5 spltail r2')
    # FR-P4 sigma leg: naive-key members
    for k, fn in enumerate([padd(pmul(PHI2N, PHI2N), [0, 729]),
                            padd(pmul(PHI2N, PHI2N), [3 ** 7, 729])]):
        JOBS.append('print("F1NV%d ", sig1(%s, 3))' % (k, pstr(fn)))
        META['F1NV%d' % k] = ('naive-sigma', [(4, 2)], 'FR-P4')
    # FR-P6 refine
    Kp = padd(list(F1.PHI2), psca(-9, P1))
    f6 = padd(padd(pmul(Kp, Kp), pmul([0, 3 ** 5], Kp)), [0, 3 ** 9])
    po, _ = F1.read_pins(f6, F1.PHI2)
    chk(po == [14, 7], 'F1 refine OLD pins %s want [14, 7]' % (po,))
    pn, _ = F1.read_pins(f6, Kp)
    chk(pn == [19, 11], 'F1 refine NEW pins %s want [19, 11]' % (pn,))
    A0, r0 = pdivmod(pdivmod(list(Kp), P1)[0], P1)
    vals = [F1.m * vp(c, 3) + a for a, c in
            enumerate(pdivmod(list(Kp), P1)[1]) if c]
    chk(A0 == [1] and min(vals) == 6,
        'refined key A0-min %s want E2 = 6' % (min(vals) if vals else None,))
    JOBS.append('print("F1RF.s1 ", sig1(%s, 3))' % pstr(f6))
    META['F1RF.s1'] = ('pairs', [(4, 2)], 'FR-P6 refined member r1')
    JOBS.append('print("F1RF.s2 ", sig2(%s, 3))' % pstr(f6))
    META['F1RF.s2'] = ('pairs', [(4, 2)], 'FR-P6 refined member r2')
    JOBS.append('print("F1RF.ef ", ef1(%s, 3))' % pstr(Kp))
    META['F1RF.ef'] = ('pairs', [(2, 2)], 'FR-P6 refined key ef')
    for nm, wrong in [('Kw1', padd(list(F1.PHI2), [0, -27])),
                      ('Kw2', padd(list(F1.PHI2), psca(-27, P1)))]:
        pw, _ = F1.read_pins(f6, wrong)
        if pw[0] == 14 or pw[1] == 7:
            TEETH['REFWRONG'] += 1
        else:
            chk(False, '%s unexpectedly killed the pin: %s' % (nm, pw))


# ---------------- FRAME F2 ----------------
P2F = [-2, 0, 0, 1]
F2 = Frame(2, P2F, 1, 3, 2, 1, 2, 7,
           padd(pmul(P2F, P2F), [0, -4]))
FLOORS_F2 = {(0, 0, 0): 5, (0, 1, 0): 5, (0, 2, 0): 5, (0, 0, 1): 4,
             (0, 1, 1): 4, (0, 2, 1): 3,
             (1, 0, 0): 3, (1, 1, 0): 3, (1, 2, 0): 2, (1, 0, 1): 2,
             (1, 1, 1): 1, (1, 2, 1): 1}


def run_f2():
    print('== F2 (e1 = 3, e2 = 2; e1e2 = 6) ==')
    for (j, a, b), want in FLOORS_F2.items():
        chk(F2.floor(j, a, b) == want,
            'F2 floor(%d,%d,%d) = %d want %d' %
            (j, a, b, F2.floor(j, a, b), want))
    anchor = padd(pmul(F2.PHI2, F2.PHI2), pmul([0, 0, 8], P2F))
    pins, _ = F2.read_pins(anchor, F2.PHI2)
    chk(pins[0] == 29 and pins[1] is None,
        'F2-EQ pins %s want (29, None)' % (pins,))
    members = [('F2-EQ', anchor)]
    for i in range(8):
        digs = {}
        for (j, a, b), fl in FLOORS_F2.items():
            if random.random() < 0.6:
                digs[(j, a, b)] = random.choice([1, -1, 3, 5]) * \
                    2 ** (fl + random.choice([0, 0, 1]))
        if not any(j == 0 for (j, a, b) in digs):
            digs[(0, 0, 0)] = 2 ** 5
        f = pmul(F2.PHI2, F2.PHI2)
        for (j, a, b), c in digs.items():
            mono = [0] * a + [c]
            for _ in range(b):
                mono = pmul(mono, P2F)
            for _ in range(j):
                mono = pmul(mono, F2.PHI2)
            f = padd(f, mono)
        members.append(('F2-R%d' % i, f))
    for tag, f in members:
        err = F2.gate(f)
        chk(err is None, '%s gate: %s' % (tag, err))
        g = padd(list(f), psca(-1, pmul(F2.PHI2, F2.PHI2)))
        chk(F2.strictly_above(g, 28), '%s not strictly above 28' % tag)
        pins, digs = F2.read_pins(f, F2.PHI2)
        for (j, a, b), c in digs.items():
            chk(vp(c, 2) >= F2.floor(j, a, b),
                '%s digit (%d,%d,%d) v=%d < floor' %
                (tag, j, a, b, vp(c, 2)))
        for j, pj in enumerate(pins):
            chk(pj is None or pj >= (2 - j) * 14 + 1,
                '%s pin p%d = %s below node' % (tag, j, pj))
        if tag in ('F2-EQ', 'F2-R0', 'F2-R3', 'F2-R6'):
            JOBS.append('print("%s.nv ", nodev(%s, 2, %s, %s, %s))' %
                        (tag, pstr(f), pstr(F2.PHI2), pstr(P2F),
                         pstr(F2.PHI2)))
            META[tag + '.nv'] = ('node2', None, tag)
    JOBS.append('print("F2EQ.s1 ", sig1(%s, 2))' % pstr(anchor))
    META['F2EQ.s1'] = ('pairs', [(12, 1)], 'FR-P7 anchor route1')
    JOBS.append('print("F2EQ.s2 ", sig2(%s, 2))' % pstr(anchor))
    META['F2EQ.s2'] = ('pairs', [(12, 1)], 'FR-P7 anchor route2')
    fS = padd(padd(pmul(F2.PHI2, F2.PHI2),
                   pmul(pmul([0, 0, 8], P2F), F2.PHI2)), [0, 32])
    pins, _ = F2.read_pins(fS, F2.PHI2)
    chk(pins == [32, 15], 'F2 SPLTAIL pins %s want [32, 15]' % (pins,))
    JOBS.append('print("F2SP.s1 ", sig1(%s, 2))' % pstr(fS))
    META['F2SP.s1'] = ('pairs', [(6, 1), (6, 1)], 'FR-P7 spltail r1')


def resolve():
    print('== PARI leg: %d jobs ==' % len(JOBS))
    res = gp_run()
    for tag, (kind, want, label) in META.items():
        if tag not in res:
            chk(False, 'missing gp answer %s (%s)' % (tag, label))
            continue
        val = res[tag]
        if kind == 'pairs':
            chk(parse_pairs(val) == sorted(want),
                '%s (%s): %s want %s' % (tag, label, parse_pairs(val),
                                         sorted(want)))
        elif kind == 'naive-sigma':
            got = parse_pairs(val)
            if got != sorted(want):
                TEETH['GAUGE-SIGMA'] += 1
                print('  [tooth] %s naive-member sigma %s != %s' %
                      (tag, got, sorted(want)))
            else:
                chk(False, '%s naive member sigma MATCHED the corrected '
                    'prediction %s -- gauge tooth failed' % (tag, got))
        elif kind == 'node1':
            for e, fdeg, vx, vP1, vP2C, vP2N in parse_rows(val, 6):
                chk(e % 2 == 0 and fdeg % 2 == 0,
                    '%s carrier (%d,%d) not divisible' % (tag, e, fdeg))
                chk(2 * vx == e, '%s v(x): 2*%d != %d' % (tag, vx, e))
                chk(2 * vP1 == 3 * e, '%s v(Phi;): %d' % (tag, vP1))
                chk(vP2C > 3 * e, '%s corrected key val %d <= 3e' %
                    (tag, vP2C))
                if vP2N == 3 * e:
                    TEETH['GAUGE-NODE'] += 1
                else:
                    chk(False, '%s naive key val %d != 3e = %d (exactness '
                        'fails)' % (tag, vP2N, 3 * e))
        elif kind == 'node2':
            for e, fdeg, vx, vP1, vP2, _ in parse_rows(val, 6):
                chk(e % 6 == 0 and fdeg % 1 == 0,
                    '%s carrier (%d,%d)' % (tag, e, fdeg))
                chk(3 * vx == e, '%s v(x): 3*%d != %d' % (tag, vx, e))
                chk(6 * vP1 == 7 * e, '%s v(Phi\'): %d' % (tag, vP1))
                chk(6 * vP2 > 14 * e, '%s node: 6*%d <= 14*%d' %
                    (tag, vP2, e))


def main():
    print('=== GENTOW1 passPE1 fresh route (sealed) ===')
    run_f1()
    run_f2()
    resolve()
    ok_teeth = TEETH['GAUGE-NODE'] >= 1 and TEETH['GAUGE-SIGMA'] >= 1 \
        and TEETH['REFWRONG'] >= 2
    print('teeth: %s' % TEETH)
    nv = len(VIOL)
    verdict = 'GREEN' if nv == 0 and ok_teeth else 'RED'
    print('=== VERDICT: %s -- %d checks, %d violations (%.1fs) ===' %
          (verdict, NCHK[0], nv, time.time() - T0))
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
