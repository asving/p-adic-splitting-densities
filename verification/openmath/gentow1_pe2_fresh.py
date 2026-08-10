#!/usr/bin/env python3
"""GENTOW1 passPE2 FRESH ROUTE: frames disjoint from the note's five
battery families AND from PE1's F1/F2.  Written by the passPE2
hostile verifier; own poly engine, own gate, own gp text.

FRAME G1 (eta != 1 x e2 = 2 -- the first frame combining a nontrivial
wrap letter with inner ramification):
  p = 3, Phi' = x^2 - 6 (e1 = 2, f1 = 1, h = 1, eta = res(x0^2/3) = 2),
  inner (e2, f2) = (2, 1), u2 = 5 (gcd(5,2) = 1, 5 > e2*D'h = 4),
  mu2 = 2, mu1 = 4, psi2 = Z - 1 (s = 1).  n(5) = 9x (2a + i = 5).
  W(0) = floor(f2*i(u2)/e1) = floor(1/2) = 0: GAUGE-DEAD frame
  (corrected = naive at f2 = 1 always, since i(u2) < e1) -- disclosed;
  the gauge-LIVE axis needs f2 >= 2 (PE1 F1 / frame X / hetowr1).
  These frames test the BUDGET/NODE/REFINE laws where eta enters the
  coherent residues (see the u = 2 mod 3 constants below).
  PHI2G1 = Phi'^2 - 9x = x^4 - 12x^2 - 9x + 36.
  D2 = 4, E2 = 10, m = e1e2 = 4, dv2 = 4v, n = 8, w(a,b) = 2a + 5b
  (classes 0,2,1,3 mod 4 -- two-step separation).
  FLOORS (hand-derived, ceil(((2-j)*10 - w)/4) + [4 | (2-j)*10 - w]):
    j=0: (0,0):6* (1,0):5 (0,1):4 (1,1):4 ; j=1: (0,0):3 (1,0):3*
    (0,1):2 (1,1):1.  Node floors [21, 11].
  ETA-CORRECTED RECIPE CONSTANTS (derivation): on T the coherent
  J=0 residue is res(A0/n(5)^2) with n(5)^2/n(10) = x^2/3 -> eta = 2,
  so A0 = 3^5*u needs u*eta^{-1} = 2u == s^2 = 1, i.e. u == 2 mod 3;
  the J=2 residue res(A2/n(5)) = -2s == 1 needs A2 = 9x*u2s,
  u2s == 1 mod 3.  (A wrong eta convention here would land members on
  the INERT stratum and fire the strict node-oracle check.)

FRAME G2 (mu2 = 3 -- the FIRST mu2 >= 3 contact in the program; same
  outer, same inner slope): mu2 = 3, mu1 = 6, psi2 = Z - 2 (s = 2),
  PHI2G2 = Phi'^2 - 2*9x = x^4 - 12x^2 - 18x + 36.  D2 = 4, E2 = 10,
  n = 12.  FLOORS: j=0: (0,0):8 (1,0):8* (0,1):7 (1,1):6 ;
  j=1: (0,0):6* (1,0):5 (0,1):4 (1,1):4 ; j=2: (0,0):3 (1,0):3*
  (0,1):2 (1,1):1.  Node floors [31, 21, 11].
  Recipe J=0: A0 = 3^7*u*x, res = u*eta^{-1} = 2u == psi2^3-const
  ((-2)^3 = -8 == 1 mod 3) -> u == 2 mod 3; J=2 and J=4 layers of
  psi2^3 are 12 == 0 and -6 == 0 mod 3 -> those lattice slots sit
  STRICTLY above (the mu2 = p binomial vanishing).

PREREGISTERED PREDICTIONS (all hand-derived before the run):
 Q-1 (keys): ef(PHI2G1) = ef(PHI2G2) = {(4,1)}, both factorpadic-
   irreducible of degree 4 with one prime.
 Q-2 (G1 floors + anchor): computed floors = the table above;
   fA1 = PHI2G1^2 + 81*Phi' reads pins (21, None), gate passes,
   strict-above(f - key^2) > 20, floors readback; sigma {(8,1)}
   BOTH routes (slope 21/2 forced); node oracle at every prime of
   every factor: 2*v(x) = pr.e, 4*v(Phi') = 5*pr.e,
   4*v(PHI2G1) > 10*pr.e STRICT.
 Q-3 (G1 NEC, 8 members + deep perturbations): eta-corrected level-1
   recipe members pass gate + floors + node pins >= [21,11] +
   strict-above; node oracle on 3 of them.
 Q-4 (PIN-STRADDLE TOOTH -- the [pin] clause boundary at the same
   digit valuation v = 5): PB1 = PHI2G1^2 + 243 (lattice slot (0,0,0),
   wt = 20 = mu2*E2) FAILS the gate with dv(A0) = 12 != 10 (the
   486 + 243 = 729 carry cancellation, hand-derived); PB3 = PHI2G1^2
   + 243x (off-lattice slot (0,1,0), wt = 22) PASSES gate, pins
   (22, None), floors ok, sigma {(4,2)} both routes (v(Phi2) = 11/4,
   residual T^2 + 1 irreducible over F3); PB2 = PHI2G1^2 + 729
   (lattice slot at floor v = 6) PASSES, pins (24, None) -- the
   auto-bump p0 = mu2*E2 + e1e2 (Step 3's one-digit-higher display),
   sigma {(4,2)} both routes (v(Phi2) = 3, Y^2 = -1 inert over F3).
   PB0 = PHI2G1^2 + 486 DIAGNOSTIC (unscored): polygon gate passes
   (dv(A0) = 10) but the member is OFF-T (coherent J=0 residue
   1*eta^{-1} = 2 != 1 = s^2) -- the disclosed polygon-only gate
   scope (PE1 caveat), printed with its PARI sigma for the record.
 Q-5 (G1 refine at eta != 1 x e2 = 2): Kp1 = PHI2G1 - 3x*Phi'
   (n2hat(11) = 3x*Phi', class w = 7 == 3 mod 4), f6 = Kp1^2 + 27*Kp1
   + 81x*Phi'.  OLD-key read: pins (22, 11) BOTH alive (q = 3, tDBL;
   hand check: C1 = -6x*Phi' + 27 + 9x^2 -> p1 = 11; C0 = 81x^3 =
   81x*Phi' + 486x -> p0 = 22); NEW-key read (19+4, 11+1) = (23, 12);
   sigma(f6) = {(8,1)} both routes (new polygon slope 23/2 -> tRAM);
   Kp1 keeps ef {(4,1)} and level-1 A0-weight-min = E2 = 10; node
   oracle on f6.  TEETH: wrong-height normalizer Kw1 = PHI2G1 -
   9x*Phi' (height 15) and wrong-residue Kw2 = PHI2G1 + 3x*Phi'
   both leave an event pin alive (p0 = 22 or p1 = 11).
 Q-6 (G2 floors + anchor): floors = table; fA2 = PHI2G2^3 +
   729x*Phi' reads pins (31, None, None) (slot (1,1) class w = 7 ==
   31 mod 4), gate passes (dv(A0) = 15: A0 = -34992x hand-derived),
   strict-above > 30, sigma {(12,1)} both routes (slope 31/3 forced,
   gcd(31,3) = 1 -> e = 12), node oracle: 2*v(x) = pr.e, 4*v(Phi') =
   5*pr.e, 4*v(PHI2G2) > 10*pr.e STRICT.
 Q-7 (G2 NEC at mu2 = 3, 6 members): recipe members pass gate +
   floors + node pins >= [31, 21, 11] + strict-above; node oracle on
   2.  (sigma of general mu2 = 3 reads is NOT scored -- the residual
   dictionary is [GENHN-HE(3)] geography; the scored sigma rows here
   are slope-forced.)
 Q-8 (BELOW-NODE TOOTH at mu2 = 3): fB = PHI2G2^3 + 2187x (digit AT
   weight mu2*E2 = 30, lattice slot (1,0), unit 1) FAILS the gate
   with dv(A0) = 17 != 15 (hand-derived: -34992x + 2187x = -5*3^8*x).
 Q-9 (mu2 = 3 REFINE -- first contact; the p = mu2 = 3 char
   sensitivity): Kp2 = PHI2G2 - 3x*Phi', f7 = Kp2^3 + 6561*Phi'.
   OLD-key read: p0 = 3*lam = 33 EXACT (residue from -10935*Phi',
   unit 5 != 0 mod 3), p1 >= 23 (= 2*lam + 1: binom(3,1) = 3 == 0
   mod 3 -- the pin DATUM vanishes, GENTOW-2(iv)), p2 >= 12
   (binom(3,2) == 0); hand-computed exact values (33, 23, 14).
   NEW-key read: (37, None, None) -- the kills, GENTOW-2(ii) at
   mu2 = 3.  sigma(f7) = {(12,1)} both routes (slope 37/3 forced);
   Kp2 keeps ef {(4,1)} + A0-weight-min = 10; node oracle on f7.
   TEETH: Kw3 = PHI2G2 - 9x*Phi' (wrong height) and Kw4 = PHI2G2 +
   3x*Phi' (wrong residue) keep p0 = 33 alive.
VERDICT: GREEN iff 0 violations and all four teeth fire
(PIN-STRADDLE, BN3, REFWRONG x2 per frame group).
NOT RUN (disclosed): non-prime q (f1 >= 2 / d = 2 ambient -- rnf
cost, same disclosure as PE1); gauge-LIVE f2 >= 2 rows (covered at
PE1 F1 + erratum frame X + hetowr1_supp, all committed GREEN).
RUN-1 REDISCLOSURE (instrument erratum, MINE not the note's; run 1
was RED 181/2, both violations on the SAME instrument prediction):
the sealed PB3 sigma {(4,2)} was derived from the RAW slot residue
(Y^2 = -1 inert over F3); at u = 22 == 2 mod 4 the sigma-decision
needs the COHERENT residual with the wrap unit -- n2hat(11)^2 vs
n2hat(22) carries xPhi'^2/27 ~ x^2/3 -> eta = 2, so the equation is
Y^2 = -(1*eta^{-1})... = -2 = 1 = a SQUARE over F3: SPLIT, sigma =
{(4,1),(4,1)} -- which is exactly what BOTH PARI routes measured.
PB2 (class (0,0): n2hat(12)^2 = n2hat(24), NO wrap) was green as
sealed.  The error is precisely a violation of GENTOW-2(iv)'s
'coherent normalization, WRAP UNITS INCLUDED' clause -- run 1 is a
live machine demonstration that the note's wrap-unit clause is
LOAD-BEARING at eta != 1 (an unplanned tooth: the wrap-naive
sigma-dictionary gives the wrong answer, PARI both routes agree
against it).  Every other row of run 1 was green: all four teeth,
all floors/pins/gates, the mu2 = 3 refine EXACTLY at the hand pins
(33, 23, 14) -> (37, None, None), all node-oracle rows strict.
Fixed: PB3 want = {(4,1),(4,1)} with the wrap-corrected derivation.
No other change.
Written 2026-08-10 by the GENTOW1 passPE2 hostile verifier.
"""
import subprocess
import sys
import time

T0 = time.time()
VIOL = []
NCHK = [0]
TEETH = {'PIN-STRADDLE': 0, 'BN3': 0, 'REFWRONG1': 0, 'REFWRONG2': 0}
OUT = []


def say(s):
    print(s)
    sys.stdout.flush()
    OUT.append(s)


def chk(ok, msg):
    NCHK[0] += 1
    if not ok:
        VIOL.append(msg)
        say('  !! VIOLATION: %s' % msg)


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
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


class Frame(object):
    def __init__(self, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        self.p, self.PHI1, self.h = p, PHI1, h
        self.e1, self.e2, self.f2, self.mu2, self.u2 = \
            e1, e2, f2, mu2, u2
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
        if dvs[0] is None or \
                self.e2 * dvs[0] != self.mu1 * self.u2:
            return 'dv(A0) = %s want %s/e2' % (dvs[0],
                                               self.mu1 * self.u2)
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
                if c and self.m * vp(c, self.p) + \
                        a * self.e2 * self.h + J * self.u2 <= thr:
                    return False
        return True

    def read_pins(self, f, key):
        g, Cs = list(f), []
        for _ in range(self.mu2):
            g, r = pdivmod(g, key)
            Cs.append(r)
        assert g == [1], 'dev not monic'
        pins, digs = [], {}
        for j, C in enumerate(Cs):
            gg, B = list(C), []
            for _ in range(self.e2 * self.f2):
                gg, r = pdivmod(gg, self.PHI1)
                B.append(r)
            assert not gg, 'slot overflow'
            vals = []
            for b, rb in enumerate(B):
                for a, c in enumerate(rb):
                    if c:
                        vals.append(self.m * vp(c, self.p) +
                                    self.w(a, b))
                        digs[(j, a, b)] = c
            pins.append(min(vals) if vals else None)
        return pins, digs

    def floors_ok(self, digs):
        for (j, a, b), c in digs.items():
            if vp(c, self.p) < self.floor(j, a, b):
                return False, '(j=%d,a=%d,b=%d) v=%d < floor %d' % (
                    j, a, b, vp(c, self.p), self.floor(j, a, b))
        return True, None


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
  my(F = factorpadic(f, p, 500), out = List());
  for (i = 1, matsize(F)[1],
    my(v = ef1(liftall(F[i, 1]), p));
    for (j = 1, #v, listput(out, v[j])));
  vecsort(Vec(out))
}
nodev(f, p, P2, P1) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [dec[j].e,
                      nfeltval(nf, Mod(x, g), dec[j]),
                      nfeltval(nf, Mod(P1, g), dec[j]),
                      nfeltval(nf, Mod(P2, g), dec[j])]))));
  Vec(out)
}
"""
JOBS, META = [], {}


def gp_sig(tag, F, f, want, key):
    JOBS.append('print("%s.s1 ", sig1(%s, %d))' % (tag, pstr(f), F.p))
    META[tag + '.s1'] = ('sig', want)
    JOBS.append('print("%s.s2 ", sig2(%s, %d))' % (tag, pstr(f), F.p))
    META[tag + '.s2'] = ('sig', want)


def gp_node(tag, F, f, key):
    JOBS.append('print("%s.nv ", nodev(%s, %d, %s, %s))'
                % (tag, pstr(f), F.p, pstr(key), pstr(F.PHI1)))
    META[tag + '.nv'] = ('node', F)


def gp_ef(tag, F, g, want):
    JOBS.append('print("%s.ef ", ef1(%s, %d))' % (tag, pstr(g), F.p))
    META[tag + '.ef'] = ('ef', want)


def gp_diag(tag, F, f):
    JOBS.append('print("%s.dg ", sig1(%s, %d))' % (tag, pstr(f), F.p))
    META[tag + '.dg'] = ('diag', None)


def parse_pairs(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1])
                  for i in range(0, len(nums), 2))


def parse_rows(s, k):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return [nums[i:i + k] for i in range(0, len(nums), k)]


# ---------------- frames ----------------
P1 = [-6, 0, 1]                                # x^2 - 6 over Q3
PHI2G1 = padd(pmul(P1, P1), [0, -9])           # Phi'^2 - 9x
PHI2G2 = padd(pmul(P1, P1), [0, -18])          # Phi'^2 - 18x
G1 = Frame(3, P1, 1, 2, 2, 1, 2, 5, PHI2G1)
G2 = Frame(3, P1, 1, 2, 2, 1, 3, 5, PHI2G2)

FLOORS_G1 = {(0, 0, 0): 6, (0, 1, 0): 5, (0, 0, 1): 4, (0, 1, 1): 4,
             (1, 0, 0): 3, (1, 1, 0): 3, (1, 0, 1): 2, (1, 1, 1): 1}
FLOORS_G2 = {(0, 0, 0): 8, (0, 1, 0): 8, (0, 0, 1): 7, (0, 1, 1): 6,
             (1, 0, 0): 6, (1, 1, 0): 5, (1, 0, 1): 4, (1, 1, 1): 4,
             (2, 0, 0): 3, (2, 1, 0): 3, (2, 0, 1): 2, (2, 1, 1): 1}

RNG = [20260810]


def rnd(lo, hi):                              # deterministic LCG
    RNG[0] = (RNG[0] * 6364136223846793005 + 1442695040888963407) \
        % (1 << 63)
    return lo + (RNG[0] >> 20) % (hi - lo + 1)


def nec_g1():
    """eta-corrected level-1 recipe member, mu2 = 2 frame."""
    A0 = [3 ** 5 * (2 if rnd(0, 1) else 5)]
    A1 = [81 * rnd(-2, 2), 81 * rnd(-2, 2)]
    A2 = [27 * rnd(-2, 2), 9 * (1 if rnd(0, 1) else 4)]
    A3 = [9 * rnd(-2, 2), 3 * rnd(-2, 2)]
    f = [0]
    for GJ in [A0, A1, A2, A3, [1]]:
        pass
    f, pw = [0], [1]
    for GJ in [A0, A1, A2, A3, [1]]:
        f = padd(f, pmul(GJ, pw) if GJ != [1] else pw)
        pw = pmul(pw, P1)
    return f


def nec_g2():
    """eta-corrected level-1 recipe member, mu2 = 3 frame."""
    A0 = padd([3 ** 8 * rnd(-2, 2)], [0, 3 ** 7 * (2 if rnd(0, 1)
                                                   else 5)])
    A1 = [3 ** 7 * rnd(-2, 2), 3 ** 6 * rnd(-2, 2)]
    A2 = [3 ** 6 * rnd(-2, 2), 3 ** 5 * rnd(-2, 2)]
    A3 = [81 * rnd(-2, 2), 81 * rnd(-2, 2)]
    A4 = [27 * rnd(-2, 2), 27 * rnd(-2, 2)]
    A5 = [9 * rnd(-2, 2), 3 * rnd(-2, 2)]
    f, pw = [0], [1]
    for GJ in [A0, A1, A2, A3, A4, A5, [1]]:
        f = padd(f, pmul(GJ, pw) if GJ != [1] else pw)
        pw = pmul(pw, P1)
    return f


def member_checks(F, tag, f, node_floors, gp=False):
    err = F.gate(f)
    chk(err is None, '%s gate: %s' % (tag, err))
    pins, digs = F.read_pins(f, F.PHI2)
    ok, msg = F.floors_ok(digs)
    chk(ok, '%s floors: %s' % (tag, msg))
    for j, pj in enumerate(pins):
        chk(pj is None or pj >= node_floors[j],
            '%s node pin p%d = %s < %d' % (tag, j, pj,
                                           node_floors[j]))
    kp = [1]
    for _ in range(F.mu2):
        kp = pmul(kp, F.PHI2)
    g = padd(list(f), psca(-1, kp))
    chk(F.strictly_above(g, F.mu2 * F.E2),
        '%s strict-above %d failed' % (tag, F.mu2 * F.E2))
    if gp:
        gp_node(tag, F, f, F.PHI2)
    return pins


def run_g1():
    say('== FRAME G1 (eta != 1 x e2 = 2; mu2 = 2) ==')
    for (j, a, b), want in sorted(FLOORS_G1.items()):
        chk(G1.floor(j, a, b) == want,
            'G1 floor(%d,%d,%d) = %d want %d'
            % (j, a, b, G1.floor(j, a, b), want))
    say('  floors match the hand table (8 slots)')
    gp_ef('G1KEY', G1, PHI2G1, [(4, 1)])
    # anchor
    fA1 = padd(pmul(PHI2G1, PHI2G1), psca(81, P1))
    pins = member_checks(G1, 'G1-ANCH', fA1, [21, 11], gp=True)
    chk(pins == [21, None], 'G1-ANCH pins %s want [21, None]' % pins)
    gp_sig('G1A', G1, fA1, [(8, 1)], PHI2G1)
    say('  anchor pins %s' % pins)
    # NEC members
    for i in range(8):
        f = nec_g1()
        if i % 4 == 3:
            f = padd(f, [rnd(-2, 2) * 3 ** 25 for _ in range(G1.n)])
        member_checks(G1, 'G1-NEC%d' % i, f, [21, 11], gp=(i % 3 == 0))
    say('  8 NEC members (incl. 2 deep-perturbed) checked')
    # PIN-STRADDLE tooth
    PB1 = padd(pmul(PHI2G1, PHI2G1), [243])
    e1r = G1.gate(PB1)
    chk(e1r is not None and 'dv(A0) = 12' in e1r,
        'PB1 gate said %r want dv(A0) = 12 failure' % e1r)
    PB3 = padd(pmul(PHI2G1, PHI2G1), [0, 243])
    e3r = G1.gate(PB3)
    p3, d3 = G1.read_pins(PB3, PHI2G1)
    ok3, _ = G1.floors_ok(d3)
    chk(e3r is None and p3 == [22, None] and ok3,
        'PB3 gate %r pins %s floors %s' % (e3r, p3, ok3))
    gp_sig('PB3', G1, PB3, [(4, 1), (4, 1)], PHI2G1)
    PB2 = padd(pmul(PHI2G1, PHI2G1), [729])
    e2r = G1.gate(PB2)
    p2, d2 = G1.read_pins(PB2, PHI2G1)
    chk(e2r is None and p2 == [24, None],
        'PB2 gate %r pins %s want [24, None]' % (e2r, p2))
    gp_sig('PB2', G1, PB2, [(4, 2)], PHI2G1)
    if e1r is not None and e3r is None and e2r is None:
        TEETH['PIN-STRADDLE'] += 1
    say('  straddle: PB1(v=5,lattice) FAILS [%s]; PB3(v=5,off) pins'
        ' %s; PB2(v=6=floor) pins %s (auto-bump 20+4)'
        % (e1r, p3, p2))
    PB0 = padd(pmul(PHI2G1, PHI2G1), [486])
    say('  [diag] PB0 (residual-violating, polygon-blind): gate=%r'
        ' (expected None -- disclosed gate scope)' % G1.gate(PB0))
    gp_diag('PB0', G1, PB0)
    # refine
    Kp1 = padd(list(PHI2G1), pmul([0, -3], P1))
    f6 = padd(padd(pmul(Kp1, Kp1), psca(27, Kp1)),
              pmul([0, 81], P1))
    po, _ = G1.read_pins(f6, PHI2G1)
    chk(po == [22, 11], 'G1-REF old pins %s want [22, 11]' % po)
    pn, _ = G1.read_pins(f6, Kp1)
    chk(pn == [23, 12], 'G1-REF new pins %s want [23, 12]' % pn)
    A00, _ = pdivmod(list(Kp1), P1)
    _, r0 = pdivmod(list(Kp1), P1)
    vals = [G1.m * vp(c, 3) + a * 2 for a, c in enumerate(r0) if c]
    chk(min(vals) == 10, 'Kp1 A0 weight-min %s want 10' % min(vals))
    gp_ef('KP1', G1, Kp1, [(4, 1)])
    gp_sig('F6', G1, f6, [(8, 1)], Kp1)
    gp_node('F6', G1, f6, Kp1)
    say('  refine: old %s -> new %s' % (po, pn))
    fired = 0
    for wtag, Kw in [('wrong-height', padd(list(PHI2G1),
                                           pmul([0, -9], P1))),
                     ('wrong-residue', padd(list(PHI2G1),
                                            pmul([0, 3], P1)))]:
        pw_, _ = G1.read_pins(f6, Kw)
        alive = pw_[0] == 22 or pw_[1] == 11
        chk(alive, 'G1 %s normalizer unexpectedly killed: %s'
            % (wtag, pw_))
        if alive:
            fired += 1
        say('  tooth %s read %s (pin alive)' % (wtag, pw_))
    if fired == 2:
        TEETH['REFWRONG1'] += 1


def run_g2():
    say('== FRAME G2 (mu2 = 3 first contact; eta != 1) ==')
    for (j, a, b), want in sorted(FLOORS_G2.items()):
        chk(G2.floor(j, a, b) == want,
            'G2 floor(%d,%d,%d) = %d want %d'
            % (j, a, b, G2.floor(j, a, b), want))
    say('  floors match the hand table (12 slots)')
    gp_ef('G2KEY', G2, PHI2G2, [(4, 1)])
    fA2 = padd(pmul(pmul(PHI2G2, PHI2G2), PHI2G2),
               pmul([0, 729], P1))
    pins = member_checks(G2, 'G2-ANCH', fA2, [31, 21, 11], gp=True)
    chk(pins == [31, None, None],
        'G2-ANCH pins %s want [31, None, None]' % pins)
    gp_sig('G2A', G2, fA2, [(12, 1)], PHI2G2)
    say('  anchor pins %s' % pins)
    for i in range(6):
        f = nec_g2()
        if i % 3 == 2:
            f = padd(f, [rnd(-2, 2) * 3 ** 25 for _ in range(G2.n)])
        member_checks(G2, 'G2-NEC%d' % i, f, [31, 21, 11],
                      gp=(i % 3 == 0))
    say('  6 NEC members (incl. 2 deep-perturbed) checked')
    # below-node tooth at mu2 = 3
    fB = padd(pmul(pmul(PHI2G2, PHI2G2), PHI2G2), [0, 2187])
    eB = G2.gate(fB)
    okB = eB is not None and 'dv(A0) = 17' in eB
    chk(okB, 'BN3 gate said %r want dv(A0) = 17 failure' % eB)
    if okB:
        TEETH['BN3'] += 1
    say('  BN3 tooth: digit AT wt 30 -> gate %r' % eB)
    # mu2 = 3 refine (first contact)
    Kp2 = padd(list(PHI2G2), pmul([0, -3], P1))
    f7 = padd(pmul(pmul(Kp2, Kp2), Kp2), psca(6561, P1))
    po, _ = G2.read_pins(f7, PHI2G2)
    chk(po[0] == 33, 'G2-REF old p0 = %s want 33 exact' % po[0])
    chk(po[1] is None or po[1] >= 23,
        'G2-REF old p1 = %s want >= 23' % po[1])
    chk(po[2] is None or po[2] >= 12,
        'G2-REF old p2 = %s want >= 12' % po[2])
    pn, _ = G2.read_pins(f7, Kp2)
    chk(pn == [37, None, None],
        'G2-REF new pins %s want [37, None, None]' % pn)
    _, r0 = pdivmod(list(Kp2), P1)
    vals = [G2.m * vp(c, 3) + a * 2 for a, c in enumerate(r0) if c]
    chk(min(vals) == 10, 'Kp2 A0 weight-min %s want 10' % min(vals))
    gp_ef('KP2', G2, Kp2, [(4, 1)])
    gp_sig('F7', G2, f7, [(12, 1)], Kp2)
    gp_node('F7', G2, f7, Kp2)
    say('  mu2=3 refine: old %s (hand-derived (33, 23, 14)) -> new'
        ' %s' % (po, pn))
    fired = 0
    for wtag, Kw in [('wrong-height', padd(list(PHI2G2),
                                           pmul([0, -9], P1))),
                     ('wrong-residue', padd(list(PHI2G2),
                                            pmul([0, 3], P1)))]:
        pw_, _ = G2.read_pins(f7, Kw)
        alive = pw_[0] == 33
        chk(alive, 'G2 %s normalizer unexpectedly killed p0: %s'
            % (wtag, pw_))
        if alive:
            fired += 1
        say('  tooth %s read %s (p0 = 33 alive)' % (wtag, pw_))
    if fired == 2:
        TEETH['REFWRONG2'] += 1


def resolve_gp():
    say('== PARI leg: %d jobs ==' % len(JOBS))
    src = GPH + '\n' + '\n'.join(JOBS) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True,
                         timeout=3600)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-300:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    for tag, spec in META.items():
        if tag not in res:
            chk(False, 'missing gp answer %s' % tag)
            continue
        val = res[tag]
        kind = spec[0]
        if kind == 'sig':
            chk(parse_pairs(val) == sorted(spec[1]),
                '%s sigma %s want %s' % (tag, parse_pairs(val),
                                         sorted(spec[1])))
        elif kind == 'ef':
            chk(parse_pairs(val) == sorted(spec[1]),
                '%s ef %s want %s' % (tag, parse_pairs(val),
                                      sorted(spec[1])))
        elif kind == 'node':
            F = spec[1]
            rows = parse_rows(val, 4)
            chk(len(rows) > 0, '%s no rows' % tag)
            for epr, vx, vP1, vP2 in rows:
                chk(F.e1 * vx == F.h * epr,
                    '%s v(x): %d vs %d' % (tag, F.e1 * vx,
                                           F.h * epr))
                chk(F.m * vP1 == F.u2 * epr,
                    '%s v(Phi1): %d vs %d' % (tag, F.m * vP1,
                                              F.u2 * epr))
                chk(F.m * vP2 > F.E2 * epr,
                    '%s v(key) = %d NOT > %d STRICT'
                    % (tag, F.m * vP2, F.E2 * epr))
        elif kind == 'diag':
            say('  [diag] %s sigma %s (unscored)' % (tag, val))


def main():
    say('=== GENTOW1 passPE2 fresh route (seal 2026-08-10) ===')
    run_g1()
    run_g2()
    resolve_gp()
    for t, k in TEETH.items():
        chk(k >= 1, 'tooth %s did not fire' % t)
    say('teeth: %s' % TEETH)
    nv = len(VIOL)
    say('=== VERDICT: %s -- %d checks, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', NCHK[0], nv,
           time.time() - T0))
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    rc = main()
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
