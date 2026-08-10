#!/usr/bin/env python3
"""GENTOW1 passPE3 FRESH ROUTE (hostile verifier's own instrument;
imports nothing from the program's readers; sealed before the full run).

TWO FRAMES, both disjoint from the sealed battery (FAM-A5/A7/B/C/D),
PE1's F1/F2, PE2's G1/G2, and hetowr1_supp's X/Z/W:

H1 = THE FIRST NON-PRIME-q FRAME ANYWHERE IN THE PROGRAM'S RECORD
  (q = Q^{f1} = 4; f1 = 2 outer key -- breaches GENTOW-BOX-2's
  "f1 = 1 outer keys only" AND "q in {2,3}" simultaneously; the
  PE1+PE2 "non-prime q NOT RUN (rnf cost)" disclosure discharged
  WITHOUT rnf: unramified outer needs plain nfinit only).
  Genre (Q=2; e1=1, f1=2, mu1=2; h=1): Phi' = x^2+2x+4 (psi = Z^2+Z+1,
  x-polygon slope 1, roots x0 = 2*zeta3); K = F4. Inner: (e2,f2)=(1,1),
  u2 = 3 > e2 D'h = 2, psi2 = Z - omega (omega in F4 \\ F2: a genuinely
  non-prime-q letter), mu2 = 2, n = 4, D2 = 2, E2 = 3, m = e1e2 = 1
  (dv2 = v; w(a,0) = a). Composed key Phi2 = Phi' - lift(omega;3)
  = x^2 - 2x + 4 (lift(omega;3) = 4x on the two-monomial f1 = 2 digit
  basis pi^3 |-> 1, pi^2 x |-> zeta). Gauge-dead (e1 = 1: W == 0),
  disclosed. HAND FLOOR TABLE (m = 1: every slot pinned, f1f2 = 2 pins
  per height): j=0: (0,0):7 (1,0):6 ; j=1: (0,0):4 (1,0):3.
  Node floors [7, 4]; mutant base D2 e2 h = 2 < E2 = 3.

H2 = THE FIRST GAUGE-LIVE x mu2 = 3 FRAME (the two hard axes together:
  eta != 1 with f2 = 2 [W(0) = 1: corrected key != naive key] AND
  mu2 = 3 = p [both middle binomials dead]; PE2's G2 was mu2 = 3 but
  gauge-dead f2 = 1; PE1's F1 was gauge-live but mu2 = 2).
  Genre (3; e1=2, f1=1, mu1=6; h=1): Phi' = x^2-6, eta = 2; inner
  (e2,f2) = (1,2), u2 = 3, psi2 = Z^2+Z+2, K2 = F9, mu2 = 3, n = 12,
  D2 = 4, E2 = 6, m = 2, w(a,b) = a + 3b. Corrected key (W = (1,0)):
  Phi2 = Phi'^2 + 3x Phi' + 108. HAND FLOOR TABLE:
  j=0: (0,0):10* (1,0):9 (0,1):8 (1,1):8* ; j=1: 7* 6 5 5* ;
  j=2: 4* 3 2 2*. Node floors [19, 13, 7].

PREREGISTERED PREDICTIONS (scored; any miss = RED):
 P1: sigma(Phi2_H1) = {(1,2)} both routes; sigma(Phi2plus_H1 =
     Phi2 - lift(omega;4) = x^2-10x+4) = {(1,2)} both routes.
 P2: 8 H1 box members (digits >= hand floors, C0 != 0, incl. 2 deep
     v = 40 perturbations): level-1 gate PASS (dv(A0) = 6 exact, pins
     >= side), hand-floor readback OK; node oracle per prime:
     val(x) = pr.e, val(Phi') = 3 pr.e, val(Phi2) > 3 pr.e STRICT.
 P3: H1 NODE-EQ anchor fA = Phi2^2 + 2^7: p0 = 7 = mu2 E2 + 1 EXACT,
     sigma = {(2,2)} both routes (slope 7/2 tRAM).
 P4: H1 refine (the q = 4 letter row; lam = 4, s = omega, q even):
     fR = Phi2^2 + 128x + 256: OLD pins (8, None) -- p0 = 2 lam = 8
     EXACT, C1 absent (2s = 0: the j = 1 pin gone, GENTOW-2(iv) q=2);
     NEW pins at Phi2plus EXACTLY (9, 5) (hand: C0+ = 768x, C1+ =
     16x + 64) -- both strictly above the lam-node (8, 4);
     sigma(fR) = {(2,2)} both routes (slope 9/2).
 P5: H1 REFWRONG x2: wrong-height key Phi2 - 16x and wrong-flavor key
     Phi2 - 16: fR's event pin p0 = 8 stays ALIVE (exact) at both.
 P6: H1 mutant-floor tooth: fM = Phi2^2 + 2^5 (clears mutant floor 5,
     violates true floor 7): gate FAILS with dv(A0) = 5 EXACT.
 P7: sigma(Phi2_H2) = {(2,2)} both routes; sigma(Phi2plus_H2 =
     Phi2 - lift(eta2;7) = Phi2 - 9 Phi') = {(2,2)} both routes.
 P8: 6 H2 box members (digits >= hand floors, C0 != 0, incl. deep
     pert): gate PASS (dv(A0) = 18 exact), floors readback OK; node
     oracle: 2 val(x) = pr.e, 2 val(Phi') = 3 pr.e,
     2 val(Phi2) > 6 pr.e STRICT.
 P9: H2 NODE-EQ anchor fA = Phi2^3 + 3^9 x: p0 = 19 = mu2 E2 + 1
     EXACT, sigma = {(6,2)} both routes (slope 19/3).
 P10: H2 below-floor tooth at the OFF-LATTICE slot (j=0,(1,0)) (the
     necessity direction at a non-(0,0,0) slot, new vs the sealed
     battery's T-MUTFLOOR): fB = Phi2^3 + 3^8 x (v = 8 < floor 9):
     gate FAILS with dv(A0) = 17 EXACT.
 P11: H2 COMBINED-AXES REFINE (gauge-live x mu2 = 3 = p; lam = 7,
     s = eta2): fE := (Phi2plus)^3 + 3^13: OLD-key pins EXACTLY
     (21, 15, 9): p0 = 3 lam EXACT (event carried by p0 alone -- both
     middle binomials binom(3,1) = binom(3,2) = 3 == 0 mod 3), p1 =
     15 = 2 lam + 1 (layer 2's bound TIGHT, the PE2-G2 2lam+1 pattern
     at a gauge-live frame), p2 = 9 = lam + 2; NEW-key pins
     (26, None, None); sigma(fE) = {(6,2)} both routes (slope 26/3);
     REFWRONG x2 (wrong-height Phi2 - 27 Phi', wrong-flavor
     Phi2 - 27x): p0 = 21 stays ALIVE at both.
 P12: H2 WINDOW at MAXIMAL RAGGED OFFSET (w = 4 class), N = 12, cap
     m N = 24: (a) 6 lifts fA + 3^12 r(x): below-cap reads (gate dv's
     and composed pins < 24) IDENTICAL; (b) MAXRAG: the LAST in-string
     digit of class (1,1) (v = 11 = N-1, height 26 > cap) added to fA
     changes NO below-cap read; (c) UNDERCUT tooth: fU = Phi2^3 + 3^13
     (p0 = 26 above cap) vs fU + 3^12: the above-cap p0 read CHANGES
     (26 -> 24).

Both sigma routes everywhere sigma is scored: (1) factor/Q + nfinit +
idealprimedec; (2) factorpadic + liftall + nfinit + idealprimedec.
Floors are HAND constants (typed above), not computed from the note's
formula at runtime. Wrap-hygiene: every scored row is a HEIGHT or a
PARI verdict; no hand-derived residue VALUE is scored (the PE2 run-1
lesson); the coherent -s^3 residue check for P11 lives in the report
prose, certified by p0 = 21 EXACT (cancellation would raise it).
SMOKE RECORD (disclosed): py_compile only before seal; no full or
partial run pre-seal. VERDICT: GREEN iff 0 violations.
"""
import random, subprocess

random.seed(20260810)
CHK = {}
VIOL = []


def say(s):
    print(s, flush=True)


def chk(tag, ok, msg):
    CHK[tag] = CHK.get(tag, 0) + 1
    if not ok:
        VIOL.append('%s: %s' % (tag, msg))
        say('  ** VIOLATION %s: %s' % (tag, msg))


def pstrip(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def padd(a, b):
    n = max(len(a), len(b))
    out = [0] * n
    for i, c in enumerate(a):
        out[i] += c
    for i, c in enumerate(b):
        out[i] += c
    return pstrip(out)


def psca(k, a):
    return pstrip([k * c for c in a])


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        for j, d in enumerate(b):
            out[i + j] += c * d
    return pstrip(out)


def ppow(a, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, a)
    return out


def pdivmod(a, b):
    a = list(a)
    q = []
    while len(a) >= len(b) and a:
        c = a[-1]
        d = len(a) - len(b)
        q = padd(q, [0] * d + [c])
        a = padd(a, psca(-c, [0] * d + b))
    return q, a


def dev(f, key, mu):
    """f = sum_{j<mu} C_j key^j + (top) key^mu; returns ([C_j], top)."""
    out, cur = [], list(f)
    for _ in range(mu):
        cur, r = pdivmod(cur, key)
        out.append(r)
    return out, cur


def vp(n, p):
    if n == 0:
        return 10 ** 9
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


class Fr:
    def __init__(self, name, p, e1, h, e2, f2, mu2, u2, PHI1, PHI2,
                 floors):
        self.__dict__.update(locals())
        self.m = e1 * e2
        self.Dp = len(PHI1) - 1
        self.D2 = self.Dp * e2 * f2
        self.mu1 = e2 * f2 * mu2
        self.E2 = e2 * f2 * u2
        self.n = mu2 * self.D2

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def slots(self, C):
        B, g = dev(list(C), self.PHI1, self.e2 * self.f2)
        assert g == [] or g == [0], 'slot overflow'
        out = {}
        for b, rb in enumerate(B):
            for a, c in enumerate(rb):
                if c:
                    out[(a, b)] = c
        return out

    def pin(self, C):
        sl = self.slots(C)
        if not sl:
            return None
        return min(self.m * vp(c, self.p) + self.w(a, b)
                   for (a, b), c in sl.items())

    def pins(self, f, key):
        Cs, top = dev(list(f), key, self.mu2)
        assert top == [1], 'not monic in key-dev'
        return [self.pin(C) for C in Cs]

    def gate(self, f):
        """level-1 gate (polygon clause): dv(A0) exact, pins >= side.
        Returns (None, dv0) if pass else (msg, dv0)."""
        A, g = dev(list(f), self.PHI1, self.mu1)
        if g != [1]:
            return 'not monic in Phi1-dev', None
        dvs = []
        for c in A:
            vals = [self.e1 * vp(cc, self.p) + i * self.h
                    for i, cc in enumerate(c) if cc]
            dvs.append(min(vals) if vals else None)
        want0 = self.mu1 * self.u2 // self.e2
        if dvs[0] is None or dvs[0] != want0:
            return 'dv(A0) = %s want %d' % (dvs[0], want0), dvs[0]
        for J in range(1, self.mu1):
            if dvs[J] is not None and \
                    self.e2 * dvs[J] < (self.mu1 - J) * self.u2:
                return 'pin J=%d below side' % J, dvs[0]
        return None, dvs[0]

    def from_digits(self, digs):
        f = [0]
        for (j, a, b), c in digs.items():
            f = padd(f, pmul([0] * a + [c],
                             pmul(ppow(self.PHI1, b),
                                  ppow(self.PHI2, j))))
        return padd(f, ppow(self.PHI2, self.mu2))

    def floors_ok(self, digs):
        for (j, a, b), c in digs.items():
            if vp(c, self.p) < self.floors[(j, a, b)]:
                return False, '(%d,%d,%d) v=%d < %d' % (
                    j, a, b, vp(c, self.p), self.floors[(j, a, b)])
        return True, None


GP_HDR = r"""
default(parisizemax, 2000000000);
sig1(f, p) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
        listput(out, [1, 1]),
        my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
ef1(g, p) = {
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  vecsort(vector(#dec, j, [dec[j].e, dec[j].f]))
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
    if (poldegree(g) == 1, listput(out, [-1, -1, -1, -1]),
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [nfeltval(nf, Mod(P2, g), dec[j]), dec[j].e,
                      nfeltval(nf, Mod(x, g), dec[j]),
                      nfeltval(nf, Mod(P1, g), dec[j])]))));
  Vec(out)
}
"""
JOBS, META = [], {}


def gp_sig(tag, F, f, want):
    for r, fn in (('r1', 'sig1'), ('r2', 'sig2')):
        JOBS.append('print("%s.%s ", %s(%s, %d))'
                    % (tag, r, fn, poly_str(f), F.p))
        META['%s.%s' % (tag, r)] = ('sig', F, want)


def gp_node(tag, F, f):
    JOBS.append('print("%s.nv ", nodev(%s, %d, %s, %s))'
                % (tag, poly_str(f), F.p, poly_str(F.PHI2),
                   poly_str(F.PHI1)))
    META[tag + '.nv'] = ('node', F, None)


def sig_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1])
                  for i in range(0, len(nums), 2))


def vec_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return [nums[i:i + 4] for i in range(0, len(nums), 4)]


def run_gp():
    src = GP_HDR + '\n' + '\n'.join(JOBS) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=3600)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-200:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    for tag, (kind, F, want) in META.items():
        if tag not in res:
            chk('GP', False, '%s missing from gp output' % tag)
            continue
        if kind == 'sig':
            got = sig_parse(res[tag])
            chk('GP-SIG', got == sorted(want),
                '%s got %s want %s' % (tag, got, sorted(want)))
        else:
            for (v2, pre, vx, v1) in vec_parse(res[tag]):
                if v2 < 0:
                    chk('GP-NODE', False, '%s: linear factor' % tag)
                    continue
                ok = (F.e1 * vx == F.h * pre
                      and F.m * v1 == F.u2 * pre
                      and F.m * v2 > F.E2 * pre)
                chk('GP-NODE', ok, '%s: (v2,e,vx,v1)=(%d,%d,%d,%d)'
                    % (tag, v2, pre, vx, v1))


# ================= FRAME H1 (q = 4, non-prime) ======================
PH1_1 = [4, 2, 1]                        # Phi' = x^2+2x+4
H1 = Fr('H1', 2, 1, 1, 1, 1, 2, 3, PH1_1, [4, -2, 1],
        {(0, 0, 0): 7, (0, 1, 0): 6, (1, 0, 0): 4, (1, 1, 0): 3})


def frame_h1():
    say('== FRAME H1: q = 4 (f1 = 2 outer), first non-prime-q ==')
    F = H1
    gp_sig('H1-KEY', F, F.PHI2, [(1, 2)])                     # P1
    P2p = padd(F.PHI2, [0, -8])                               # x^2-10x+4
    gp_sig('H1-KEYP', F, P2p, [(1, 2)])                       # P1
    # P2: box members
    mems = []
    for i in range(6):
        digs = {}
        for (j, a, b), fl in F.floors.items():
            if random.random() < 0.75 or (j, a, b) == (0, 0, 0):
                u = random.choice([1, 3, 5, 7])
                digs[(j, a, b)] = u * 2 ** (fl + random.choice(
                    [0, 0, 1, 2]))
        if (0, 0, 0) not in digs and (0, 1, 0) not in digs:
            digs[(0, 0, 0)] = 2 ** 7
        mems.append((digs, F.from_digits(digs)))
    for k in range(2):                   # deep perturbations
        digs, f = mems[k]
        mems.append((digs, padd(list(f),
                                [random.randint(-3, 3) * 2 ** 40
                                 for _ in range(F.n)])))
    for i, (digs, f) in enumerate(mems):
        msg, dv0 = F.gate(f)
        chk('H1-GATE', msg is None, 'mem%d: %s' % (i, msg))
        ok, m2 = F.floors_ok(digs)
        chk('H1-FLOOR', ok, 'mem%d: %s' % (i, m2))
        gp_node('H1-M%d' % i, F, f)
    # P3: anchor
    fA = padd(ppow(F.PHI2, 2), [128])
    chk('H1-ANCH', F.pins(fA, F.PHI2) == [7, None],
        'pins %s' % F.pins(fA, F.PHI2))
    msg, _ = F.gate(fA)
    chk('H1-ANCH', msg is None, 'gate: %s' % msg)
    gp_sig('H1-ANCH', F, fA, [(2, 2)])
    # P4: refine
    fR = padd(ppow(F.PHI2, 2), [256, 128])
    chk('H1-REF', F.pins(fR, F.PHI2) == [8, None],
        'old pins %s' % F.pins(fR, F.PHI2))
    newp = F.pins(fR, P2p)
    chk('H1-REF', newp == [9, 5], 'new pins %s want [9,5]' % newp)
    chk('H1-REF', newp[0] > 8 and newp[1] > 4, 'not above lam-node')
    gp_sig('H1-REF', F, fR, [(2, 2)])
    # P5: REFWRONG
    for tag, wk in (('wh', padd(F.PHI2, [0, -16])),
                    ('wf', padd(F.PHI2, [-16]))):
        wp = F.pins(fR, wk)
        chk('H1-REFWRONG', wp[0] == 8,
            '%s: pin %s (want alive at 8)' % (tag, wp))
    # P6: mutant tooth
    fM = padd(ppow(F.PHI2, 2), [32])
    msg, dv0 = F.gate(fM)
    chk('H1-MUT', msg is not None and dv0 == 5,
        'gate %s dv0 %s (want FAIL at 5)' % (msg, dv0))


# ============ FRAME H2 (gauge-live x mu2 = 3) =======================
PH2_1 = [-6, 0, 1]                       # Phi' = x^2-6
PH2_2 = padd(padd(pmul(PH2_1, PH2_1), pmul([0, 3], PH2_1)), [108])
H2 = Fr('H2', 3, 2, 1, 1, 2, 3, 3, PH2_1, PH2_2,
        {(0, 0, 0): 10, (0, 1, 0): 9, (0, 0, 1): 8, (0, 1, 1): 8,
         (1, 0, 0): 7, (1, 1, 0): 6, (1, 0, 1): 5, (1, 1, 1): 5,
         (2, 0, 0): 4, (2, 1, 0): 3, (2, 0, 1): 2, (2, 1, 1): 2})


def frame_h2():
    say('== FRAME H2: gauge-live (f2 = 2, eta = 2) x mu2 = 3 ==')
    F = H2
    gp_sig('H2-KEY', F, F.PHI2, [(2, 2)])                     # P7
    P2p = padd(F.PHI2, psca(-9, PH2_1))  # Phi2 - 9 Phi'
    gp_sig('H2-KEYP', F, P2p, [(2, 2)])                       # P7
    # P8: box members
    mems = []
    for i in range(5):
        digs = {}
        for (j, a, b), fl in F.floors.items():
            if random.random() < 0.6:
                digs[(j, a, b)] = random.choice([1, 2, -1]) * \
                    3 ** (fl + random.choice([0, 0, 1, 2]))
        if not any(j == 0 for (j, a, b) in digs):
            digs[(0, 0, 0)] = 3 ** 10
        mems.append((digs, F.from_digits(digs)))
    digs, f = mems[0]
    mems.append((digs, padd(list(f), [random.randint(-3, 3) * 3 ** 40
                                      for _ in range(F.n)])))
    for i, (digs, f) in enumerate(mems):
        msg, dv0 = F.gate(f)
        chk('H2-GATE', msg is None, 'mem%d: %s' % (i, msg))
        ok, m2 = F.floors_ok(digs)
        chk('H2-FLOOR', ok, 'mem%d: %s' % (i, m2))
        gp_node('H2-M%d' % i, F, f)
    # P9: anchor
    fA = padd(ppow(F.PHI2, 3), [0, 3 ** 9])
    chk('H2-ANCH', F.pins(fA, F.PHI2) == [19, None, None],
        'pins %s' % F.pins(fA, F.PHI2))
    msg, _ = F.gate(fA)
    chk('H2-ANCH', msg is None, 'gate: %s' % msg)
    gp_sig('H2-ANCH', F, fA, [(6, 2)])
    # P10: below-floor tooth at off-lattice slot (0,(1,0))
    fB = padd(ppow(F.PHI2, 3), [0, 3 ** 8])
    msg, dv0 = F.gate(fB)
    chk('H2-BELOW', msg is not None and dv0 == 17,
        'gate %s dv0 %s (want FAIL at 17)' % (msg, dv0))
    # P11: combined refine (lam = 7, s = eta2, p = mu2 = 3)
    fE = padd(ppow(P2p, 3), [3 ** 13])
    oldp = F.pins(fE, F.PHI2)
    chk('H2-REF', oldp == [21, 15, 9],
        'old pins %s want [21,15,9]' % oldp)
    chk('H2-REF', oldp[1] > 14 and oldp[2] > 7,
        'middle binomial pins not dead')
    newp = F.pins(fE, P2p)
    chk('H2-REF', newp == [26, None, None],
        'new pins %s want [26,None,None]' % newp)
    gp_sig('H2-REF', F, fE, [(6, 2)])
    for tag, wk in (('wh', padd(F.PHI2, psca(-27, PH2_1))),
                    ('wf', padd(F.PHI2, [0, -27]))):
        wp = F.pins(fE, wk)
        chk('H2-REFWRONG', wp[0] == 21,
            '%s: pin %s (want alive at 21)' % (tag, wp))
    # P12: window, N = 12, cap 24, max ragged offset w = 4
    N, cap = 12, 24

    def read_capped(f):
        A, _ = dev(list(f), F.PHI1, F.mu1)
        dvs = []
        for c in A:
            vals = [F.e1 * vp(cc, F.p) + i * F.h
                    for i, cc in enumerate(c) if cc]
            d = min(vals) if vals else None
            dvs.append(d if (d is not None and d < cap) else 'HI')
        ps = [q if (q is not None and q < cap) else 'HI'
              for q in F.pins(f, F.PHI2)]
        return dvs, ps

    base = read_capped(fA)
    for i in range(6):
        r = [random.randint(-4, 4) * 3 ** N for _ in range(F.n)]
        chk('H2-WIN', read_capped(padd(list(fA), r)) == base,
            'lift %d read differs below cap' % i)
    maxrag = padd(list(fA), pmul([0, 2 * 3 ** 11], PH2_1))
    chk('H2-MAXRAG', read_capped(maxrag) == base,
        'v=11 digit at height 26 > cap changed a below-cap read')
    fU = padd(ppow(F.PHI2, 3), [3 ** 13])
    p0a = F.pins(fU, F.PHI2)[0]
    p0b = F.pins(padd(list(fU), [3 ** 12]), F.PHI2)[0]
    chk('H2-UNDERCUT', (p0a, p0b) == (26, 24),
        'got (%s,%s) want (26,24)' % (p0a, p0b))


frame_h1()
frame_h2()
say('== gp oracle batch (%d jobs) ==' % len(JOBS))
run_gp()
tot = sum(CHK.values())
say('check tally: %s' % CHK)
say('=== VERDICT: %s -- %d checks, %d violations ===' %
    ('GREEN' if not VIOL else 'RED', tot, len(VIOL)))
for v in VIOL:
    say('  RED: %s' % v)
