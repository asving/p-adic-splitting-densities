#!/usr/bin/env python3
"""GENTOW3 passPE4 FRESH INSTRUMENT (hostile verifier, 2026-08-10).
Own primitives (dict-keyed integer polynomials, own level-1
developer, own two-variable K2-division and honest Phi2-division
loops -- written from scratch for this pass), frames DISJOINT from
all five prior fresh frames (PE1: FR-M3/FR-D5/FR-GL; PE2: FR2-C1;
PE3: FR3-B7) and from both constructed members (Phi2^3+32; the W
family). FR-M3 appears ONLY as replication/decorrelation rows (the
key-power self-shadow and the W members now cited by the r3 S0
sentence -- re-measured here on this pass's own primitives).

THE NEW FRAME
  FR4-E22: p = 2, Phi' = x^2 - 2 (e1 = 2, f1 = 1, h = 1, eta = 1),
    e2 = 2, f2 = 2, u2 = 7, mu2 = 2, mu1 = e2f2mu2 = 8.
    psi2 = Z^2 + Z + 1 over F2; nhat(7) = 8x (i(7) = 1),
    nhat(14) = 128 (i(14) = 0):
    K2(x,Y) = Y^4 + 8x*Y^2 + 128,  Phi2 = K2(x,Phi') =
    x^8 - 8x^6 + 8x^5 + 24x^4 - 32x^3 - 32x^2 + 32x + 144.
    delta = u2 - e2*D'*h = 7 - 4 = 3, E2 = e2f2u2 = 28,
    THETA = (59, 31).
    WHY THIS FRAME: first e2 > 1 frame in ANY verifier fresh leg
    (PE1/PE2/PE3 all ran e2 = 1; the battery's e2 in {2,3} rows
    are the imported eta = 1 GENTOW1 families, never re-run on
    independent primitives), and the first frame ANYWHERE (battery
    included) with e2f2 = 4: the recarry threshold Phi'-exponent
    e2f2 = 4 and the slot grid dv2 = 4v + 2a + 7b (a < 2, b < 4,
    TWO slots per height class since f1f2 = 2) are both new.
  FR-M3 (replication only): p = 2, Phi' = x^2 - 2,
    Phi2 = x^2 - 2x - 2, e2 = f2 = 1, u2 = 3, mu2 = 3, delta = 1,
    E2 = 3, THETA = (10, 7, 4).

PREREGISTERED PREDICTIONS (sealed before the first run; every
value hand-derived first -- the FR4-E22 self-shadow on two paper
routes: direct two-variable division, and the identity
F == K2(x,Y)^2 + 64*Y^5 (mod x^2 - 2) with shadow(K2^2 red) =
DRAIN; the FR-M3 W chain re-traced by hand on these conventions
and matching PE3's committed values before any code ran):
 P4-1 (SELF-E22): f = Phi2^2 honest DRAIN (C_0 = C_1 = 0); shadow
   EXACTLY Ghat_1 = 64*Y (single slot (v,a,b) = (6,0,1), height
   4*6+7 = 31 = THETA_1, pin 31) and Ghat_0 = -512x*Y^3 - 8192*Y
   (slots (9,1,3) and (13,0,1), heights 36+2+21 = 59 and 52+7 =
   59, BOTH = THETA_0): certificate LIVE at both coordinates; the
   THETA_0 digit is TWO-SLOT with distinct Phi'-exponents b = 3
   and b = 1 (first such anywhere; FR3-B7's two-slot digits paired
   b = 1 with the x-slot b = 0).
 P4-2 (BAND57): f = Phi2^2 + 2^12*x*Phi' -- honest pins (57, inf);
   shadow pin_0 = 57 with the SAME digit; mindiff = (59, 31); both
   hulls = the single edge (0,57)-(2,0) (the fake shadow point
   (1,31) sits strictly above: line value 28.5); a FAITHFUL
   decided leaf at THETA_0 - 2; PARI sigma {(8,2)}.
 P4-3 (BAND58): f = Phi2^2 + 2^11*Phi'^2 -- honest pin_0 = 58 =
   THETA_0 - 1; shadow pin + digit identical; mindiff = (59, 31):
   the delta = 3 faithful leaf band [57, 58] sampled at BOTH
   heights. PARI sigma {(8,2)}.
 P4-4 (DIV67): f = Phi2^2 + 2^15*Phi' -- honest pin_0 = 67; shadow
   pin_0 = 59 = THETA_0 (vertex undercut (0,67) -> (0,59));
   mindiff_0 = 59 EXACTLY (floor attained on a nondegenerate
   member); both hulls single-edge, PARI sigma {(8,2)} on BOTH
   priced routes = a delta = 3, e2 = 2 parity-luck row (pin
   corrupted, sigma-stratum intact): the count-law's
   necessary-not-sufficient clause measured at the new frame.
 P4-5 (CANCEL): f = Phi2^2 + 512x*Phi'^3 + 8192*Phi' -- honest
   pin_0 = 59 = THETA_0, decided, PARI sigma {(8,2)}; shadow
   coordinate 0 IDENTICALLY ZERO (the member content exactly
   cancels the self-shadow) while Ghat_1 = 64*Y: the shadow sees
   C_0 = 0, C_1 != 0 and prices f as Phi2-divisible (split into
   two degree-8 blocks) against an irreducible truth -- the
   sharpest shadow-not-a-function-of-honest-data witness at
   e2 > 1; mindiff_0 = 59 (floor attained via cancellation).
 P4-6 (FLOOR/ENTRY): 40 seeded gated members (strictly-above-side
   slot perturbations, <= 4 terms, units {1,-1,3,-3}): every
   mindiff_j >= THETA_j and > (mu2-j)*E2 (80 + 80 checks).
 P4-7 (REP -- FR-M3 on this pass's primitives; the r3 S0
   sentence's machine face): key power ShC = [64, 40x, 12], pins
   [12, 7, 4] vs THETA [10, 7, 4], j = 0 height-10 digit ZERO
   (certificate cancelled); W-A = Phi2^3 + 2x*Phi2^2 + 8*Phi2:
   honest pins [inf, 6, 3], shadow [10, 6, 3], Ghat_0 = 32,
   mindiff = [10, 9, 4]; W-B = W-A + 64: expansion ==
   x^6 - 4x^5 - 2x^4 + 16x^3 + 12x^2 - 32x + 40 (the polynomial
   the r3 S0 clause displays), honest pins [12, 6, 3], shadow
   [10, 6, 3], C_0 = 64, Ghat_0 = 96, mindiff_0 = 10 = THETA_0
   EXACTLY at the certificate-cancelled coordinate, honest hull
   vertices [(0,12),(1,6),(3,0)] vs shadow [(0,10),(1,6),(3,0)]
   (deciding vertex undercut, first-edge slope 6 -> 4); PARI
   sigma(W-B) = {(2,1),(2,2)}.
 P4-8 (GP carriers): sig(Phi2_E22) = {(4,2)} = (e1e2, f1f2);
   sig(Phi2_M3) = {(2,1)}.
 TEETH:
 T4-UP: the THETA+1 mutant is killed by every attained row (SELF
   pins 59/31, DIV67 mindiff 59, CANCEL mindiff 59, W-A/W-B
   mindiff 10): >= 6 kills.
 T4-DOWN: the THETA-1 mutant (floor 58 at FR4 j = 0) is refuted:
   BAND58's measured agreement at 58 = THETA_0 - 1 plus the
   measured first divergences at exactly 59.
 T4-BICOND: the retired r2 only-if reading ("fails AT THETA_j
   only at certificate coordinates") is killed at FR-M3 j = 0:
   the certificate is CANCELLED there (height-10 digit zero,
   checked in-run) AND W-A/W-B fail at exactly 10.

DESIGN-PHASE DISCLOSURE: one pre-seal probe (scratch, not
committed): member expansions cross-checked and the seven PARI
sigma want-lists computed once (all seven matched the hand
derivation where I had one -- the B58 want {(8,2)} was UNCERTAIN
by hand (residual-separability question) and is adopted from the
probe). No full run of THIS runner before seal; run-1 output kept
whatever its color.
"""

import random
import subprocess
import sys

# ---------------- own primitives (poly = dict {deg: int}) -----------


def pn(d):
    return {k: v for k, v in d.items() if v}


def padd(a, b):
    r = dict(a)
    for i, c in b.items():
        r[i] = r.get(i, 0) + c
    return pn(r)


def psub(a, b):
    return padd(a, {i: -c for i, c in b.items()})


def pmul(a, b):
    r = {}
    for i, c in a.items():
        for j, d in b.items():
            r[i + j] = r.get(i + j, 0) + c * d
    return pn(r)


def psca(a, s):
    return pn({i: c * s for i, c in a.items()})


def ppow(a, n):
    r = {0: 1}
    for _ in range(n):
        r = pmul(r, a)
    return r


def pdeg(a):
    return max(a) if a else -1


def pdivmod(f, g):
    """divide by MONIC g over Z; return (q, r)."""
    assert g[pdeg(g)] == 1
    f = dict(f)
    q = {}
    dg = pdeg(g)
    while pdeg(f) >= dg:
        d = pdeg(f)
        c = f[d]
        q[d - dg] = q.get(d - dg, 0) + c
        for j, e in g.items():
            f[d - dg + j] = f.get(d - dg + j, 0) - c * e
        f = pn(f)
    return pn(q), f


def dev(f, key, nmax=None):
    """development of f in powers of monic `key`: list of coeff polys."""
    out = []
    while f or (nmax is not None and len(out) < nmax):
        f, r = pdivmod(f, key)
        out.append(r)
        if nmax is not None and len(out) >= nmax and not f:
            break
        if nmax is None and not f:
            break
    return out


def v2(n, p):
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def digit_at(c, v, p):
    """p-adic digit of the integer c at position v (works for c < 0)."""
    return (c % p ** (v + 1)) // p ** v


# ---------------- frames --------------------------------------------


class Frame:
    def __init__(self, name, p, phi1, h, e1, e2, f2, mu2, u2, phi2):
        self.name, self.p = name, p
        self.phi1, self.h, self.e1 = phi1, h, e1
        self.e2, self.f2, self.mu2, self.u2 = e2, f2, mu2, u2
        self.phi2 = phi2
        self.D1 = pdeg(phi1)
        self.delta = u2 - e2 * self.D1 * h
        self.E2 = e2 * f2 * u2
        self.mu1 = e2 * f2 * mu2
        # K2(x,Y) as {Ydeg: coeffpoly}: recovered from phi2's dev in phi1
        k2dev = dev(phi2, phi1)
        self.K2 = {j: c for j, c in enumerate(k2dev) if c}
        assert self.K2.get(self.e2 * self.f2) == {0: 1}

    def theta(self, j):
        return (self.mu2 - j) * self.E2 + self.delta

    def wt(self, v, a, b):
        return self.e1 * self.e2 * v + a * self.e2 * self.h + b * self.u2


PHI1 = {2: 1, 0: -2}
P2E22 = padd(padd(ppow(PHI1, 4), pmul({1: 8}, ppow(PHI1, 2))), {0: 128})
E22 = Frame('FR4-E22', 2, PHI1, 1, 2, 2, 2, 2, 7, P2E22)
assert (E22.delta, E22.E2, E22.theta(0), E22.theta(1)) == (3, 28, 59, 31)
assert sorted(P2E22.items()) == [(0, 144), (1, 32), (2, -32), (3, -32),
                                 (4, 24), (5, 8), (6, -8), (8, 1)]

P2M3 = {2: 1, 1: -2, 0: -2}
M3 = Frame('FR-M3', 2, PHI1, 1, 2, 1, 1, 3, 3, P2M3)
assert (M3.delta, M3.E2, M3.theta(0), M3.theta(2)) == (1, 3, 10, 4)

# ---------------- the two reads -------------------------------------


def honest(fr, f):
    """composed read: C_j (coeff polys of the Phi2-development), j < mu2."""
    cs = dev(f, fr.phi2, nmax=fr.mu2 + 1)
    while len(cs) < fr.mu2 + 1:
        cs.append({})
    assert cs[fr.mu2] == {0: 1}, 'member not monic-exact at the top'
    return cs[:fr.mu2]


def xred(fr, c):
    """reduce a coeff poly mod Phi' (the shadow's per-step reduction)."""
    return pdivmod(c, fr.phi1)[1]


def shadow(fr, f):
    """stage-shadow read: iterated K2-division over R = O[x]/(Phi').
    Returns list of Ghat_j as {Ydeg: coeffpoly (deg < D')}, j < mu2."""
    F = {j: xred(fr, c) for j, c in enumerate(dev(f, fr.phi1)) if c}
    F = {j: c for j, c in F.items() if c}
    d = fr.e2 * fr.f2
    out = []
    cur = F
    for _ in range(fr.mu2):
        q = {}
        rem = dict(cur)
        while rem and max(rem) >= d:
            m = max(rem)
            c = rem.pop(m)
            q[m - d] = padd(q.get(m - d, {}), c)
            for j, k in fr.K2.items():
                if j == d:
                    continue
                t = psub(rem.get(m - d + j, {}), pmul(c, k))
                t = xred(fr, t)
                if t:
                    rem[m - d + j] = t
                else:
                    rem.pop(m - d + j, None)
        out.append({j: c for j, c in rem.items() if c})
        cur = {j: c for j, c in q.items() if c}
    assert cur == {0: {0: 1}}, 'shadow top quotient != 1'
    return out


def slots_honest(fr, cj):
    """honest coordinate poly -> {(a,b): int} on the slot grid."""
    out = {}
    for b, g in enumerate(dev(cj, fr.phi1)):
        for a, c in g.items():
            out[(a, b)] = c
    return out


def slots_shadow(fr, gj):
    out = {}
    for b, g in gj.items():
        for a, c in g.items():
            out[(a, b)] = c
    return out


def pin_of(fr, sl):
    hs = [fr.wt(v2(c, fr.p), a, b) for (a, b), c in sl.items() if c]
    return min(hs) if hs else None


def mindiff(fr, hsl, ssl):
    d = {}
    for k in set(hsl) | set(ssl):
        c = ssl.get(k, 0) - hsl.get(k, 0)
        if c:
            d[k] = c
    return pin_of(fr, d)


def digit_at_height(fr, sl, m):
    """assembled digit (per-slot vector) of a slot object at height m."""
    out = {}
    for (a, b), c in sl.items():
        w = fr.wt(0, a, b)
        if c and (m - w) % (fr.e1 * fr.e2) == 0 and m >= w:
            v = (m - w) // (fr.e1 * fr.e2)
            dg = digit_at(c, v, fr.p)
            if dg:
                out[(a, b)] = dg
    return out


def hull(pts):
    """lower convex hull vertices of [(j, pin)] + implicit monic top."""
    pts = sorted(pts)
    h = []
    for pt in pts:
        while len(h) >= 2 and \
              (h[-1][1] - h[-2][1]) * (pt[0] - h[-1][0]) >= \
              (pt[1] - h[-1][1]) * (h[-1][0] - h[-2][0]):
            h.pop()
        h.append(pt)
    return h


def read_data(fr, f, which):
    cs = honest(fr, f) if which == 'H' else None
    sl = ([slots_honest(fr, c) for c in cs] if which == 'H'
          else [slots_shadow(fr, g) for g in shadow(fr, f)])
    pins = [pin_of(fr, s) for s in sl]
    pts = [(j, pnn) for j, pnn in enumerate(pins) if pnn is not None]
    pts.append((fr.mu2, 0))
    return sl, pins, hull(pts)


def gate(fr, f):
    """level-1 side gate: e2*dv1(A_J) >= (mu1-J)*u2, monic top."""
    AJ = dev(f, fr.phi1)
    if pdeg(f) != fr.D1 * fr.mu1 or AJ[fr.mu1] != {0: 1}:
        return False
    for J in range(fr.mu1):
        g = AJ[J]
        if not g:
            continue
        dv1 = min(fr.e1 * v2(c, fr.p) + a for a, c in g.items())
        if fr.e2 * dv1 < (fr.mu1 - J) * fr.u2:
            return False
    return True


# ---------------- check plumbing ------------------------------------

NCHK, NVIO = 0, 0
TALLY = {}


def chk(tag, cond, msg=''):
    global NCHK, NVIO
    NCHK += 1
    TALLY[tag] = TALLY.get(tag, 0) + 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))
    return cond


def say(s):
    print(s)


# ---------------- gp (second oracle) --------------------------------

GP_JOBS, GP_WANT = [], {}


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in sorted(f.items())) \
        or '0'


def gp_add(tag, f, p, want):
    GP_JOBS.append('print("%s ", sig(%s, %d))' % (tag, poly_str(f), p))
    GP_WANT[tag] = sorted(want)


def gp_run():
    say('== GP leg: %d jobs ==' % len(GP_JOBS))
    hdr = ('default(parisizemax, 2000000000);\n'
           'sig(f,p)={my(fa=factor(f),out=List());'
           'for(i=1,matsize(fa)[1],my(g=fa[i,1]);'
           'if(poldegree(g)==1,listput(out,[1,1]),'
           'my(nf=nfinit([g,[p]]),dec=idealprimedec(nf,p));'
           'for(j=1,#dec,listput(out,[dec[j].e,dec[j].f]))));'
           'vecsort(Vec(out))}\n')
    src = hdr + '\n'.join(GP_JOBS) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=1800)
    got = {}
    for line in out.stdout.splitlines():
        ps = line.split(' ', 1)
        if len(ps) == 2 and ps[0] in GP_WANT:
            n = [int(t) for t in ps[1].replace('[', ' ')
                 .replace(']', ' ').replace(',', ' ').split()]
            got[ps[0]] = sorted((n[i], n[i + 1])
                                for i in range(0, len(n), 2))
    for tag, want in sorted(GP_WANT.items()):
        chk('GP', got.get(tag) == want,
            '%s: got %s want %s' % (tag, got.get(tag), want))
        say('  GP %s: %s (want %s)' % (tag, got.get(tag), want))


# ---------------- the battery ---------------------------------------


def main():
    random.seed(20260810)
    F2 = ppow(P2E22, 2)
    MEAS = {}

    say('== P4-1 SELF-E22 ==')
    hsl, hp, _ = read_data(E22, F2, 'H')
    ssl, sp, _ = read_data(E22, F2, 'S')
    chk('SELF', hp == [None, None], 'honest not DRAIN: %s' % hp)
    chk('SELF', ssl[1] == {(0, 1): 64}, 'Ghat_1 != 64*Phi\': %s' % ssl[1])
    chk('SELF', ssl[0] == {(1, 3): -512, (0, 1): -8192},
        'Ghat_0 != -512x*Phi\'^3 - 8192*Phi\': %s' % ssl[0])
    chk('SELF', sp == [59, 31], 'self-shadow pins %s != [59,31]' % sp)
    d0 = digit_at_height(E22, ssl[0], 59)
    d1 = digit_at_height(E22, ssl[1], 31)
    chk('SELF', sorted(d0) == [(0, 1), (1, 3)] and all(d0.values()),
        'THETA_0 digit not two-slot-nonzero: %s' % d0)
    chk('SELF', d1 == {(0, 1): 1}, 'THETA_1 digit: %s' % d1)
    MEAS['self_pins'] = list(sp)
    MEAS['self_d58'] = digit_at_height(E22, ssl[0], 58)
    say('  self-shadow pins %s = THETA; cert digit at 59: %s; at 31: %s'
        % (sp, d0, d1))

    say('== P4-2/3 BAND (delta = 3: faithful leaf band [57, 58]) ==')
    for tag, g, pin0, sig in (
            ('B57', pmul({1: 4096}, PHI1), 57, [(8, 2)]),
            ('B58', psca(ppow(PHI1, 2), 2048), 58, [(8, 2)])):
        f = padd(F2, g)
        chk('BAND', gate(E22, f), tag + ' gate')
        hsl, hp, hh = read_data(E22, f, 'H')
        ssl, sp, sh = read_data(E22, f, 'S')
        md = [mindiff(E22, hsl[j], ssl[j]) for j in range(2)]
        chk('BAND', hp[0] == pin0 and sp[0] == pin0,
            '%s pins h%s s%s' % (tag, hp, sp))
        chk('BAND', md == [59, 31], '%s mindiff %s' % (tag, md))
        chk('BAND', digit_at_height(E22, hsl[0], pin0) ==
            digit_at_height(E22, ssl[0], pin0), tag + ' pin digit')
        chk('BAND', hh == sh == [(0, pin0), (2, 0)],
            '%s hulls h%s s%s' % (tag, hh, sh))
        gp_add(tag, f, 2, sig)
        MEAS[tag + '_md0'] = md[0]
        say('  %s: pins %s both reads, mindiff %s, hull %s' %
            (tag, pin0, md, hh))

    say('== P4-4 DIV67 (undercut at the new frame) ==')
    f = padd(F2, psca(PHI1, 32768))
    chk('DIV', gate(E22, f), 'D67 gate')
    hsl, hp, hh = read_data(E22, f, 'H')
    ssl, sp, sh = read_data(E22, f, 'S')
    md = [mindiff(E22, hsl[j], ssl[j]) for j in range(2)]
    chk('DIV', hp[0] == 67 and sp[0] == 59, 'D67 pins h%s s%s' % (hp, sp))
    chk('DIV', md[0] == 59, 'D67 mindiff_0 %s != 59' % md[0])
    chk('DIV', hh == [(0, 67), (2, 0)] and sh == [(0, 59), (2, 0)],
        'D67 hulls h%s s%s' % (hh, sh))
    gp_add('D67', f, 2, [(8, 2)])
    MEAS['D67_md0'] = md[0]
    say('  D67: honest pin 67 -> shadow 59 = THETA_0; mindiff %s' % md)

    say('== P4-5 CANCEL (shadow coordinate identically zero) ==')
    f = padd(F2, padd(pmul({1: 512}, ppow(PHI1, 3)), psca(PHI1, 8192)))
    chk('CANCEL', gate(E22, f), 'CAN gate')
    hsl, hp, hh = read_data(E22, f, 'H')
    ssl, sp, sh = read_data(E22, f, 'S')
    md = [mindiff(E22, hsl[j], ssl[j]) for j in range(2)]
    chk('CANCEL', hp[0] == 59 and hp[1] is None, 'CAN honest %s' % hp)
    chk('CANCEL', ssl[0] == {} and sp[0] is None,
        'CAN shadow coord 0 not zero: %s' % ssl[0])
    chk('CANCEL', sp[1] == 31, 'CAN shadow fake pin_1 %s' % sp[1])
    chk('CANCEL', md == [59, 31], 'CAN mindiff %s' % md)
    gp_add('CAN', f, 2, [(8, 2)])
    MEAS['CAN_md0'] = md[0]
    say('  CANCEL: honest pin 59 decided vs shadow C_0 == 0 (prices a '
        'Phi2-split); mindiff %s' % md)

    say('== P4-6 FLOOR/ENTRY sweep (40 seeded gated members) ==')
    nm = 0
    while nm < 40:
        g = {}
        for _ in range(random.randint(1, 4)):
            j = random.randint(0, 1)
            b = random.randint(0, 3)
            a = random.randint(0, 1)
            lo = max(0, -(-(57 - 28 * j - 2 * a - 7 * b) // 4))
            v = random.randint(lo, lo + 4)
            c = random.choice([1, -1, 3, -3])
            t = psca(pmul(pmul(ppow(PHI1, b), {a: 1}),
                          ppow(P2E22, j)), c * 2 ** v)
            g = padd(g, t)
        f = padd(F2, g)
        if not gate(E22, f) or pdeg(f) != 16:
            continue
        nm += 1
        hsl, hp, _ = read_data(E22, f, 'H')
        ssl, sp, _ = read_data(E22, f, 'S')
        for j in range(2):
            md = mindiff(E22, hsl[j], ssl[j])
            chk('FLOOR', md is None or md >= E22.theta(j),
                'member %d j=%d mindiff %s' % (nm, j, md))
            chk('ENTRY', md is None or md > (2 - j) * 28,
                'member %d j=%d entry %s' % (nm, j, md))
    say('  40 members x 2 coords: FLOOR + ENTRY clean')

    say('== P4-7 REP: FR-M3 on this pass\'s primitives ==')
    F3 = ppow(P2M3, 3)
    ssl3, sp3, _ = read_data(M3, F3, 'S')
    chk('REP', [dict(s) for s in ssl3] ==
        [{(0, 0): 64}, {(1, 0): 40}, {(0, 0): 12}],
        'M3 self-shadow %s' % ssl3)
    chk('REP', sp3 == [12, 7, 4], 'M3 pins %s' % sp3)
    chk('REP', digit_at_height(M3, ssl3[0], 10) == {},
        'M3 j=0 height-10 digit not zero')
    MEAS['cert10'] = digit_at_height(M3, ssl3[0], 10)
    say('  key power: pins %s vs THETA [10,7,4]; height-10 digit at '
        'j=0 CANCELLED' % sp3)
    WA = padd(padd(F3, pmul({1: 2}, ppow(P2M3, 2))), psca(P2M3, 8))
    WB = padd(WA, {0: 64})
    chk('REP', sorted(WB.items()) == [(0, 40), (1, -32), (2, 12),
                                      (3, 16), (4, -2), (5, -4), (6, 1)],
        'W-B expansion mismatch: %s' % sorted(WB.items()))
    for tag, f, hpins, hhull in (
            ('W-A', WA, [None, 6, 3], [(1, 6), (3, 0)]),
            ('W-B', WB, [12, 6, 3], [(0, 12), (1, 6), (3, 0)])):
        chk('REP', gate(M3, f), tag + ' gate')
        hsl, hp, hh = read_data(M3, f, 'H')
        ssl, sp, sh = read_data(M3, f, 'S')
        md = [mindiff(M3, hsl[j], ssl[j]) for j in range(3)]
        chk('REP', hp == hpins and sp == [10, 6, 3],
            '%s pins h%s s%s' % (tag, hp, sp))
        chk('REP', md == [10, 9, 4], '%s mindiff %s' % (tag, md))
        chk('REP', hh == hhull and sh == [(0, 10), (1, 6), (3, 0)],
            '%s hulls h%s s%s' % (tag, hh, sh))
        MEAS[tag + '_md0'] = md[0]
        say('  %s: shadow pins %s, mindiff %s (10 = THETA_0 at the '
            'cancelled coordinate)' % (tag, sp, md))
    chk('REP', slots_honest(M3, honest(M3, WB)[0]) == {(0, 0): 64} and
        slots_shadow(M3, shadow(M3, WB)[0]) == {(0, 0): 96},
        'W-B C_0/ShC_0 values')
    gp_add('WB', WB, 2, [(2, 1), (2, 2)])

    say('== P4-8 GP carriers + all sigma jobs ==')
    gp_add('P2E22', P2E22, 2, [(4, 2)])
    gp_add('P2M3', P2M3, 2, [(2, 1)])
    gp_run()

    say('== TEETH (all fed by values MEASURED in this run) ==')
    # T4-UP: the THETA+1 mutant asserts first disagreement >= THETA+1
    # at every coordinate; every measured attainment AT THETA kills it.
    attained = [('SELF pin_0', MEAS['self_pins'][0], E22.theta(0)),
                ('SELF pin_1', MEAS['self_pins'][1], E22.theta(1)),
                ('D67 mindiff_0', MEAS['D67_md0'], E22.theta(0)),
                ('CAN mindiff_0', MEAS['CAN_md0'], E22.theta(0)),
                ('W-A mindiff_0', MEAS['W-A_md0'], M3.theta(0)),
                ('W-B mindiff_0', MEAS['W-B_md0'], M3.theta(0))]
    kills_up = sum(1 for _, m, th in attained if m is not None
                   and m < th + 1)
    chk('TEETH', kills_up == 6,
        'T4-UP: mutant floor THETA+1 survives (%d kills)' % kills_up)
    say('  T4-UP: THETA+1 mutant killed %d/6 times (measured content '
        'AT THETA violates the mutant floor)' % kills_up)
    # T4-DOWN: the THETA-1 mutant (floor 58 at FR4 j = 0, band ending
    # at 57) is refuted iff the measured self-shadow carries ZERO
    # content at 58 while every measured FR4 j=0 divergence sits at
    # exactly 59 -- i.e. 58 is measured-faithful, against the mutant's
    # sharpness at 58.
    chk('TEETH', MEAS['self_d58'] == {} and
        all(MEAS[k] == 59 for k in ('B57_md0', 'B58_md0', 'D67_md0',
                                    'CAN_md0')),
        'T4-DOWN: self d58 %s, mds %s' %
        (MEAS['self_d58'], [MEAS[k] for k in ('B57_md0', 'B58_md0',
                                              'D67_md0', 'CAN_md0')]))
    say('  T4-DOWN: THETA-1 mutant refuted: measured self-shadow digit '
        'at 58 is ZERO; B57/B58 faithful at 57/58; every measured '
        'first divergence sits at exactly 59')
    # T4-BICOND: the retired r2 only-if ("fails AT THETA_j only at
    # certificate coordinates") requires: cert cancelled at (FR-M3, 0)
    # => no member fails at exactly 10 there. Killed by the measured
    # cert-cancellation + two measured members failing at exactly 10.
    chk('TEETH', MEAS['cert10'] == {} and MEAS['W-A_md0'] == 10
        and MEAS['W-B_md0'] == 10,
        'T4-BICOND: cert10 %s, W mds %s %s' %
        (MEAS['cert10'], MEAS['W-A_md0'], MEAS['W-B_md0']))
    say('  T4-BICOND: measured cert digit at 10 ZERO at FR-M3 j=0 AND '
        'W-A/W-B measured failing at exactly 10: the r2 only-if is '
        'dead on this leg too')

    say('')
    verdict = 'GREEN' if NVIO == 0 else 'RED'
    say('=== VERDICT: %s -- %d checks, %d violations, teeth 3/3 ==='
        % (verdict, NCHK, NVIO))
    say('tally: %s' % TALLY)
    return 0 if NVIO == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
