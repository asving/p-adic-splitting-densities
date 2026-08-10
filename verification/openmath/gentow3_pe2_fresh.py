#!/usr/bin/env python3
"""GENTOW3 passPE2 FRESH ROUTE (second hostile verifier's independent
instrument, 2026-08-10).  Primitives written from scratch (NOT imported
from gentow1_checks / gentow3_checks / gentow3_pe1_fresh); frames and
members chosen DISJOINT from PE1's route: the compound frame (mu2 = 3
AND eta != 1 together -- PE1 ran them separately), the j = mu2 top
boundary, the delta = 0 corner (analytic + arithmetic probe), and the
S4 count-law counter-member at PE1's measured-slack frame FR-M3.

FRAMES:
  FR2-C1 (COMPOUND, new): p = 3, Phi' = x^2-6 (e1 = 2, f1 = 1, h = 1,
         eta = 2 != 1), e2 = 1, f2 = 2, u2 = 3, CORRECTED key
         Phi2 = Phi'^2 + 3x*Phi' + 108 (erratum 59c1966; the FR-GL /
         HETOW frame-X key), but at mu2 = 3 (mu1 = 6, n = 12) --
         the first frame anywhere with BOTH mu2 = 3 and eta != 1.
         delta = 1, E2 = 6, THETA = (19, 13, 7).
  FR-M3 (PE1's frame, reused ONLY for the count-law counter-member):
         p = 2, Phi' = x^2-2, e2 = f2 = 1, u2 = 3,
         Phi2 = x^2 - 2x - 2, mu2 = 3, delta = 1, E2 = 3,
         THETA = (10, 7, 4); PE1 measured self-shadow pins
         [12, 7, 4]: SLACK at j = 0 (12 > 10).

PREREGISTERED PREDICTIONS (hand-derived before the first run; the
FR2-C1 self-shadow was computed by explicit 3-step K2-division with
x^2 -> 6 reduction at every step, on paper):
 P2-1 (FR2-C1 self-shadow, exact polynomial values): honest DRAIN
   (C_j = 0, j = 0,1,2); shadow
     ShC_0 = -157464*Phi' - 314928*x   (v3: 9/9; heights 21/19)
     ShC_1 =    486*Phi' + 17496*x     (v3: 5/7; heights 13/15)
     ShC_2 =     27*Phi' -   135*x     (v3: 3/3; heights  9/7)
   pins [19, 13, 7] = THETA exactly: the floor ATTAINED at ALL
   THREE coordinates at the compound frame (no FR-M3-style slack).
 P2-2 (FR2-GL replication, decorrelation row): same frame at
   mu2 = 2 (PE1's FR-GL): my primitives reproduce the committed
   values ShC_0 = -486*Phi' + 2916*x, ShC_1 = 9*Phi' - 27*x,
   pins [13, 7].
 P2-3 (count-law counter-member at FR-M3): f = Phi2^3 + 32
   (32 = pi^5: slot height 10 = THETA_0 = the node floor, x-free
   monomial => zero own discrepancy).  Honest: C = [32, 0, 0],
   pins [10, inf, inf]; polygon = single edge (0,10)-(3,0), decided
   (slope 10/3, e-part 3).  Shadow: ShC = [96, 40x, 12], pins
   [10, 7, 4]; fake pins (1,7) and (2,4) lie strictly ABOVE the
   edge (values 20/3, 10/3) => hulls IDENTICAL, vertex digit at
   (0,10) IDENTICAL (96 = 2^5*3 -> residue 1 = 32 -> residue 1);
   mindiff = [12, 7, 4] all >= THETA.  PARI: sigma {(6,1)}.
   => a delta = 1 LEAF member whose deciding height REACHES
   THETA_0 with shadow read = honest read on every consulted
   datum: refutes S4's "mislabeled exactly on the members whose
   deciding heights reach THETA_j ... at delta = 1 that is the
   entire leaf population" and S0's unconditional "fails AT
   THETA_j (attained by the key power's own shadow)".
 P2-4 (FR2-C1 faithful deep member): f = Phi2^3 + 3^9 (height 18 =
   THETA_0 - 1): mindiff [19, 13, 7]; hulls identical (single edge
   (0,18)-(3,0); fakes (1,13),(2,7) above the line values 12/6);
   vertex digits equal => faithful read below THETA (clause (ii)).
 P2-5 (FR2-C1 mislabeled member -- the compound-frame divergence
   witness): f = Phi2^3 + 3^10 (height 20 > THETA_0): honest pins
   [20, inf, inf], hull edge (0,20)-(3,0); shadow ShC_0 =
   3^10 - 157464*Phi' - 314928*x has pin 19 (the fake x-slot at
   19 = THETA_0 UNDERCUTS the honest pin 20), and the fakes
   (1,13),(2,7) lie above the (0,19)-(3,0) edge => shadow hull =
   (0,19)-(3,0) DIFFERS from honest: a mislabeled leaf (the
   PE1-anchor undercut genre, now at the compound frame); mindiff
   = THETA = [19,13,7].  PARI on honest truth: single factor
   (e,f) = (6,2).
 P2-6 (floor sweep): 40 random in-budget members at FR2-C1 (slot
   content at heights weakly above the composed side (mu2-j)*E2):
   per coordinate, mindiff_j is None or >= THETA_j (floor), and
   > (mu2-j)*E2 (entry band clean, COR 3.C margin).
 P2-7 (PARI frame facts): FR2-C1 corrected key: factorpadic gives
   one factor, (e,f) = (2,2) (carrier); the gauge-NAIVE key
   Phi'^2 + 3x*Phi' + 54 gives (e,f) = (4,1) (NOT a carrier) --
   the compound frame is meaningful only at the corrected key.
 P2-8 (top boundary j = mu2): the K2-adic expansion of Phi2^mu2
   has G-hat_{mu2} = 1 on BOTH routes (trivial agreement at the
   monic top; the theorem's j < mu2 scoping fences exactly the
   nontrivial coordinates).
 P2-9 (delta = 0 corner, arithmetic probe): delta = 0 forces
   u2 = e2*D'*h, so m_t = u2*(f2-t) = e2*e1*f1*h*(f2-t) == 0
   mod e1: i(m_t) = 0 for every t.  At f1 = 1 the second clause
   (c_t*eta^W in F_Q) is automatic => EVERY delta = 0, f1 = 1
   genre is x-free and the geography trivializes (clause (iii):
   shadow exact); no attainment content exists at the corner.
   Probe: i(m_t) = 0 verified over a parameter grid e1 in {2,3,4},
   f1 in {1,2,3}, h coprime, e2 in {1,2,3}, f2 in {1,2,3}.
 TEETH:
   T2-UP: THETA+1 mutant [20,14,8] at FR2-C1 killed by the three
     attained self-shadow pins.
   T2-DOWN: THETA-1 mutant [18,12,6] refuted by P2-4's faithful
     member (mindiff 19 > 18 claimed unfaithful at 18: no digit
     exists there to diverge -- the mutant kills the band edge).
   T2-CL: the count-law reading "every delta = 1 leaf member with
     deciding height >= THETA is mislabeled" killed by P2-3
     (identical hulls + identical vertex digits + PARI-confirmed
     honest sigma).
Run discipline: run 1 verdict kept whatever it says.
"""
import re
import subprocess
import sys
import random

# ---------- exact Z[x] arithmetic (own primitives) ----------

def pstrip(a):
    while a and a[-1] == 0:
        a.pop()
    return a

def padd(a, b):
    n = max(len(a), len(b))
    return pstrip([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                   for i in range(n)])

def pneg(a):
    return [-c for c in a]

def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i + j] += ai * bj
    return pstrip(out)

def pdivmod_monic(f, g):
    """f = q*g + r with g monic; exact over Z."""
    f = f[:]
    dg = len(g) - 1
    assert g[-1] == 1
    q = [0] * max(len(f) - dg, 0)
    while len(f) - 1 >= dg and f:
        c = f[-1]
        d = len(f) - 1 - dg
        q[d] = c
        for i in range(len(g)):
            f[i + d] -= c * g[i]
        pstrip(f)
    return pstrip(q), f

def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

# ---------- frame ----------

class Fr:
    def __init__(self, name, p, PHIP, e1, h, e2, f2, u2, mu2, PHI2):
        self.name, self.p = name, p
        self.PHIP, self.e1, self.h = PHIP, e1, h
        self.e2, self.f2, self.u2, self.mu2 = e2, f2, u2, mu2
        self.PHI2 = PHI2
        self.Dp = len(PHIP) - 1            # D' (f1 = 1 frames here)
        self.E2 = e2 * f2 * u2
        self.delta = u2 - e2 * self.Dp * h
        self.TH = [(mu2 - j) * self.E2 + self.delta for j in range(mu2)]

    # slot height of monomial c * x^a * Phi'^b
    def hgt(self, c, a, b):
        v = vp(c, self.p)
        if v is None:
            return None
        return self.e1 * self.e2 * v + a * self.e2 * self.h + b * self.u2

    def phip_dev(self, P):
        """P (deg < D2) -> [g_0, ..., g_{e2f2-1}] with deg g_b < D'."""
        out = []
        for _ in range(self.e2 * self.f2):
            P, r = pdivmod_monic(P, self.PHIP)
            out.append(r)
        assert not P, 'phip_dev overflow'
        return out

    def pin_of(self, P):
        """min slot height over nonzero monomials of P (deg < D2)."""
        best = None
        for b, g in enumerate(self.phip_dev(P)):
            for a, c in enumerate(g):
                if c:
                    m = self.hgt(c, a, b)
                    if best is None or m < best:
                        best = m
        return best

    def digit_at(self, P, m):
        """tuple of slot residues of P at height m (one per (a,b)
        class whose congruence admits m)."""
        out = []
        dev = self.phip_dev(P)
        for b in range(self.e2 * self.f2):
            for a in range(self.Dp):
                w = a * self.e2 * self.h + b * self.u2
                d, r = divmod(m - w, self.e1 * self.e2)
                if r == 0 and d >= 0:
                    c = dev[b][a] if a < len(dev[b]) else 0
                    out.append((a, b, (c // self.p ** d) % self.p))
        return tuple(out)

# ---------- the two reads ----------

def honest_coords(F, f):
    """iterated Phi2-division in Z[x]: [C_0, ..., C_{mu2-1}], top."""
    out = []
    for _ in range(F.mu2):
        f, r = pdivmod_monic(f, F.PHI2)
        out.append(r)
    return out, f

def red(F, P):
    """reduce P mod Phi' (deg < D')."""
    return pdivmod_monic(P, F.PHIP)[1]

def shadow_coords(F, f):
    """level-1 dev of f -> F(x,Y); iterated K2-division over
    Z[x]/(Phi') (reduction at every arithmetic step);
    returns [ShC_0, ..., ShC_{mu2-1}], top-quotient (Y-poly)."""
    # level-1 development
    A = []
    g = f[:]
    while g:
        g, r = pdivmod_monic(g, F.PHIP)
        A.append(r)
    # K2 from Phi2 (its own Phi'-adic dev; coefficients deg < D')
    K2 = []
    g = F.PHI2[:]
    while g:
        g, r = pdivmod_monic(g, F.PHIP)
        K2.append(r)
    assert K2[-1] == [1], 'K2 not Y-monic'
    dK = len(K2) - 1                      # = e2 f2
    out = []
    cur = [red(F, a) for a in A]          # Y-poly, reduced coeffs
    for _ in range(F.mu2):
        # divide cur by K2 in (Z[x]/Phi')[Y]
        cur = [c[:] for c in cur]
        q = [[] for _ in range(max(len(cur) - dK, 0))]
        while len(cur) - 1 >= dK and pstrip_list(cur):
            c = cur[-1]
            d = len(cur) - 1 - dK
            q[d] = c
            for i in range(len(K2)):
                cur[i + d] = red(F, padd(cur[i + d],
                                         pneg(pmul(c, K2[i]))))
            while cur and not cur[-1]:
                cur.pop()
        # remainder cur = G-hat_j (deg_Y < dK); evaluate at Y = Phi'
        sh = []
        for i, c in enumerate(cur):
            sh = padd(sh, pmul(c, ppow(F.PHIP, i)))
        out.append(sh)
        cur = q
    return out, cur

def pstrip_list(cur):
    while cur and not cur[-1]:
        cur.pop()
    return cur

def ppow(g, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, g)
    return out

def mindiff(F, C, Sh):
    return [F.pin_of(padd(Sh[j], pneg(C[j]))) for j in range(F.mu2)]

# ---------- polygon (lower hull incl. monic top) ----------

def hull(F, pins):
    pts = [(j, m) for j, m in enumerate(pins) if m is not None]
    pts.append((F.mu2, 0))
    pts.sort()
    h = []
    for pt in pts:
        while len(h) >= 2 and \
              (h[-1][0] - h[-2][0]) * (pt[1] - h[-2][1]) <= \
              (pt[0] - h[-2][0]) * (h[-1][1] - h[-2][1]):
            h.pop()
        h.append(pt)
    return h

# ---------- PARI oracle (idealprimedec route, exact (e,f)) ----------

def gp_sigma(f, p):
    """sorted [(e,f), ...] over Q_p: factor over Q, then
    idealprimedec per irreducible factor (PARI primitives)."""
    pol = '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                   if c) or '0'
    src = ("default(parisizemax, 2000000000);\n"
           "sig(f, p) = {\n"
           "  my(fa = factor(f), out = List());\n"
           "  for (i = 1, matsize(fa)[1],\n"
           "    my(g = fa[i, 1]);\n"
           "    if (poldegree(g) == 1, listput(out, [1, 1]),\n"
           "      my(nf = nfinit([g, [p]]),"
           " dec = idealprimedec(nf, p));\n"
           "      for (j = 1, #dec,"
           " listput(out, [dec[j].e, dec[j].f]))));\n"
           "  vecsort(Vec(out))\n"
           "}\n"
           "print(\"SIG \", sig(" + pol + ", " + str(p) + "));\n"
           "quit\n")
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=900)
    m = re.search(r'SIG (.*)', out.stdout)
    if not m:
        return None, out.stderr[-120:]
    s = m.group(1).replace('[', ' ').replace(']', ' ').replace(',', ' ')
    n = [int(t) for t in s.split()]
    return sorted((n[i], n[i + 1]) for i in range(0, len(n), 2)), ''

# ---------- checks ----------

NCHK = 0
NBAD = 0
TALLY = {}

def chk(tag, ok, msg):
    global NCHK, NBAD
    NCHK += 1
    TALLY[tag] = TALLY.get(tag, 0) + 1
    if not ok:
        NBAD += 1
        print('  VIOLATION [%s] %s' % (tag, msg))

def say(s):
    print(s)

# ---------- frames ----------

# FR2-C1: p=3, Phi' = x^2-6, e2=1, f2=2, u2=3, mu2=3,
# Phi2 = Phi'^2 + 3x Phi' + 108 = x^4 + 3x^3 - 12x^2 - 18x + 144
PHIP_C1 = [-6, 0, 1]
PHI2_C1 = padd(padd(pmul(PHIP_C1, PHIP_C1),
                    pmul([0, 3], PHIP_C1)), [108])
FR2C1 = Fr('FR2-C1', 3, PHIP_C1, 2, 1, 1, 2, 3, 3, PHI2_C1)

# FR2-GL-REP: same frame at mu2 = 2 (PE1's FR-GL) for decorrelation
FRGLR = Fr('FR2-GL-REP', 3, PHIP_C1, 2, 1, 1, 2, 3, 2, PHI2_C1)

# FR-M3 (PE1's frame, count-law counter-member only)
FRM3 = Fr('FR-M3', 2, [-2, 0, 1], 2, 1, 1, 1, 3, 3, [-2, -2, 1])

def main():
    say('=== GENTOW-3 passPE2 fresh route (2026-08-10) ===')
    say('FR2-C1: D2=%d E2=%d delta=%d THETA=%s' %
        (len(FR2C1.PHI2) - 1, FR2C1.E2, FR2C1.delta, FR2C1.TH))
    assert FR2C1.PHI2 == [144, -18, -12, 3, 1]

    # ---- P2-1: compound self-shadow ----
    F = FR2C1
    f = ppow(F.PHI2, 3)
    C, top = honest_coords(F, f)
    Sh, shtop = shadow_coords(F, f)
    chk('SELF', all(not c for c in C) and top == [1],
        'honest not DRAIN: %s' % C)
    want = [padd(pmul([-157464], F.PHIP), [0, -314928]),
            padd(pmul([486], F.PHIP), [0, 17496]),
            padd(pmul([27], F.PHIP), [0, -135])]
    for j in range(3):
        chk('SELF', Sh[j] == want[j],
            'ShC_%d = %s want %s' % (j, Sh[j], want[j]))
    pins = [F.pin_of(s) for s in Sh]
    chk('SELF', pins == F.TH, 'pins %s vs THETA %s' % (pins, F.TH))
    say('  P2-1 self-shadow pins %s = THETA %s (attained x3), '
        'values match hand derivation' % (pins, F.TH))
    md = mindiff(F, C, Sh)
    chk('SELF', md == F.TH, 'self mindiff %s' % md)

    # ---- P2-2: FR-GL replication (mu2 = 2, committed values) ----
    G = FRGLR
    f = ppow(G.PHI2, 2)
    C, top = honest_coords(G, f)
    Sh, _ = shadow_coords(G, f)
    wgl = [padd(pmul([-486], G.PHIP), [0, 2916]),
           padd(pmul([9], G.PHIP), [0, -27])]
    ok = all(not c for c in C) and Sh[0] == wgl[0] and Sh[1] == wgl[1]
    chk('REP', ok, 'FR-GL rep: %s / %s' % (Sh[0], Sh[1]))
    chk('REP', [G.pin_of(s) for s in Sh] == [13, 7], 'GL pins')
    say('  P2-2 FR-GL (mu2=2) replicated: ShC_0 = -486Phi\'+2916x, '
        'ShC_1 = 9Phi\'-27x, pins [13, 7]')

    # ---- P2-3: count-law counter-member at FR-M3 ----
    F = FRM3
    f = padd(ppow(F.PHI2, 3), [32])
    C, top = honest_coords(F, f)
    Sh, _ = shadow_coords(F, f)
    chk('CL', C[0] == [32] and not C[1] and not C[2],
        'honest C %s' % C)
    chk('CL', Sh[0] == [96] and Sh[1] == [0, 40] and Sh[2] == [12],
        'shadow %s' % Sh)
    hp = [F.pin_of(c) for c in C]
    sp = [F.pin_of(s) for s in Sh]
    chk('CL', hp == [10, None, None] and sp == [10, 7, 4],
        'pins h%s s%s' % (hp, sp))
    md = mindiff(F, C, Sh)
    chk('CL', md == [12, 7, 4] and all(md[j] >= F.TH[j] for j in
        range(3)), 'mindiff %s' % md)
    hh, sh_ = hull(F, hp), hull(F, sp)
    chk('CL', hh == sh_ == [(0, 10), (3, 0)],
        'hulls h%s s%s' % (hh, sh_))
    dh = F.digit_at(C[0], 10)
    ds = F.digit_at(Sh[0], 10)
    chk('CL', dh == ds and any(t[2] for t in dh),
        'vertex digits h%s s%s' % (dh, ds))
    say('  P2-3 FR-M3 f = Phi2^3+32: leaf decided at pin 10 = '
        'THETA_0 (node floor); hulls identical %s, vertex digit '
        'identical %s; mindiff %s -- the shadow read equals the '
        'honest read on every consulted datum: NOT mislabeled, '
        'yet its deciding height reaches THETA_0 at delta = 1' %
        (hh, dh, md))
    sig, err = gp_sigma(f, 2)
    chk('GP', sig == [(6, 1)],
        'PARI M3 member sigma %s (%s)' % (sig, err))
    say('  P2-3 PARI sigma: %s = {(6,1)} -- honest read tRAM(10) '
        'confirmed; both routes priced it identically' % sig)

    # ---- P2-4: FR2-C1 faithful deep member (height 18 < 19) ----
    F = FR2C1
    f = padd(ppow(F.PHI2, 3), [3 ** 9])
    C, _ = honest_coords(F, f)
    Sh, _ = shadow_coords(F, f)
    md = mindiff(F, C, Sh)
    hp = [F.pin_of(c) for c in C]
    sp = [F.pin_of(s) for s in Sh]
    chk('BAND', md == F.TH and hp == [18, None, None] and
        sp == [18, 13, 7], 'P2-4 %s %s %s' % (md, hp, sp))
    hh, sh_ = hull(F, hp), hull(F, sp)
    chk('BAND', hh == sh_ == [(0, 18), (3, 0)],
        'P2-4 hulls %s %s' % (hh, sh_))
    chk('BAND', F.digit_at(C[0], 18) == F.digit_at(Sh[0], 18),
        'P2-4 vertex digit')
    say('  P2-4 f = Phi2^3 + 3^9: faithful at 18 = THETA_0 - 1 '
        '(hulls + vertex digits identical; fakes at (1,13),(2,7) '
        'above the edge)')

    # ---- P2-5: FR2-C1 mislabeled member (height 20 > 19) ----
    f = padd(ppow(F.PHI2, 3), [3 ** 10])
    C, _ = honest_coords(F, f)
    Sh, _ = shadow_coords(F, f)
    hp = [F.pin_of(c) for c in C]
    sp = [F.pin_of(s) for s in Sh]
    md = mindiff(F, C, Sh)
    hh, sh_ = hull(F, hp), hull(F, sp)
    chk('DIV', hp == [20, None, None] and sp == [19, 13, 7] and
        md == F.TH, 'P2-5 %s %s %s' % (hp, sp, md))
    chk('DIV', hh == [(0, 20), (3, 0)] and sh_ == [(0, 19), (3, 0)],
        'P2-5 hulls h%s s%s' % (hh, sh_))
    say('  P2-5 f = Phi2^3 + 3^10: shadow hull %s (fake pin 19 '
        'undercuts the honest pin 20) vs honest %s -- mislabeled '
        'leaf, floor respected (mindiff %s)' % (sh_, hh, md))
    sig, err = gp_sigma(f, 3)
    chk('GP', sig == [(6, 2)],
        'PARI C1 member sigma %s (%s)' % (sig, err))
    say('  P2-5 PARI sigma: %s = {(6,2)} (honest truth; the '
        'shadow hull would misprice it)' % sig)

    # ---- P2-6: floor sweep ----
    rng = random.Random(20260810)
    nfloor = 0
    for trial in range(40):
        f = ppow(F.PHI2, 3)
        for j in range(3):
            if rng.random() < 0.8:
                # random slot monomial weakly above the side
                side = (3 - j) * F.E2
                v = (side + rng.randrange(0, 7) + 1) // 2 + 1
                a = rng.randrange(0, 2)
                b = rng.randrange(0, 2)
                c = rng.choice([1, 2, -1, 4]) * 3 ** v
                g = pmul([c], pmul([0, 1] if a else [1],
                                   ppow(F.PHIP, b)))
                if F.pin_of(g) is not None and \
                   F.pin_of(g) >= side:
                    f = padd(f, pmul(g, ppow(F.PHI2, j)))
        C, _ = honest_coords(F, f)
        Sh, _ = shadow_coords(F, f)
        md = mindiff(F, C, Sh)
        for j in range(3):
            ok = md[j] is None or (md[j] >= F.TH[j] and
                                   md[j] > (3 - j) * F.E2)
            chk('FLOOR', ok, 'sweep %d j%d md %s' % (trial, j, md))
            nfloor += 1
    say('  P2-6 floor sweep: %d coordinate checks, floor + entry '
        'margin hold' % nfloor)

    # ---- P2-7: PARI frame facts (corrected vs naive key) ----
    sig, err = gp_sigma(FR2C1.PHI2, 3)
    chk('GP', sig == [(2, 2)],
        'corrected key sigma %s (%s)' % (sig, err))
    naive = padd(padd(pmul(PHIP_C1, PHIP_C1), pmul([0, 3], PHIP_C1)),
                 [54])
    sig2, err2 = gp_sigma(naive, 3)
    chk('GP', sig2 == [(4, 1)],
        'naive key sigma %s (%s)' % (sig2, err2))
    say('  P2-7 PARI: corrected key sigma %s = {(2,2)} = '
        '(e1e2, f1f2) carrier; gauge-NAIVE key sigma %s = {(4,1)} '
        'NOT a carrier -- the compound frame is meaningful only at '
        'the corrected key (erratum 59c1966)' % (sig, sig2))

    # ---- P2-8: top boundary j = mu2 ----
    F = FR2C1
    f = ppow(F.PHI2, 3)
    C, top = honest_coords(F, f)
    Sh, shtop = shadow_coords(F, f)
    chk('TOP', top == [1], 'honest top %s' % top)
    chk('TOP', len(shtop) == 1 and shtop[0] == [1],
        'shadow top %s' % shtop)
    say('  P2-8 j = mu2 top: both routes carry the monic 1 '
        '(trivial agreement; the theorem correctly scopes j < mu2)')

    # ---- P2-9: delta = 0 corner arithmetic ----
    bad = 0
    for e1 in (2, 3, 4):
        for f1 in (1, 2, 3):
            for h in (1, 3, 5):
                if h % e1 == 0 and e1 > 1:
                    continue
                for e2 in (1, 2, 3):
                    for f2 in (1, 2, 3):
                        u2 = e2 * e1 * f1 * h   # delta = 0
                        for t in range(f2):
                            if (u2 * (f2 - t)) % e1 != 0:
                                bad += 1
    chk('D0', bad == 0, 'delta=0 i(m_t) != 0 cases: %d' % bad)
    say('  P2-9 delta = 0 corner: i(m_t) = 0 across the whole '
        'grid (delta = 0 => u2 = e2*D\'*h == 0 mod e1) -- at '
        'f1 = 1 every delta = 0 genre is x-free, the geography '
        'trivializes; the corner is fenced by [r1] AND carries no '
        'attainment content at f1 = 1')

    # ---- TEETH ----
    teeth = 0
    # T2-UP
    F = FR2C1
    Sh, _ = shadow_coords(F, ppow(F.PHI2, 3))
    up = [t + 1 for t in F.TH]
    kills = sum(1 for j in range(3) if F.pin_of(Sh[j]) < up[j])
    chk('TEETH', kills == 3, 'T2-UP kills %d' % kills)
    if kills == 3:
        teeth += 1
        say('tooth T2-UP fired x3 (THETA+1 mutant killed at all '
            'three attained pins)')
    # T2-DOWN
    down = [t - 1 for t in F.TH]
    f = padd(ppow(F.PHI2, 3), [3 ** 9])
    C, _ = honest_coords(F, f)
    Sh, _ = shadow_coords(F, f)
    md = mindiff(F, C, Sh)
    # mutant claims unfaithfulness possible at height 18 = down[0];
    # measured: no divergence below 19 anywhere in this run
    chk('TEETH', md[0] == 19 > down[0], 'T2-DOWN md %s' % md)
    if md[0] == 19:
        teeth += 1
        say('tooth T2-DOWN fired (THETA-1 mutant refuted: the '
            'height-18 digit is faithful, first divergence 19)')
    # T2-CL
    F = FRM3
    f = padd(ppow(F.PHI2, 3), [32])
    C, _ = honest_coords(F, f)
    Sh, _ = shadow_coords(F, f)
    ok = (hull(F, [F.pin_of(c) for c in C]) ==
          hull(F, [F.pin_of(s) for s in Sh]) and
          F.digit_at(C[0], 10) == F.digit_at(Sh[0], 10))
    chk('TEETH', ok, 'T2-CL')
    if ok:
        teeth += 1
        say('tooth T2-CL fired (the "entire delta = 1 leaf '
            'population mislabeled" reading killed by the '
            'correctly-read THETA-reaching leaf member)')

    say('=== VERDICT: %s -- %d checks, %d violations ===' %
        ('GREEN' if NBAD == 0 else 'RED', NCHK, NBAD))
    say('tally: %s  teeth: %d/3' % (TALLY, teeth))
    return 0 if NBAD == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
