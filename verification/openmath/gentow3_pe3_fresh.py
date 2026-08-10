#!/usr/bin/env python3
"""GENTOW3 passPE3 FRESH INSTRUMENT (hostile verifier, 2026-08-10).
Own primitives (dict-based polynomials, own division loops), frames
DISJOINT from PE1's (FR-M3 sweeps/FR-D5/FR-GL) and PE2's (FR2-C1,
delta=0, j=mu2 top): the new frame is FR3-B7; FR-M3 appears only as
(a) a replication/decorrelation row and (b) the site of the NEW
witness family W (entry-digit-driven failure at exactly THETA_0 at
the certificate-cancelled coordinate -- the passPE3 F-1 machine
face).

FRAMES
  FR3-B7: p=2, Phi'=x^2-2 (e1=2, f1=1, h=1, eta=1), e2=1, f2=2,
    u2=9, mu2=2, Phi2 = Phi'^2 - 16x Phi' - 512
    = x^4 - 16x^3 - 4x^2 + 32x - 508.
    delta = 9 - 1*2*1 = 7 (> 5: largest delta in any leg; battery
    max 3, PE1 max 5), E2 = 18, THETA = (43, 25), mu1 = 4.
    First frame with the key-power certificate LIVE at an INTERIOR
    coordinate (0 < j=1 < mu2) with a TWO-SLOT witness, and first
    delta >= 2 frame with a both-coordinate fake (band rows must
    keep the fake (1, THETA_1) point OFF their hulls).
  FR-M3: p=2, Phi'=x^2-2, e2=f2=1, u2=3, mu2=3,
    Phi2 = x^2-2x-2 = Phi' - 2x; delta=1, E2=3, THETA=(10,7,4).
    Key-power certificate CANCELLED at j=0 (committed PE1 value:
    ShC_0 = 64, pin 12 > 10, height-10 digit ZERO).

PREREGISTERED PREDICTIONS (sealed before the first run; every
displayed value hand-derived first -- the FR3-B7 self-shadow on two
independent paper routes: direct two-variable division AND the
identity F == K2(x,Y)^2 + 256*Y^3 mod (x^2-2); the W-witness
discrepancy sign-checked by hand: D_0(g) = -32 from the -16x^2
overflow at the last division step):
 P3-1 (SELF-B7): f = Phi2^2 honest DRAIN; shadow EXACTLY
   ShC_0 = 2^18*Phi' + 2^21*x   (slots 45/43, pin 43 = THETA_0)
   ShC_1 = 2^8*Phi'  + 2^12*x   (slots 25/25, pin 25 = THETA_1,
                                 BOTH slots at THETA_1);
   the ShC_1 Phi'-digit 2^8 = (chat_{t*})^2 * pi^{2a_9}
   (a_9 = 4) = GENTOW6's CERT-TOP display, independent
   corroboration.
 P3-2 (REP-M3, decorrelation): key-power self-shadow EXACTLY
   [[64], [0,40], [12]], pins [12,7,4] vs THETA [10,7,4]; the
   j=0 height-10 slot digit is ZERO (certificate cancelled --
   checked in-run, this is T3-BICOND's precondition).
 P3-3 (REP-P32): f = Phi2^3 + 32 at FR-M3: honest pins
   [10,None,None], shadow pins [10,7,4], mindiff [12,7,4]; fake
   pins (1,7),(2,4) STRICTLY above the deciding edge (line values
   20/3, 10/3); vertex residues mod 2 equal (96 vs 32 -> 1 = 1);
   PARI sigma {(6,1)}. (The S4/S7.6 counter-member, replicated on
   my primitives.)
 P3-4 (W, the F-1 witness family): g = 2x*Phi2^2 + 8*Phi2 (+64):
   W-A = Phi2^3 + g: gate TRUE, honest pins [None,6,3], shadow
   [10,6,3], ShC_0 = 32 exactly, mindiff [10,9,4]:
   mindiff_0 = 10 = THETA_0 EXACTLY at the cancelled coordinate.
   W-B = W-A + 64: gate TRUE, nondegenerate (PARI sigma
   {(2,1),(2,2)}); honest pins [12,6,3], shadow [10,6,3],
   ShC_0 = 96, C_0 = 64, discrepancy = 32 at height 10 exactly;
   the shadow undercuts the honest deciding vertex (0,12)->(0,10)
   (first-edge slope 6 -> 4). Witness SEARCH (the design-phase
   sweep re-run in-code, deterministic): over g = sum of <= 3
   on-side slot monomials from {2x@j2, 8@j1, 16x@j0} with units
   {1,-1,3,-3}, EXACTLY 32 gated members have mindiff_0 == 10.
 P3-5 (BAND-B7, width-6 faithful leaf band sampled at 3 heights):
   f = Phi2^2 + 2^18*x / 2^19*x / 2^20*x: honest pins (37/39/41,
   None) tRAM; shadow pins (same, 25) with the fake (1,25)
   strictly above the deciding edge: identical hulls and labels;
   mindiff_0 = 43, mindiff_1 = 25 (>= THETA, never consulted);
   height-42 slot digits agree on both reads (T3-DOWN face);
   PARI sigma {(4,2)} each.
 P3-6 (DIV-B7, first violation at exactly 43): DIV43 = Phi2^2 -
   2^21*x: honest (43,None) tRAM(43), shadow ShC_0 = 2^18*Phi'
   EXACTLY (pin 45), mindiff_0 = 43 = THETA_0: pin-stratum
   corrupted, sigma intact {(4,2)} (parity luck at delta=7).
   CANC = Phi2^2 - (2^18*Phi' + 2^21*x as x-poly): honest
   (43,None) tRAM(43) PARI {(4,2)}; shadow ShC_0 IDENTICALLY 0,
   shadow pins (None,25): the sharpest shadow-not-a-function-of-
   honest-data witness at delta=7; mindiff_0 = 43.
 P3-7 (FLOOR/ENTRY sweeps, seeded RNG 20260810): 60 gated random
   members at FR3-B7 (2 coords) + 25 at FR-M3 (3 coords): every
   mindiff_j is None or >= THETA_j (FLOOR) and > (mu2-j)*E2
   (ENTRY, COR 3.C face).
 P3-8 (GP, dual oracle, 8 jobs): EFB7 {(2,2)} carrier; F37/F39/
   F41/DIV43/CANC {(4,2)}; WB {(2,1),(2,2)}; P32 {(6,1)}.
TEETH (all three must fire):
 T3-UP: the THETA+1 mutant is killed by every measured
   attainment: SELF-B7 pins 43/25, REP-M3 pins 7/4 (j=1,2), W-A/
   W-B mindiff_0 = 10, DIV43/CANC mindiff_0 = 43: >= 6 kills.
 T3-DOWN: the THETA-1 mutant (first violation allowed at 42 at
   FR3-B7 j=0) is refuted: all five constructed THETA-exact/band
   rows have zero discrepancy content at height 42 (slot digits
   equal) and the measured first violations sit at 43 exactly;
   PARI confirms the band rows' sigma.
 T3-BICOND: the reading "failure AT THETA_j occurs ONLY at
   coordinates carrying (iv)'s certificate" (the corrected S0
   clause's only-if) is KILLED: at (FR-M3, j=0) the key power's
   height-10 digit is 0 (P3-2, certificate cancelled) AND W-A/W-B
   have mindiff_0 = 10 = THETA_0 (P3-4): fires x2.
DESIGN SMOKE (disclosed): a design script (own primitives, same
algebra) ran the FR3-B7 self-shadow (matched the hand derivation),
the FR-M3 replication, the witness search (32 hits, first
displayed variants), and one gp batch fixing the exact sigma wants
above; no prediction was changed after sealing this docstring.
Verdict: GREEN iff 0 violations and 3/3 teeth.
Written 2026-08-10 by the GENTOW3 passPE3 verifier.
"""

import itertools
import random
import subprocess
import sys

# ---------------- primitives (own, dict-based) ----------------------


def pnorm(d):
    return {k: v for k, v in d.items() if v}


def padd(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, 0) + v
    return pnorm(c)


def psub(a, b):
    return padd(a, {k: -v for k, v in b.items()})


def pmul(a, b):
    c = {}
    for i, u in a.items():
        for j, w in b.items():
            c[i + j] = c.get(i + j, 0) + u * w
    return pnorm(c)


def pconst(n):
    return pnorm({0: n})


def deg(a):
    return max(a) if a else -1


def pdivmod(f, g):
    q, r = {}, dict(f)
    dg = deg(g)
    assert g.get(dg, 0) == 1
    while r and deg(r) >= dg:
        d = deg(r)
        c = r[d]
        q[d - dg] = q.get(d - dg, 0) + c
        for j, w in g.items():
            r[d - dg + j] = r.get(d - dg + j, 0) - c * w
        r = pnorm(r)
    return pnorm(q), pnorm(r)


def ppow(f, n):
    r = pconst(1)
    for _ in range(n):
        r = pmul(r, f)
    return r


def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def dev(f, key, n):
    A, g = [], dict(f)
    for _ in range(n):
        g, r = pdivmod(g, key)
        A.append(r)
    return A, g


class Frame:
    def __init__(s, name, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        s.name, s.p, s.PHI1, s.h = name, p, PHI1, h
        s.e1, s.e2, s.f2, s.mu2, s.u2 = e1, e2, f2, mu2, u2
        s.PHI2 = PHI2
        s.Dp, s.D2 = deg(PHI1), deg(PHI2)
        s.mu1 = e2 * f2 * mu2
        s.E2 = e2 * f2 * u2
        s.delta = u2 - e2 * s.Dp * h
        s.ee = e1 * e2

    def theta(s, j):
        return (s.mu2 - j) * s.E2 + s.delta

    def slots(s, C):
        """[(height, digit-coeff, a, b)] of coefficient C."""
        if not C:
            return []
        gs, top = dev(C, s.PHI1, s.e2 * s.f2)
        assert not top, 'slot overflow'
        out = []
        for b, g in enumerate(gs):
            for a, c in g.items():
                out.append((s.ee * vp(c, s.p) + a * s.e2 * s.h
                            + b * s.u2, c, a, b))
        return sorted(out)

    def pin(s, C):
        sl = s.slots(C)
        return sl[0][0] if sl else None

    def digit_at(s, C, ht):
        return sorted((a, b, c) for (m, c, a, b) in s.slots(C)
                      if m == ht)


def honest(F, f):
    Cs, top = dev(f, F.PHI2, F.mu2)
    assert top == {0: 1}
    return Cs


def shadow(F, f):
    A, top = dev(f, F.PHI1, F.mu1)
    assert top == {0: 1}
    K2c, kt = dev(F.PHI2, F.PHI1, F.e2 * F.f2)
    assert kt == {0: 1}
    e = F.e2 * F.f2
    red = lambda c: pdivmod(c, F.PHI1)[1]
    P = [red(a) for a in A] + [pconst(1)]
    out = []
    for _ in range(F.mu2):
        R = [dict(c) for c in P]
        Q = [{} for _ in range(max(1, len(P) - e))]
        for i in range(len(R) - 1, e - 1, -1):
            c = pnorm(R[i])
            R[i] = {}
            if not c:
                continue
            Q[i - e] = padd(Q[i - e], c)
            for b in range(e):
                R[i - e + b] = red(psub(R[i - e + b],
                                        pmul(c, K2c[b])))
        C = {}
        for b in range(e):
            C = padd(C, pmul(pnorm(R[b]), ppow(F.PHI1, b)))
        out.append(C)
        P = [pnorm(q) for q in Q]
    assert P == [pconst(1)]
    return out


def gate(F, f):
    A, top = dev(f, F.PHI1, F.mu1)
    if top != {0: 1}:
        return False
    for J, a in enumerate(A):
        if not a:
            if J == 0:
                return False
            continue
        dv = min(F.e1 * vp(c, F.p) + i * F.h for i, c in a.items())
        if F.e2 * dv < (F.mu1 - J) * F.u2:
            return False
        if J == 0 and F.e2 * dv != F.mu1 * F.u2:
            return False
    return True


def mindiff(F, f, hs=None, ss=None):
    hs = hs or honest(F, f)
    ss = ss or shadow(F, f)
    return [F.pin(psub(ss[j], hs[j])) for j in range(F.mu2)]


# ---------------- harness -------------------------------------------
NCHK = 0
NBAD = 0
TEETH = {'T3-UP': 0, 'T3-DOWN': 0, 'T3-BICOND': 0}


def chk(tag, ok, msg):
    global NCHK, NBAD
    NCHK += 1
    if not ok:
        NBAD += 1
        print('VIOLATION [%s] %s' % (tag, msg))


def say(m):
    print(m)
    sys.stdout.flush()


# ---------------- frames --------------------------------------------
PHI1 = pnorm({2: 1, 0: -2})
B7 = Frame('FR3-B7', 2, PHI1, 1, 2, 1, 2, 2, 9,
           padd(psub(ppow(PHI1, 2), pmul(pnorm({1: 16}), PHI1)),
                pconst(-512)))
M3 = Frame('FR-M3', 2, PHI1, 1, 2, 1, 1, 3, 3,
           pnorm({2: 1, 1: -2, 0: -2}))
assert (B7.delta, B7.E2, B7.theta(0), B7.theta(1)) == (7, 18, 43, 25)
assert (M3.delta, M3.E2, M3.theta(0), M3.theta(2)) == (1, 3, 10, 4)

# ---------------- gp plumbing ---------------------------------------
GP_JOBS, GP_META = [], {}


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i)
                    for i, c in sorted(f.items())) or '0'


def gp_sig(tag, f, p, want):
    GP_JOBS.append('print("%s ", sig(%s, %d))'
                   % (tag, poly_str(f), p))
    GP_META[tag] = sorted(want)


def sig_parse(s):
    n = [int(t) for t in s.replace('[', ' ').replace(']', ' ')
         .replace(',', ' ').split()]
    return sorted((n[i], n[i + 1]) for i in range(0, len(n), 2))


def resolve_gp():
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
                         capture_output=True, text=True,
                         timeout=1800)
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0] in GP_META:
            res[parts[0]] = parts[1].strip()
    for tag, want in GP_META.items():
        if tag not in res:
            chk('GP', False, 'missing %s' % tag)
            continue
        got = sig_parse(res[tag])
        chk('GP', got == want, '%s got %s want %s'
            % (tag, got, want))


# ---------------- P3-1 SELF-B7 --------------------------------------
say('== P3-1 SELF-B7 ==')
fkB = ppow(B7.PHI2, 2)
hsB = honest(B7, fkB)
chk('SELF', all(not c for c in hsB), 'B7 honest not DRAIN')
ssB = shadow(B7, fkB)
WANT0 = padd(pmul(pconst(2 ** 18), PHI1), pnorm({1: 2 ** 21}))
WANT1 = padd(pmul(pconst(2 ** 8), PHI1), pnorm({1: 2 ** 12}))
chk('SELF', ssB[0] == WANT0, 'ShC_0 %s' % sorted(ssB[0].items()))
chk('SELF', ssB[1] == WANT1, 'ShC_1 %s' % sorted(ssB[1].items()))
chk('SELF', [h for h, _c, _a, _b in B7.slots(ssB[0])] == [43, 45],
    'ShC_0 slot heights')
chk('SELF', [h for h, _c, _a, _b in B7.slots(ssB[1])] == [25, 25],
    'ShC_1 slot heights (both at THETA_1, interior j)')
for j in range(2):
    pn = B7.pin(ssB[j])
    chk('SELF', pn == B7.theta(j),
        'B7 self pin_%d %s != THETA' % (j, pn))
    if pn == B7.theta(j):
        TEETH['T3-UP'] += 1
say('  ShC_0 = 2^18*Phi\' + 2^21*x (pin 43); '
    'ShC_1 = 2^8*Phi\' + 2^12*x (pin 25, both slots)')

# ---------------- P3-2 REP-M3 ---------------------------------------
say('== P3-2 REP-M3 ==')
fkM = ppow(M3.PHI2, 3)
hsM = honest(M3, fkM)
chk('REP', all(not c for c in hsM), 'M3 honest not DRAIN')
ssM = shadow(M3, fkM)
chk('REP', ssM[0] == pconst(64) and ssM[1] == pnorm({1: 40})
    and ssM[2] == pconst(12),
    'M3 self-shadow %s' % [sorted(c.items()) for c in ssM])
chk('REP', [M3.pin(c) for c in ssM] == [12, 7, 4], 'M3 pins')
CERT10 = M3.digit_at(ssM[0], 10)
chk('REP', CERT10 == [],
    'M3 j=0 height-10 digit not cancelled: %s' % CERT10)
for j in (1, 2):
    if M3.pin(ssM[j]) == M3.theta(j):
        TEETH['T3-UP'] += 1

# ---------------- P3-3 REP-P32 --------------------------------------
say('== P3-3 REP-P32 ==')
f32 = padd(fkM, pconst(32))
hs, ss = honest(M3, f32), shadow(M3, f32)
chk('REP', [M3.pin(c) for c in hs] == [10, None, None],
    'P32 honest pins')
chk('REP', [M3.pin(c) for c in ss] == [10, 7, 4],
    'P32 shadow pins')
chk('REP', mindiff(M3, f32, hs, ss) == [12, 7, 4], 'P32 mindiff')
chk('REP', 3 * 7 > 20 and 3 * 4 > 10,
    'fake pins strictly above the (0,10)-(3,0) edge')
h10 = M3.digit_at(hs[0], 10)
s10 = M3.digit_at(ss[0], 10)
chk('REP', len(h10) == 1 and len(s10) == 1 and
    (h10[0][2] // 32) % 2 == (s10[0][2] // 32) % 2,
    'vertex residues differ: %s vs %s' % (h10, s10))
gp_sig('P32', f32, 2, [(6, 1)])

# ---------------- P3-4 the W witness family -------------------------
say('== P3-4 W (entry-driven failure AT THETA_0, certificate-'
    'cancelled coordinate) ==')
gW = padd(pmul(pnorm({1: 2}), ppow(M3.PHI2, 2)),
          pmul(pconst(8), M3.PHI2))
WA = padd(fkM, gW)
WB = padd(WA, pconst(64))
for tag, f, wanth, wantS0, wantC0 in (
        ('W-A', WA, [None, 6, 3], pconst(32), {}),
        ('W-B', WB, [12, 6, 3], pconst(96), pconst(64))):
    chk('WIT', gate(M3, f), '%s fails the gate' % tag)
    hs, ss = honest(M3, f), shadow(M3, f)
    chk('WIT', [M3.pin(c) for c in hs] == wanth,
        '%s honest pins %s' % (tag, [M3.pin(c) for c in hs]))
    chk('WIT', [M3.pin(c) for c in ss] == [10, 6, 3],
        '%s shadow pins %s' % (tag, [M3.pin(c) for c in ss]))
    chk('WIT', ss[0] == wantS0 and hs[0] == pnorm(wantC0),
        '%s ShC_0/C_0 %s / %s'
        % (tag, sorted(ss[0].items()), sorted(hs[0].items())))
    md = mindiff(M3, f, hs, ss)
    chk('WIT', md == [10, 9, 4], '%s mindiff %s' % (tag, md))
    if md[0] == M3.theta(0):
        TEETH['T3-UP'] += 1
        if CERT10 == []:
            TEETH['T3-BICOND'] += 1
say('  W-B: honest deciding vertex (0,12), shadow (0,10) -- '
    'first-edge slope 6 -> 4, mislabel AT THETA_0 = 10 where the '
    'key-power certificate CANCELS')
gp_sig('WB', WB, 2, [(2, 1), (2, 2)])

# witness search (design sweep re-run, deterministic)
sing = [(2, 1, 1), (1, 0, 3), (0, 1, 4)]        # (j, a, vp)
units = [1, -1, 3, -3]
nfound = 0
for L in (1, 2, 3):
    for pick in itertools.combinations_with_replacement(sing, L):
        for us in itertools.product(units, repeat=L):
            g = {}
            for (j, a, v), u in zip(pick, us):
                g = padd(g, pmul(pnorm({a: u * 2 ** v}),
                                 ppow(M3.PHI2, j)))
            f = padd(fkM, g)
            if gate(M3, f) and mindiff(M3, f)[0] == 10:
                nfound += 1
chk('WIT', nfound == 32,
    'witness census %d != 32 (genericity)' % nfound)
say('  witness census: %d gated members with mindiff_0 == 10'
    % nfound)

# ---------------- P3-5 BAND-B7 --------------------------------------
say('== P3-5 BAND-B7 (width-6 faithful leaf band) ==')
BANDROWS = []
for k, pinw in ((18, 37), (19, 39), (20, 41)):
    f = padd(fkB, pnorm({1: 2 ** k}))
    hs, ss = honest(B7, f), shadow(B7, f)
    chk('BAND', [B7.pin(c) for c in hs] == [pinw, None],
        'h%d honest pins' % pinw)
    chk('BAND', [B7.pin(c) for c in ss] == [pinw, 25],
        'h%d shadow pins' % pinw)
    chk('BAND', 2 * 25 > pinw,
        'h%d fake (1,25) not above the edge' % pinw)
    md = mindiff(B7, f, hs, ss)
    chk('BAND', md == [43, 25], 'h%d mindiff %s' % (pinw, md))
    d42 = (B7.digit_at(ss[0], 42), B7.digit_at(hs[0], 42))
    chk('BAND', d42[0] == d42[1],
        'h%d height-42 digits differ' % pinw)
    BANDROWS.append(d42[0] == d42[1])
    gp_sig('F%d' % pinw, f, 2, [(4, 2)])

# ---------------- P3-6 DIV-B7 ---------------------------------------
say('== P3-6 DIV-B7 (first violation at exactly 43) ==')
D43 = psub(fkB, pnorm({1: 2 ** 21}))
hs, ss = honest(B7, D43), shadow(B7, D43)
chk('DIV', [B7.pin(c) for c in hs] == [43, None], 'DIV43 honest')
chk('DIV', ss[0] == pmul(pconst(2 ** 18), PHI1)
    and B7.pin(ss[0]) == 45, 'DIV43 ShC_0')
md = mindiff(B7, D43, hs, ss)
chk('DIV', md == [43, 25], 'DIV43 mindiff %s' % md)
d42 = (B7.digit_at(ss[0], 42), B7.digit_at(hs[0], 42))
chk('DIV', d42[0] == d42[1], 'DIV43 height-42 digit')
BANDROWS.append(d42[0] == d42[1])
divkills = [md[0] == 43]
gp_sig('DIV43', D43, 2, [(4, 2)])

S0poly = padd(pmul(pconst(2 ** 18), PHI1), pnorm({1: 2 ** 21}))
CANC = psub(fkB, S0poly)
hs, ss = honest(B7, CANC), shadow(B7, CANC)
chk('DIV', [B7.pin(c) for c in hs] == [43, None], 'CANC honest')
chk('DIV', ss[0] == {} and [B7.pin(c) for c in ss] == [None, 25],
    'CANC shadow (j=0 coordinate must be identically zero)')
md = mindiff(B7, CANC, hs, ss)
chk('DIV', md == [43, 25], 'CANC mindiff %s' % md)
d42 = (B7.digit_at(ss[0], 42), B7.digit_at(hs[0], 42))
chk('DIV', d42[0] == d42[1], 'CANC height-42 digit')
BANDROWS.append(d42[0] == d42[1])
divkills.append(md[0] == 43)
gp_sig('CANC', CANC, 2, [(4, 2)])
for k in divkills:
    if k:
        TEETH['T3-UP'] += 1
if all(BANDROWS) and all(divkills):
    TEETH['T3-DOWN'] += len(BANDROWS)

# ---------------- P3-7 FLOOR/ENTRY sweeps ---------------------------
say('== P3-7 FLOOR/ENTRY sweeps ==')
random.seed(20260810)


def rand_member(F):
    for _ in range(200):
        f = ppow(F.PHI2, F.mu2)
        for j in range(F.mu2):
            for a in range(F.Dp):
                for b in range(F.e2 * F.f2):
                    if random.random() < 0.6:
                        need = (F.mu2 - j) * F.E2 - a * F.e2 * F.h \
                            - b * F.u2
                        v = max(0, -(-need // F.ee)) \
                            + random.randrange(0, 4)
                        u = random.choice([1, -1, 3, -3])
                        mono = pmul(pnorm({a: u * F.p ** v}),
                                    pmul(ppow(F.PHI1, b),
                                         ppow(F.PHI2, j)))
                        f = padd(f, mono)
        if gate(F, f):
            return f
    raise RuntimeError('no member found')


for F, nmem in ((B7, 60), (M3, 25)):
    for _ in range(nmem):
        f = rand_member(F)
        md = mindiff(F, f)
        for j in range(F.mu2):
            chk('FLOOR', md[j] is None or md[j] >= F.theta(j),
                '%s mindiff_%d = %s < THETA' % (F.name, j, md[j]))
            chk('ENTRY', md[j] is None
                or md[j] > (F.mu2 - j) * F.E2,
                '%s mindiff_%d = %s inside entry band'
                % (F.name, j, md[j]))

# ---------------- GP + verdict --------------------------------------
gp_sig('EFB7', B7.PHI2, 2, [(2, 2)])
resolve_gp()

say('teeth: %s' % TEETH)
ok_teeth = (TEETH['T3-UP'] >= 6 and TEETH['T3-DOWN'] >= 5
            and TEETH['T3-BICOND'] >= 2)
if not ok_teeth:
    chk('TEETH', False, 'teeth did not all fire: %s' % TEETH)
else:
    NCHK += 3
say('=== VERDICT: %s -- %d checks, %d violations, teeth %s ==='
    % ('GREEN' if (NBAD == 0 and ok_teeth) else 'RED',
       NCHK, NBAD, '3/3' if ok_teeth else 'MISSING'))
sys.exit(0 if (NBAD == 0 and ok_teeth) else 1)
