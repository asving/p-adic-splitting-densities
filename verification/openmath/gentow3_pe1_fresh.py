#!/usr/bin/env python3
"""GENTOW3 passPE1 FRESH ROUTE (hostile verifier's independent
instrument, 2026-08-10).  Primitives written from scratch (NOT
imported from gentow1_checks/gentow3_checks); frames chosen to
stress THETA_j = (mu2-j)*E2 + delta OUTSIDE the sealed battery.

FRAMES (none in the sealed battery):
  FR-M3  mu2 = 3 (battery is mu2 = 2 only), e2f2 = 1 (identity
         Phi'-carrier: every Phi'-overflow recarries instantly):
         p = 2, Phi' = x^2-2 (e1 = 2, f1 = 1, h = 1), e2 = f2 = 1,
         u2 = 3, Phi2 = Phi' - 2x = x^2 - 2x - 2, mu1 = 3, n = 6.
         delta = 1, E2 = 3, THETA = (10, 7, 4).
  FR-D5  delta = 5 (battery max is 3): p = 2, Phi' = x^2-2,
         e2 = 2, f2 = 1, u2 = 9 (> e2D'h = 4), Phi2 = Phi'^2-16x,
         mu2 = 2, n = 8.  E2 = 18, THETA = (41, 23); node floor 37;
         predicted faithful leaf band [37, 40] of width 4 = delta-1.
  FR-GL  gauge-live eta != 1 (battery is eta = 1 blind): p = 3,
         Phi' = x^2-6, eta = 2, e2 = 1, f2 = 2, u2 = 3, K2 = F9,
         CORRECTED key Phi2 = Phi'^2 + 3x*Phi' + 108 (the GENTOW1
         PE1/HETOW frame-X key, chat_t = lift(c_t*eta^W(t))).
         delta = 1, E2 = 6, THETA = (13, 7).

PREREGISTERED PREDICTIONS (hand-derived before this run):
 FR-P1 (self-shadows, exact polynomial values):
   FR-M3: honest DRAIN; ShC = [64, 40x, 12], pins [12, 7, 4] vs
     THETA [10, 7, 4] -- floor holds everywhere, ATTAINED at
     j = 1, 2, slack (12 > 10) at j = 0.
   FR-D5: honest DRAIN; ShC = [256*Phi', 0], pins [41, None],
     41 = THETA_0 ATTAINED.
   FR-GL: honest DRAIN; ShC_0 = -486*Phi' + 2916x (pin 13 =
     THETA_0), ShC_1 = 9*Phi' - 27x (pin 7 = THETA_1) -- BOTH
     attained, each digit two-flavored (f2 = 2).
 FR-P2 (floors): ~30 random in-budget members per frame: per
   coordinate j, mindiff_j is None or >= THETA_j; also
   > (mu2-j)*E2 (entry band clean).  Level-1 side gate spot-checked
   on 3 members per frame (pins weakly above the inner side,
   endpoint exact).
 FR-P3 (FR-D5 faithful band, delta - 1 = 4 wide): single-pin
   members at p_0 = 37, 38, 39, 40 and the (40, 19) 2SIDED member:
   shadow digit strings identical (mindiff None or >= 41), labels
   equal; PARI sigma on the decided rows: 37/39 tRAM {(8,1)},
   (40,19) t2SIDED {(4,1),(4,1)}.
 FR-P4 (THETA-attainment interference rows):
   FR-D5 cancel41: f = Phi2^2 - 256*Phi': honest tRAM(41) sigma
     {(8,1)} (PARI); shadow C_0 = 0 IDENTICALLY (the fake digit
     cancels the honest one: shadow blind at j = 0).
   FR-D5 add41: f = Phi2^2 + 256*Phi': honest tRAM(41); shadow
     pin 45; mindiff = 41 = THETA_0 exactly.
   FR-M3 cancel7: f = Phi2^3 - 40x*Phi2: honest p_1 = 7; shadow
     ShC_1 = 80 (pin 8) -- shadow blind to the honest pin at
     THETA_1; mindiff_1 = 7.
   FR-GL anchor13: f = Phi2^2 + 729x: honest tRAM(13) sigma
     {(4,2)} (PARI); shadow pin also 13 but DIFFERENT digit
     (mindiff_0 = 13 = THETA_0).
 FR-P5 (battery digit replication, closing the note's
   "machine-checked digits" attribution): self-shadow VALUES at
   the five sealed families equal the note's displayed digits:
   A5: ShC_0 = 16*Phi'; A7: ShC_0 = 64*Phi'; C: ShC_0 = 64*Phi';
   B: ShC_0 = 64*Phi' + 64x, ShC_1 = 4*Phi' + 8x; D: DRAIN.
 FR-P6 (PARI frame facts): ef(Phi2) = {(2,1)} at FR-M3 and
   {(4,1)} at FR-D5 and {(2,2)} at FR-GL (carrier (e1e2, f1f2)).
TEETH (all must fire):
 T-F-UP: the THETA+1 mutant is killed by >= 5 attained pins
   (FR-M3 j=1,2; FR-D5 j=0; FR-GL j=0,1).
 T-F-DOWN: the THETA-1 mutant calls FR-D5 height 40 unfaithful;
   the (40,19) row shows agreement + PARI sigma: refuted.
 T-F-CANCEL: cancel41 -- honest DECIDED tRAM(41) PARI-confirmed
   while the shadow j=0 coordinate is IDENTICALLY ZERO: kills any
   reading in which the shadow read at >= THETA is a function of
   the honest data.
Verdict: GREEN iff 0 violations and 3/3 teeth.
"""
import random
import subprocess
import sys
import time

random.seed(20260810)
T0 = time.time()
VIOL = []
NCHK = {}
TEETH = {'T-F-UP': 0, 'T-F-DOWN': 0, 'T-F-CANCEL': 0}
OUT = []


def say(s):
    print(s)
    sys.stdout.flush()
    OUT.append(s)


def chk(cat, ok, msg):
    NCHK[cat] = NCHK.get(cat, 0) + 1
    if not ok:
        VIOL.append('%s: %s' % (cat, msg))
        say('  !! VIOLATION %s: %s' % (cat, msg))


# ---------- polynomial primitives (own, low -> high int lists) -----
def pstrip(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return pstrip([(a[i] if i < len(a) else 0) +
                   (b[i] if i < len(b) else 0) for i in range(n)])


def psca(c, a):
    return pstrip([c * x for x in a])


def pmul(a, b):
    a, b = pstrip(a), pstrip(b)
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return pstrip(out)


def ppow(a, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, a)
    return r


def pdivmod(f, g):
    """monic g: exact integer division f = q*g + r."""
    f, g = pstrip(f), pstrip(g)
    assert g and g[-1] == 1
    q = [0] * max(1, len(f) - len(g) + 1)
    r = list(f)
    while len(r) >= len(g):
        c = r[-1]
        d = len(r) - len(g)
        q[d] += c
        for i, gc in enumerate(g):
            r[d + i] -= c * gc
        r = r[:-1]
        while r and r[-1] == 0:
            r.pop()
    return pstrip(q), pstrip(r)


def vp(n, p):
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def dev(f, key, nslots):
    """key-adic development: f = sum_{i<nslots} A_i key^i + top*key^nslots."""
    A, g = [], list(f)
    for _ in range(nslots):
        g, r = pdivmod(g, key)
        A.append(r)
    return A, g


# ---------- frame ---------------------------------------------------
class Fr:
    def __init__(self, name, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        self.name, self.p, self.PHI1, self.h = name, p, PHI1, h
        self.e1, self.e2, self.f2, self.mu2 = e1, e2, f2, mu2
        self.u2, self.PHI2 = u2, PHI2
        self.Dp = len(PHI1) - 1
        self.D2 = len(PHI2) - 1
        self.mu1 = e2 * f2 * mu2
        self.E2 = e2 * f2 * u2
        self.delta = u2 - e2 * self.Dp * h
        self.ee = e1 * e2

    def theta(self, j):
        return (self.mu2 - j) * self.E2 + self.delta

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def floor(self, j, a, b):
        s = (self.mu2 - j) * self.E2 - self.w(a, b)
        fl = -((-s) // self.ee)          # ceil
        if s >= 0 and s % self.ee == 0:
            fl += 1
        return fl

    def pin(self, C):
        """slot pin: min over Phi'-dev monomials of
        ee*v(c) + a*e2h + b*u2; None if C = 0."""
        C = pstrip(list(C))
        if not C:
            return None
        gs, top = dev(C, self.PHI1, self.e2 * self.f2)
        assert not pstrip(top), 'slot view overflow'
        m = None
        for b, g in enumerate(gs):
            for a, c in enumerate(g):
                if c:
                    ht = self.ee * vp(c, self.p) + self.w(a, b)
                    m = ht if m is None else min(m, ht)
        return m


def from_slots(F, digs):
    f = ppow(F.PHI2, F.mu2)
    for (j, a, b), c in digs.items():
        mono = pmul(pmul([0] * a + [1], ppow(F.PHI1, b)),
                    ppow(F.PHI2, j))
        f = padd(f, psca(c, mono))
    return f


# ---------- the two reads -------------------------------------------
def honest(F, f):
    Cs, g = dev(list(f), F.PHI2, F.mu2)
    assert g == [1], 'composed dev not monic'
    return Cs


def xred(F, c):
    return pdivmod(list(c), F.PHI1)[1]


def shadow(F, f):
    """level-1 dev -> iterated two-variable division by K2 with
    every coefficient reduced mod Phi' (the T(b)'(iv) object)."""
    A, top = dev(list(f), F.PHI1, F.mu1)
    assert top == [1], 'level-1 dev not monic'
    K2, ktop = dev(list(F.PHI2), F.PHI1, F.e2 * F.f2)
    assert ktop == [1]
    K2 = K2 + [[1]]
    e = F.e2 * F.f2
    P = [xred(F, a) for a in A] + [[1]]
    ShC = []
    for _ in range(F.mu2):
        Q = [[] for _ in range(max(1, len(P) - e))]
        R = [list(c) for c in P]
        for i in range(len(R) - 1, e - 1, -1):
            c = pstrip(R[i])
            if c:
                Q[i - e] = padd(Q[i - e], c)
                for b in range(e + 1):
                    R[i - e + b] = xred(F, padd(
                        R[i - e + b], psca(-1, pmul(c, K2[b]))))
        rem = [pstrip(r) for r in R[:e]]
        C = []
        for b, gb in enumerate(rem):
            C = padd(C, pmul(gb, ppow(F.PHI1, b)))
        ShC.append(C)
        P = [pstrip(q) for q in Q]
    assert [pstrip(q) for q in P] == [[1]], 'shadow quotient chain'
    return ShC


def mindiff(F, S, C):
    return F.pin(padd(list(S), psca(-1, C)))


# ---------- level-1 entry gate (independent T-membership check) ----
def level1_gate(F, f):
    A, top = dev(list(f), F.PHI1, F.mu1)
    if top != [1]:
        return False
    for J, a in enumerate(A):
        a = pstrip(a)
        if not a:
            continue
        dv = min(F.e1 * vp(c, F.p) + i * F.h
                 for i, c in enumerate(a) if c)
        if F.e2 * dv < (F.mu1 - J) * F.u2:
            return False
    a0 = pstrip(A[0])
    if not a0:
        return False
    dv0 = min(F.e1 * vp(c, F.p) + i * F.h for i, c in enumerate(a0)
              if c)
    return F.e2 * dv0 == F.mu1 * F.u2


# ---------- label reading (mu2 = 2, f1f2 = 1 tame trichotomy) ------
def label_p2(F, C0, C1):
    """p = 2, K2 = F2 read: enough for FR-D5's decided rows."""
    u, w_ = F.pin(C0), F.pin(C1)
    if u is None:
        return (u, w_, 'DRAIN')
    if w_ is None or u < 2 * w_:
        return (u, w_, 'tRAM' if u % 2 else 'tEVEN')
    if u > 2 * w_:
        return (u, w_, 't2SIDED')
    return (u, w_, 'tEQ')


# ---------- gp oracle ------------------------------------------------
GP_HDR = r"""
default(parisizemax, 2000000000);
ef1(g, p) = {
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  vecsort(vector(#dec, j, [dec[j].e, dec[j].f]))
}
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
"""
GP_JOBS, GP_META = [], {}


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


def gp_sig(tag, F, f, want, fun='sig1'):
    GP_JOBS.append('print("%s ", %s(%s, %d))'
                   % (tag, fun, poly_str(f), F.p))
    GP_META[tag] = want


def sig_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    n = [int(t) for t in s.split()]
    return sorted((n[i], n[i + 1]) for i in range(0, len(n), 2))


def resolve_gp():
    say('== PARI leg: %d jobs ==' % len(GP_JOBS))
    src = GP_HDR + '\n' + '\n'.join(GP_JOBS) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=1800)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-200:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    for tag, want in GP_META.items():
        if tag not in res:
            chk('GP', False, 'missing %s' % tag)
            continue
        got = sig_parse(res[tag])
        chk('GP', got == sorted(want),
            '%s got %s want %s' % (tag, got, sorted(want)))


# ---------- frames ---------------------------------------------------
P12 = [-2, 0, 1]                                     # x^2 - 2
FRM3 = Fr('FR-M3', 2, P12, 1, 2, 1, 1, 3, 3, [-2, -2, 1])
FRD5 = Fr('FR-D5', 2, P12, 1, 2, 2, 1, 2, 9,
          padd(pmul(P12, P12), [0, -16]))            # (x^2-2)^2-16x
P16 = [-6, 0, 1]                                     # x^2 - 6
PHI2GL = padd(padd(pmul(P16, P16), pmul([0, 3], P16)), [108])
FRGL = Fr('FR-GL', 3, P16, 1, 2, 1, 2, 2, 3, PHI2GL)

# battery frames (replication leg, constructed from GENTOW1 S1 data)
BA5 = Fr('FAM-A5', 2, P12, 1, 2, 2, 1, 2, 5,
         padd(pmul(P12, P12), [0, -4]))
BA7 = Fr('FAM-A7', 2, P12, 1, 2, 2, 1, 2, 7,
         padd(pmul(P12, P12), [0, -8]))
BB = Fr('FAM-B', 2, P12, 1, 2, 1, 2, 2, 3,
        padd(padd(pmul(P12, P12), pmul([0, -2], P12)), [-8]))
BC = Fr('FAM-C', 2, P12, 1, 2, 3, 1, 2, 7,
        padd(pmul(pmul(P12, P12), P12), [0, -8]))
P13 = [-3, 0, 1]
BD = Fr('FAM-D', 3, P13, 1, 2, 1, 2, 2, 3,
        padd(pmul(P13, P13), [27]))


# ---------- FR-P1: self-shadows -------------------------------------
def self_shadow(F, want):
    fk = ppow(F.PHI2, F.mu2)
    Cs = honest(F, fk)
    chk('SELF', all(not pstrip(c) for c in Cs),
        '%s honest not DRAIN' % F.name)
    Sh = shadow(F, fk)
    pins = [F.pin(c) for c in Sh]
    say('  %s self-shadow: ShC = %s pins %s THETA %s' %
        (F.name, [pstrip(c) for c in Sh], pins,
         [F.theta(j) for j in range(F.mu2)]))
    chk('SELF', [pstrip(c) for c in Sh] ==
        [pstrip(w) for w in want],
        '%s self-shadow values %s want %s' %
        (F.name, [pstrip(c) for c in Sh], want))
    for j, pn in enumerate(pins):
        chk('SELF', pn is None or pn >= F.theta(j),
            '%s self-shadow pin %s < THETA_%d' % (F.name, pn, j))
        if pn is not None and pn == F.theta(j):
            TEETH['T-F-UP'] += 1
    return Sh


# ---------- FR-P2: floors on random in-budget members ---------------
def floor_sweep(F, nmem=30):
    ngate = 0
    for i in range(nmem):
        digs = {}
        for j in range(F.mu2):
            for a in range(F.Dp):
                for b in range(F.e2 * F.f2):
                    if random.random() < 0.7:
                        u = random.choice([1, 2, -1, -2]
                                          if F.p == 3 else
                                          [1, 3, 5, -1, -3])
                        digs[(j, a, b)] = u * F.p ** (
                            F.floor(j, a, b) + random.choice(
                                [0, 0, 1, 2]))
        f = from_slots(F, digs)
        if i < 3:
            chk('GATE', level1_gate(F, f),
                '%s member %d fails level-1 gate' % (F.name, i))
            ngate += 1
        Cs, Sh = honest(F, f), shadow(F, f)
        for j in range(F.mu2):
            md = mindiff(F, Sh[j], Cs[j])
            chk('FLOOR', md is None or md >= F.theta(j),
                '%s mem%d j=%d mindiff %s < THETA %d'
                % (F.name, i, j, md, F.theta(j)))
            chk('ENTRY', md is None or md > (F.mu2 - j) * F.E2,
                '%s mem%d j=%d diff in entry band' % (F.name, i, j))
    say('  %s floor sweep: %d members (%d gate-checked)' %
        (F.name, nmem, ngate))


# ---------- FR-P3/P4: the FR-D5 band + interference rows ------------
def d5_rows():
    F = FRD5
    say('== FR-D5 band rows (faithful band [37, 40], THETA_0 41) ==')
    rows = [('D5-B37', {(0, 0, 1): 128}, 37, 'tRAM', [(8, 1)]),
            ('D5-B39', {(0, 1, 1): 128}, 39, 'tRAM', [(8, 1)]),
            ('D5-B40', {(0, 0, 0): 2 ** 10, (1, 1, 1): 4}, 40,
             't2SIDED', [(4, 1), (4, 1)])]
    for tag, digs, p0, lab, sig in rows:
        f = from_slots(F, digs)
        Cs, Sh = honest(F, f), shadow(F, f)
        rh = label_p2(F, Cs[0], Cs[1])
        rs = label_p2(F, Sh[0], Sh[1])
        mds = [mindiff(F, Sh[j], Cs[j]) for j in range(2)]
        chk('BAND', rh[0] == p0 and rh[2] == lab,
            '%s honest %s want p0 %d %s' % (tag, rh, p0, lab))
        # [run-1 RED disclosure 2026-08-10: run 1 (output kept at
        # gentow3_pe1_fresh_output_run1_RED.txt, md5 485946fc, runner
        # md5 de905729) demanded mindiff >= 41 at BOTH coordinates of
        # D5-B40; coordinate 1's threshold is THETA_1 = 23 and the
        # measured divergence 24 clears it (and the consulted pin 19)
        # -- theorem fine, literal over-strict.  Repaired to the
        # per-coordinate form below; no other edit.]
        chk('BAND', rh == rs and all(
            m is None or (m >= F.theta(j) and
                          (rh[j] is None or m > rh[j]))
            for j, m in enumerate(mds)),
            '%s shadow %s != honest %s or mindiff %s below '
            'THETA/consulted pins' % (tag, rs, rh, mds))
        gp_sig(tag, F, f, sig)
        if tag == 'D5-B40' and rh == rs:
            TEETH['T-F-DOWN'] += 1
    # cancel41: fake digit cancels the honest pin
    fc = from_slots(F, {(0, 0, 1): -256})
    Cs, Sh = honest(F, fc), shadow(F, fc)
    rh = label_p2(F, Cs[0], Cs[1])
    chk('CANCEL', rh[:1] == (41,) and rh[2] == 'tRAM',
        'cancel41 honest %s' % (rh,))
    chk('CANCEL', not pstrip(Sh[0]),
        'cancel41 shadow C_0 = %s not identically 0'
        % pstrip(Sh[0]))
    md = mindiff(F, Sh[0], Cs[0])
    chk('CANCEL', md == 41, 'cancel41 mindiff %s != 41' % md)
    gp_sig('D5-CANCEL41', F, fc, [(8, 1)])
    if not pstrip(Sh[0]) and rh[2] == 'tRAM':
        TEETH['T-F-CANCEL'] += 1
    say('  cancel41: honest tRAM(41) vs shadow j=0 IDENTICALLY 0')
    # add41: divergence at THETA exactly, shadow pin displaced
    fa = from_slots(F, {(0, 0, 1): 256})
    Cs, Sh = honest(F, fa), shadow(F, fa)
    md = mindiff(F, Sh[0], Cs[0])
    chk('ADD', F.pin(Cs[0]) == 41 and F.pin(Sh[0]) == 45 and
        md == 41, 'add41 honest %s shadow %s md %s'
        % (F.pin(Cs[0]), F.pin(Sh[0]), md))
    say('  add41: honest pin 41, shadow pin 45, mindiff 41')


def m3_cancel():
    F = FRM3
    f = from_slots(F, {(1, 1, 0): -40})
    Cs, Sh = honest(F, f), shadow(F, f)
    p1h, p1s = F.pin(Cs[1]), F.pin(Sh[1])
    md = mindiff(F, Sh[1], Cs[1])
    chk('CANCEL', p1h == 7 and p1s == 8 and md == 7,
        'm3-cancel honest p1 %s shadow p1 %s md %s'
        % (p1h, p1s, md))
    say('  FR-M3 cancel7: honest p_1 = 7 = THETA_1, shadow p_1 = 8 '
        '(blind), mindiff 7')


def gl_anchor():
    F = FRGL
    f = from_slots(F, {(0, 1, 0): 729})
    Cs, Sh = honest(F, f), shadow(F, f)
    p0h, p0s = F.pin(Cs[0]), F.pin(Sh[0])
    md = mindiff(F, Sh[0], Cs[0])
    chk('CANCEL', p0h == 13 and md == 13,
        'gl-anchor honest p0 %s mindiff %s' % (p0h, md))
    say('  FR-GL anchor13: honest p_0 = 13 = THETA_0 (tRAM), shadow '
        'pin %s, digits DIFFER at 13 (mindiff 13)' % p0s)
    gp_sig('GL-ANCHOR', F, f, [(4, 2)])


# ---------- main -----------------------------------------------------
def main():
    say('=== GENTOW3 passPE1 FRESH ROUTE (own primitives) ===')
    say('== FR-P1 self-shadows ==')
    self_shadow(FRM3, [[64], [0, 40], [12]])
    self_shadow(FRD5, [psca(256, P12), []])
    self_shadow(FRGL, [padd(psca(-486, P16), [0, 2916]),
                       padd(psca(9, P16), [0, -27])])
    say('== FR-P5 battery digit replication ==')
    self_shadow(BA5, [psca(16, P12), []])
    self_shadow(BA7, [psca(64, P12), []])
    self_shadow(BC, [psca(64, P12), []])
    self_shadow(BB, [padd(psca(64, P12), [0, 64]),
                     padd(psca(4, P12), [0, 8])])
    self_shadow(BD, [[], []])
    say('== FR-P2 floor sweeps ==')
    for F in (FRM3, FRD5, FRGL):
        floor_sweep(F)
    d5_rows()
    m3_cancel()
    gl_anchor()
    gp_sig('EF-M3', FRM3, FRM3.PHI2, [(2, 1)], fun='ef1')
    gp_sig('EF-D5', FRD5, FRD5.PHI2, [(4, 1)], fun='ef1')
    gp_sig('EF-GL', FRGL, FRGL.PHI2, [(2, 2)], fun='ef1')
    resolve_gp()
    for t, n in TEETH.items():
        chk('TEETH', n >= 1, 'tooth %s did not fire' % t)
        say('tooth %s fired x%d' % (t, n))
    nv = len(VIOL)
    say('=== VERDICT: %s -- %d checks, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', sum(NCHK.values()), nv,
           time.time() - T0))
    say('tally: %s' % NCHK)
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    rc = main()
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
