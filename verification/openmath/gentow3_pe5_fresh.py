"""GENTOW3 passPE5 fresh route — own primitives, frames disjoint from
FR-M3 / FR-D5 / FR-GL / FR2-C1 / FR3-B7 / FR4-E22 and both constructed
members (PE3 W at FR-M3; PE4 rows at FR4-E22).

FRAME FR5X (the delta-extreme x e2>1 compound, run at TWO depths):
  p = 2, Phi' = x^2-2 (e1 = 2, f1 = 1, h = 1, eta = 1), e2 = 2, f2 = 1,
  u2 = 13 (slope 13/2), K2 = Y^2 - 64x, Phi2 = Phi'^2 - 64x
  = x^4 - 4x^2 - 64x + 4.  delta = 13 - 2*2*1 = 9 (largest anywhere:
  battery max 3, PE1 max 5, PE3 max 7), E2 = 26.
  FR5X-2: mu2 = 2 (mu1 = 4, deg 8),  THETA = [61, 35].
  FR5X-3: mu2 = 3 (mu1 = 6, deg 12), THETA = [87, 61, 35] — the FIRST
  mu2 = 3 x e2 > 1 frame in any leg, battery included.

PREREGISTERED EXACT PREDICTIONS (hand-derived on paper BEFORE any run;
two routes for the self-shadows: direct two-variable division with
x^2 -> 2 reduction, and the dev-identities dev(Phi2^2) = Y^4 - 128xY^2
+ 4096Y + 8192 / dev(Phi2^3) = Y^6 - 192xY^4 + 12288Y^3 + 24576Y^2
- 262144xY - 524288x):
P5-1 SELF-2: f = Phi2^2 honest DRAIN; shadow G_0 = 4096*Y (slot
  (a,b) = (0,1)), G_1 IDENTICALLY ZERO; pins [61, None] — THETA_0
  ATTAINED (certificate digit at 61 = bit 12 of 4096, nonzero);
  coordinate j = 1 certificate-free via an identically-zero shadow.
P5-2 SELF-3: f = Phi2^3 shadow G_0 = 524288*x*Y, G_1 = 12288*Y,
  G_2 IDENTICALLY ZERO; pins [91, 61, None] vs THETA [87, 61, 35]:
  SLACK at j = 0 (91 = 87 + 4; the height-87 digit = bit 18 of 2^19 at
  slot (1,1) = 0: certificate CANCELS), ATTAINED at j = 1, ZERO at
  j = 2.
P5-3 W5 = Phi2^3 + 64x*Phi2^2 (gate passes, weakly on-side at J = 2):
  honest C = [0, 0, 64x]; shadow [262144*x*Y, 4096*Y, 64x];
  mindiff [87, 61, None] — an entry-digit-driven member failing at
  EXACTLY THETA_0 = 87 AT THE CANCELLED COORDINATE (the retired r2
  only-if's killer at a second frame; F_W = Y^6 - 128xY^4 + 4096Y^3
  + 8192Y^2 on paper).
P5-4 W5B = W5 + 2^21*(x^2-2): honest pins [97, None, 26] (deciding
  vertex (0,97)); shadow pin_0 = 87; mindiff_0 = 87; the shadow
  undercuts (0,97) -> (0,87); PARI sigma {(4,1),(8,1)} (honest edges
  35.5 & 26; shadow reprices 30.5 — pin-corrupted, sigma parity-luck).
P5-5 mu2 = 2 member rows: DIV (+ 8192*Phi'): honest pin 65 tRAM
  {(8,1)}, shadow pin 61 = THETA_0, mindiff 61, undercut (0,65) ->
  (0,61). ADEEP (+ 2^25*Phi'): honest 113 {(8,1)}, shadow 61 — deep
  perturbation keeps the divergence. BANDA (+ 8x*Phi'*Phi2 + 8192x):
  pins [54, 27] BOTH reads, decided {(4,2)}, mindiff [61, None] —
  faithful leaf in the width-8 band. BANDB (+ 128x*Phi2 + 2^15):
  pins [60, 30] both reads, {(4,2)}, faithful at THETA_0 - 1.
P5-6 FLOOR/ENTRY sweeps (seed 20260810): every gated member at both
  depths has mindiff_j >= THETA_j and a clean entry band, each j.
P5-7 REP-M3 (decorrelation + rider audit, MY primitives): FR-M3 self
  [64, 40x, 12] pins [12,7,4]; W-A honest [None,6,3], ShC_0 = 32,
  mindiff [10,9,4]; W-B honest [12,6,3], shadow [10,6,3], ShC_0 = 96,
  C_0 = 64, mindiff [10,9,4].
P5-8 PARI carrier: ef(Phi2_FR5X) = {(4,1)}.
TEETH: T5-UP (THETA+1 mutant killed at >= 6 measured THETA-exact
  rows); T5-DOWN (THETA-1 mutant refuted: BANDB faithful at 60 +
  measured zero shadow content below 61); T5-BICOND (the retired r2
  only-if killed: certificate measured CANCELLED at (FR5X-3, 0) while
  W5/W5B fail there at exactly 87; FR-M3 REP re-fires it at 10).
Design disclosure: the frame constants and all displayed values above
were hand-derived (no machine exploration); the only pre-seal machine
step was a python3 -m py_compile syntax check. No smoke run.
"""
import subprocess, random

# ---------- integer x-poly primitives (dense lists, own code) --------
def pstrip(f):
    while f and f[-1] == 0:
        f.pop()
    return f

def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])

def pneg(f):
    return [-c for c in f]

def pscale(f, s):
    return pstrip([c * s for c in f])

def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return pstrip(out)

def pdivmod(f, g):
    # g monic: exact division over Z
    f = list(f)
    assert g[-1] == 1
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(pstrip(f)) - 1 >= dg and pstrip(f):
        d = len(f) - 1 - dg
        c = f[-1]
        q[d] = c
        for k in range(len(g)):
            f[d + k] -= c * g[k]
        pstrip(f)
    return pstrip(q), pstrip(f)

def v2(n):
    n = abs(n)
    assert n
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v

def dev(C, PHI, nslots):
    """PHI-adic development, nslots coefficients of deg < deg(PHI)."""
    out, r = [], list(C)
    for _ in range(nslots):
        r, rem = pdivmod(r, PHI)
        out.append(rem)
    assert not pstrip(r), 'dev overflow'
    return out

# ---------- frame ----------------------------------------------------
class Frame:
    def __init__(self, name, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        self.name, self.PHI1, self.h = name, PHI1, h
        self.e1, self.e2, self.f2, self.mu2, self.u2 = e1, e2, f2, mu2, u2
        self.PHI2 = PHI2
        self.Dp, self.D2 = len(PHI1) - 1, len(PHI2) - 1
        self.m = e2 * f2
        self.mu1 = self.m * mu2
        self.E2 = self.m * u2
        self.delta = u2 - e2 * self.Dp * h
        self.ee = e1 * e2
        self.K2 = dev(PHI2, PHI1, self.m + 1)
        assert self.K2[self.m] == [1]

    def theta(self, j):
        return (self.mu2 - j) * self.E2 + self.delta

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def red(self, c):
        return pdivmod(c, self.PHI1)[1]

    def honest(self, f):
        out, r = [], list(f)
        for _ in range(self.mu2):
            r, rem = pdivmod(r, self.PHI2)
            out.append(rem)
        assert r == [1], 'not monic of the right degree'
        return out                      # C_j as x-polys, deg < D2

    def level1(self, f):
        A = dev(f, self.PHI1, self.mu1 + 1)
        assert A[self.mu1] == [1]
        return A

    def shadow(self, f):
        A = [self.red(a) for a in self.level1(f)]
        out = []
        for _ in range(self.mu2):
            q = [[] for _ in range(max(1, len(A) - self.m))]
            for i in range(len(A) - 1, self.m - 1, -1):
                c = A[i]
                if c:
                    q[i - self.m] = c
                    A[i] = []
                    for k in range(self.m):
                        A[i - self.m + k] = self.red(
                            padd(A[i - self.m + k],
                                 pneg(pmul(c, self.K2[k]))))
            out.append([list(A[b]) for b in range(self.m)])
            A = q
        assert A and A[0] == [1] and all(not pstrip(list(a))
                                         for a in A[1:])
        return out                      # G_j as m slot-polys, deg < Dp

    def slots(self, C):
        return dev(C, self.PHI1, self.m)

    def pin(self, sl):
        best = None
        for b, g in enumerate(sl):
            for a, c in enumerate(g):
                if c:
                    ht = self.ee * v2(c) + self.w(a, b)
                    best = ht if best is None else min(best, ht)
        return best

    def mindiff(self, slH, slS):
        best = None
        for b in range(self.m):
            n = max(len(slH[b]), len(slS[b]))
            for a in range(n):
                cH = slH[b][a] if a < len(slH[b]) else 0
                cS = slS[b][a] if a < len(slS[b]) else 0
                if cH != cS:
                    ht = self.ee * v2(cH - cS) + self.w(a, b)
                    best = ht if best is None else min(best, ht)
        return best

    def digit_at(self, sl, H):
        tot = 0
        for b, g in enumerate(sl):
            for a, c in enumerate(g):
                if c and (H - self.w(a, b)) >= 0 \
                        and (H - self.w(a, b)) % self.ee == 0:
                    tot += (abs(c) >> ((H - self.w(a, b)) // self.ee)) & 1
        return tot

    def gate(self, f):
        A = self.level1(f)
        for J in range(self.mu1):
            if pstrip(list(A[J])):
                dv = min(self.e1 * v2(c) + a * self.h
                         for a, c in enumerate(A[J]) if c)
                if self.e2 * dv < (self.mu1 - J) * self.u2:
                    return False
        return True

# ---------- harness ---------------------------------------------------
NCHK = NVIO = 0
TALLY = {}
def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    TALLY[tag] = TALLY.get(tag, 0) + 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

def say(s):
    print(s)

P12 = [-2, 0, 1]
X2 = Frame('FR5X-2', P12, 1, 2, 2, 1, 2, 13, [4, -64, -4, 0, 1])
X3 = Frame('FR5X-3', P12, 1, 2, 2, 1, 3, 13, [4, -64, -4, 0, 1])
M3 = Frame('FR-M3', P12, 1, 2, 1, 1, 3, 3, [-2, -2, 1])
assert (X2.delta, X2.E2, X2.theta(0), X2.theta(1)) == (9, 26, 61, 35)
assert (X3.theta(0), X3.theta(1), X3.theta(2)) == (87, 61, 35)
assert (M3.theta(0), M3.theta(1), M3.theta(2)) == (10, 7, 4)

def member(F, gs, extra=None):
    """Phi2^mu2 + sum gs[j]*Phi2^j (+ extra)."""
    acc = [1]
    for _ in range(F.mu2):
        acc = pmul(acc, F.PHI2)
    for j, g in enumerate(gs):
        t = list(g)
        for _ in range(j):
            t = pmul(t, F.PHI2)
        acc = padd(acc, t)
    if extra:
        acc = padd(acc, extra)
    return acc

def reads(F, f):
    hs = [F.slots(c) for c in F.honest(f)]
    ss = F.shadow(f)
    return hs, ss

def pins(F, sl_list):
    return [F.pin(sl) for sl in sl_list]

def mds(F, hs, ss):
    return [F.mindiff(hs[j], ss[j]) for j in range(F.mu2)]

THEXACT = []      # measured THETA-exact rows, feeds T5-UP
CERT_CANCELLED_HITS = []   # (frame,j) cancelled + member exact rows

# ---------- gp plumbing (oracle harness, same method as prior legs) --
GP_JOBS, GP_META = [], {}
def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'

def gp_sig(tag, f, p, want):
    GP_JOBS.append('print("%s ", sig(%s, %d))' % (tag, poly_str(f), p))
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
                         capture_output=True, text=True, timeout=1800)
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0] in GP_META:
            res[parts[0]] = parts[1].strip()
    for tag, want in GP_META.items():
        got = sig_parse(res[tag]) if tag in res else None
        chk('GP', got == want, 'gp %s: got %s want %s' % (tag, got, want))

# ================== P5-1 / P5-2: the self-shadows =====================
say('== P5-1 SELF-2 ==')
f2k = member(X2, [])
ssS2 = X2.shadow(f2k)
chk('SELF', all(not pstrip(list(c)) for c in X2.honest(f2k)),
    'SELF-2 honest not DRAIN')
chk('SELF', ssS2[0] == [[], [4096]], 'SELF-2 G_0 = %s' % ssS2[0])
chk('SELF', all(not pstrip(list(a)) for a in ssS2[1]),
    'SELF-2 G_1 not identically zero')
chk('SELF', X2.pin(ssS2[0]) == 61 and X2.pin(ssS2[1]) is None,
    'SELF-2 pins %s' % [X2.pin(s) for s in ssS2])
chk('SELF', X2.digit_at(ssS2[0], 61) == 1, 'SELF-2 cert digit at 61')
THEXACT.append(('SELF-2 j0', 61, X2.theta(0)))
say('  G = [4096*Y, 0]; pins [61, None] = [THETA_0, cert-free zero]')

say('== P5-2 SELF-3 ==')
f3k = member(X3, [])
ss3 = X3.shadow(f3k)
chk('SELF', ss3[0] == [[], [0, 524288]], 'SELF-3 G_0 = %s' % ss3[0])
chk('SELF', ss3[1] == [[], [12288]], 'SELF-3 G_1 = %s' % ss3[1])
chk('SELF', all(not pstrip(list(a)) for a in ss3[2]),
    'SELF-3 G_2 not identically zero')
chk('SELF', [X3.pin(s) for s in ss3] == [91, 61, None],
    'SELF-3 pins %s' % [X3.pin(s) for s in ss3])
chk('SELF', X3.digit_at(ss3[0], 87) == 0,
    'SELF-3 height-87 digit does NOT cancel')
chk('SELF', X3.digit_at(ss3[1], 61) == 1, 'SELF-3 cert digit at 61')
CERT_CANCELLED_HITS.append(('FR5X-3', 0))
THEXACT.append(('SELF-3 j1', 61, X3.theta(1)))
say('  G = [2^19*x*Y, 12288*Y, 0]; pins [91, 61, None] vs THETA'
    ' [87, 61, 35]: SLACK/ATTAINED/ZERO; cert CANCELS at j=0')

# ================== P5-3 / P5-4: the W member ========================
say('== P5-3/P5-4 W5 (entry-driven, THETA_0-exact at the cancelled'
    ' coordinate) ==')
W5 = member(X3, [[], [], [0, 64]])
chk('WIT', X3.gate(W5), 'W5 fails the gate')
hsW, ssW = reads(X3, W5)
chk('WIT', pins(X3, hsW) == [None, None, 26],
    'W5 honest pins %s' % pins(X3, hsW))
chk('WIT', ssW[0] == [[], [0, 262144]] and ssW[1] == [[], [4096]]
    and ssW[2] == [[0, 64], []],
    'W5 shadow %s' % ssW)
mdW = mds(X3, hsW, ssW)
chk('WIT', mdW == [87, 61, None], 'W5 mindiff %s' % mdW)
THEXACT.append(('W5 j0', 87, X3.theta(0)))
THEXACT.append(('W5 j1', 61, X3.theta(1)))

W5B = member(X3, [[], [], [0, 64]], pscale(P12, 2097152))
chk('WIT', X3.gate(W5B), 'W5B fails the gate')
hsB, ssB = reads(X3, W5B)
chk('WIT', pins(X3, hsB) == [97, None, 26],
    'W5B honest pins %s' % pins(X3, hsB))
chk('WIT', X3.pin(ssB[0]) == 87 and mds(X3, hsB, ssB)[0] == 87,
    'W5B shadow pin/mindiff %s %s'
    % (X3.pin(ssB[0]), mds(X3, hsB, ssB)))
THEXACT.append(('W5B j0', 87, X3.theta(0)))
gp_sig('W5B', W5B, 2, [(4, 1), (8, 1)])
say('  W5 mindiff [87, 61, None]; W5B honest vertex (0,97) undercut'
    ' -> (0,87); the r2 only-if is dead at a second frame')

# ================== P5-5: mu2 = 2 member rows ========================
say('== P5-5 mu2=2 rows ==')
DIV = member(X2, [pscale(P12, 8192)])
chk('DIV', X2.gate(DIV), 'DIV gate')
hsD, ssD = reads(X2, DIV)
chk('DIV', pins(X2, hsD) == [65, None] and X2.pin(ssD[0]) == 61
    and mds(X2, hsD, ssD)[0] == 61,
    'DIV pins/mindiff %s %s %s'
    % (pins(X2, hsD), X2.pin(ssD[0]), mds(X2, hsD, ssD)))
THEXACT.append(('DIV j0', 61, X2.theta(0)))
gp_sig('DIV', DIV, 2, [(8, 1)])

ADEEP = member(X2, [pscale(P12, 2 ** 25)])
hsA, ssA = reads(X2, ADEEP)
chk('DIV', pins(X2, hsA) == [113, None] and X2.pin(ssA[0]) == 61,
    'ADEEP pins %s shadow %s' % (pins(X2, hsA), X2.pin(ssA[0])))
gp_sig('ADEEP', ADEEP, 2, [(8, 1)])

BANDA = member(X2, [[0, 8192], [0, -16, 0, 8]])
chk('BAND', X2.gate(BANDA), 'BANDA gate')
hsBA, ssBA = reads(X2, BANDA)
chk('BAND', pins(X2, hsBA) == [54, 27]
    and [X2.pin(s) for s in ssBA] == [54, 27]
    and mds(X2, hsBA, ssBA) == [61, None],
    'BANDA %s %s %s' % (pins(X2, hsBA), [X2.pin(s) for s in ssBA],
                        mds(X2, hsBA, ssBA)))
THEXACT.append(('BANDA j0 mindiff', 61, X2.theta(0)))
gp_sig('BANDA', BANDA, 2, [(4, 2)])

BANDB = member(X2, [[32768], [0, 128]])
chk('BAND', X2.gate(BANDB), 'BANDB gate')
hsBB, ssBB = reads(X2, BANDB)
chk('BAND', pins(X2, hsBB) == [60, 30]
    and [X2.pin(s) for s in ssBB] == [60, 30]
    and mds(X2, hsBB, ssBB) == [61, None],
    'BANDB %s %s %s' % (pins(X2, hsBB), [X2.pin(s) for s in ssBB],
                        mds(X2, hsBB, ssBB)))
gp_sig('BANDB', BANDB, 2, [(4, 2)])
say('  DIV undercut (0,65)->(0,61); BANDA/BANDB faithful at 54/60')

# ================== P5-6: FLOOR/ENTRY sweeps =========================
say('== P5-6 FLOOR/ENTRY sweeps (seed 20260810) ==')
rng = random.Random(20260810)
def rand_g(F, j):
    g = []
    for _ in range(rng.randint(1, 3)):
        a = rng.randint(0, 3)
        vmin = max(0, ((F.mu2 - j) * F.E2 - 2 * a + F.ee - 1) // F.ee)
        v = vmin + rng.randint(0, 4)
        c = rng.choice([1, -1, 3, -3])
        t = [0] * a + [c * (2 ** v)]
        g = padd(g, t)
    return g

for F, nmem in ((X2, 30), (X3, 20)):
    ngated = 0
    for i in range(nmem):
        gs = [rand_g(F, j) if rng.random() < 0.8 else []
              for j in range(F.mu2)]
        f = member(F, gs)
        if not F.gate(f):
            continue
        ngated += 1
        hs, ss = reads(F, f)
        md = mds(F, hs, ss)
        for j in range(F.mu2):
            chk('FLOOR', md[j] is None or md[j] >= F.theta(j),
                '%s sweep %d j=%d mindiff %s < %d'
                % (F.name, i, j, md[j], F.theta(j)))
            chk('ENTRY', md[j] is None
                or md[j] > (F.mu2 - j) * F.E2,
                '%s sweep %d j=%d entry-band hit' % (F.name, i, j))
    chk('SWEEP', ngated >= nmem - 6,
        '%s: only %d gated members' % (F.name, ngated))
    say('  %s: %d gated members swept' % (F.name, ngated))

# ================== P5-7: REP-M3 (rider audit, own primitives) =======
say('== P5-7 REP-M3 ==')
fm = member(M3, [])
ssM = M3.shadow(fm)
chk('REP', ssM == [[[64]], [[0, 40]], [[12]]],
    'M3 self %s' % ssM)
chk('REP', [M3.pin(s) for s in ssM] == [12, 7, 4],
    'M3 self pins %s' % [M3.pin(s) for s in ssM])
chk('REP', M3.digit_at(ssM[0], 10) == 0, 'M3 cert at 10 not zero')
CERT_CANCELLED_HITS.append(('FR-M3', 0))
gW = padd(pmul([0, 2], pmul(M3.PHI2, M3.PHI2)),
          pscale(M3.PHI2, 8))
WA = padd(member(M3, []), gW)
WB = padd(WA, [64])
for tag, f, wanth, wantS0, wantC0 in (
        ('W-A', WA, [None, 6, 3], [32], []),
        ('W-B', WB, [12, 6, 3], [96], [64])):
    chk('REP', M3.gate(f), '%s gate' % tag)
    hs, ss = reads(M3, f)
    chk('REP', pins(M3, hs) == wanth,
        '%s honest pins %s' % (tag, pins(M3, hs)))
    chk('REP', ss[0] == [wantS0] and hs[0] == [wantC0],
        '%s ShC_0/C_0 %s/%s' % (tag, ss[0], hs[0]))
    md = mds(M3, hs, ss)
    chk('REP', md == [10, 9, 4], '%s mindiff %s' % (tag, md))
    THEXACT.append(('%s j0' % tag, 10, M3.theta(0)))
say('  self [64, 40x, 12] pins [12,7,4]; W-A/W-B mindiff [10,9,4]')

# ================== P5-8 + GP resolution =============================
gp_sig('EF', X2.PHI2, 2, [(4, 1)])
resolve_gp()

# ================== TEETH ============================================
say('== TEETH ==')
up_kills = sum(1 for _, ht, th in THEXACT if ht == th)
chk('TEETH', up_kills >= 6,
    'T5-UP: only %d THETA-exact rows kill the +1 mutant' % up_kills)
down_ok = (mds(X2, hsBB, ssBB)[0] == 61
           and X2.digit_at(ssS2[0], 60) == 0
           and pins(X2, hsBB) == [60, 30])
chk('TEETH', down_ok, 'T5-DOWN: THETA-1 mutant not refuted')
bicond_dead = (X3.digit_at(ss3[0], 87) == 0 and mdW[0] == 87
               and mds(X3, hsB, ssB)[0] == 87
               and M3.digit_at(ssM[0], 10) == 0)
chk('TEETH', bicond_dead, 'T5-BICOND: retired only-if not killed')
say('teeth: T5-UP kills=%d T5-DOWN=%s T5-BICOND=%s'
    % (up_kills, down_ok, bicond_dead))

say('tally: %s' % sorted(TALLY.items()))
say('=== VERDICT: %s -- %d checks, %d violations ==='
    % ('GREEN' if NVIO == 0 else 'RED', NCHK, NVIO))

