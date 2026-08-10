#!/usr/bin/env python3
"""GENTOW6-BOX-1 machine leg: THEOREM GENTOW-6.5 (mu2-general
attainment at the top coordinate, f1 = 1) — sealed instrument,
two-commit seal (this docstring preregistered at commit 1, BEFORE
the first run). Note: lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md
(S2 theorem, S3 display, S4 leg).

SELF-CONTAINED integer-exact code (no import of any sealed runner).
DUAL ORACLES: route R (the shadow's own definition — two-variable
division with every coefficient reduced mod Phi' at every step) vs
route E (EXACT division over Z[x][Y], ONE terminal reduction — the
proof's Step III object); bit-equality per coordinate slot dict is
the functoriality face. Plus PARI/gp decorrelation (factorpadic
carriers via nfinit/idealprimedec, poldisc) on committed wants.

SEVEN FRAMES (name, p, Phi', e2, f2, mu2, u2, Phi2):
  X3  FR5X geometry Q2, x^2-2, e2=2, f2=1, mu2=3, u2=13, Phi2=Phi'^2-64x
  X4  same geometry at mu2=4
  A53 FAM-A5 genre  Q2, x^2-2, e2=2, f2=1, mu2=3, u2=5,  Phi2=Phi'^2-4x
  B3  FAM-B genre   Q2, x^2-2, e2=1, f2=2, mu2=3, u2=3,  Phi2=Phi'^2-2x*Phi'-8
  P33/P34/P35 GEN-P3 genre Q3, x^2-3, e2=2, f2=1, mu2=3/4/5, u2=5,
      Phi2=Phi'^2-18x (chat = 2)

CONSTANTS (asserted): X: E2=26 delta=9 THETA(m=3)=[87,61,35],
THETA(m=4)=[113,87,61,35]; A5: E2=10 delta=1 THETA=[31,21,11];
B: E2=6 delta=1 THETA=[19,13,7], T={0,1}, t*=1, B*=4, j*=2, b*=1;
P3: E2=10 delta=1, THETA(m)=[(m-j)*10+1]. j* = (m-2) +
floor((2 e2 t* + 1)/(e2 f2)); top slot (a*,b*) = (2 i_{t*} - D',
(2 e2 t* + 1) mod e2 f2).

PREREGISTERED PREDICTIONS (all hand-ledger-derived from THEOREM
GENTOW-6.5 + the S3 display BEFORE any run of this instrument; no
pre-seal machine smoke of this file — a RED run-1, if any, will be
kept and disclosed per the PE5 precedent):
 P-DUAL  route R == route E slot-dict-identical on every scored
   member (self-shadows + all perturbation rows), every coordinate.
 P-X3    ShC_0 = {(1,1): 524288} pin 91; ShC_1 = {(0,1): 12288}
   pin 61 = THETA_1 with graded height-61 digit NONZERO (v = 12);
   ShC_2 = {} — bit-equal to the committed PE5 vector
   [2^19 x Y, 12288 Y, 0]; graded height-87 digit at (1,1)@j0 ZERO
   (v = 19 > 18 = (87-15)/4): the S3 slack, (-1+3) = 2 killed at
   p = 2.
 P-X4    ShC_2 = {(0,1): 24576} EXACT (v = 13 = v0+1, v0 = 12:
   graded height-THETA_2 = 61 digit ZERO — p = 2 | binom(4,2) = 6;
   pin(ShC_2) = 65); ShC_3 = {}; j0/j1 floors only (P-FLOOR).
 P-A53   ShC_1 = {(0,1): 48} pin 21 = THETA_1, graded digit
   NONZERO (v = 4 = 2 a_{t*}; binom(3,2) = 3 a 2-unit);
   ShC_2 = {}; ShC_0 = {(1,1): 128} pin 35 (graded height-31
   digit ZERO: the S3 assembly -1 + 3 = 2 at p = 2, v = 7 > 6).
 P-B3    ShC_2 = {(0,1): 12, (1,0): -8} pin 7 = THETA_2 — TWO
   graded height-7 slots in one coordinate: (0,1) v = 2 = 2 a_{t*}
   (the certificate, binom(3,2)*chat_1^2*2^{2a_1} = 12) and (1,0)
   v = 3 (the triple {1,1,1} branch -8x); f2 = 2 / t* = 1 /
   j* = m-1 axis; j0/j1 floors only.
 P-P33   ShC_1 = {(0,1): 972} with graded height-21 digit ZERO
   (972 = 4*3^5, v = 5 > 4 = v0: p = 3 | binom(3,2) — the odd-p
   cancellation), pin(ShC_1) = 25; ShC_2 = {}; ShC_0 =
   {(1,1): 11664} pin 31 = THETA_0 (v = 6 = v0: the SAME -1+3 = 2
   assembly is a 3-UNIT — the S3 genre arithmetic is p-dependent:
   j0 attains at p = 3 while the top coordinate cancels).
 P-P34   ShC_2 = {(0,1): 1944} graded height-21 digit ZERO
   (1944 = 8*3^5: 3 | binom(4,2) = 6), pin 25; ShC_3 = {}.
 P-P35   ShC_3 = {(0,1): 3240} pin 21 = THETA_3 with graded digit
   NONZERO (3240 = 2^3*3^4*5, v = 4 = v0: binom(5,2) = 10 a
   3-unit — attainment returns at m = 5); ShC_4 = {}.
 P-FLOOR every frame, every member (self + perturbed), every j:
   mindiff_j is None or >= THETA_j (GENTOW-3(i) instances).
 P-TOP   ShC_j == {} for every j > j* at each frame (X3: j2;
   X4: j3; A53: j2; P33: j2; P34: j3; P35: j3 and j4 — B3 has
   j* = mu2-1, no coordinate above).
 P-PERS  4 perturbation rows per frame (seed 20260810, g = c *
   p^50 * x^alpha * Phi2^{j'}, in-budget deep): honest read
   non-DRAIN; mindiff_j == the self-shadow's mindiff_j wherever
   the latter is not None; where it is None, mindiff_j is None or
   >= ee*45 (the perturbation's own discrepancy floor).
 P-PARI  factorpadic carriers: X-geometry Phi2 {(4,1)}, A5 Phi2
   {(4,1)}, B Phi2 {(2,2)}, P3 Phi2 {(4,1)}; poldisc != 0 at one
   perturbed member per geometry (4 jobs).
TEETH (mutant wants that MUST be killed; kill counts asserted):
 T-ALLM  "graded THETA_{j*} digit at (a*,b*) nonzero at every
   frame with 2 i_{t*} >= D'" — must die exactly at X4, P33, P34
   (3 kills; the naive m = 2 extrapolation).
 T-COEF  coefficient m instead of binom(m,2) — must die at X4
   (v 14 vs 13) and P34 (4 a 3-unit vs 6 = 0 mod 3): 2 kills;
   recorded non-kills at m = 3 frames (m = binom(3,2) = 3) and
   P35 (same v) are the tooth's honest blind rows.
 T-VAL   v* - 1 at the top slot — 7 kills (one per frame).
 T-TOPZ  "ShC_{j*+1} != 0" — 6 kills (every frame with
   j* + 1 < mu2).
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
    f = list(f)
    assert g[-1] == 1, 'divisor not monic'
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while pstrip(f) and len(f) - 1 >= dg:
        d = len(f) - 1 - dg
        c = f[-1]
        q[d] = c
        for k in range(len(g)):
            f[d + k] -= c * g[k]
        pstrip(f)
    return pstrip(q), pstrip(f)

def vp(n, p):
    n = abs(n)
    assert n
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def dev(C, PHI, nslots):
    out, r = [], list(C)
    for _ in range(nslots):
        r, rem = pdivmod(r, PHI)
        out.append(rem)
    assert not pstrip(r), 'dev overflow'
    return out

def ppow(f, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, f)
    return out

# ---------- frame ----------------------------------------------------
class Frame:
    def __init__(self, name, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2):
        self.name, self.p, self.PHI1, self.h = name, p, PHI1, h
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
        return out

    def level1(self, f):
        A = dev(f, self.PHI1, self.mu1 + 1)
        assert A[self.mu1] == [1]
        return A

    def _divide(self, A, reduce_each):
        """iterated division by K2 in Y; A = list of x-polys per
        Y-power. reduce_each: reduce coefficients mod Phi' at every
        step (route R) or not (route E)."""
        out = []
        for _ in range(self.mu2):
            q = [[] for _ in range(max(1, len(A) - self.m))]
            for i in range(len(A) - 1, self.m - 1, -1):
                c = A[i]
                if pstrip(list(c)):
                    q[i - self.m] = padd(q[i - self.m], c)
                    A[i] = []
                    for k in range(self.m):
                        t = padd(A[i - self.m + k],
                                 pneg(pmul(c, self.K2[k])))
                        A[i - self.m + k] = self.red(t) if reduce_each \
                            else t
                    c = []
            out.append([list(A[b]) for b in range(self.m)])
            A = q
        assert A and pstrip(list(A[0])) == [1] and \
            all(not pstrip(list(x)) for x in A[1:]), 'top quotient != 1'
        return out

    def shadow_R(self, f):
        A = [self.red(a) for a in self.level1(f)]
        return self._divide(A, True)

    def shadow_E(self, f):
        A = [list(a) for a in self.level1(f)]
        out = self._divide(A, False)
        return [[self.red(list(c)) for c in coord] for coord in out]

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

    def mindiff(self, cH, cS):
        dif = [padd(list(sb), pneg(hb)) for sb, hb in
               zip(cS, dev(cH, self.PHI1, self.m))]
        return self.pin(dif)

    def graded_nonzero(self, coord, a, b, H):
        """is the height-H graded digit at slot (a,b) nonzero?"""
        c = self.slotdict(coord).get((a, b), 0)
        if c == 0:
            return False
        n = H - self.w(a, b)
        return n >= 0 and n % self.ee == 0 and vp(c, self.p) == n // self.ee

# ---------- harness ---------------------------------------------------
NCHK = NVIO = 0
TALLY, KILLS = {}, {}
def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    TALLY[tag] = TALLY.get(tag, 0) + 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

def tooth(name, killed, msg):
    KILLS[name] = KILLS.get(name, 0) + (1 if killed else 0)
    chk('TEETH', killed, 'tooth %s NOT killed: %s' % (name, msg))

# ---------- frames ----------------------------------------------------
PX = [-2, 0, 1]
PP = [-3, 0, 1]
X3 = Frame('X3', 2, PX, 1, 2, 2, 1, 3, 13, [4, -64, -4, 0, 1])
X4 = Frame('X4', 2, PX, 1, 2, 2, 1, 4, 13, [4, -64, -4, 0, 1])
A53 = Frame('A53', 2, PX, 1, 2, 2, 1, 3, 5, [4, -4, -4, 0, 1])
B3 = Frame('B3', 2, PX, 1, 2, 1, 2, 3, 3, [-4, 4, -4, -2, 1])
P33 = Frame('P33', 3, PP, 1, 2, 2, 1, 3, 5, [9, -18, -6, 0, 1])
P34 = Frame('P34', 3, PP, 1, 2, 2, 1, 4, 5, [9, -18, -6, 0, 1])
P35 = Frame('P35', 3, PP, 1, 2, 2, 1, 5, 5, [9, -18, -6, 0, 1])
assert [X3.theta(j) for j in range(3)] == [87, 61, 35]
assert [X4.theta(j) for j in range(4)] == [113, 87, 61, 35]
assert [A53.theta(j) for j in range(3)] == [31, 21, 11]
assert [B3.theta(j) for j in range(3)] == [19, 13, 7]
assert [P33.theta(j) for j in range(3)] == [31, 21, 11]
assert (X3.delta, A53.delta, B3.delta, P33.delta) == (9, 1, 1, 1)

# (frame, j*, top slot dict want, v* want, graded-THETA nonzero want,
#  mutant-m graded-nonzero want [for T-COEF at cancel rows])
TOP = [
    (X3, 1, {(0, 1): 12288}, 12, True),
    (X4, 2, {(0, 1): 24576}, 13, False),
    (A53, 1, {(0, 1): 48}, 4, True),
    (B3, 2, {(0, 1): 12, (1, 0): -8}, 2, True),
    (P33, 1, {(0, 1): 972}, 5, False),
    (P34, 2, {(0, 1): 1944}, 5, False),
    (P35, 3, {(0, 1): 3240}, 4, True),
]
# extra exact lower-coordinate wants (S3 displays; binomial-key
# genres are fully weight-exact so the assembly is the whole value)
EXTRA = {
    'X3': [(0, {(1, 1): 524288}, 91, False)],   # slack: graded-87 zero
    'A53': [(0, {(1, 1): 128}, 35, False)],     # slack at p = 2
    'P33': [(0, {(1, 1): 11664}, 31, True)],    # ATTAINED at p = 3
}

# ---------- gp plumbing ----------------------------------------------
GP_JOBS, GP_META = [], {}
def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'

def gp_sig(tag, f, p, want):
    GP_JOBS.append('print("%s ", sig(%s, %d))' % (tag, poly_str(f), p))
    GP_META[tag] = ('sig', sorted(want))

def gp_disc(tag, f):
    GP_JOBS.append('print("%s ", poldisc(%s))' % (tag, poly_str(f)))
    GP_META[tag] = ('disc', None)

def sig_parse(s):
    n = [int(t) for t in s.replace('[', ' ').replace(']', ' ')
         .replace(',', ' ').split()]
    return sorted((n[i], n[i + 1]) for i in range(0, len(n), 2))

def resolve_gp():
    print('== GP leg: %d jobs ==' % len(GP_JOBS))
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
    for tag, (kind, want) in GP_META.items():
        if kind == 'sig':
            got = sig_parse(res[tag]) if tag in res else None
            chk('GP', got == want, 'gp %s: got %s want %s'
                % (tag, got, want))
        else:
            got = res.get(tag)
            chk('GP', got is not None and got.lstrip('-').isdigit()
                and int(got) != 0, 'gp %s: poldisc %s' % (tag, got))

# ---------- the run ----------------------------------------------------
random.seed(20260810)

def run_frame(F, jstar, topwant, vstar, graded_want):
    name = F.name
    print('== frame %s (p=%d mu2=%d j*=%d) ==' % (name, F.p, F.mu2, jstar))
    f = ppow(F.PHI2, F.mu2)
    hs = F.honest(f)
    chk('SELF', all(not pstrip(list(c)) for c in hs),
        '%s honest not DRAIN' % name)
    sR, sE = F.shadow_R(f), F.shadow_E(f)
    for j in range(F.mu2):
        chk('DUAL', F.slotdict(sR[j]) == F.slotdict(sE[j]),
            '%s route R != E at j=%d: %s vs %s'
            % (name, j, F.slotdict(sR[j]), F.slotdict(sE[j])))
    top = F.slotdict(sR[jstar])
    chk('TOPD', top == topwant, '%s ShC_%d = %s want %s'
        % (name, jstar, top, topwant))
    (a0, b0) = (0, 1)
    c0 = top.get((a0, b0), 0)
    chk('TOPV', c0 != 0 and vp(c0, F.p) == vstar,
        '%s top slot v = %s want %d'
        % (name, vp(c0, F.p) if c0 else None, vstar))
    got_graded = F.graded_nonzero(sR[jstar], a0, b0, F.theta(jstar))
    chk('GRAD', got_graded == graded_want,
        '%s graded THETA_%d digit nonzero = %s want %s'
        % (name, jstar, got_graded, graded_want))
    for j in range(jstar + 1, F.mu2):
        chk('TOP0', F.slotdict(sR[j]) == {},
            '%s ShC_%d = %s want {}' % (name, j, F.slotdict(sR[j])))
    selfmd = []
    for j in range(F.mu2):
        md = F.pin(sR[j])
        selfmd.append(md)
        chk('FLOOR', md is None or md >= F.theta(j),
            '%s self mindiff_%d = %s < THETA %d'
            % (name, j, md, F.theta(j)))
    for (jx, dwant, pinwant, gwant) in EXTRA.get(name, []):
        dx = F.slotdict(sR[jx])
        chk('XTRA', dx == dwant, '%s ShC_%d = %s want %s'
            % (name, jx, dx, dwant))
        chk('XTRA', F.pin(sR[jx]) == pinwant, '%s pin_%d = %s want %d'
            % (name, jx, F.pin(sR[jx]), pinwant))
        (ax, bx) = list(dwant.keys())[0]
        gx = F.graded_nonzero(sR[jx], ax, bx, F.theta(jx))
        chk('XTRA', gx == gwant, '%s graded THETA_%d at %s = %s want %s'
            % (name, jx, (ax, bx), gx, gwant))
    # pins of the top coordinate
    if graded_want:
        chk('PIN', selfmd[jstar] == F.theta(jstar),
            '%s pin_%d = %s want THETA %d'
            % (name, jstar, selfmd[jstar], F.theta(jstar)))
    else:
        chk('PIN', selfmd[jstar] is not None
            and selfmd[jstar] > F.theta(jstar),
            '%s cancel row pin_%d = %s not > THETA %d'
            % (name, jstar, selfmd[jstar], F.theta(jstar)))
    # perturbation persistence rows
    first = True
    for r in range(4):
        c = random.randrange(1, F.p ** 6)
        if c % F.p == 0:
            c += 1
        alpha = random.randrange(F.D2)
        jp = random.randrange(F.mu2)
        g = pscale(pmul([0] * alpha + [1], ppow(F.PHI2, jp)),
                   c * F.p ** 50)
        fp = padd(list(f), g)
        hp = F.honest(fp)
        chk('PERS', any(pstrip(list(x)) for x in hp),
            '%s pert %d honest DRAIN' % (name, r))
        spR, spE = F.shadow_R(fp), F.shadow_E(fp)
        for j in range(F.mu2):
            chk('DUAL', F.slotdict(spR[j]) == F.slotdict(spE[j]),
                '%s pert %d R != E at j=%d' % (name, r, j))
            md = F.mindiff(hp[j], spR[j])
            if selfmd[j] is not None:
                chk('PERS', md == selfmd[j],
                    '%s pert %d mindiff_%d = %s want %s'
                    % (name, r, j, md, selfmd[j]))
            else:
                chk('PERS', md is None or md >= F.ee * 45,
                    '%s pert %d mindiff_%d = %s (want None/>=%d)'
                    % (name, r, j, md, F.ee * 45))
            chk('FLOOR', md is None or md >= F.theta(j),
                '%s pert %d mindiff_%d = %s < THETA' % (name, r, j, md))
        if first:
            gp_disc('PD_%s' % name, fp)
            first = False
    # teeth
    if not graded_want:
        tooth('T-ALLM', got_graded is False,
              '%s mutant all-m attainment survived' % name)
    if name == 'X4':
        tooth('T-COEF', c0 != 0 and vp(c0, F.p) != 14,
              'X4 mutant coefficient m=4 (v=14) survived')
    if name == 'P34':
        tooth('T-COEF', got_graded is False,
              'P34 mutant m=4 (a 3-unit) survived')
    tooth('T-VAL', c0 != 0 and vp(c0, F.p) != vstar - 1,
          '%s mutant v*-1 survived' % name)
    if jstar + 1 < F.mu2:
        tooth('T-TOPZ', F.slotdict(sR[jstar + 1]) == {},
              '%s mutant above-top content survived' % name)

def main():
    for row in TOP:
        run_frame(*row)
    gp_sig('EF_X', X3.PHI2, 2, [(4, 1)])
    gp_sig('EF_A5', A53.PHI2, 2, [(4, 1)])
    gp_sig('EF_B', B3.PHI2, 2, [(2, 2)])
    gp_sig('EF_P3', P33.PHI2, 3, [(4, 1)])
    resolve_gp()
    print('== TALLY ==')
    for k in sorted(TALLY):
        print('  %-6s %d' % (k, TALLY[k]))
    print('  teeth kills: %s' % sorted(KILLS.items()))
    ok_teeth = (KILLS.get('T-ALLM', 0) == 3 and KILLS.get('T-COEF', 0)
                == 2 and KILLS.get('T-VAL', 0) == 7
                and KILLS.get('T-TOPZ', 0) == 6)
    if not ok_teeth:
        print('TEETH COUNT MISMATCH (want ALLM 3 / COEF 2 / VAL 7 / '
              'TOPZ 6)')
    print('RESULT: %d checks, %d violations, teeth %s'
          % (NCHK, NVIO, 'OK' if ok_teeth else 'MISMATCH'))
    return 0 if (NVIO == 0 and ok_teeth) else 1

if __name__ == '__main__':
    raise SystemExit(main())
