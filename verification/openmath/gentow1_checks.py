#!/usr/bin/env python3
"""GENTOW-1 battery: [GENHN-TOW-1] items (1), (2), (5) -- composed
entry budgets, inner refine transfer, composed window ledger at the
composed key Phi2.  Examples-first instrument + sealed teeth.

SETTING (from LEMMA GENHN-T(b)', GENHN_PROOF S8 [r2] annex): outer
genre (Q; e1,f1,mu1; h), key Phi' (deg D'), inner event slope
kappa2 = u2/e2 residual psi2^{mu2}, composed key Phi2 (deg D2 =
D'e2f2), composed ladder dv2 = e1e2*v, composed basis {x^a Phi'^b},
slot offsets w(a,b) = a*e2h + b*u2.  THE CONSTANT E2 := e2*f2*u2
(dv2-height of every side term of Phi2; E2 > dv2(x^{D2}) = D2*e2h
via the [r1] node floor u2 > e2*D'h).
WEIGHT of pi^v x^a Phi'^b Phi2^j := e1e2*v + w(a,b) + j*E2.

FAMILIES (mu2 = 2 everywhere; all constructions independent of the
sealed GENHN battery):
  FAM-A5 (2,1,4)->(2,1,2) /Q2, u2=5: Phi2 = (x^2-2)^2 - 4x, E2=10
  FAM-A7 (2,1,4)->(2,1,2) /Q2, u2=7: Phi2 = (x^2-2)^2 - 8x, E2=14
  FAM-B  (2,1,4)->(1,2,2) /Q2, u2=3: Phi2 = Phi'^2-2x*Phi'-8, K2=F4
  FAM-C  (2,1,6)->(3,1,2) /Q2, u2=7: Phi2 = (x^2-2)^3 - 8x, E2=21
  FAM-D  (2,1,4)->(1,2,2) /Q3, u2=3: Phi2 = (x^2-3)^2 + 27, K2=F9

PREREGISTERED PREDICTIONS (sealed before the first full run):
 P-1 (KEY): Phi2 irreducible with single prime (e,f) = (e1e2,f1f2);
   nfeltval: v(x) = e2h/(e1e2)-normalized, v(Phi') = u2 pr-units.
 P-2 (BUDGET-NEC): every level-1-recipe locus member (supp/PE3-style
   entry constructions, disc != 0) has ALL composed digits c_{j,a,b}
   >= the floors  ceil(((mu2-j)E2 - w(a,b))/(e1e2)) + [pin],
   [pin] = 1 iff (mu2-j)E2 == w(a,b) mod e1e2; node pins p_j >=
   (mu2-j)E2 + 1; and f - Phi2^mu2 is strictly above weight mu2*E2.
 P-3 (NODE-ORACLE): for every scored member and EVERY prime of every
   factor: e1e2*nfeltval(Phi2)/pr.e > E2; e1*nfeltval(x) = h*pr.e;
   e1e2*nfeltval(Phi')/pr.e = u2 exactly.
 P-4 (BUDGET-REAL): every in-budget random member (digits >= floors,
   C0 != 0) passes the level-1 entry gate + strict-above; decided
   composed reads match PARI sigma (route 1 all, route 2 subsample).
 P-5 (NODE-EQ): the four anchor members realize p0 = mu2*E2 + 1
   exactly and are tRAM with sigma {(2e1e2, f1f2)}.
 P-6 (REFINE): each composed-alpha event member (C0 pin s^2 at
   2*lam, C1 pin -2s at lam if p != 2) refined by Phi2' = Phi2 -
   shat*n2hat(lam) has new pins p0' > 2*lam and p1' >= lam + 1;
   Phi2' keeps the key grammar (level-1 one-sidedness + PARI
   (e1e2, f1f2)); PARI sigma of the member matches the refined
   read when decided.
 P-7 (WINDOW): decided reads at heights m* are invariant under all
   6 random p^N-lifts with e1e2*N > m* (pins, labels, sigma); read
   of (f mod p^N) equals read of f.
 P-8 (STRINGS): per class the max in-window slot height equals
   e1e2*(N-1) + w(a,b) (formula vs direct scan).
 P-9 (ROUNDTRIP): composed digits -> polynomial -> digits is the
   identity (triangular bijection, machine side).
TEETH (all must fire; >= 3 required, 5 shipped):
 T-MUTFLOOR: mutant floors with E2 replaced by D2*e2h (the naive
   leading-monomial base) accept members that FAIL the entry gate /
   strict-above (8 per family, all must fail the truth).
 T-BELOWNODE: FAM-A5 member with a digit AT weight mu2*E2 exactly
   (pin violated) breaks the entry endpoint (gate fails).
 T-REFWRONG: refine by the WRONG normalizer (height lam+1, or wrong
   residue at q=3) leaves the event pin alive.
 T-UNDERCUT: below-cap perturbation (v = N' with e1e2*N' <= m*)
   changes the composed read (two lifts, different reads).
 T-SHADOW (regression): the three PE1 stage-shadow instances keep
   corrected pins (25,14)/(21,14)/(21,14) and sigma {(8,1)} vs PARI.
SMOKE DISCLOSURE: wiring smoke (3 NEC + 2 REAL per family, anchors,
refine rows, teeth; NO PARI leg) ran before seal and caught two
CONSTANT slips, fixed pre-seal: (a) the FAM-A5 NODE-EQ anchor was
2xPhi' (height 11 < node 21 -- not a node witness); corrected to
16Phi' (height 21); (b) A7-R1's normalizer was transcribed 4xPhi'
(height 17); n2hat(15) = 4Phi'.  No prediction was changed; every
other row was green on smoke.  Verdict: GREEN iff 0 violations and
5/5 teeth.
POST-SEAL REDISCLOSURE (run 1, 2026-08-09): three INSTRUMENT fixes,
no prediction change: (i) the P-7 window check compared reads
INCLUDING above-cap values, over-claiming the lemma (which asserts
lift-stability only below e1e2*N) -- reads are now censored at the
cap, exactly the ledger's (a); the 25 run-1 'violations' were all
of this shape (above-cap p1 appearing under a lift, below-cap data
and sigma identical); (ii) vec_parse made robust to nfeltval +oo
(members with Phi2 | f -- dv2(Phi2(x0)) = infinity satisfies the
floor trivially); (iii) DRAIN members (C0 = 0, Phi2 | f) skip PARI
legs (no scored content; sigma of a split-off Phi2-factor is not a
mu2 = 2 leaf read).
Written 2026-08-09 by GENTOW-1 (BOX-CLOSURE wave B1).
"""
import random
import subprocess
import sys
import time

random.seed(20260809)
T0 = time.time()
VIOL = []
NCHK = {}
TEETH = {'T-MUTFLOOR': 0, 'T-BELOWNODE': 0, 'T-REFWRONG': 0,
         'T-UNDERCUT': 0, 'T-SHADOW': 0}
OUT = []


def say(s):
    print(s)
    sys.stdout.flush()
    OUT.append(s)


def chk(fam, ok, msg):
    NCHK[fam] = NCHK.get(fam, 0) + 1
    if not ok:
        VIOL.append('%s: %s' % (fam, msg))
        say('  !! VIOLATION %s: %s' % (fam, msg))


# ----------------- Z[x] engine (lists, low->high) ------------------
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


def pdivmod_monic(f, g):
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


def dev(f, key, mu):
    g, D = list(f), []
    for _ in range(mu):
        g, r = pdivmod_monic(g, key)
        D.append(r)
    return D, g


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


# ----------------- family objects ----------------------------------
class Fam(object):
    def __init__(self, name, p, PHI1, h, e1, e2, f2, mu2, u2, PHI2,
                 psi2_c, sig_ram, sig_2s, sig_inert, sig_split=None):
        self.name, self.p, self.PHI1, self.h = name, p, PHI1, h
        self.e1, self.e2, self.f2, self.mu2 = e1, e2, f2, mu2
        self.u2, self.PHI2 = u2, PHI2
        self.f1 = 1                      # all families here f1 = 1
        self.Dp = e1 * self.f1           # D' = deg Phi'
        self.D2 = self.Dp * e2 * f2
        self.E2 = e2 * f2 * u2
        self.m = e1 * e2                 # dv2 = m*v
        self.mu1 = e2 * f2 * mu2
        self.n = self.Dp * self.mu1
        self.psi2_c = psi2_c             # psi2 coeffs low->high in K2
        self.sig_ram, self.sig_2s = sig_ram, sig_2s
        self.sig_inert, self.sig_split = sig_inert, sig_split

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def slots(self, C):
        """C deg < D2 -> dict (a,b) -> integer coeff."""
        B, g = dev(list(C), self.PHI1, self.e2 * self.f2)
        assert g == [] or g == [0], 'slot overflow'
        out = {}
        for b, rb in enumerate(B):
            for a, c in enumerate(rb):
                if c:
                    out[(a, b)] = c
        return out

    def floor(self, j, a, b):
        num = (self.mu2 - j) * self.E2 - self.w(a, b)
        if num <= 0:
            return 0
        fl = -((-num) // self.m)         # ceil
        if num % self.m == 0:
            fl += 1                      # consumed pin
        return fl

    def mut_floor(self, j, a, b):
        E2m = self.D2 * self.e2 * self.h  # the WRONG base dv2(x^D2)
        num = (self.mu2 - j) * E2m - self.w(a, b)
        if num <= 0:
            return 0
        fl = -((-num) // self.m)
        if num % self.m == 0:
            fl += 1
        return fl

    def pin(self, C):
        """(min dv2 height, K2 residue) of a deg < D2 coefficient.
        K2 residue as pair (s,t) = s + t*eta2 over F_p (f2 <= 2)."""
        sl = self.slots(C)
        if not sl:
            return None, None
        best = min(self.m * vp(c, self.p) + self.w(a, b)
                   for (a, b), c in sl.items())
        r = [0, 0]
        for (a, b), c in sl.items():
            if self.m * vp(c, self.p) + self.w(a, b) == best:
                fl = b % (2 if self.f2 == 2 else 1) if self.f2 == 2 \
                    else 0
                rc = (c // self.p ** vp(c, self.p)) % self.p
                r[1 if (self.f2 == 2 and b % 2 == 1) else 0] = \
                    (r[1 if (self.f2 == 2 and b % 2 == 1) else 0]
                     + rc) % self.p
        return best, (r[0], r[1])

    def strictly_above(self, g, thr):
        """all weights of g's x^a Phi'^J slots >= thr + 1."""
        B, top = dev(list(g), self.PHI1, self.mu1 + self.mu2 + 1)
        if top:
            return False, 'dev overflow'
        for J, rb in enumerate(B):
            for a, c in enumerate(rb):
                if c and self.m * vp(c, self.p) + \
                        a * self.e2 * self.h + J * self.u2 <= thr:
                    return False, 'slot (a=%d,J=%d) wt %d <= %d' % (
                        a, J, self.m * vp(c, self.p) +
                        a * self.e2 * self.h + J * self.u2, thr)
        return True, None

    def gate(self, f):
        """level-1 entry gate: dv(A0) = mu1*u2/e2 exact (dv = e1*v),
        pins weakly above the inner side."""
        A, g = dev(list(f), self.PHI1, self.mu1)
        if g != [1]:
            return 'not monic in Phi\'-dev'
        dvs = []
        for c in A:
            vals = [self.e1 * vp(cc, self.p) + i * self.h
                    for i, cc in enumerate(c) if cc]
            dvs.append(min(vals) if vals else None)
        want0 = self.mu1 * self.u2 // self.e2 if \
            (self.mu1 * self.u2) % self.e2 == 0 else None
        if dvs[0] is None or self.e2 * dvs[0] != self.mu1 * self.u2:
            return 'dv(A0) = %s want %s/e2' % (dvs[0],
                                               self.mu1 * self.u2)
        for J in range(1, self.mu1):
            if dvs[J] is not None and \
                    self.e2 * dvs[J] < (self.mu1 - J) * self.u2:
                return 'pin J=%d below side' % J
        return None


# ----------------- the five families -------------------------------
PA = [-2, 0, 1]                          # x^2 - 2 over Q2
PB = [-3, 0, 1]                          # x^2 - 3 over Q3
FAMS = [
    Fam('FAM-A5', 2, PA, 1, 2, 2, 1, 2, 5,
        padd(pmul(PA, PA), [0, -4]), [1, 1],
        [(8, 1)], [(4, 1), (4, 1)], [(4, 2)]),
    Fam('FAM-A7', 2, PA, 1, 2, 2, 1, 2, 7,
        padd(pmul(PA, PA), [0, -8]), [1, 1],
        [(8, 1)], [(4, 1), (4, 1)], [(4, 2)]),
    Fam('FAM-B', 2, PA, 1, 2, 1, 2, 2, 3,
        padd(padd(pmul(PA, PA), pmul([0, -2], PA)), [-8]),
        [1, 1, 1], [(4, 2)], [(2, 2), (2, 2)], [(2, 4)],
        [(2, 2), (2, 2)]),
    Fam('FAM-C', 2, PA, 1, 2, 3, 1, 2, 7,
        padd(pmul(pmul(PA, PA), PA), [0, -8]), [1, 1],
        [(12, 1)], [(6, 1), (6, 1)], [(6, 2)]),
    Fam('FAM-D', 3, PB, 1, 2, 1, 2, 2, 3,
        padd(pmul(PB, PB), [27]), [1, 0, 1],
        [(4, 2)], [(2, 2), (2, 2)], [(2, 4)],
        [(2, 2), (2, 2)]),
]
FBY = {F.name: F for F in FAMS}


# ----------------- mu2 = 2 composed dictionary ---------------------
def k2_mul(F, x, y):
    """multiply (s,t) pairs in K2 = F_p[eta2]/psi2 (f2 <= 2)."""
    p = F.p
    if F.f2 == 1:
        return ((x[0] * y[0]) % p, 0)
    # eta2^2 = -c0 - c1*eta2  (psi2 = T^2 + c1 T + c0 monic; psi2_c
    # holds [c0, c1, 1] up to sign convention: T^2 - c1 T - c0 form
    # is NOT used -- psi2 = sum psi2_c[i] T^i)
    c0, c1 = F.psi2_c[0], F.psi2_c[1]
    s = x[0] * y[0] - c0 * x[1] * y[1]
    t = x[0] * y[1] + x[1] * y[0] - c1 * x[1] * y[1]
    return (s % p, t % p)


def read2(F, f):
    """composed mu2 = 2 read of monic f, deg n: pins + label + sigma.
    Returns (p0, p1, label, sigma or None)."""
    q1, C0 = pdivmod_monic(list(f), F.PHI2)
    q2, C1 = pdivmod_monic(q1, F.PHI2)
    if q2 != [1]:
        return None
    u, ru = F.pin(C0)
    w_, rw = F.pin(C1)
    p = F.p
    if u is None:
        return (u, w_, 'DRAIN', None)
    if w_ is None or u < 2 * w_:
        if u % 2 == 1:
            return (u, w_, 'tRAM', F.sig_ram)
        # residual T^2 + ru ~ Y^2 = -ru
        if p == 2:
            return (u, w_, 'tEVEN', None)
        mr = ((-ru[0]) % p, (-ru[1]) % p)
        sq = [z for z in [(s, t) for s in range(p) for t in range(p)]
              if k2_mul(F, z, z) == mr]
        if not sq:
            return (u, w_, 'tINERT', F.sig_inert)
        return (u, w_, 'tSPLIT', F.sig_split or F.sig_2s)
    if u == 2 * w_:
        # residual T^2 + rw T + ru over K2
        roots = [z for z in [(s, t) for s in range(p)
                             for t in range(p)]
                 if ((k2_mul(F, z, z)[0] + k2_mul(F, rw, z)[0] +
                      ru[0]) % p,
                     (k2_mul(F, z, z)[1] + k2_mul(F, rw, z)[1] +
                      ru[1]) % p) == (0, 0)]
        if len(roots) == 2:
            return (u, w_, 'tSPLIT', F.sig_split or F.sig_2s)
        if len(roots) == 0:
            return (u, w_, 'tINERT', F.sig_inert)
        return (u, w_, 'tDBL', None)     # double root: continue
    return (u, w_, 't2SIDED', F.sig_2s)


# ----------------- gp plumbing -------------------------------------
GP_HDR = r"""
default(parisizemax, 4000000000);
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
  \\ per factor, per prime: [m*val(P2), pr.e, m*val(x), m*val(P1)]
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [nfeltval(nf, Mod(P2, g), dec[j]),
                      dec[j].e,
                      nfeltval(nf, Mod(x, g), dec[j]),
                      nfeltval(nf, Mod(P1, g), dec[j])]))));
  Vec(out)
}
"""


def run_gp(lines):
    src = GP_HDR + '\n' + '\n'.join(lines) + '\nquit\n'
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
    return res


def sig_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1])
                  for i in range(0, len(nums), 2))


def vec_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    s = s.replace('+oo', '1000000000')   # Phi2 | f: val = infinity
    nums = [int(t) for t in s.split()]
    return [nums[i:i + 4] for i in range(0, len(nums), 4)]


GP_JOBS = []                             # (tag, gp print line)
GP_META = {}                             # tag -> callback data


def gp_sig(tag, F, f, want, route2=False):
    GP_JOBS.append('print("%s ", sig1(%s, %d))'
                   % (tag, poly_str(f), F.p))
    GP_META[tag] = ('sig', F.name, want)
    if route2:
        GP_JOBS.append('print("%s.r2 ", sig2(%s, %d))'
                       % (tag, poly_str(f), F.p))
        GP_META[tag + '.r2'] = ('sig', F.name, want)


def gp_node(tag, F, f):
    GP_JOBS.append('print("%s.nv ", nodev(%s, %d, %s, %s))'
                   % (tag, poly_str(f), F.p, poly_str(F.PHI2),
                      poly_str(F.PHI1)))
    GP_META[tag + '.nv'] = ('node', F.name, None)


def gp_disc(tag, F, f):
    GP_JOBS.append('print("%s.d ", poldisc(%s) != 0)'
                   % (tag, poly_str(f)))
    GP_META[tag + '.d'] = ('disc', F.name, None)


# ----------------- constructions -----------------------------------
def from_slots(F, digs):
    """digs: dict (j,a,b) -> c.  f = Phi2^mu2 + sum c x^a Phi'^b
    Phi2^j."""
    f = [0]
    for (j, a, b), c in digs.items():
        mono = pmul([0] * a + [c], pmul(ppow(F.PHI1, b),
                                        ppow(F.PHI2, j)))
        f = padd(f, mono)
    return padd(f, ppow(F.PHI2, F.mu2))


def ppow(g, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, g)
    return out


def to_digits(F, f):
    """inverse: Phi2-dev then slots per coordinate; also returns
    node pins."""
    g, digs, pins = list(f), {}, []
    Cs = []
    for j in range(F.mu2):
        g, r = pdivmod_monic(g, F.PHI2)
        Cs.append(r)
    assert g == [1], 'dev not monic'
    for j, C in enumerate(Cs):
        for (a, b), c in F.slots(C).items():
            digs[(j, a, b)] = c
        pv = [F.m * vp(c, F.p) + F.w(a, b)
              for (a, b), c in F.slots(C).items()]
        pins.append(min(pv) if pv else None)
    return digs, pins


def floors_ok(F, digs):
    for (j, a, b), c in digs.items():
        if vp(c, F.p) < F.floor(j, a, b):
            return False, '(j=%d,a=%d,b=%d) v=%d < floor %d' % (
                j, a, b, vp(c, F.p), F.floor(j, a, b))
    return True, None


def nec_members(F, k):
    """level-1 entry-recipe members (decorrelated from the composed
    parameterization).  Returns list of (tag, f)."""
    out = []
    p, u2 = F.p, F.u2
    for i in range(k):
        if F.name in ('FAM-A5', 'FAM-A7'):
            sc = {5: (16, 8, 4), 7: (128, 32, 8)}[u2]
            G = [(p ** u2) * random.choice([1, 3, 5, 7]),
                 sc[0] * random.randint(0, 15),
                 sc[1] * random.randint(0, 15),
                 sc[2] * random.randint(0, 15), 1]
        elif F.name == 'FAM-B':
            G = [64 * random.choice([1, 3, 5, 7]),
                 32 * random.randint(0, 15),
                 8 * random.choice([1, 3, 5, 7]),
                 4 * random.randint(0, 15), 1]
        elif F.name == 'FAM-C':
            G = [128 * random.choice([1, 3, 5, 7]),
                 64 * random.randint(0, 15),
                 32 * random.randint(0, 15),
                 16 * random.randint(0, 15),
                 8 * random.randint(0, 15),
                 4 * random.randint(0, 15), 1]
        else:                            # FAM-D /Q3
            G = [729 * random.choice([1, 4, 7]),
                 243 * random.randint(0, 8),
                 27 * random.choice([2, 5, 8]),
                 9 * random.randint(0, 8), 1]
        f, pw = [0], [1]
        for g in G:
            f = padd(f, psca(g, pw))
            pw = pmul(pw, F.PHI1)
        out.append(('%s-NEC%d' % (F.name, i), f))
        if i % 3 == 0:
            pert = [random.randint(-3, 3) * p ** 45
                    for _ in range(F.n)]
            out.append(('%s-NEC%dp' % (F.name, i), padd(list(f),
                                                        pert)))
    return out


def real_members(F, k):
    out = []
    for i in range(k):
        digs = {}
        for j in range(F.mu2):
            for a in range(F.Dp):
                for b in range(F.e2 * F.f2):
                    if random.random() < 0.7:
                        u = random.choice(
                            [1, 2, -1, -2] if F.p == 3 else
                            [1, 3, 5, -1, -3])
                        e = random.choice([0, 0, 1, 2])
                        digs[(j, a, b)] = u * F.p ** (
                            F.floor(j, a, b) + e)
        if not any(j == 0 for (j, a, b) in digs):
            digs[(0, 0, 0)] = F.p ** F.floor(0, 0, 0)
        out.append(('%s-REAL%d' % (F.name, i), from_slots(F, digs)))
    return out


def mutant_members(F, k):
    """clear MUTANT floors, violate the true floor at slot
    (0,0,0)."""
    out = []
    vbad = -((-F.mu2 * F.D2 * F.e2 * F.h) // F.m)
    for i in range(k):
        digs = {(0, 0, 0): F.p ** vbad *
                random.choice([1, 2] if F.p == 3 else [1, 3])}
        for j in range(F.mu2):
            for a in range(F.Dp):
                for b in range(F.e2 * F.f2):
                    if (j, a, b) not in digs and \
                            random.random() < 0.4:
                        digs[(j, a, b)] = F.p ** (
                            F.floor(j, a, b) + random.choice([0, 1]))
        out.append(from_slots(F, digs))
    return out, vbad


# ----------------- refine executor ---------------------------------
def read2k(F, f, key):
    """read2 with an explicit key (refined)."""
    old = F.PHI2
    F.PHI2 = key
    try:
        return read2(F, f)
    finally:
        F.PHI2 = old


REFINE_ROWS = [
    # (fam, tag, lam, what(poly), D0, J1, wrong_what)
    ('FAM-A5', 'A5-R1', 13, psca(-4, PA),
     pmul([0, 64], PA), pmul([1], [0, 8]), [0, -8]),
    ('FAM-A5', 'A5-R2', 21, psca(-16, PA),
     pmul([0, 1024], PA), [0, 32], [0, -32]),
    ('FAM-A7', 'A7-R1', 15, psca(-4, PA),
     psca(128, PA), [16], [-16]),
    ('FAM-B', 'B-R1', 7, psca(-4, PA),
     [0, 128], [16], [-16]),
    ('FAM-B', 'B-R2', 8, padd([-16], pmul([0, -4], PA)),
     [0, 512], [0, 32], [0, -32]),
    ('FAM-C', 'C-R1', 22, pmul([0, -4], PA),
     pmul([0, 32], pmul(PA, PA)), psca(8, PA),
     pmul([0, -2], pmul(PA, PA))),
    ('FAM-D', 'D-R1', 9, psca(-27, PB),
     [0, 19683], [243], psca(27, PB)),
    ('FAM-D', 'D-R2', 10, pmul([0, -27], PB),
     [0, 59049], [0, 729], [-243]),
]


def run_refines():
    say('== REFINE (item 2): composed-alpha transport rows ==')
    for fam, tag, lam, what, D0, J1, wrong in REFINE_ROWS:
        F = FBY[fam]
        Kp = padd(list(F.PHI2), what)        # refined key Phi2 + w
        f = padd(padd(pmul(Kp, Kp), pmul(J1, Kp)), D0)
        # OLD-key read: the alpha event must show at (2lam, lam..)
        r_old = read2(F, f)
        chk('REFINE', r_old is not None and r_old[0] == 2 * lam,
            '%s old p0 = %s want %d' % (tag, r_old and r_old[0],
                                        2 * lam))
        chk('REFINE', r_old[1] is None or r_old[1] >= lam,
            '%s old p1 = %s < lam %d' % (tag, r_old[1], lam))
        # NEW-key read: pins die
        r_new = read2k(F, f, Kp)
        chk('REFINE', r_new is not None and r_new[0] > 2 * lam,
            '%s new p0 = %s not > %d' % (tag, r_new and r_new[0],
                                         2 * lam))
        chk('REFINE', r_new[1] is None or r_new[1] >= lam + 1,
            '%s new p1 = %s < lam+1' % (tag, r_new[1]))
        # refined-key grammar: level-1 dev one-sided at kappa2
        A, g = dev(list(Kp), F.PHI1, F.e2 * F.f2)
        vals = [F.m * vp(c, F.p) + a * F.e2 * F.h
                for a, c in enumerate(A[0]) if c]
        chk('REFINE', g == [1] and min(vals) == F.E2,
            '%s refined key dv2(A0) = %s want E2 = %d'
            % (tag, min(vals) if vals else None, F.E2))
        say('  %s: old (%s,%s,%s) -> new (%s,%s,%s) %s' %
            (tag, r_old[0], r_old[1], r_old[2], r_new[0], r_new[1],
             r_new[2], r_new[3]))
        gp_sig(tag, F, f, r_new[3], route2=True)
        gp_disc(tag, F, f)
        gp_node(tag, F, f)
        GP_JOBS.append('print("%s.ef ", ef1(%s, %d))'
                       % (tag, poly_str(Kp), F.p))
        GP_META[tag + '.ef'] = ('ef', F.name, None)
        # tooth: wrong normalizer leaves the pin alive
        Kw = padd(list(F.PHI2), wrong)
        r_w = read2k(F, f, Kw)
        if r_w is not None and (r_w[0] == 2 * lam or
                                r_w[1] == lam):
            TEETH['T-REFWRONG'] += 1
        else:
            chk('REFINE', False, '%s wrong-normalizer read %s '
                'unexpectedly killed the pin' % (tag, r_w and
                                                 r_w[:2]))


ANCHORS = {                              # NODE-EQ: p0 = mu2*E2 + 1
    'FAM-A5': psca(16, PA), 'FAM-A7': pmul([0, 32], PA),
    'FAM-B': [0, 64], 'FAM-C': psca(64, PA), 'FAM-D': [0, 729]}
PE1_REG = [                              # T-SHADOW regression rows
    ([96, 16, 0, 0, 1], (25, 14)),
    ([96, 0, 32, 16, 1], (21, 14)),
    ([224, 0, 32, 16, 1], (21, 14))]


def fam_driver(F):
    say('== %s: n=%d D2=%d E2=%d m=%d ==' % (F.name, F.n, F.D2,
                                             F.E2, F.m))
    # floor table (S1 material)
    for j in range(F.mu2):
        row = ['(a=%d,b=%d):%d%s' % (a, b, F.floor(j, a, b),
               '*' if ((F.mu2 - j) * F.E2 - F.w(a, b)) % F.m == 0
               and (F.mu2 - j) * F.E2 - F.w(a, b) > 0 else '')
               for b in range(F.e2 * F.f2) for a in range(F.Dp)]
        say('  floors j=%d: %s   (* = consumed pin)' % (j,
                                                        ' '.join(row)))
    say('  node floors: %s ; mutant base %d vs E2 %d' %
        ([(F.mu2 - j) * F.E2 + 1 for j in range(F.mu2)],
         F.D2 * F.e2 * F.h, F.E2))
    # ---- BUDGET-NEC ----
    for tag, f in nec_members(F, 10):
        err = F.gate(f)
        chk('NEC', err is None, '%s gate: %s' % (tag, err))
        digs, pins = to_digits(F, f)
        ok, msg = floors_ok(F, digs)
        chk('NEC', ok, '%s floor: %s' % (tag, msg))
        for j, pj in enumerate(pins):
            chk('NEC', pj is None or pj >= (F.mu2 - j) * F.E2 + 1,
                '%s node pin p%d = %s < %d' % (tag, j, pj,
                                               (F.mu2 - j) * F.E2
                                               + 1))
        g = padd(list(f), psca(-1, ppow(F.PHI2, F.mu2)))
        ok, msg = F.strictly_above(g, F.mu2 * F.E2)
        chk('NEC', ok, '%s strict-above: %s' % (tag, msg))
        r = read2(F, f)
        if tag.endswith(('0', '4', '8')) and r[0] is not None:
            gp_sig(tag, F, f, r[3], route2=tag.endswith('4'))
            gp_disc(tag, F, f)
            gp_node(tag, F, f)
    # ---- BUDGET-REAL ----
    for tag, f in real_members(F, 12):
        err = F.gate(f)
        chk('REAL', err is None, '%s gate: %s' % (tag, err))
        g = padd(list(f), psca(-1, ppow(F.PHI2, F.mu2)))
        ok, msg = F.strictly_above(g, F.mu2 * F.E2)
        chk('REAL', ok, '%s strict-above: %s' % (tag, msg))
        digs, pins = to_digits(F, f)
        ok, msg = floors_ok(F, digs)
        chk('REAL', ok, '%s floor readback: %s' % (tag, msg))
        r = read2(F, f)
        if r[3] is not None and int(tag[-1]) < 6:
            gp_sig(tag, F, f, r[3], route2=int(tag[-1]) % 4 == 0)
            gp_disc(tag, F, f)
            if int(tag[-1]) % 3 == 0:
                gp_node(tag, F, f)
    # ---- ROUNDTRIP ----
    for i in range(30):
        digs = {}
        for j in range(F.mu2):
            for a in range(F.Dp):
                for b in range(F.e2 * F.f2):
                    if random.random() < 0.6:
                        digs[(j, a, b)] = random.choice(
                            [1, -1, 2, 5]) * F.p ** \
                            random.randint(0, 9)
        back, _ = to_digits(F, from_slots(F, digs))
        chk('ROUNDTRIP', back == digs,
            '%s rt #%d mismatch' % (F.name, i))
    # ---- NODE-EQ anchor ----
    fa = padd(ppow(F.PHI2, F.mu2), ANCHORS[F.name])
    r = read2(F, fa)
    tag = '%s-EQ' % F.name
    chk('NODE-EQ', r[0] == F.mu2 * F.E2 + 1 and r[2] == 'tRAM',
        '%s read %s want (p0=%d, tRAM)' % (tag, r[:3],
                                           F.mu2 * F.E2 + 1))
    gp_sig(tag, F, fa, F.sig_ram, route2=True)
    gp_disc(tag, F, fa)
    gp_node(tag, F, fa)
    # ---- MUTANT floors (T-MUTFLOOR) ----
    muts, vbad = mutant_members(F, 8)
    nfail = 0
    for i, f in enumerate(muts):
        err = F.gate(f)
        g = padd(list(f), psca(-1, ppow(F.PHI2, F.mu2)))
        ok, _ = F.strictly_above(g, F.mu2 * F.E2)
        if err is not None or not ok:
            nfail += 1
    chk('MUTANT', nfail == 8, '%s: only %d/8 mutant members '
        'rejected by the truth' % (F.name, nfail))
    if nfail == 8:
        TEETH['T-MUTFLOOR'] += 1
    say('  mutant leg: 8/8 below-E2 members (v=%d at slot (0,0,0))'
        ' rejected: %s' % (vbad, nfail == 8))
    # ---- WINDOW (P-7) ----
    mstar = F.mu2 * F.E2 + 1
    N = mstar // F.m + 1
    cap = F.m * N

    def censor(r):
        return (r[0] if r[0] is not None and r[0] < cap else None,
                r[1] if r[1] is not None and r[1] < cap else None,
                r[3])
    base = read2(F, fa)
    for i in range(6):
        pert = [random.randint(-F.p ** 3, F.p ** 3) * F.p ** N
                for _ in range(F.n)]
        gl = padd(list(fa), pert)
        rl = read2(F, gl)
        chk('WINDOW', censor(rl) == censor(base),
            '%s lift %d censored read %s != base %s'
            % (F.name, i, censor(rl), censor(base)))
        if i < 2:
            gp_sig('%s-W%d' % (F.name, i), F, gl, base[3])
    fmod = [c % F.p ** N for c in fa[:-1]] + [1]
    chk('WINDOW', censor(read2(F, pstrip(fmod))) == censor(base),
        '%s mod-p^N read differs' % F.name)
    # ---- STRINGS (P-8) ----
    for a in range(F.Dp):
        for b in range(F.e2 * F.f2):
            hs = [F.m * v + F.w(a, b) for v in range(N)]
            chk('STRINGS', max(hs) == F.m * (N - 1) + F.w(a, b),
                'string end (a=%d,b=%d)' % (a, b))


def undercut_rows():
    say('== T-UNDERCUT: below-cap digits change the read ==')
    for fam, Np, slot_add in [('FAM-A5', 2, 4), ('FAM-B', 3, 8)]:
        F = FBY[fam]
        fa = padd(ppow(F.PHI2, F.mu2), ANCHORS[F.name])
        base = read2(F, fa)
        g = padd(list(fa), [slot_add])   # p^N' at slot (0,0), j=0
        rg = read2(F, g)
        fired = rg is None or rg[:3] != base[:3]
        chk('UNDERCUT', fired, '%s: read unchanged by below-cap '
            'digit' % fam)
        if fired:
            TEETH['T-UNDERCUT'] += 1
        say('  %s: base %s -> undercut %s (N\'=%d, e1e2N\'=%d <= '
            'm*=%d)' % (fam, base[:3], rg and rg[:3], Np,
                        F.m * Np, base[0]))
        gp_sig('%s-UC' % fam, F, g, None)


def belownode_row():
    F = FBY['FAM-A5']
    f = from_slots(F, {(0, 0, 0): 32})   # v=5, wt = 20 = mu2*E2
    err = F.gate(f)
    fired = err is not None
    chk('BELOWNODE', fired, 'pin-violating digit did not break '
        'the entry gate')
    if fired:
        TEETH['T-BELOWNODE'] += 1
    say('== T-BELOWNODE: digit AT wt mu2*E2 breaks entry: %s ==' %
        err)


def shadow_regression():
    F = FBY['FAM-A5']
    say('== T-SHADOW: PE1 corrected-read regression (3 rows) ==')
    allok = True
    for i, (G, want_pins) in enumerate(PE1_REG):
        f, pw = [0], [1]
        for g in G:
            f = padd(f, psca(g, pw))
            pw = pmul(pw, F.PHI1)
        r = read2(F, f)
        ok = (r[0], r[1]) == want_pins and r[2] == 'tRAM' and \
            r[3] == [(8, 1)]
        chk('SHADOW', ok, 'PE1 row %d read %s want pins %s tRAM'
            % (i, r and r[:3], (want_pins,)))
        allok = allok and ok
        gp_sig('SHAD%d' % i, F, f, [(8, 1)], route2=(i == 0))
    if allok:
        TEETH['T-SHADOW'] += 1


def resolve_gp():
    say('== PARI leg: %d jobs ==' % len(GP_JOBS))
    res = run_gp(GP_JOBS)
    for tag, (kind, fam, want) in GP_META.items():
        F = FBY[fam]
        if tag not in res:
            chk('GP', False, 'missing gp answer %s' % tag)
            continue
        val = res[tag]
        if kind == 'sig':
            got = sig_parse(val)
            if want is None:
                say('  [diag] %s sigma %s (unscored)' % (tag, got))
            else:
                chk('GP-SIG', got == sorted(want),
                    '%s sigma %s want %s' % (tag, got,
                                             sorted(want)))
        elif kind == 'disc':
            chk('GP-DISC', val == '1', '%s disc == 0' % tag)
        elif kind == 'ef':
            chk('GP-EF', sig_parse(val) == [(F.m, F.f1 * F.f2)],
                '%s refined key ef %s want %s'
                % (tag, sig_parse(val), (F.m, F.f1 * F.f2)))
        elif kind == 'node':
            rows = vec_parse(val)
            chk('GP-NODE', len(rows) > 0, '%s no factor rows' % tag)
            for vP2, epr, vx, vP1 in rows:
                chk('GP-NODE', F.m * vP2 > F.E2 * epr,
                    '%s dv2(Phi2) = %d*%d/%d NOT > E2 = %d'
                    % (tag, F.m, vP2, epr, F.E2))
                chk('GP-NODE', F.e1 * vx == F.h * epr,
                    '%s v(x) off: %d vs %d' % (tag, F.e1 * vx,
                                               F.h * epr))
                chk('GP-NODE', F.m * vP1 == F.u2 * epr,
                    '%s v(Phi\') off: %d vs %d'
                    % (tag, F.m * vP1, F.u2 * epr))


def main():
    say('=== GENTOW-1 battery (items (1)/(2)/(5)) seal '
        '2026-08-09 ===')
    for F in FAMS:
        fam_driver(F)
    belownode_row()
    shadow_regression()
    undercut_rows()
    run_refines()
    resolve_gp()
    for t, n in TEETH.items():
        chk('TEETH', n >= 1, 'tooth %s did not fire' % t)
        say('tooth %s fired x%d' % (t, n))
    nv = len(VIOL)
    say('=== VERDICT: %s -- %d checks, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', sum(NCHK.values()), nv,
           time.time() - T0))
    say('per-family check tally: %s' % NCHK)
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    rc = main()
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
