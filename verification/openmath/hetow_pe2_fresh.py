#!/usr/bin/env python3
"""HETOW passPE2 FRESH-ROUTE instrument (hostile verifier; zero reader
imports; exact residue algebra + dual PARI oracle routes).

DISJOINT from: the sealed battery's eta=1 frames, PE1's frames X/Y,
r1's frames Z/W.  Fresh frames (h = 1 everywhere):

 V (f2 = 3, ord(eta) = 6 -- the first multi-wrap frame anywhere;
   W = (1,1,0) with TWO live wrap units): p=7, Phi' = x^2-21, e1=2,
   f1=1, eta=3; (e2,f2)=(1,3), u2=3, psi2 = Z^3+Z^2+Z+2 irreducible
   (c2,c1,c0) = (6,6,5); Q(3)=1.
   coh key  = Phi'^3 - 42x*Phi'^2 - 1372*Phi' - 2401x
   naive    = Phi'^3 - 42x*Phi'^2 - 2058*Phi' - 12005x
 U (ord(eta) = 5 > 4, prime order): p=11, Phi' = x^2-33, eta=3;
   (e2,f2)=(1,2), u2=3, psi2 = Z^2+Z+4; W=(1,0), Q(3)=1.
   coh = Phi'^2 - 110x*Phi' - 13310;  naive = Phi'^2 - 110x*Phi' - 9317
 S (e2 = 2 wrap frame -- eta != 1 with e2 >= 2, a HETOW-BOX-3
   unexercised axis; twist trivial (eta^Q = 1), wrap live): p=3,
   Phi' = x^2-6, eta=2; (e2,f2)=(2,2), u2=5 (kappa2 = 5/2 > 2),
   psi2 = Z^2+Z+2; W=(1,0), Q(5)=2.  Slots {0,2}, heights {10,5}.
   coh = Phi'^4 - 18x*Phi'^2 - 486;  naive = Phi'^4 - 18x*Phi'^2 - 243
 R (f1 = 2 x eta != 1 -- another unexercised BOX-3 axis; ord(eta)=8;
   first two-digit (LIFT); e1=3 so r' = e1-2 = 1 MAXIMAL for the F-2
   carry check): p=5, Phi' = x^6-50 (genre (5;3,2,1), K = F_25 =
   F_5(w), w^2 = 2, eta = w); (e2,f2)=(1,2), u2=8 > D'h=6, i(8)=2,
   Q(8)=2, W=(1,0); psi2 = Z^2+Z+(1+w) irreducible over F_25.
   L_8(-1) = 100x^2; L_16(c0*eta) = 9375x + 2500x^4 (c0*eta = 3+4w);
   L_16(c0) = 12500x + 2500x^4 (c0 = 4+4w).
   coh = Phi'^2 - 100x^2*Phi' - 2500x^4 - 9375x
   naive = Phi'^2 - 100x^2*Phi' - 2500x^4 - 12500x

PREREGISTERED PREDICTIONS (scored; any miss = RED):
 E1 W-two-ways per frame: Q(f2*u2) - f2*Q(u2) == floor(f2*i(u2)/e1)
    (V additionally: Q(6)-2Q(3) == W(1) == 1).
 E2 corrected slot residues == minpoly(beta), beta = eta^{-Q(u2)}eta2:
    V: Z^3+5Z^2+4Z+5; U: Z^2+4Z+9; S: Z^2+Z+2 (= psi2: twist trivial,
    wrap-only frame -- twist-real check N/A at S, scored at V/U/R);
    R: Z^2+3Z+(4+4w) over F_25.
 E3 naive slot poly diverges from minpoly(beta) at every frame:
    V: Z^3+5Z^2+6Z+4 IRREDUCIBLE over F_7 (predicted: the first
    sigma-BLIND wrap frame -- naive sigma = carrier sigma, only the
    LETTER distinguishes); U: Z^2+4Z+3 = (Z+1)(Z+3);
    S: Z^2+Z+1 = (Z+2)^2; R: Z^2+3Z+(4+2w) = (Z-(4+3w))(Z-(3+2w)).
 G1 sigma(coh) = composed carrier: V {(2,3)}, U {(2,2)}, S {(4,2)},
    R {(3,4)}.
 G2 TOOTH sigma(naive): U {(2,1),(2,1)}; R {(3,2),(3,2)};
    S != {(4,2)} (INFO shape; killed poly a square);
    V == {(2,3)} SCORED AS EQUAL (sigma-blind seam) -- the tooth at V
    is G2L only.
 G2L LETTER jobs (route 1, nfmodpr): eta2bar := res(Phi'(x)^{e2}/
    n(u2)(x)) in the residue field; V: psi2(eta2bar)=0 at coh,
    psi2(eta2bar)!=0 AND N(eta2bar)=0 at naive; R: same with
    psi2 = Z^2+Z+(1+wbar), N = Z^2+3Z+(4+2*wbar), wbar = res(x^3/5).
 G3 mu2 = 2 trichotomy members at V (n = 12, T2 = 9; GENHN-T(b)'(iii)
    composed trichotomy at a wrap frame, from the display side):
    RAM (dv2(A0)=19) -> {(4,3)} x2 FORCED; 2SIDED (pins (0,21),(1,10))
    -> {(2,3),(2,3)} x2 FORCED; INERT-family (dv2(A0)=20, c in
    {1,2,3,5}) menu {{(4,3)},{(2,6)},{(2,3),(2,3)}}; 3RAM mu2=3
    (dv2(A0)=28, n=18) -> {(6,3)} FORCED (first f2=3 mu2=3 contact).
 G4 first e2f2 = 4 contact at S (mu2 = 2, n = 16, T2 = 20):
    RAM A0 = pi^9*Phi' (dv2 = 41) -> {(8,2)} FORCED; integer-lambda2
    A0 = c*x*pi^10 (dv2 = 42) menu {{(8,2)},{(4,4)},{(4,2),(4,2)}}.
 G5 F-2 stationary/moved accounting at R (r' = e1-2 = 1 maximal),
    v_pr-units = dv2: v(x0)=1, v(Phi'(x0))=8, v(x0^7)=7,
    v(x0^7 - 50*x0) = 9 (= 1 + 8, the moved piece x0*Phi'(x0):
    residue of the overflow monomial x^7 = residue of the stationary
    piece 50x at height 7 -- the O[x]-identity leg).
 G6 slot-lemma (GENHN-2') exactness ties at R, v_pr = dv2 = 16 on:
    3*x^4*625 + 2*x*3125 (digit tie), x^4*625 + x*3125,
    Phi'(x)^2 + 2*x*3125 (letter tie), Phi'(x)^2 + 3*x^4*625.
 All sigma jobs run BOTH oracle routes (factorpadic+idealprimedec vs
 factor/Q+idealprimedec); letter/valuation jobs are route-1 only
 (disclosed).  SMOKE record: exact legs E1-E3 smoke-run before the gp
 battery (HETOWPE2_SMOKE=1); no full-run result seen before seal.
VERDICT: GREEN iff 0 violations."""
import json, os, subprocess, time

# ---------------------------------------------------- exact Z[x] core
def padd(a, b):
    n = max(len(a), len(b)); out = [0]*n
    for i, c in enumerate(a): out[i] += c
    for i, c in enumerate(b): out[i] += c
    while out and out[-1] == 0: out.pop()
    return out

def pscal(k, a): return [k*c for c in a] if k else []

def pmul(a, b):
    if not a or not b: return []
    out = [0]*(len(a)+len(b)-1)
    for i, c in enumerate(a):
        for j, d in enumerate(b): out[i+j] += c*d
    while out and out[-1] == 0: out.pop()
    return out

def ppow(a, k):
    out = [1]
    for _ in range(k): out = pmul(out, a)
    return out

def pdivmod(a, b):
    a = list(a); q = []
    while len(a) >= len(b) and a:
        c = a[-1]; d = len(a)-len(b)
        q = padd(q, [0]*d + [c])
        a = padd(a, pscal(-c, [0]*d + b))
    return q, a

def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'

def vp(n, p):
    if n == 0: return 10**9
    k = 0
    while n % p == 0: n //= p; k += 1
    return k

VIOL = []
def check(leg, ok, detail):
    print('  %-34s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

# ------------------------------------------- F_p / F_{p^2} = F_p(w) core
class Fq:                              # F_p[w]/(w^2 - wsq); wsq=None -> F_p
    def __init__(self, p, wsq=None): self.p, self.wsq = p, wsq
    def norm(self, a):
        if self.wsq is None: return a % self.p
        return (a[0] % self.p, a[1] % self.p)
    def add(self, a, b):
        if self.wsq is None: return (a + b) % self.p
        return ((a[0]+b[0]) % self.p, (a[1]+b[1]) % self.p)
    def mul(self, a, b):
        if self.wsq is None: return (a * b) % self.p
        return ((a[0]*b[0] + self.wsq*a[1]*b[1]) % self.p,
                (a[0]*b[1] + a[1]*b[0]) % self.p)
    def scal(self, k, a):
        if self.wsq is None: return (k*a) % self.p
        return ((k*a[0]) % self.p, (k*a[1]) % self.p)
    def zero(self): return 0 if self.wsq is None else (0, 0)
    def pow(self, a, k):
        out = 1 if self.wsq is None else (1, 0)
        for _ in range(k): out = self.mul(out, a)
        return out
    def inv(self, a):
        n = self.p**2 - 2 if self.wsq is not None else self.p - 2
        return self.pow(a, n)
    def elts(self):
        if self.wsq is None: return list(range(self.p))
        return [(i, j) for i in range(self.p) for j in range(self.p)]

def minpoly_deg(K, beta, deg):
    """monic degree-`deg` polys over K killing beta in K[Z]/(psi2)-arith
    supplied by mul2/add2 closures -- here beta lives in K2 given as
    pairs over K; returns coeff tuple (c_0..c_{deg-1}) or None."""
    return None  # placeholder (frame-specific search below)

# ------------------------------------------------------- frame objects
class Frame:
    """f1 = 1 frames (V, U, S): K = F_p; psi2 of degree f2 over F_p."""
    def __init__(self, name, p, e1, phip, eta, e2, f2, u2, cs, carrier):
        # cs = (c_0, ..., c_{f2-1}) of psi2 = Z^f2 - sum c_t Z^t, mod p
        self.name, self.p, self.e1, self.phip = name, p, e1, phip
        self.eta, self.e2, self.f2, self.u2 = eta, e2, f2, u2
        self.cs, self.carrier = cs, carrier
    def i(self, k): return k % self.e1                     # h = 1
    def Q(self, k): return (k - self.i(k)) // self.e1
    def W(self, t): return ((self.f2 - t)*self.i(self.u2)) // self.e1
    def nhat(self, k): return [0]*self.i(k) + [self.p**self.Q(k)]
    def key(self, corrected):
        f = ppow(self.phip, self.e2*self.f2)
        for t in range(self.f2):
            c = self.cs[t] * (self.eta**self.W(t) if corrected else 1) % self.p
            term = pmul(pscal(c, self.nhat((self.f2-t)*self.u2)),
                        ppow(self.phip, self.e2*t))
            f = padd(f, pscal(-1, term))
        return f
    def slot_res(self, c, k):
        p, r, seen = self.p, 0, False
        for a, ca in enumerate(c):
            if ca == 0: continue
            hgt = self.e1*vp(ca, p) + a
            if hgt < k: return None
            if hgt == k:
                seen = True
                g = vp(ca, p); u = ca // p**g
                r = (r + u*pow(self.eta, (-g) % (p-1) if g else 0, p)) % p
        return r % p if seen else 0
    def killed(self, key):
        cs, q = [], list(key)
        for t in range(self.f2):
            q, rem = pdivmod(q, ppow(self.phip, self.e2))
            cs.append(self.slot_res(rem, (self.f2-t)*self.u2))
        assert q == [1], (self.name, q)
        return tuple(cs)          # (const, ..., Z^{f2-1}) coefficients
    def minpoly_beta(self):
        p, f2 = self.p, self.f2
        # K2 = F_p[Z]/(psi2); beta = eta^{-Q(u2)} * Z
        def red(vec):             # reduce Z^f2 -> sum cs[t] Z^t
            vec = list(vec)
            while len(vec) > f2:
                top = vec.pop()
                for t in range(f2): vec[t] = (vec[t] + top*self.cs[t]) % p
            while len(vec) < f2: vec.append(0)
            return [v % p for v in vec]
        def mulz(a, b):
            out = [0]*(len(a)+len(b)-1)
            for i, x in enumerate(a):
                for j, y in enumerate(b): out[i+j] += x*y
            return red(out)
        ei = pow(self.eta, (-self.Q(self.u2)) % (p-1) if self.Q(self.u2)
                 else 0, p)
        beta = red([0, ei])
        pows = [red([1])]
        for _ in range(f2): pows.append(mulz(pows[-1], beta))
        # solve beta^f2 + sum_{t<f2} r_t beta^t = 0 over F_p (linear)
        import itertools
        for rr in itertools.product(range(p), repeat=f2):
            acc = [pows[f2][j] for j in range(f2)]
            for t, r in enumerate(rr):
                for j in range(f2): acc[j] = (acc[j] + r*pows[t][j]) % p
            if all(a == 0 for a in acc): return tuple(rr)
        return None

FV = Frame('V', 7, 2, [-21, 0, 1], 3, 1, 3, 3, (5, 6, 6), ((2, 3),))
FU = Frame('U', 11, 2, [-33, 0, 1], 3, 1, 2, 3, (7, 10), ((2, 2),))
FS = Frame('S', 3, 2, [-6, 0, 1], 2, 2, 2, 5, (1, 2), ((4, 2),))

# ------------------------------------------------ frame R (K = F_25)
class FrameR:
    name, p, e1, f2, u2, carrier = 'R', 5, 3, 2, 8, ((3, 4),)
    phip = [-50, 0, 0, 0, 0, 0, 1]
    K = Fq(5, wsq=2)                      # w^2 = 2, eta = w
    eta = (0, 1)
    c0, c1 = (4, 4), (4, 0)               # psi2 = Z^2+Z+(1+w): -(1+w), -1
    def i(self, k): return k % 3
    def Q(self, k): return (k - self.i(k)) // 3
    def W(self, t): return ((2 - t)*2) // 3      # i(u2) = i(8) = 2
    def L(self, k, c):                     # (LIFT): digits in eta-basis
        d0, d1 = c[0] % 5, c[1] % 5        # c = d0 + d1*w
        a, q = self.i(k), self.Q(k)
        out = pscal(d0, [0]*a + [5**q])
        if d1: out = padd(out, pscal(d1, [0]*(a+3) + [5**(q-1)]))
        return out
    def key(self, corrected):
        K = self.K
        cc1 = self.c1                              # W(1) = 0
        cc0 = K.mul(self.c0, self.eta) if corrected else self.c0
        f = ppow(self.phip, 2)
        f = padd(f, pscal(-1, pmul(self.L(8, cc1), self.phip)))
        return padd(f, pscal(-1, self.L(16, cc0)))
    def slot_res(self, c, k):
        K, r, seen = self.K, self.K.zero(), False
        etainv = K.inv(self.eta)
        for a, ca in enumerate(c):
            if ca == 0: continue
            g = vp(ca, 5); hgt = 3*g + a
            if hgt < k: return None
            if hgt == k:
                seen = True
                r = K.add(r, K.scal(ca // 5**g, K.pow(etainv, g)))
        return K.norm(r) if seen else K.zero()
    def killed(self, key):
        q1, c0 = pdivmod(key, self.phip)
        q2, c1 = pdivmod(q1, self.phip)
        assert q2 == [1]
        return (self.slot_res(c0, 16), self.slot_res(c1, 8))
    def minpoly_beta(self):
        K = self.K
        cs = (self.c0, self.c1)               # Z^2 = c1 Z + c0
        ei = K.pow(K.inv(self.eta), self.Q(8))   # eta^{-Q(u2)}
        beta = (K.zero(), ei)                    # coords in K2 = K[Z]
        def mul2(a, b):
            d0 = K.mul(a[0], b[0]); d1 = K.add(K.mul(a[0], b[1]),
                                               K.mul(a[1], b[0]))
            d2 = K.mul(a[1], b[1])
            return (K.add(d0, K.mul(cs[0], d2)), K.add(d1, K.mul(cs[1], d2)))
        b2 = mul2(beta, beta)
        for r1 in K.elts():
            for r0 in K.elts():
                t0 = K.add(K.add(b2[0], K.mul(r1, beta[0])), r0)
                t1 = K.add(b2[1], K.mul(r1, beta[1]))
                if t0 == K.zero() and t1 == K.zero(): return (r0, r1)
        return None
FR = FrameR()

# ------------------------------------------------------------ exact legs
def exact_legs_f1(fr):
    naive, coh = fr.key(False), fr.key(True)
    print('frame %s: naive = %s' % (fr.name, polystr(naive)))
    print('frame %s: coh   = %s' % (fr.name, polystr(coh)))
    wd = fr.Q(fr.f2*fr.u2) - fr.f2*fr.Q(fr.u2)
    check('E1-W-two-ways-%s' % fr.name, wd == fr.W(0),
          'Q(%d)-%dQ(%d) = %d vs floor = %d'
          % (fr.f2*fr.u2, fr.f2, fr.u2, wd, fr.W(0)))
    if fr.name == 'V':
        w1 = fr.Q(2*fr.u2) - 2*fr.Q(fr.u2)
        check('E1-W1-two-ways-V', w1 == fr.W(1) == 1, 'Q(6)-2Q(3) = %d' % w1)
    kn, kc, mp = fr.killed(naive), fr.killed(coh), fr.minpoly_beta()
    print('  killed(naive) %s  killed(coh) %s  minpoly(beta) %s'
          % (kn, kc, mp))
    check('E2-coh-eq-minpoly-%s' % fr.name, kc == mp, '%s vs %s' % (kc, mp))
    if hasattr(fr, 'cs'):
        psi2 = tuple((-c) % fr.p for c in fr.cs)
    else:
        psi2 = tuple(fr.K.scal(-1, c) for c in (fr.c0, fr.c1))
    if fr.name != 'S':
        check('E2-twist-real-%s' % fr.name, mp != psi2,
              'minpoly %s != psi2 %s' % (mp, psi2))
    check('E3-naive-diverges-%s' % fr.name, kn != mp,
          'naive %s vs minpoly %s' % (kn, mp))
    check('E23-prereg-%s' % fr.name,
          kc == PRED_KILLED[fr.name]['coh'] and
          kn == PRED_KILLED[fr.name]['naive'],
          'prereg coh %s naive %s' % (PRED_KILLED[fr.name]['coh'],
                                      PRED_KILLED[fr.name]['naive']))
    return naive, coh

PRED_KILLED = {                     # preregistered exact values (scored)
    'V': {'coh': (5, 4, 5), 'naive': (4, 6, 5)},
    'U': {'coh': (9, 4), 'naive': (3, 4)},
    'S': {'coh': (2, 1), 'naive': (1, 1)},
    'R': {'coh': ((4, 4), (3, 0)), 'naive': ((4, 2), (3, 0))},
}

GP_HDR = r"""
default(parisize, "2000M");
ef(g, p) = { if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f] }
sig(f, p) = { my(F = factorpadic(f, p, 600));
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p))) }
sigq(f, p) = { my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1], my(g = fa[i, 1]);
    if (poldegree(g) == 1, listput(out, [1, 1]),
        my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out)) }
"""

def prs(t):
    ns = [int(x) for x in t.replace('[', ' ').replace(']', ' ')
          .replace(',', ' ').split()]
    return tuple(sorted(zip(ns[0::2], ns[1::2])))

def run_gp(script):
    out = subprocess.run(['gp', '-q', '-f'], input=script,
                         capture_output=True, text=True, timeout=3000)
    if out.returncode != 0:
        print('GP STDERR:', out.stderr[:2000])
    return out.stdout

def mono(a, g, b, fr):
    return pmul([0]*a + [fr.p**g], ppow(fr.phip, b))

def member(key, mu2, A):                    # A = {j: A_j}
    f = ppow(key, mu2)
    for j, Aj in A.items(): f = padd(f, pmul(Aj, ppow(key, j)))
    return f

MENU_V2 = {((4, 3),), ((2, 6),), ((2, 3), (2, 3))}
MENU_S2 = {((8, 2),), ((4, 4),), ((4, 2), (4, 2))}

def main():
    t0 = time.time()
    print('HETOW passPE2 fresh route: 4 new wrap frames (V f2=3, U ord5,'
          ' S e2=2, R f1=2) + letters + F-2 + slot ties')
    nV, cV = exact_legs_f1(FV)
    nU, cU = exact_legs_f1(FU)
    nS, cS = exact_legs_f1(FS)
    nR, cR = exact_legs_f1(FR)
    if os.environ.get('HETOWPE2_SMOKE'):
        print('SMOKE MODE: exact legs only, %d violations' % len(VIOL)); return
    jobs, tags, pred = [], [], []
    def add(f, p, tag, pr): jobs.append((f, p)); tags.append(tag); pred.append(pr)
    add(cV, 7, 'G1-coh-V', {FV.carrier}); add(cU, 11, 'G1-coh-U', {FU.carrier})
    add(cS, 3, 'G1-coh-S', {FS.carrier}); add(cR, 5, 'G1-coh-R', {FR.carrier})
    add(nV, 7, 'G2-naive-V-SIGMABLIND', {((2, 3),)})
    add(nU, 11, 'G2-TOOTH-naive-U', {((2, 1), (2, 1))})
    add(nS, 3, 'G2-TOOTH-naive-S', ('NOT', FS.carrier))
    add(nR, 5, 'G2-TOOTH-naive-R', {((3, 2), (3, 2))})
    for c in (1, 3):
        add(member(cV, 2, {0: pscal(c, mono(1, 9, 0, FV))}), 7,
            'G3-RAM', {((4, 3),)})
    for c in (1, 2):
        add(member(cV, 2, {0: pscal(c, mono(1, 10, 0, FV)),
                           1: mono(0, 5, 0, FV)}), 7,
            'G3-2SIDED', {((2, 3), (2, 3))})
    for c in (1, 2, 3, 5):
        add(member(cV, 2, {0: pscal(c, mono(0, 10, 0, FV))}), 7,
            'G3-INERTFAM', MENU_V2)
    add(member(cV, 3, {0: mono(0, 14, 0, FV)}), 7, 'G3-3RAM', {((6, 3),)})
    add(member(cS, 2, {0: mono(0, 9, 1, FS)}), 3, 'G4-RAM', {((8, 2),)})
    for c in (1, 2):
        add(member(cS, 2, {0: pscal(c, mono(1, 10, 0, FS))}), 3,
            'G4-INT', MENU_S2)
    lines = [GP_HDR]
    for i, (f, p) in enumerate(jobs):
        ps = polystr(f)
        lines.append('print("R %d ", poldisc(Pol(%s)) != 0, " ", sig(%s, %d),'
                     ' " | ", sigq(%s, %d))' % (i, ps, ps, p, ps, p))
    lines.append(
        'lv(f) = { my(nf=nfinit([f,[7]]), pr=idealprimedec(nf,7)[1],'
        ' X=Mod(x,f), e2b); e2b = nfmodpr(nf, nfeltdiv(nf, X^2-21, 7*X), pr);'
        ' [e2b^3+e2b^2+e2b+2 == 0, e2b^3+5*e2b^2+6*e2b+4 == 0] }')
    lines.append('print("L V-coh ", lv(Pol(%s)))' % polystr(cV))
    lines.append('print("L V-naive ", lv(Pol(%s)))' % polystr(nV))
    lines.append(
        'lr(f) = { my(nf=nfinit([f,[5]]), pr=idealprimedec(nf,5)[1],'
        ' X=Mod(x,f), wb, e2b); wb = nfmodpr(nf, nfeltdiv(nf, X^3, 5), pr);'
        ' e2b = nfmodpr(nf, nfeltdiv(nf, X^6-50, 25*X^2), pr);'
        ' [e2b^2+e2b+1+wb == 0, e2b^2+3*e2b+4+2*wb == 0, wb^2 == 2] }')
    lines.append('print("L R-coh ", lr(Pol(%s)))' % polystr(cR))
    lines.append('print("L R-naive ", lr(Pol(%s)))' % polystr(nR))
    lines.append(
        'gv() = { my(f=Pol(%s), nf=nfinit([f,[5]]),'
        ' pr=idealprimedec(nf,5)[1], X=Mod(x,f));'
        ' [pr.e, pr.f, idealval(nf,X,pr), idealval(nf,X^6-50,pr),'
        ' idealval(nf,X^7,pr), idealval(nf,X^7-50*X,pr),'
        ' idealval(nf,3*X^4*625+2*X*3125,pr), idealval(nf,X^4*625+X*3125,pr),'
        ' idealval(nf,(X^6-50)^2+2*X*3125,pr),'
        ' idealval(nf,(X^6-50)^2+3*X^4*625,pr)] }' % polystr(cR))
    lines.append('print("Vl R ", gv())')
    lines.append('quit')
    out = run_gp('\n'.join(lines))
    got, letters, vals = {}, {}, None
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            dnz, rest = rest.split(' ', 1)
            r1txt, r2txt = rest.split('|')
            got[int(idx)] = (dnz == '1', prs(r1txt), prs(r2txt))
        elif line.startswith('L '):
            tag, rest = line[2:].split(' ', 1)
            letters[tag] = [int(z) for z in rest.replace('[', ' ')
                            .replace(']', ' ').replace(',', ' ').split()]
        elif line.startswith('Vl R'):
            vals = [int(z) for z in line[4:].replace('[', ' ')
                    .replace(']', ' ').replace(',', ' ').split()]
    census = {}
    for i, tag in enumerate(tags):
        if i not in got:
            check(tag, False, 'gp job %d missing' % i); continue
        dnz, s1, s2 = got[i]
        check(tag + '-routes-agree', s1 == s2, '%s vs %s' % (s1, s2))
        if not dnz:
            print('  %-34s DROPPED (disc = 0)' % tag); continue
        if isinstance(pred[i], tuple) and pred[i][0] == 'NOT':
            check(tag, s1 != pred[i][1], 'sigma = %s (INFO)' % (s1,))
        else:
            check(tag, s1 in pred[i], 'sigma = %s' % (s1,))
        census[tag + ':' + str(s1)] = census.get(tag + ':' + str(s1), 0) + 1
    check('G2L-V-coh', letters.get('V-coh') == [1, 0],
          'psi2/N at eta2bar: %s (pred [1,0])' % letters.get('V-coh'))
    check('G2L-V-naive', letters.get('V-naive') == [0, 1],
          '%s (pred [0,1] -- the LETTER tooth at the sigma-blind frame)'
          % letters.get('V-naive'))
    check('G2L-R-coh', letters.get('R-coh') == [1, 0, 1],
          '%s (pred [1,0,1])' % letters.get('R-coh'))
    check('G2L-R-naive', letters.get('R-naive') == [0, 1, 1],
          '%s (pred [0,1,1])' % letters.get('R-naive'))
    check('G5G6-R-valuations', vals == [3, 4, 1, 8, 7, 9, 16, 16, 16, 16],
          '%s (pred [3,4,1,8,7,9,16,16,16,16])' % (vals,))
    print('\ncensus:')
    for k in sorted(census): print('   %-56s %d' % (k, census[k]))
    print('\nTOTAL gp sigma jobs %d + 4 letter + 1 val-block;'
          ' violations %d (%.1fs)' % (len(jobs), len(VIOL), time.time() - t0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))
    json.dump({'viol': VIOL, 'census': census, 'letters': letters,
               'vals': vals, 'jobs': len(jobs)},
              open('hetow_pe2_fresh_results.json', 'w'), indent=1)

if __name__ == '__main__':
    main()
