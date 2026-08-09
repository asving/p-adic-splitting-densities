#!/usr/bin/env python3
"""HETOW r1 SUPPLEMENTARY LEG (additive; the PE1 sealed battery and
hetow_pe1_fresh.py artifacts stay BYTE-FROZEN — this runner re-derives,
imports nothing from the program's readers).

Charge: machine-validate the wrap-corrected composed key
    Phi2 := Phi'^{e2 f2} - sum_{t<f2} lift(c_t * eta^{W(t)}) * n(u2(f2-t)) * Phi'^{e2 t},
    W(t) = floor((f2-t)*i(u2)/e1)
at PE1's frame X AND at two NEW eta != 1 frames, with an eta != 1 TOOTH:
the gauge-naive key (plain lifts c_t, the GENHN-T(b)'/HETOW display) must
FAIL the composed-carrier prediction at every wrap-live frame.

FRAMES (f1 = 1, h = 1, varpi = x, K = F_p throughout; i(k) = k mod e1,
Q(k) = (k - i(k))/e1; all exact-residue legs computed from scratch):
 X (PE1 regression): p=3, Phi' = x^2-6, e1=2, D'=2, eta=2 (ord 2);
   (e2,f2)=(1,2), u2=3, psi2 = Z^2+Z+2 (c1=-1, c0=-2), W=(1,0).
   keys: naive = Phi'^2+3xPhi'+54, coh = Phi'^2+3xPhi'+108.
 Z (NEW): p=5, Phi' = x^2-10, e1=2, D'=2, eta=2 (ord 4);
   (e2,f2)=(1,2), u2=3 > D'h=2, psi2 = Z^2+Z+1 (c1=-1, c0=-1), W=(1,0).
   keys: naive = Phi'^2+5xPhi'+125, coh = Phi'^2+5xPhi'+250.
 W (NEW, e1=3): p=5, Phi' = x^3-10, e1=3, D'=3, eta=2;
   (e2,f2)=(1,2), u2=5 > D'h=3, psi2 = Z^2+Z+1, n(5)=5x^2, n(10)=125x,
   W=(1,0).  keys: naive = Phi'^2+5x^2Phi'+125x, coh = Phi'^2+5x^2Phi'+250x.

PREREGISTERED PREDICTIONS (scored; any miss = RED):
 E1 (per frame): W(0) two ways agree: Q(f2*u2) - f2*Q(u2) == floor(f2*i(u2)/e1) = 1.
 E2 (per frame): killed(coh) == minpoly(beta), beta = eta^{-Q(u2)}*eta2:
    X: Z^2+2Z+2;  Z: Z^2+3Z+4;  W: Z^2+3Z+4.  Each != psi2 (twist real).
 E3 (per frame): killed(naive) != minpoly(beta), and killed(naive) has a
    root in F_p (degenerate): X: Z^2+2Z+1=(Z+1)^2; Z,W: Z^2+3Z+2=(Z+1)(Z+2).
 G1 (per frame): PARI sigma(coh key) = composed carrier {(e1e2, f1f2)}:
    X {(2,2)}, Z {(2,2)}, W {(3,2)}.
 G2 TOOTH (per frame): sigma(naive key) != carrier sigma.  Derived shapes
    scored where the killed poly is separable: Z -> {(2,1),(2,1)},
    W -> {(3,1),(3,1)}; X scored as != {(2,2)} only (killed poly is a
    square; PE1 measured {(4,1)}, recorded INFO).
 G3 (frame Z, mu2 = 3, n = 12, T2 = 6): members f = K^3+A2K^2+A1K+A0 on
    the coh key: forced 3RAM (slope 20/3) -> {(6,2)}; forced 2+1
    (pins (0,22),(1,15),(2,7)) -> {(2,2),(4,2)}; ONE21 (slope 7) in the
    case-B menu {(6,2)},{(2,6)},{(2,2)}^3,{(2,4),(2,2)},{(4,2),(2,2)}.
 G4 (frame W, mu2 = 3, n = 18, T2 = 10): forced 3RAM (slope 31/3) ->
    {(9,2)}; forced 2+1 (pins (0,34),(2,11)) -> {(3,2),(6,2)};
    integer-slope 11 members in the menu {(9,2)},{(3,6)},{(3,2)}^3,
    {(3,4),(3,2)},{(6,2),(3,2)}.
 All gp jobs run BOTH oracle routes (factorpadic+idealprimedec vs
 factor/Q+idealprimedec); routes must agree per job.

SMOKE RECORD (disclosed): exact legs E1-E3 + the six key polynomials were
smoke-run before sealing (HETOWR1_SMOKE=1, no gp); full gp battery runs
only after the seal commit.  VERDICT: GREEN iff 0 violations.
"""
import json, os, subprocess, time

# ------------------------------------------------------ exact Z[x] core
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

def pdivmod(a, b):                      # b monic
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

# --------------------------------------------------------- frame object
class Frame:
    def __init__(self, name, p, e1, phip, eta, u2, c1, c0, carrier):
        self.name, self.p, self.e1, self.phip = name, p, e1, phip
        self.eta, self.u2, self.c1, self.c0 = eta, u2, c1, c0
        self.f2 = 2; self.carrier = carrier          # composed sigma
        # psi2 = Z^2 - c1 Z - c0  (coeffs displayed mod p)
        self.psi2 = ((-c0) % p, (-c1) % p)           # (const, lin) of monic
    def i(self, k):  return k % self.e1              # h = 1 at every frame
    def Q(self, k):  return (k - self.i(k)) // self.e1
    def W(self, t):  return ((self.f2 - t) * self.i(self.u2)) // self.e1
    def nhat(self, k):                               # x^{i(k)} p^{a(k)}
        return [0]*self.i(k) + [self.p**self.Q(k)]
    def keys(self):
        """(naive, coh): Phi2 = Phi'^2 - c1h*n(u2)*Phi' - c0h*n(2u2)."""
        u2 = self.u2
        def build(l1, l0):
            t = padd(ppow(self.phip, 2),
                     pscal(-l1, pmul(self.nhat(u2), self.phip)))
            return padd(t, pscal(-l0, self.nhat(2*u2)))
        naive = build(self.c1, self.c0)
        coh = build(self.c1 * self.eta**self.W(1), self.c0 * self.eta**self.W(0))
        return naive, coh
    # residue algebra: K = F_p; res(x^a p^g / x^k) = eta^{-g} at e1*g+a = k
    def slot_res(self, c, k):
        p, r, seen = self.p, 0, False
        for a, ca in enumerate(c):
            if ca == 0: continue
            hgt = self.e1 * vp(ca, p) + a
            if hgt < k: return None
            if hgt == k:
                seen = True
                g = vp(ca, p); u = ca // p**g
                r = (r + u * pow(self.eta, -g % (p-1) if g else 0, p)) % p
        return r % p if seen else 0
    def killed(self, key):
        """Z^2 + r1 Z + r0 from key's slot varpi-residues (heights u2, 2u2)."""
        q1, c0 = pdivmod(key, self.phip)
        q2, c1 = pdivmod(q1, self.phip)
        assert q2 == [1], (self.name, q2)
        return (self.slot_res(c0, 2*self.u2), self.slot_res(c1, self.u2))
    def fqmul(self, a, b):
        # F_{p^2} = F_p[Z]/(psi2); Z^2 = c1 Z + c0 (as psi2 = Z^2-c1Z-c0)
        p, c1, c0 = self.p, self.c1 % self.p, self.c0 % self.p
        d0 = a[0]*b[0]; d1 = a[0]*b[1] + a[1]*b[0]; d2 = a[1]*b[1]
        return ((d0 + c0*d2) % p, (d1 + c1*d2) % p)
    def minpoly_beta(self):
        p = self.p
        etainv = pow(self.eta, -self.Q(self.u2) % (p-1) or 0, p) \
            if self.Q(self.u2) else 1
        beta = (0, etainv % p)                        # eta^{-Q(u2)} * eta2
        b2 = self.fqmul(beta, beta)
        for r1 in range(p):
            for r0 in range(p):
                if ((b2[0] + r1*beta[0] + r0) % p, (b2[1] + r1*beta[1]) % p) \
                        == (0, 0):
                    return (r0, r1)
        return None

FX = Frame('X', 3, 2, [-6, 0, 1], 2, 3, -1, -2, ((2, 2),))
FZ = Frame('Z', 5, 2, [-10, 0, 1], 2, 3, -1, -1, ((2, 2),))
FW = Frame('W', 5, 3, [-10, 0, 0, 1], 2, 5, -1, -1, ((3, 2),))

MENU_Z = {((2, 6),), ((6, 2),), ((2, 2), (2, 2), (2, 2)),
          ((2, 2), (2, 4)), ((2, 2), (4, 2))}
MENU_W = {((9, 2),), ((3, 6),), ((3, 2), (3, 2), (3, 2)),
          ((3, 2), (3, 4)), ((3, 2), (6, 2))}

GP_HDR = r"""
default(parisize, "2000M");
ef(g, p) = { if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f] }
sig(f, p) = { my(F = factorpadic(f, p, 400));
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p))) }
sigq(f, p) = { my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1], my(g = fa[i, 1]);
    if (poldegree(g) == 1, listput(out, [1, 1]),
        my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out)) }
"""

def gp_sigs(jobs):
    lines = [GP_HDR]
    for i, (f, p) in enumerate(jobs):
        ps = polystr(f)
        lines.append('print("R %d ", poldisc(Pol(%s)) != 0, " ", sig(%s, %d),'
                     ' " | ", sigq(%s, %d))' % (i, ps, ps, p, ps, p))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=3000)
    got = {}
    for line in out.stdout.splitlines():
        if not line.startswith('R '): continue
        idx, rest = line[2:].split(' ', 1)
        dnz, rest = rest.split(' ', 1)
        r1txt, r2txt = rest.split('|')
        def prs(t):
            ns = [int(x) for x in t.replace('[', ' ').replace(']', ' ')
                  .replace(',', ' ').split()]
            return tuple(sorted(zip(ns[0::2], ns[1::2])))
        got[int(idx)] = (dnz == '1', prs(r1txt), prs(r2txt))
    return got

VIOL = []
def check(leg, ok, detail):
    print('  %-30s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

def exact_legs(fr):
    naive, coh = fr.keys()
    print('frame %s: naive = %s' % (fr.name, polystr(naive)))
    print('frame %s: coh   = %s' % (fr.name, polystr(coh)))
    w_direct = fr.Q(fr.f2*fr.u2) - fr.f2*fr.Q(fr.u2)
    check('E1-W-two-ways-%s' % fr.name, w_direct == fr.W(0) == 1,
          'Q(%d)-2Q(%d) = %d vs floor = %d' %
          (2*fr.u2, fr.u2, w_direct, fr.W(0)))
    kn, kc, mp = fr.killed(naive), fr.killed(coh), fr.minpoly_beta()
    print('  killed(naive) Z^2+%dZ+%d  killed(coh) Z^2+%dZ+%d  '
          'minpoly(beta) Z^2+%dZ+%d' % (kn[1], kn[0], kc[1], kc[0],
                                        mp[1], mp[0]))
    check('E2-coh-eq-minpoly-%s' % fr.name, kc == mp,
          'slot residues %s vs minpoly %s' % (kc, mp))
    check('E2-twist-real-%s' % fr.name, mp != fr.psi2,
          'minpoly %s != psi2 %s' % (mp, fr.psi2))
    check('E3-naive-diverges-%s' % fr.name, kn != mp,
          'naive killed %s vs minpoly %s' % (kn, mp))
    has_root = any((z*z + kn[1]*z + kn[0]) % fr.p == 0 for z in range(fr.p))
    check('E3-naive-degenerate-%s' % fr.name, has_root,
          'killed(naive) has an F_%d root' % fr.p)
    return naive, coh

def mono(a, g, b, fr):                  # x^a p^g Phi'^b
    return pmul([0]*a + [fr.p**g], ppow(fr.phip, b))

def member(key, A0, A1, A2):
    f = ppow(key, 3)
    f = padd(f, pmul(A2, ppow(key, 2)))
    f = padd(f, pmul(A1, key))
    return padd(f, A0)

def main():
    t0 = time.time()
    print('HETOW r1 supp: wrap-corrected key at 3 eta != 1 frames + teeth')
    kxn, kxc = exact_legs(FX)
    kzn, kzc = exact_legs(FZ)
    kwn, kwc = exact_legs(FW)
    if os.environ.get('HETOWR1_SMOKE'):
        print('SMOKE MODE: exact legs only, %d violations' % len(VIOL)); return
    jobs, tags, pred = [], [], []
    def add(f, p, tag, pr): jobs.append((f, p)); tags.append(tag); pred.append(pr)
    add(kxc, 3, 'G1-coh-X', {FX.carrier}); add(kzc, 5, 'G1-coh-Z', {FZ.carrier})
    add(kwc, 5, 'G1-coh-W', {FW.carrier})
    add(kxn, 3, 'G2-TOOTH-naive-X', ('NOT', FX.carrier))
    add(kzn, 5, 'G2-TOOTH-naive-Z', {((2, 1), (2, 1))})
    add(kwn, 5, 'G2-TOOTH-naive-W', {((3, 1), (3, 1))})
    # G3: frame Z members (dv2(x,pi,Phi') = (1,2,3), T2 = 6)
    for c in (1, 2):
        for rep in ((0, 10, 0), (1, 8, 1)):
            add(member(kzc, pscal(c, mono(*rep, FZ)), [], []), 5,
                'G3-3RAM', {((6, 2),)})
        for rep0, rep1 in (((0, 11, 0), (1, 7, 0)), ((1, 9, 1), (0, 6, 1))):
            add(member(kzc, pscal(c, mono(*rep0, FZ)), mono(*rep1, FZ),
                       mono(1, 3, 0, FZ)), 5, 'G3-2+1', {((2, 2), (4, 2))})
    n_one21 = 0
    for i0, A0 in enumerate([pscal(c, mono(*rep, FZ)) for c in (1, 2)
                             for rep in ((1, 10, 0), (0, 9, 1))]):
        for i1, A1 in enumerate([[], mono(0, 7, 0, FZ)]):
            for i2, A2 in enumerate([[], mono(1, 3, 0, FZ)]):
                if (i0 + i1 + i2) % 2 == 0:
                    add(member(kzc, A0, A1, A2), 5, 'G3-ONE21', MENU_Z)
                    n_one21 += 1
    # G4: frame W members (dv2(x,pi,Phi') = (1,3,5), T2 = 10)
    for c in (1, 2):
        add(member(kwc, pscal(c, mono(1, 10, 0, FW)), [], []), 5,
            'G4-3RAM', {((9, 2),)})
        add(member(kwc, pscal(c, mono(1, 11, 0, FW)), [],
                   mono(2, 3, 0, FW)), 5, 'G4-2+1', {((3, 2), (6, 2))})
        add(member(kwc, pscal(c, mono(0, 11, 0, FW)), [], []), 5,
            'G4-int-slope', MENU_W)
    add(member(kwc, mono(0, 11, 0, FW), mono(1, 7, 0, FW),
               mono(0, 4, 0, FW)), 5, 'G4-int-slope', MENU_W)
    print('%d gp jobs (both routes on all; %d ONE21) ...'
          % (len(jobs), n_one21))
    got = gp_sigs(jobs)
    census = {}
    for i, tag in enumerate(tags):
        if i not in got:
            check(tag, False, 'gp job %d missing' % i); continue
        dnz, s1, s2 = got[i]
        check(tag + '-routes-agree', s1 == s2, '%s vs %s' % (s1, s2))
        if not dnz:
            print('  %-30s DROPPED (disc = 0)' % tag); continue
        if isinstance(pred[i], tuple) and pred[i][0] == 'NOT':
            check(tag, s1 != pred[i][1], 'sigma = %s (INFO)' % (s1,))
        else:
            check(tag, s1 in pred[i], 'sigma = %s' % (s1,))
        census[tag + ':' + str(s1)] = census.get(tag + ':' + str(s1), 0) + 1
    print('\ncensus:')
    for k in sorted(census): print('   %-56s %d' % (k, census[k]))
    print('\nTOTAL jobs %d violations %d (%.1fs)'
          % (len(jobs), len(VIOL), time.time() - t0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))
    json.dump({'viol': VIOL, 'census': census, 'jobs': len(jobs)},
              open('hetowr1_supp_results.json', 'w'), indent=1)

if __name__ == '__main__':
    main()
