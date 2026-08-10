#!/usr/bin/env python3
"""HETOW TOWERRAT-R1 leg: LEMMA HETOW-4 (the normalizer bridge
n-hat-2 vs HE7's n2) verified at committed battery frames.

Charge (CODEX_TOWERRAT_2026-08-10.md S2 F-1 / S6 R1): the S1 row
"unit-residue discrepancy in K2^x only; sigma-content twist-invariant
(J-D0)" asserted coverage without the formula.  This runner verifies
the DERIVED formula and its consequences:

  (a) IDENTITY: n2hat(k) = nhat(m(k)) * Phi'^{s(k)} with
      s(k) = k*u2^{-1} mod e2, m(k) = (k - s(k)u2)/e2, hence
      n2hat(k)/n2(k) = nhat(m(k))/varpi^{m(k)} = (x^{e1}/pi^h)^{-Q(m(k))}
      as Laurent monomials; residue at locus points = eta^{-Q(m(k))}
      =: tau(k)  (a grade-determined power of the LEVEL-1 letter).
  (b) ASSEMBLED-RESIDUAL BRIDGE (the telescoping): with each system's
      own cocycle bracket (HE7 S5.3 Step 2 / GENHN S4 coherence), the
      side-residual coefficients are rho_t = res(A_j * N(u3)^t / N(H0)),
      so   rho_t(he7) = rho_t(hat) * tau(H0) * delta^{-t},
      delta := tau(u3), i.e. R(Z) = tau(H0) * Rhat(Z/delta): a global
      unit times a K^x variable rescale = the J-D0-covered species.
  (c) ROUTING TRANSPORT: factor multisets (deg, mult) equal, separability
      equal, K2-rational roots s2 = delta*s2hat; SEP members' sigma
      dictionary (e1e2*l2, f1f2*deg r2) matches PARI on dual routes.
  (d) RAW TOOTH: WITHOUT the brackets the per-height residue strings
      differ (tau(H_t) != 1) and are non-geometric in t at eta != 1
      frames -- the per-height twist does NOT cancel; only the
      assembled comparison does.

FRAMES (committed data, byte-same as hetowr1_supp.py / hetow_pe2_fresh.py;
h = 1, f1 = 1, varpi = x, i0 = 1 at each):
  X: p=3, e1=2, Phi'=x^2-6,  eta=2, (e2,f2)=(1,2), u2=3, psi2=Z^2+Z+2
  Z: p=5, e1=2, Phi'=x^2-10, eta=2, (e2,f2)=(1,2), u2=3, psi2=Z^2+Z+1
  S: p=3, e1=2, Phi'=x^2-6,  eta=2, (e2,f2)=(2,2), u2=5, psi2=Z^2-2Z-1

PREREGISTERED PREDICTIONS (derived in the note append; any miss = RED):
  P-A  identity legs pass at k = 1..60 per frame (exact).
  P-B  bridge rho(he7)_t == rho(hat)_t * tau(H0) * delta^{-t} at every
       scored side; derived constants: X/Z INT7 (u3=7): delta=2, tau(14)=2,
       tau(21)=1; X/Z HALF15: delta=tau(15)=2; X/Z MU3-20: delta=tau(20)=1;
       S INT21: delta=tau(21)=1 (letter-dead side); S HALF43: delta=tau(43)=2
       (letter-LIVE at e2=2).
  P-C  factor/routing/sigma transport on every member; PARI dual routes
       agree; coverage: X grid realizes SEP-IRRED + SEP-SPLIT + REP-LIN
       (derived: c1=0/A0=3^5xPhi' irred; c1=0/A0=3^7 split; c1=1/A0=2*3^7
       rep at shat=1); Z grid realizes SEP-SPLIT + REP-LIN (c1=0/c0=2 split;
       c1=1/c0=3 rep at shat=2); other classes recorded.
  P-D  T-RAW fires at X and at Z (INT7 tau-string (2,2,1) non-geometric,
       mu2=3 string (1,2,2,1) non-geometric); at S: INT21 raw strings
       EQUAL (tau trivial: Q(21),Q(8),Q(0) even) while the e2-bracket is
       live (c_1 = 1, bracket residue = beta != 1); HALF43 raw DIFFERS
       (Q(19) = 9 odd).
  P-E  HE7-bracket cross-check: res(n2-bracket) == beta^{c_t},
       c_t = (s(H_t) + t*s(u3) - s(H0))/e2 integer, beta = eta^{-Q(u2)}eta2.
  G0   each frame's corrected key has PARI sigma = carrier
       (X {(2,2)}, Z {(2,2)}, S {(4,2)}), dual routes.

SMOKE RECORD (disclosed): exact legs P-A/P-B smoke-run pre-seal at frame X
only (HETOW4_SMOKE=1); full battery + gp only after the seal commit.
VERDICT: GREEN iff 0 violations.
"""
import json, os, subprocess, time

# ---------------------------------------------------------- Z[x] core
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

def pdivmod(a, b):                        # b monic
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
def check(leg, ok, detail=''):
    print('  %-34s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

# ------------------------------------------------------------- frames
class Frame:
    """h = 1, f1 = 1, varpi = x (i0 = 1, a0 = 0); psi2 = Z^2 - c1 Z - c0."""
    def __init__(self, name, p, e1, phip, eta, e2, u2, c0, c1, carrier):
        self.name, self.p, self.e1, self.phip = name, p, e1, phip
        self.eta, self.e2, self.f2, self.u2 = eta, e2, 2, u2
        self.c0, self.c1, self.carrier = c0, c1, carrier
        self.q = p*p
    # level-1 ladder (h = 1)
    def i(self, k):  return k % self.e1
    def Q(self, k):  return (k - self.i(k)) // self.e1
    def W(self, t):  return ((self.f2 - t)*self.i(self.u2)) // self.e1
    # level-2 ladder bookkeeping
    def s2(self, k):
        return (k * pow(self.u2, -1, self.e2)) % self.e2 if self.e2 > 1 else 0
    def m2(self, k): return (k - self.s2(k)*self.u2) // self.e2
    def nhat2(self, k):   # (pi, x, Phi') exponents of n2hat(k)
        m = self.m2(k)
        return (self.Q(m), self.i(m), self.s2(k))
    def nhe7(self, k):    # (pi, x, Phi') exponents of n2(k) = varpi^m Phi'^s
        return (0, self.m2(k), self.s2(k))
    def tau(self, k):     # res(n2hat(k)/n2(k)) = eta^{-Q(m2(k))} in F_p
        return pow(self.eta, (-self.Q(self.m2(k))) % (self.p - 1), self.p)
    # K2 = F_p[Z]/(psi2), elements (a0, a1) = a0 + a1*eta2
    def fq(self, x): return (x % self.p, 0)
    def fqadd(self, a, b): return ((a[0]+b[0]) % self.p, (a[1]+b[1]) % self.p)
    def fqmul(self, a, b):
        p, c1, c0 = self.p, self.c1 % self.p, self.c0 % self.p
        d0 = a[0]*b[0]; d1 = a[0]*b[1] + a[1]*b[0]; d2 = a[1]*b[1]
        return ((d0 + c0*d2) % p, (d1 + c1*d2) % p)
    def fqinv(self, a):
        for x0 in range(self.p):
            for x1 in range(self.p):
                if self.fqmul(a, (x0, x1)) == (1, 0): return (x0, x1)
        raise ZeroDivisionError(a)
    def fqpow(self, a, k):
        if k < 0: a, k = self.fqinv(a), -k
        out = (1, 0)
        for _ in range(k): out = self.fqmul(out, a)
        return out
    def allfq(self):
        return [(a, b) for a in range(self.p) for b in range(self.p)]
    def res0(self, v, a, b):
        """residue of the dv2-0 Laurent monomial pi^v x^a Phi'^b."""
        assert self.e1*self.e2*v + a*self.e2 + b*self.u2 == 0, (v, a, b)
        assert b % self.e2 == 0, (v, a, b)
        be = b // self.e2
        a2 = a + self.i(self.u2)*be
        v2 = v + self.Q(self.u2)*be
        assert a2 % self.e1 == 0, (v, a, b)
        g = a2 // self.e1
        assert v2 == -g, (v, a, b, v2, g)
        sc = pow(self.eta, g % (self.p - 1), self.p)
        return self.fqmul(self.fq(sc), self.fqpow((0, 1), be))
    def key(self):
        """corrected composed key Phi2 (wrap-corrected lifts)."""
        f = ppow(self.phip, self.e2*self.f2)
        for t, ct in ((0, self.c0), (1, self.c1)):
            k = (self.f2 - t)*self.u2
            lift = [0]*self.i(k) + [self.p**self.Q(k)]     # nhat(k)
            co = ct * self.eta**self.W(t)
            f = padd(f, pscal(-co, pmul(lift, ppow(self.phip, self.e2*t))))
        return f

FX = Frame('X', 3, 2, [-6, 0, 1],  2, 1, 3, -2, -1, ((2, 2),))
FZ = Frame('Z', 5, 2, [-10, 0, 1], 2, 1, 3, -1, -1, ((2, 2),))
FS = Frame('S', 3, 2, [-6, 0, 1],  2, 2, 5, 1, 2, ((4, 2),))

# ------------------------------------------- residues along one side
def monomials(fr, A):
    """(v, a, b, unit) list of A's composed-grid monomials."""
    out, b = [], 0
    while A:
        A, cb = pdivmod(A, fr.phip)
        for a, c in enumerate(cb):
            if c: out.append((vp(c, fr.p), a, b, c // fr.p**vp(c, fr.p)))
        b += 1
    return out

def raw(fr, A, H, sysN):
    """res(A / N(H)) for N = sysN (exponent triple fn); asserts no
    monomial below height H."""
    r = (0, 0); nv, na, nb = sysN(H)
    for v, a, b, u in monomials(fr, A):
        h = fr.e1*fr.e2*v + a*fr.e2 + b*fr.u2
        assert h >= H, ('below-line', v, a, b, H)
        if h == H:
            r = fr.fqadd(r, fr.fqmul(fr.fq(u), fr.res0(v-nv, a-na, b-nb)))
    return r

def assembled(fr, Ajs, mu2, l2, u3, sysN):
    """[rho_t]: rho_t = res(A_{l2 t} * N(u3)^t / N(H0)), t = 0..d."""
    d = mu2 // l2; H0 = d*u3
    Nu, N0 = sysN(u3), sysN(H0)
    out = []
    for t in range(d + 1):
        j = l2*t
        A = [1] if j == mu2 else Ajs.get(j, [])
        Ht = H0 - t*u3
        if not A:
            out.append((0, 0)); continue
        rw = raw(fr, A, Ht, sysN)
        NH = sysN(Ht)
        br = tuple(NH[i] + t*Nu[i] - N0[i] for i in range(3))
        out.append(fr.fqmul(rw, fr.res0(*br)))
    return out

# ------------------------------------ deg <= 3 factoring over K2, routing
def factorK2(fr, R):
    """R low->high over K2, deg <= 3 -> (factors [(deg, mult, root)], lead)."""
    R = list(R)
    while R and R[-1] == (0, 0): R.pop()
    lead = R[-1]; li = fr.fqinv(lead)
    R = [fr.fqmul(li, c) for c in R]                     # monic
    facs = []
    for r in fr.allfq():                                 # root peeling
        mult = 0
        while len(R) > 1:
            q, rem = [], (0, 0)                          # synth. division
            for c in reversed(R[1:]):
                rem = fr.fqadd(fr.fqmul(rem, r), c); q.append(rem)
            if fr.fqadd(fr.fqmul(rem, r), R[0]) != (0, 0): break
            R = list(reversed(q)); mult += 1
        if mult: facs.append((1, mult, r))
    if len(R) - 1 >= 2:
        assert len(R) - 1 in (2, 3)
        facs.append((len(R) - 1, 1, None))               # irreducible tail
    return facs, lead

def routing(fr, facs, l2):
    if all(m == 1 for _, m, _ in facs):
        sig = tuple(sorted((fr.e1*fr.e2*l2, fr.f2*dg) for dg, m, _ in facs))
        return 'SEP', sig
    if l2 == 1 and all(dg == 1 for dg, m, _ in facs if m >= 2):
        return 'REFINE', None
    return 'LEVEL3', None

# ----------------------------------------------------------------- gp
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
        lines.append('print("R %d ", sig(%s, %d), " | ", sigq(%s, %d))'
                     % (i, ps, p, ps, p))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=3000)
    got = {}
    for line in out.stdout.splitlines():
        if not line.startswith('R '): continue
        idx, rest = line[2:].split(' ', 1)
        r1, r2 = rest.split('|')
        def prs(t):
            ns = [int(x) for x in t.replace('[', ' ').replace(']', ' ')
                  .replace(',', ' ').split()]
            return tuple(sorted(zip(ns[0::2], ns[1::2])))
        got[int(idx)] = (prs(r1), prs(r2))
    return got

# -------------------------------------------------------------- members
def mono(fr, v, a, b):
    return pmul([0]*a + [fr.p**v], ppow(fr.phip, b))

def members(fr, key):
    """[(tag, mu2, l2, u3, {j: A_j})] scored sides ending at (mu2, 0)."""
    out = []
    if fr.e2 == 1:                                    # frames X, Z
        p7, p14f1, p14f2 = mono(fr, 3, 1, 0), mono(fr, 7, 0, 0), \
            mono(fr, 5, 1, 1)
        for c1 in (0, 1, 2):
            for tag, A0 in (('f1', p14f1), ('2f1', pscal(2, p14f1)),
                            ('f2', p14f2)):
                out.append(('INT7-c1=%d-%s' % (c1, tag), 2, 1, 7,
                            {1: pscal(c1, p7), 0: A0}))
        if fr.name == 'Z':                            # REP-LIN coverage at Z
            out.append(('INT7-c1=1-3f1', 2, 1, 7,
                        {1: p7, 0: pscal(3, p14f1)}))
        for c in (1, 2):
            out.append(('HALF15-c=%d' % c, 2, 2, 15,
                        {0: pscal(c, mono(fr, 7, 1, 0))}))
        out.append(('MU3-20', 3, 3, 20, {0: mono(fr, 8, 1, 1)}))
        for c2, c1, c0 in ((1, 1, 1), (2, 0, 1), (0, 1, 2)):
            out.append(('MU3-INT7-%d%d%d' % (c2, c1, c0), 3, 1, 7,
                        {2: pscal(c2, mono(fr, 3, 1, 0)),
                         1: pscal(c1, mono(fr, 7, 0, 0)),
                         0: pscal(c0, mono(fr, 9, 0, 1))}))
    else:                                             # frame S (e2 = 2)
        p21, p42f, p42x = mono(fr, 4, 0, 1), mono(fr, 8, 0, 2), \
            mono(fr, 10, 1, 0)
        for c1 in (0, 1, 2):
            for tag, A0 in (('f', p42f), ('2f', pscal(2, p42f)),
                            ('x', p42x)):
                if c1 == 2 and tag != 'f': continue
                out.append(('INT21-c1=%d-%s' % (c1, tag), 2, 1, 21,
                            {1: pscal(c1, p21), 0: A0}))
        for c in (1, 2):
            out.append(('HALF43-c=%d' % c, 2, 2, 43,
                        {0: pscal(c, mono(fr, 9, 1, 1))}))
    return out

def member_poly(fr, key, mu2, Ajs):
    f = ppow(key, mu2)
    for j, A in Ajs.items():
        f = padd(f, pmul(A, ppow(key, j)))
    return f

def run_frame(fr, jobs, tags, preds):
    print('--- frame %s (p=%d, e1=%d, e2=%d, u2=%d, eta=%d)'
          % (fr.name, fr.p, fr.e1, fr.e2, fr.u2, fr.eta))
    # P-A identity leg
    okA = True
    for k in range(1, 61):
        nh = fr.nhat2(k); m = fr.m2(k)
        ok = (nh == (fr.Q(m), fr.i(m), fr.s2(k)))
        # independent ladder solve
        sols = [(v, i, b) for b in range(fr.e2) for i in range(fr.e1)
                for v in [(k - b*fr.u2 - i*fr.e2) // (fr.e1*fr.e2)]
                if fr.e1*fr.e2*v + i*fr.e2 + b*fr.u2 == k]
        ok = ok and len(sols) == 1 and sols[0] == nh
        # Laurent ratio = (x^{e1}/pi)^{-Q(m)}
        dv, da, db = (nh[0] - 0, nh[1] - m, nh[2] - fr.s2(k))
        ok = ok and (da == -fr.e1*fr.Q(m)) and (dv == fr.Q(m)) and db == 0
        okA = okA and ok
    check('P-A-identity-%s' % fr.name, okA, 'k = 1..60')
    key = fr.key()
    print('  key = %s' % polystr(key))
    jobs.append((key, fr.p)); tags.append('G0-key-%s' % fr.name)
    preds.append({fr.carrier})
    tooth_raw, raw_eq_int, classes = False, True, set()
    for tag, mu2, l2, u3, Ajs in members(fr, key):
        d = mu2 // l2; H0 = d*u3
        rh = assembled(fr, Ajs, mu2, l2, u3, fr.nhat2)
        r7 = assembled(fr, Ajs, mu2, l2, u3, fr.nhe7)
        tauH0, dlt = fr.tau(H0), fr.tau(u3)
        # P-B bridge
        okB = all(r7[t] == fr.fqmul(rh[t],
                  fr.fq(tauH0 * pow(dlt, (-t) % (fr.p-1), fr.p)))
                  for t in range(d + 1))
        check('P-B-%s-%s' % (fr.name, tag), okB,
              'tau(H0)=%d delta=%d' % (tauH0, dlt))
        # P-C factor/routing transport
        fh, lh = factorK2(fr, rh); f7, l7 = factorK2(fr, r7)
        okC = sorted((dg, m) for dg, m, _ in fh) == \
            sorted((dg, m) for dg, m, _ in f7)
        rts_h = sorted(fr.fqmul(fr.fq(dlt), r) for dg, m, r in fh if r
                       for _ in range(m))
        rts_7 = sorted(r for dg, m, r in f7 if r for _ in range(m))
        okC = okC and rts_h == rts_7
        route_h, sig_h = routing(fr, fh, l2)
        route_7, sig_7 = routing(fr, f7, l2)
        okC = okC and route_h == route_7 and sig_h == sig_7
        check('P-C-%s-%s' % (fr.name, tag), okC,
              'route %s sigma %s' % (route_h, sig_h))
        # P-E he7 bracket = beta^{c_t}
        beta = fr.fqmul(fr.fq(pow(fr.eta, (-fr.Q(fr.u2)) % (fr.p-1), fr.p)),
                        (0, 1))
        okE, cts = True, []
        for t in range(d + 1):
            Ht = H0 - t*u3
            num = fr.s2(Ht) + t*fr.s2(u3) - fr.s2(H0)
            okE = okE and num % fr.e2 == 0
            ct = num // fr.e2; cts.append(ct)
            NH, Nu, N0 = fr.nhe7(Ht), fr.nhe7(u3), fr.nhe7(H0)
            br = fr.res0(*[NH[i] + t*Nu[i] - N0[i] for i in range(3)])
            okE = okE and br == fr.fqpow(beta, ct)
        check('P-E-bracket-%s-%s' % (fr.name, tag), okE, 'c_t = %s' % cts)
        # raw-string twist data
        taus = [fr.tau(H0 - t*u3) for t in range(d + 1)]
        if any(tv != 1 for tv in taus):
            geo = all(taus[t+1]*taus[t+1] % fr.p ==
                      taus[t]*taus[t+2] % fr.p for t in range(d - 1))
            if not geo: tooth_raw = True
        if tag.startswith('INT21') and any(tv != 1 for tv in taus):
            raw_eq_int = False
        if route_h == 'SEP':
            if any(dg >= 2 for dg, m, _ in fh): classes.add('SEP-IRRED')
            if len([1 for dg, m, _ in fh if dg == 1]) >= 2:
                classes.add('SEP-SPLIT')
            jobs.append((member_poly(fr, key, mu2, Ajs), fr.p))
            tags.append('SIGMA-%s-%s' % (fr.name, tag)); preds.append({sig_h})
        else:
            classes.add(route_h)
        print('    %-18s taus %s route %s' % (tag, taus, route_h))
    print('  realized routing classes: %s' % sorted(classes))
    if fr.name == 'X':
        check('P-C-coverage-X',
              {'SEP-IRRED', 'SEP-SPLIT', 'REFINE'} <= classes, sorted(classes))
    if fr.name == 'Z':
        check('P-C-coverage-Z', {'SEP-SPLIT', 'REFINE'} <= classes,
              sorted(classes))
    if fr.e2 == 1:
        check('P-D-T-RAW-%s' % fr.name, tooth_raw,
              'a non-geometric raw tau-string occurred')
    else:
        check('P-D-RAWEQ-INT21-%s' % fr.name, raw_eq_int,
              'INT21 letter-dead as derived')
        check('P-D-RAWLIVE-HALF43-%s' % fr.name, fr.tau(43) != 1,
              'tau(43) = %d' % fr.tau(43))
    return jobs, tags, preds

def main():
    t0 = time.time()
    print('HETOW-4 bridge battery (TOWERRAT-R1): frames X, Z, S')
    jobs, tags, preds = [], [], []
    for fr in (FX, FZ, FS):
        run_frame(fr, jobs, tags, preds)
        if os.environ.get('HETOW4_SMOKE'): break
    if os.environ.get('HETOW4_SMOKE'):
        print('SMOKE: %d violations' % len(VIOL)); return
    print('%d gp jobs ...' % len(jobs))
    got = gp_sigs(jobs)
    for i, tag in enumerate(tags):
        if i not in got:
            check(tag, False, 'gp job %d missing' % i); continue
        s1, s2 = got[i]
        check(tag + '-routes', s1 == s2, '%s vs %s' % (s1, s2))
        check(tag, s1 in preds[i], 'sigma = %s' % (s1,))
    print('\nTOTAL violations %d (%.1fs)' % (len(VIOL), time.time() - t0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))
    json.dump({'viol': VIOL, 'jobs': len(jobs)},
              open('hetow_r2_hetow4_results.json', 'w'), indent=1)

if __name__ == '__main__':
    main()
