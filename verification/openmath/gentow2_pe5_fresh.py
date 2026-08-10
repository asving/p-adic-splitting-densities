#!/usr/bin/env python3
"""GENTOW2 passPE5 FRESH ROUTE (hostile verifier, 2026-08-10).

FIRST gamma_2-LIVE COCYCLE CONTACT ANYWHERE.  Route disjoint from all
prior contacts (battery W1-W5/N1/N2, PE1 F1-F3, PE2 G1-G3, r2 LP1,
PE3 LV1/LV2, PE4 LD1-LD3): every prior theta-cocycle contact had the
gamma_2 leg SILENT (z2 = 1 at LP1) or TRIVIAL (f3 = 1, or e2 = 1
forcing Phi'-free normalizers, k = 0).  THIS tower has e2 = 2 AND
f2 = 2: z2 = eta2 in F4\\F2 with z1 = 1 — theta's letter monomial is a
PURE z2-power, the gamma_2-component acting alone.  Plus the first
e3 >= 2 x f3 >= 2 frame anywhere (GA3: cocycle live at e3 = 2).

TOWER GB (hand-derived; NO pre-seal machine contact with any of these
polynomials): p = 2, mu1 = [mu0; (x, 1/2)] (e1 = 2, h1 = 1, f1 = 1,
z1 = 1 forced over F2).  PHIP = x^2 - 2 (w2 = 1).  Stage 2: lam2 =
1/4 (h2 = 1, e2 = 2), f2 = 2, psi2 = y^2 + y + 1; level-2 recipe at
kappa2 = 5/2, u2' = 5: nhat1(5) = 4x, nhat1(10) = 32, digits (1, 1)
(z1 = 1: the GENHN erratum eta^W corrections are trivial), so
  PHI2 = PHIP^4 - 4x*PHIP^2 - 32,  deg 8.
Data: w3 = mu2(PHI2) = 5, e(mu2) = 4, u2 = dv2(PHIP) = 5, dv2(x) = 2,
dv2(2) = 4, dv2(PHI2) = 20 = e2*f2*u2 (the depth-3 floor).  Field of
PHI2: e = e(mu2) = 4, f = f1*f2 = 2 (FGMN eq (9): e(phi_i) =
e(mu_{i-1}), f(phi_i) = f0...f_{i-1}).  eta2 = res(PHIP(x0)^2/(4x0)),
a psi2-root; LETTER FORMULA: floor(l1*u2/e1) = 2, z1 = 1 => z2 = eta2
!= 1: level-2 letter LIVE.

LADDER (normal form 0 <= i < e1 = 2, 0 <= b < e2 = 2, m = 4a+2i+5b):
nhat2(21) = 16*PHIP, nhat2(42) = 1024x, nhat2(41) = 512*PHIP,
nhat2(82) = 2^20 x.

THE COCYCLE (gamma-calculus, hand-derived): gamma1 = x^2/2 (lattice
(2,-1,0)), gamma2 = PHIP^2/x^5 (pi2 = x since l1 = 1, l'1 = 0; u2 =
5; lattice (-5,0,2)).
  theta(0) = res(nhat2(2*u3)/nhat2(u3)^2):
   e3 = 1 (u3 = 21): 1024x/(16PHIP)^2 = 4x/PHIP^2, lattice (1,2,-2)
     = -1*(-5,0,2) - 2*(2,-1,0) = gamma2^{-1}gamma1^{-2}
     -> res = z2^{-1}z1^{-2} = eta2^{-1} = eta2^2.
   e3 = 2 (u3 = 41): 2^20 x/(512PHIP)^2 = 4x/PHIP^2 -> SAME eta2^2.
  theta(1) = 1 (top slot, M = N).
So theta(0) = eta2^2 = z2^2: the FIRST live gamma_2 leg.  B''(6):
u(beta_t) = theta(t) w^{f3-t}; verdict-frame realized residual
P = y^2 + theta(1)c1*y + theta(0)c0 = y^2 + c1*y + eta2^2*c0.

STAGE-3 FRAMES (floor kappa3 > 20 holds at each; digits are
PER-HEIGHT strings (c1, c0); e3*f3 >= 2 proper; all khat exact-grade
single ladder monomials, deg < 8, Phi2-free, on-line pins):
  GA1: e3 = 1, f3 = 2, kappa3 = u3 = 21 (lam3 = 1/4), digits (1, eta2):
       k1 = nhat2(21) = 16PHIP; k0 = 256PHIP^2 (dv2 = 42, digit
       res(256PHIP^2/1024x) = res(PHIP^2/4x) = gamma2*gamma1^2 ->
       z2*z1^2 = eta2).
       PHI3 = PHI2^2 - 16*PHIP*PHI2 - 256*PHIP^2, deg 16.
       Per-height psi3 = y^2+y+eta2: IRREDUCIBLE /F4 (Tr(eta2) = 1)
       -> B-2/per-height predicts [(4,4)].
       B''-realized P = y^2+y+eta2^3 = y^2+y+1 = (y+eta2)(y+eta2^2):
       SPLIT -> predict NPR 2, EF (4,2) x2.  << TOOTH: opposite
       verdicts; only the theta(0) = z2^2 leg separates them.
  GA2: same stage, digits (1, 1): k0 = nhat2(42) = 1024x.
       PHI3 = PHI2^2 - 16*PHIP*PHI2 - 1024x.
       Per-height psi3 = y^2+y+1 SPLIT -> [(4,2),(4,2)].
       B''-realized P = y^2+y+eta2^2: IRREDUCIBLE (Tr(eta2^2) = 1)
       -> predict NPR 1, EF (4,4).  << TOOTH, opposite direction.
  GA4: same stage, digits (eta2, 1): k1 = 2x*PHIP^3 (dv2 = 4+2+15 =
       21, digit res(2xPHIP^3/16PHIP) = res(xPHIP^2/8) =
       gamma2*gamma1^3 -> z2 = eta2); k0 = 1024x.
       PHI3 = PHI2^2 - 2x*PHIP^3*PHI2 - 1024x.
       Per-height psi3 = y^2+eta2*y+1: IRREDUCIBLE (y = eta2*u ->
       u^2+u+eta2^{-2} = u^2+u+eta2, Tr = 1) -> [(4,4)].
       B''-realized P = y^2+eta2*y+eta2^2 = (y+1)(y+eta2^2): SPLIT
       -> predict NPR 2, EF (4,2) x2.  << top-slot tooth: also kills
       theta(1) = z2^{+-1} alternatives (those predict single prime).
  GA3: e3 = 2, f3 = 2, kappa3 = 41/2 (lam3 = 1/8), u3 = 41, digits
       (1, eta2): k1 = nhat2(41) = 512PHIP; k0 = 2^18*PHIP^2 (dv2 =
       72+10 = 82, digit res(2^18 PHIP^2/2^20 x) = eta2).
       PHI3 = PHI2^4 - 512*PHIP*PHI2^2 - 262144*PHIP^2, deg 32.
       Per-height psi3 = y^2+y+eta2 irred -> [(8,4)].
       B''-realized P = y^2+y+1 SPLIT -> predict NPR 2, EF (8,2) x2.
       << the first e3 >= 2 x letter-live-cocycle frame.

PREREGISTERED PREDICTIONS (all hand-derived; sealed before first run;
py_compile only, no smoke run; every GA prediction below is the
B''/r3 value — the per-height/B-2 alternative and the wrong-exponent
alternative theta(0) = z2 are teeth, both flipping verdicts as noted
above; theta(0) = z2 would make GA1 [(4,4)] and GA2 [(4,4)]):

A-route (own exact integer arithmetic: monic-division adic expansions,
dv1/dv2 ladder heights via Phi'-expansion grammar, Sylvester/Bareiss
resultants):
  T-PINS: PHIP-adic pins of PHI2: (4,0),(2,5),(0,10) on line slope
    5/2, a3 = a1 = 0 (psi2 full support at abscissas 0,2,4).
  Per GA frame: K1H/K0H ladder heights (21,42)/(21,42)/(21,42)/
    (41,82); PHI2-adic expansion: A_{e3f3} = 1, A_{e3} = -k1,
    A_0 = -k0, ALL other abscissas literally zero, heights on the
    kappa3-line; PHIP-adic development one-sided of slope 5/2 from
    (L,0), L = 8 (GA1/2/4) resp 16 (GA3): no pin below the line,
    ON-line exactly at abscissas {0,4,8} resp {0,8,16} = the char-2
    psi2^{e3f3}-square signature (R2(PHI3) = psi2^2 = y^4+y^2+1 resp
    psi2^4 = y^8+y^4+1: odd/non-multiple-of-4 y-coefficients vanish),
    strictly above at every other nonzero pin.
  RESVALS v2(Res(PHI3, g)) = deg(PHI3)*v(g):
    GA1/GA2/GA4: g = x: 8; g = PHIP: 20; g = PHI2: 84.
    GA3: 16; 40; 164.
T-RESVALS for PHI2: g = x: v2 = 8*(1/2) = 4; g = PHIP: 8*(5/4) = 10.

B-route (PARI/gp: factorpadic prec 150/260; factor over Q, per
rational factor nfinit([.,[2]]) + idealprimedec + nfeltval + nfmodpr;
per-prime predictions invariant under any Q-factorization):
  T: PHI2 padic factor degs [8]; NPR 1; EF (4,2); VALS (x,PHIP) =
     (2,5); PSI2: E2R^2+E2R+1 == 0 where E2R = res(PHIP^2/(4x));
     LIVE: E2R != 1  << the z2 != 1 certificate.
  GA1: DEGS [8,8]; NPR 2; EFS {(4,2),(4,2)}; per prime VALS
     (x,PHIP,PHI2) = (2,5,21); PSI2 + LIVE at every prime;
     COC := res(1024x/(16PHIP)^2) == E2R^2 and != 1 and != E2R
     (the DIRECT gamma_2-cocycle measurement, first anywhere);
     MP (r3 := res(PHI2/(16PHIP))): r3^2+r3+1 == 0 at every prime;
     MPB r3^2+r3+E2R^2 != 0 at every prime; DEEP r3^4 == r3 (f = 2);
     ROOTPAT: multiset over primes of (r3==E2R, r3==E2R^2) =
     {(1,0),(0,1)} (the two primes read the two DISTINCT P-roots).
  GA2: DEGS [16]; NPR 1; EF (4,4); VALS (2,5,21); PSI2+LIVE;
     COC == E2R^2, != 1, != E2R; MP r3^2+r3+E2R^2 == 0;
     MPA r3^2+r3+1 != 0; DEEP r3^4 != r3 (f = 4: F16 live);
     ROOTPAT {(0,0)} (r3 not in F4).
  GA4: DEGS [8,8]; NPR 2; EFS {(4,2),(4,2)}; VALS (2,5,21) x2;
     PSI2+LIVE; COC == E2R^2; MP r3^2+E2R*r3+E2R^2 == 0 both;
     DEEP r3^4 == r3; ROOTPAT multiset of (r3==1, r3==E2R^2) =
     {(1,0),(0,1)}.
  GA3: DEGS [16,16]; NPR 2; EFS {(8,2),(8,2)}; per prime VALS =
     (4,10,41) (e = 8); PSI2+LIVE; COC := res(2^20 x/(512PHIP)^2)
     == E2R^2; MP (r := res(PHI2^2/(512PHIP))): r^2+r+1 == 0 both;
     DEEP r^4 == r; ROOTPAT {(1,0),(0,1)} on (r==E2R, r==E2R^2).
"""

import subprocess, sys
from fractions import Fraction

def norm(p):
    while p and p[-1] == 0: p.pop()
    return p

def pmul(a, b):
    r = [0]*(len(a)+len(b)-1 if a and b else 0)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b): r[i+j] += ca*cb
    return norm(r)

def padd(a, b):
    r = [0]*max(len(a), len(b))
    for i, c in enumerate(a): r[i] += c
    for i, c in enumerate(b): r[i] += c
    return norm(r)

def gsub(a, b): return padd(a, [-c for c in b])

def pdivmod_monic(a, b):
    a = a[:]; q = [0]*max(len(a)-len(b)+1, 1)
    while len(a) >= len(b):
        c = a[-1]; d = len(a)-len(b); q[d] = c
        for i, cb in enumerate(b): a[i+d] -= c*cb
        norm(a)
    return norm(q), norm(a)

def expand_adic(g, base):
    out = []
    while g:
        g, r = pdivmod_monic(g, base)
        out.append(r)
    return out

def v2(n):
    n = abs(n); assert n
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

def dv1(p):
    return min(2*v2(c) + i for i, c in enumerate(p) if c)

PHIP = [-2, 0, 1]

def dv2(p):
    assert len(p) <= 8
    bs = expand_adic(p[:], PHIP)
    return min(2*dv1(b) + 5*k for k, b in enumerate(bs) if b)

def sylv_res_v2(a, b):
    n, m = len(a)-1, len(b)-1
    N = n + m
    M = [[0]*N for _ in range(N)]
    for i in range(m):
        for j, c in enumerate(reversed(a)): M[i][i+j] = c
    for i in range(n):
        for j, c in enumerate(reversed(b)): M[m+i][i+j] = c
    # fraction-free Bareiss
    prev = 1
    for k in range(N-1):
        if M[k][k] == 0:
            for r in range(k+1, N):
                if M[r][k]: M[k], M[r] = M[r], M[k]; prev = -prev if False else prev; break
            else: return None
        for i in range(k+1, N):
            for j in range(k+1, N):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
            M[i][k] = 0
        prev = M[k][k]
    return M[N-1][N-1]

class T:
    def __init__(self): self.n = 0; self.bad = []
    def chk(self, ok, msg):
        self.n += 1
        print('%s %s' % ('ok ' if ok else 'VIOLATION', msg))
        if not ok: self.bad.append(msg)

def phi1_side(t, tag, F, L):
    a = expand_adic(F[:], PHIP)
    online = {0, L//2, L}
    good_side = True; good_on = True
    for j, aj in enumerate(a):
        if not aj: continue
        h = Fraction(dv1(aj)); line = Fraction(5, 2)*(L - j)
        if h < line: good_side = False
        if j in online and h != line: good_on = False
        if j not in online and h == line: good_on = False
    t.chk(good_side, '%s PHI1SIDE one-sided slope 5/2' % tag)
    t.chk(good_on, '%s PHI1ON on-line support exactly {0,%d,%d}' % (tag, L//2, L))

def frame_A(t, tag, F, PHI2, k1, k0, e3, f3, u3, resvals):
    t.chk(dv2(k1) == u3, '%s K1H dv2 = %d' % (tag, u3))
    t.chk(dv2(k0) == 2*u3, '%s K0H dv2 = %d' % (tag, 2*u3))
    A = expand_adic(F[:], PHI2)
    okA = (len(A) == e3*f3+1 and A[e3*f3] == [1] and A[e3] == [-c for c in k1]
           and A[0] == [-c for c in k0]
           and all(not A[j] for j in range(e3*f3) if j not in (0, e3)))
    t.chk(okA, '%s PHI2ADIC exact shape (monic top, -k1 at %d, -k0 at 0, zero elsewhere)' % (tag, e3))
    phi1_side(t, tag, F, 4*e3*f3)
    for g, name, want in ((([0,1]), 'x', resvals[0]), (PHIP, 'PHIP', resvals[1]), (PHI2, 'PHI2', resvals[2])):
        r = sylv_res_v2(F, g if isinstance(g, list) else g)
        t.chk(r is not None and r != 0 and v2(r) == want, '%s RES %s v2 = %d' % (tag, name, want))

GP_HEAD = r"""
default(parisize, 512000000);
probe(tag, F, PREC, e3, NHU3, NH2U3) = {
  my(fp, fq, K, dec, pr, xF, e2r, coc, r3, degs = List(), tot = 0);
  fp = factorpadic(F, 2, PREC);
  for(i = 1, #fp[,1], listput(degs, poldegree(fp[i,1])));
  listsort(degs);
  print(tag, " DEGS ", Vec(degs));
  fq = factor(F)[,1];
  for(qi = 1, #fq,
    K = nfinit([fq[qi], [2]]);
    dec = idealprimedec(K, 2);
    tot += #dec;
    for(pi = 1, #dec,
      pr = dec[pi];
      xF = Mod(x, fq[qi]);
      print(tag, " EF ", pr.e, " ", pr.f);
      print(tag, " VALS ", nfeltval(K, xF, pr), " ",
            nfeltval(K, Mod(PHIP, fq[qi]), pr), " ",
            nfeltval(K, Mod(PHI2, fq[qi]), pr));
      e2r = nfmodpr(K, Mod(PHIP, fq[qi])^2/(4*xF), pr);
      print(tag, " PSI2 ", e2r^2 + e2r + 1 == 0);
      print(tag, " LIVE ", e2r != 1);
      coc = nfmodpr(K, Mod(NH2U3, fq[qi])/Mod(NHU3, fq[qi])^2, pr);
      print(tag, " COCE2 ", coc == e2r^2);
      print(tag, " COCNOT1 ", coc != 1);
      print(tag, " COCNOTE ", coc != e2r);
      if(e3 == 1,
        r3 = nfmodpr(K, Mod(PHI2, fq[qi])/Mod(NHU3, fq[qi]), pr),
        r3 = nfmodpr(K, Mod(PHI2, fq[qi])^2/Mod(NHU3, fq[qi]), pr));
      print(tag, " MPA ", r3^2 + r3 + 1 == 0);
      print(tag, " MPB ", r3^2 + r3 + e2r^2 == 0);
      print(tag, " MPC ", r3^2 + e2r*r3 + e2r^2 == 0);
      print(tag, " DEEP4 ", r3^4 == r3);
      print(tag, " RE ", r3 == e2r);
      print(tag, " RE2 ", r3 == e2r^2);
      print(tag, " R1 ", r3 == 1);
    );
  );
  print(tag, " NPR ", tot);
}
tprobe(F, PREC) = {
  my(fp, K, dec, pr, xF, e2r, degs = List());
  fp = factorpadic(F, 2, PREC);
  for(i = 1, #fp[,1], listput(degs, poldegree(fp[i,1])));
  listsort(degs);
  print("T DEGS ", Vec(degs));
  K = nfinit([F, [2]]);
  dec = idealprimedec(K, 2);
  print("T NPR ", #dec);
  pr = dec[1]; xF = Mod(x, F);
  print("T EF ", pr.e, " ", pr.f);
  print("T VALS ", nfeltval(K, xF, pr), " ", nfeltval(K, Mod(PHIP, F), pr));
  e2r = nfmodpr(K, Mod(PHIP, F)^2/(4*xF), pr);
  print("T PSI2 ", e2r^2 + e2r + 1 == 0);
  print("T LIVE ", e2r != 1);
}
"""

def main():
    t = T()
    PHI2 = gsub(gsub(pmul(pmul(PHIP, PHIP), pmul(PHIP, PHIP)),
                     pmul([0, 4], pmul(PHIP, PHIP))), [32])
    k1a = pmul([16], PHIP)
    k0_ga1 = pmul([256], pmul(PHIP, PHIP))
    k0_x = [0, 1024]
    k1_ga4 = pmul([0, 2], pmul(PHIP, pmul(PHIP, PHIP)))
    k1_ga3 = pmul([512], PHIP)
    k0_ga3 = pmul([262144], pmul(PHIP, PHIP))
    PHI2sq = pmul(PHI2, PHI2)
    GA1 = gsub(gsub(PHI2sq, pmul(k1a, PHI2)), k0_ga1)
    GA2 = gsub(gsub(PHI2sq, pmul(k1a, PHI2)), k0_x)
    GA4 = gsub(gsub(PHI2sq, pmul(k1_ga4, PHI2)), k0_x)
    GA3 = gsub(gsub(pmul(PHI2sq, PHI2sq), pmul(k1_ga3, PHI2sq)), k0_ga3)

    # ---- A-route: tower ----
    a = expand_adic(PHI2[:], PHIP)
    t.chk(len(a) == 5 and a[4] == [1] and not a[3] and not a[1]
          and dv1(a[2]) == 5 and dv1(a[0]) == 10,
          'T PINS PHI2 phi1-adic (4,0),(2,5),(0,10), a3 = a1 = 0')
    for g, name, want in (([0, 1], 'x', 4), (PHIP, 'PHIP', 10)):
        r = sylv_res_v2(PHI2, g)
        t.chk(r is not None and r != 0 and v2(r) == want, 'T RES %s v2 = %d' % (name, want))
    # ---- A-route: frames ----
    frame_A(t, 'GA1', GA1, PHI2, k1a, k0_ga1, 1, 2, 21, (8, 20, 84))
    frame_A(t, 'GA2', GA2, PHI2, k1a, k0_x, 1, 2, 21, (8, 20, 84))
    frame_A(t, 'GA4', GA4, PHI2, k1_ga4, k0_x, 1, 2, 21, (8, 20, 84))
    frame_A(t, 'GA3', GA3, PHI2, k1_ga3, k0_ga3, 2, 2, 41, (16, 40, 164))

    # ---- B-route ----
    lit = lambda p: 'Pol(%s)' % list(reversed(p))
    prog = 'PHIP = %s; PHI2 = %s;\n' % (lit(PHIP), lit(PHI2)) + GP_HEAD
    prog += 'tprobe(PHI2, 150);\n'
    prog += 'probe("GA1", %s, 150, 1, %s, %s);\n' % (lit(GA1), lit(k1a), lit(k0_x))
    prog += 'probe("GA2", %s, 150, 1, %s, %s);\n' % (lit(GA2), lit(k1a), lit(k0_x))
    prog += 'probe("GA4", %s, 150, 1, %s, %s);\n' % (lit(GA4), lit(k1a), lit(k0_x))
    prog += 'probe("GA3", %s, 260, 2, %s, %s);\n' % (lit(GA3), lit(k1_ga3), lit([0, 1 << 20]))
    out = subprocess.run(['gp', '-q', '-f'], input=prog, capture_output=True,
                         text=True, timeout=3600)
    lines = [l.strip() for l in out.stdout.splitlines() if l.strip()]
    for l in lines: print(' ', l)
    if out.stderr.strip(): print('gp stderr:', out.stderr.strip()[:500])
    grab = lambda tag, key: [l.split()[2:] for l in lines if l.startswith(tag + ' ' + key)]
    one = lambda tag, key: grab(tag, key)[0]

    t.chk(one('T', 'DEGS') == ['[8]'], 'T DEGS [8]')
    t.chk(one('T', 'NPR') == ['1'], 'T NPR 1')
    t.chk(one('T', 'EF') == ['4', '2'], 'T EF 4 2')
    t.chk(one('T', 'VALS') == ['2', '5'], 'T VALS 2 5')
    t.chk(one('T', 'PSI2') == ['1'], 'T PSI2 psi2-root')
    t.chk(one('T', 'LIVE') == ['1'], 'T LIVE z2 != 1')

    spec = {
        'GA1': ('[8,', 2, ['4', '2'], ['2', '5', '21'], 'MPA', '1', [('1', '0'), ('0', '1')], 'RE'),
        'GA2': ('[16]', 1, ['4', '4'], ['2', '5', '21'], 'MPB', '0', [('0', '0')], 'RE'),
        'GA4': ('[8,', 2, ['4', '2'], ['2', '5', '21'], 'MPC', '1', [('1', '0'), ('0', '1')], 'R1'),
        'GA3': ('[16,', 2, ['8', '2'], ['4', '10', '41'], 'MPA', '1', [('1', '0'), ('0', '1')], 'RE'),
    }
    for tag, (dg, npr, ef, vals, mpown, deep, rootpat, rk) in spec.items():
        t.chk(' '.join(one(tag, 'DEGS')).startswith(dg), '%s DEGS %s..' % (tag, dg))
        t.chk(one(tag, 'NPR') == [str(npr)], '%s NPR %d' % (tag, npr))
        efs = grab(tag, 'EF')
        t.chk(len(efs) == npr and all(e == ef for e in efs), '%s EFS %s x%d' % (tag, ef, npr))
        t.chk(all(v == vals for v in grab(tag, 'VALS')), '%s VALS %s' % (tag, vals))
        for key in ('PSI2', 'LIVE', 'COCE2', 'COCNOT1', 'COCNOTE'):
            t.chk(all(v == ['1'] for v in grab(tag, key)) and len(grab(tag, key)) == npr,
                  '%s %s all primes' % (tag, key))
        t.chk(all(v == ['1'] for v in grab(tag, mpown)), '%s MPOWN %s == 0 all primes' % (tag, mpown))
        if tag == 'GA1':
            t.chk(all(v == ['0'] for v in grab(tag, 'MPB')), 'GA1 MPB != 0 all primes')
        if tag == 'GA2':
            t.chk(all(v == ['0'] for v in grab(tag, 'MPA')), 'GA2 MPA != 0')
        t.chk(all(v == [deep] for v in grab(tag, 'DEEP4')), '%s DEEP4 == %s' % (tag, deep))
        pat = sorted(zip((v[0] for v in grab(tag, rk)), (v[0] for v in grab(tag, 'RE2'))))
        t.chk(pat == sorted(rootpat), '%s ROOTPAT %s/RE2 = %s' % (tag, rk, sorted(rootpat)))

    print('== passPE5 FRESH-ROUTE VERDICT ==')
    print('checks: %d, violations: %d' % (t.n, len(t.bad)))
    print('GENTOW2 passPE5 fresh route: %s' % ('GREEN' if not t.bad else 'RED'))
    return len(t.bad)

if __name__ == '__main__':
    sys.exit(1 if main() else 0)
