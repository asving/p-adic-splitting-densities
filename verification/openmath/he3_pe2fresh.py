#!/usr/bin/env python3
"""HE3 passPE2 FRESH ROUTE (hostile verifier's own instrument; disjoint from
PE1's legs A/B/C and from he3r1_supp.py's rows).

FR-A  THE NEVER-RUN GEOGRAPHY e1 >= 2 AND f1 >= 2: genre (3; 2, 2, mu; 1),
      O = Z_3, Phi' = x^4 + 9 (single entry side slope 1/2, residual
      psi = y^2 + 1 irreducible over F_3), D' = 4, D'h = 4, K = F_9 = F_3(eta),
      eta = res(theta^2/3), eta^2 = -1. Members constructed as products of
      HE3-1L-carrier key-translates (predictions from THEOREM HE3.A's
      dictionary (e,f) = (2 e_s, 2 f_s)); PARI factorpadic + idealprimedec is
      the sigma oracle. HE-NORM (HE3-1a) at e1 = 2: v3(Res(f, key)) ==
      2 * dv(B0), dv = min_i(2*v3(b_i) + i) -- never machine-run at e1 >= 2
      on the HE3 side.
FR-B  THE TWIST ADJUDICATOR. Member f = Phi'^2 + 9x*Phi' + 243: all three
      pins ON the lam = 5 line. Coherent residual (HE6 pi-convention,
      pi_norm = x since i0*h + e1*a0 = 1 gives i0=1, a0=0):
      R(Z) = res(243/th^10) + res(9th/th^5) Z + Z^2 = -eta - Z + Z^2,
      disc = 1 + eta NONSQUARE in F_9 => IRREDUCIBLE => sigma {(2,4)}.
      NAIVE untwisted n(kappa)-read: Z^2 + Z + 1 = (Z-1)^2 in char 3 =>
      ALPHA (repeated rational root) => NOT {(2,4)}. PARI adjudicates.
      Peel cross-check: m_s = 0 for ALL 8 letters (no rational root).
FR-C  LEMMA HE3-1L EXACT SET at (2,2,1), INDEPENDENT LEG: realized residues
      res(C(theta)/n(kappa)(theta)) computed by PARI (nfeltval heights +
      nfmodpr residues in the residue field of the unique prime over 3),
      NOT by the note's slot formula; compared against the displayed
      T(kappa)-span. Boundary instances: kappa = 3 = (i0 + e1(f1-1))h
      exactly (full, 8 letters) vs kappa = 1 (T = {0}: 2 letters only).
FR-D  THE [r1-N1] REAL GEOGRAPHY (Q, f1) = (2,1): O = Z_2, Phi' = x - 2,
      three consecutive slopes 2,3,4 (supp P2-N1 demoed the mechanics only
      at f1 = 2 over Z_3 where letters abound). Exact member
      (x-6)(x-10)(x-18): PARI sigma = {(1,1)}^3; A0' = 0 branch: quotient
      dev slopes {2,3}; junk variant: A0' != 0 branch, gap integer 4
      strictly inside (3, delta).
Exit 0 iff 0 violations. All integer arithmetic exact (Bareiss resultants).
"""
import json, subprocess, sys
from fractions import Fraction

VIOL = 0
def fail(msg):
    global VIOL; VIOL += 1; print('VIOLATION:', msg)

def sylvester_res(f, g):
    F, G = list(reversed(f)), list(reversed(g))
    m, n = len(F)-1, len(G)-1
    N = m + n
    M = [[0]*N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(F): M[i][i+j] = c
    for i in range(m):
        for j, c in enumerate(G): M[n+i][i+j] = c
    prev, sign = 1, 1
    A = [row[:] for row in M]
    for k in range(N-1):
        if A[k][k] == 0:
            piv = next((r for r in range(k+1, N) if A[r][k] != 0), None)
            if piv is None: return 0
            A[k], A[piv] = A[piv], A[k]; sign = -sign
        for i in range(k+1, N):
            for j in range(k+1, N):
                A[i][j] = (A[i][j]*A[k][k] - A[i][k]*A[k][j]) // prev
        prev = A[k][k]
    return sign * A[N-1][N-1]

def vp(n, p):
    n = int(n)
    if n == 0: return 10**9
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

def pmul(f, g):
    out = [0]*(len(f)+len(g)-1)
    for a, ca in enumerate(f):
        for b, cb in enumerate(g): out[a+b] += ca*cb
    return out

def psub(f, g):
    n = max(len(f), len(g))
    return [(f[k] if k < len(f) else 0) - (g[k] if k < len(g) else 0)
            for k in range(n)]

def padd(f, g):
    n = max(len(f), len(g))
    return [(f[k] if k < len(f) else 0) + (g[k] if k < len(g) else 0)
            for k in range(n)]

def pdivmod(f, g):
    f = f[:]; dg = len(g)-1; q = [0]*max(1, len(f)-dg)
    while len(f)-1 >= dg and any(f):
        d = len(f)-1
        while d >= 0 and f[d] == 0: d -= 1
        if d < dg: break
        c = f[d]; q[d-dg] = c
        for k, gc in enumerate(g): f[d-dg+k] -= c*gc
    while len(f) > dg: f.pop()
    while len(f) < dg: f.append(0)
    return q, f

def dvA(A, p, e1, h):
    best = 10**9
    for i, c in enumerate(A):
        if c: best = min(best, e1*vp(c, p) + i*h)
    return best

def dev(f, key, mu):
    A, cur = [], f[:]
    for _ in range(mu):
        q, r = pdivmod(cur, key)
        A.append(r); cur = q
    return A

def polygon(f, key, mu, p, e1, h):
    dvs = [dvA(a, p, e1, h) for a in dev(f, key, mu)] + [0]
    pts = [(j, dvs[j]) for j in range(mu+1) if dvs[j] < 10**8]
    pts = sorted(pts); H = [pts[0]]
    for q in pts[1:]:
        while len(H) >= 2 and (Fraction(H[-1][1]-H[-2][1], H[-1][0]-H[-2][0])
                               >= Fraction(q[1]-H[-1][1], q[0]-H[-1][0])):
            H.pop()
        H.append(q)
    sides = []
    for k in range(len(H)-1):
        (j1, m1), (j2, m2) = H[k], H[k+1]
        sides.append((Fraction(m1-m2, j2-j1), j2-j1))
    return dvs, sides

def above_line(f, key, mu, lam, p, e1, h):
    dvs = [dvA(a, p, e1, h) for a in dev(f, key, mu)] + [0]
    hF = min(dvs[j] + lam*j for j in range(mu+1))
    m = 0
    while m < mu and dvs[m] + lam*m > hF: m += 1
    return m

def he31a(f, key, Dp, p, e1, h):
    """Sigma_rho dv(key(rho)) = e1*vp(Res(f,key)) ?= D' * dv(f mod key)."""
    q, B0 = pdivmod(f, key)
    if not any(B0):
        return vp(sylvester_res(f, key), p) >= 10**8
    return e1*vp(sylvester_res(f, key), p) == Dp*dvA(B0, p, e1, h)

def gp_run(script):
    r = subprocess.run(['gp', '-q'], input=script, capture_output=True,
                       text=True, timeout=600)
    if r.returncode != 0:
        fail('gp failed: ' + r.stderr[:400]); return ''
    return r.stdout

GP_FUN = r"""
ef(g, p) = { if (poldegree(g)==1, return([1,1]));
  my(nf = nfinit([g,[p]]), dec = idealprimedec(nf, p)); [dec[1].e, dec[1].f] }
sig(f, p) = { my(d = poldisc(f), F); if (d==0, return([[-1,-1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i,1]), p))) }
"""
def gp_sig(polys, p):
    lines = ['print(sig(%s,%d))' % ('+'.join('(%d)*x^%d' % (c, k)
             for k, c in enumerate(f) if c) or '0', p) for f in polys]
    out = gp_run(GP_FUN + '\n'.join(lines) + '\n')
    sigs = []
    for ln in out.strip().splitlines():
        ln = ln.strip()
        if not ln.startswith('[['): continue
        nums = [int(t) for t in ln.replace('[', ' ').replace(']', ' ')
                .replace(',', ' ').split()]
        sigs.append(tuple(sorted(zip(nums[0::2], nums[1::2]))))
    return sigs

# ---------------- FR-A / FR-B: genre (3; 2, 2, mu; 1) ----------------
print('== FR-A: genre (3;2,2,mu;1), Phi\' = x^4+9, K = F_9, D\'h = 4 ==')
K4 = [9, 0, 0, 0, 1]                       # Phi' = x^4 + 9
def carrier22(s, kap):
    """HE3-1L carrier at (e1,f1,h)=(2,2,1) for s = a + b*eta, integer
    kap >= 3 = (i0+e1(f1-1))h at odd kap (i0=1), >= 2 at even kap (i0=0):
    odd kap:  C = a*3^((kap-1)/2) x + b*3^((kap-3)/2) x^3
    even kap: C = a*3^(kap/2)     + b*3^((kap-2)/2) x^2."""
    a, b = s
    if kap % 2 == 1:
        return [0, a*3**((kap-1)//2), 0, b*3**((kap-3)//2)]
    return [a*3**(kap//2), 0, b*3**((kap-2)//2), 0]

F9X = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]

mb = psub(pmul(K4, K4), pmul([0,0,0,3], [0,0,0,3]))       # (P'-3x^3)(P'+3x^3)
mc = pmul(psub(K4, carrier22((1,0),5)), psub(K4, carrier22((0,1),5)))
md = padd(pmul(K4, K4), [0, 243])                          # ell=2, lam=11/2
me = pmul(pmul(psub(K4, carrier22((1,0),5)), psub(K4, carrier22((0,1),5))),
          psub(K4, carrier22((0,2),5)))
mf = padd(padd(pmul(K4, K4), pmul([0,0,9], K4)), [3**5, 0, 2*3**4])
mg = padd(padd(pmul(K4, K4), pmul([0,0,9], K4)), [3**5])
ma = padd(padd(pmul(K4, K4), pmul([0,9], K4)), [3**5])     # FR-B adjudicator
membersA = [
  ('mb {eta,-eta} letters',       mb, ((2,2),(2,2)), 5, {(0,1):1,(0,2):1}),
  ('mc {1,eta} letters',          mc, ((2,2),(2,2)), 5, {(1,0):1,(0,1):1}),
  ('md ell=2 lam=11/2 -> (2,1)',  md, ((4,2),),      None, None),
  ('me mu=3 {1,eta,-eta}',        me, ((2,2),(2,2),(2,2)), 5,
                                  {(1,0):1,(0,1):1,(0,2):1}),
  ('mf coherent Z^2+(2-eta) irred', mf, ((2,4),),    5, {}),
  ('mg coherent Z^2-eta split roots +-(1-eta)', mg, ((2,2),(2,2)), 5,
                                  {(1,2):1,(2,1):1}),
  # NOTE (verifier lesson): first draft predicted +-(1+eta); but
  # (1+eta)^2 = 2eta = -eta while (1-eta)^2 = -2eta = +eta in char 3.
  # The exact instrument caught the hand-slip; the peel letters are the
  # square roots of eta, as the coherent residual Z^2 - eta demands.
  ('ma TWIST ADJUDICATOR (FR-B)', ma, ((2,4),),      5, {}),
]
MU = {tuple(): 0}
sigsA = gp_sig([m[1] for m in membersA], 3)
if len(sigsA) != len(membersA): fail('FR-A: PARI returned %d/%d sigs'
                                     % (len(sigsA), len(membersA)))
for (name, f, pred, lam, roots), got in zip(membersA, sigsA):
    mu = (len(f)-1)//4
    okn = he31a(f, K4, 4, 3, 2, 1)
    tag = 'OK ' if (got == tuple(sorted(pred)) and okn) else 'BAD'
    if tag == 'BAD': fail('FR-A %s: pred %s pari %s he31a %s'
                          % (name, pred, got, okn))
    print('   [%s] %-42s pred %s pari %s' % (tag, name, pred, got))
    if lam is None or roots is None: continue
    prof = {}
    for s in F9X:
        key2 = psub(K4, carrier22(s, lam))
        if not he31a(f, key2, 4, 3, 2, 1):
            fail('FR-A %s HE3-1a at test key s=%s' % (name, s))
        prof[s] = above_line(f, key2, mu, lam, 3, 2, 1)
    if prof != {s: roots.get(s, 0) for s in F9X}:
        fail('FR-A %s peel profile %s != want %s' % (name, prof, roots))
    print('        peel m_s profile over F_9^x:',
          {'%d+%de' % s: v for s, v in prof.items() if v} or 'all zero')

# FR-B naive-vs-coherent verdict line
_, sa = polygon(ma, K4, 2, 3, 2, 1)
print('== FR-B: ma polygon sides (slope,len):', [(str(s), L) for s, L in sa])
if sa != [(Fraction(5), 2)]: fail('FR-B: ma not a single lam=5 side')
if sigsA[-1] == ((2, 4),):
    print('   PARI sigma((2,4)) => COHERENT (pi-convention) residual '
          'Z^2 - Z - eta CONFIRMED irreducible;')
    print('   NAIVE untwisted read Z^2+Z+1 = (Z-1)^2 (ALPHA/refine) REFUTED.')
else:
    fail('FR-B adjudicator: PARI %s (neither prediction?)' % (sigsA[-1],))

# ---------------- FR-C: HE3-1L independent leg via PARI ----------------
print('== FR-C: HE3-1L exact set at (2,2,1) by PARI valuations+residues ==')
gp_c = GP_FUN + r"""
nf = nfinit(x^4+9); P = idealprimedec(nf,3)[1];
print("efP ", P.e, " ", P.f);
mo = nfmodprinit(nf, P);
etab = nfmodpr(nf, x^2/3, mo); print("eta ", etab);
{ for (kap = 0, 5,
    i0 = kap % 2; nk = x^i0 * 3^((kap - i0)/2);
    S = Set();
    for (c0 = 0, 2, for (c1 = 0, 2, for (c2 = 0, 2, for (c3 = 0, 2,
      for (k0 = 0, 3, for (k1 = 0, 3, for (k2 = 0, 3, for (k3 = 0, 3,
        C = c0*3^k0 + c1*3^k1*x + c2*3^k2*x^2 + c3*3^k3*x^3;
        if (C == 0, next);
        if (nfeltval(nf, C, P) != kap, next);
        r = nfmodpr(nf, nfeltdiv(nf, C, nk), mo);
        S = setunion(S, Set([r]));
      ))))))));
    print("kap ", kap, " nreal ", #S, " : ", S)); }
"""
outc = gp_run(gp_c)
print('\n'.join('   ' + l for l in outc.strip().splitlines()[:10]))
want = {0: 2, 1: 2, 2: 8, 3: 8, 4: 8, 5: 8}
got_n = {}
for ln in outc.splitlines():
    t = ln.split()
    if t[:1] == ['kap']: got_n[int(t[1])] = int(t[3])
    if t[:1] == ['efP'] and (t[1], t[2]) != ('2', '2'): fail('FR-C: e,f != 2,2')
for k, n in want.items():
    if got_n.get(k) != n:
        fail('FR-C kappa=%d: realized %s letters, formula says %d'
             % (k, got_n.get(k), n))
print('   realized-set sizes:', got_n, '| formula (T(kappa)-span):', want)
print('   BOUNDARY: kap=3 = (i0+e1(f1-1))h exactly -> FULL;'
      ' kap=1 (odd, T={0}) -> F_3^x only')

# ---------------- FR-D: (Q,f1) = (2,1) consecutive triple ----------------
print('== FR-D: [r1-N1] real geography (Q,f1)=(2,1), Z_2, slopes 2,3,4 ==')
KEY2 = [-2, 1]
fD = pmul(pmul([-6, 1], [-10, 1]), [-18, 1])
_, sD = polygon(fD, KEY2, 3, 2, 1, 1)
if [(str(s), L) for s, L in sD] != [('4', 1), ('3', 1), ('2', 1)]:
    fail('FR-D: base polygon not slopes {2,3,4}: %s' % sD)
sig_d = gp_sig([fD], 2)
if sig_d != [((1, 1), (1, 1), (1, 1))]:
    fail('FR-D: PARI sigma %s != {(1,1)}^3' % sig_d)
print('   base slopes', [(str(s), L) for s, L in sD], '| PARI sigma', sig_d)
keytop = [-18, 1]                          # Phi'' = Phi' - 1*n(4), n(4)=2^4
q, r0 = pdivmod(fD, keytop)
if any(r0): fail('FR-D: exact member not in A0\'=0 branch')
_, sq = polygon(q, keytop, 2, 2, 1, 1)
if sorted(str(s) for s, _ in sq) != ['2', '3']:
    fail('FR-D: quotient dev slopes %s != {2,3}' % sq)
fDb = fD[:]; fDb[0] += 2**11
_, sb = polygon(fDb, keytop, 3, 2, 1, 1)
slb = [s for s, _ in sb]
if not (Fraction(2) in slb and Fraction(3) in slb
        and all(s != 4 for s in slb) and any(s > 4 for s in slb)):
    fail('FR-D: junk-variant recentered slopes %s lack gap shape' % sb)
if not he31a(fDb, keytop, 1, 2, 1, 1): fail('FR-D: HE3-1a at junk/keytop')
print('   A0\'=0 branch: quotient slopes', [(str(s), L) for s, L in sq],
      '| A0\'!=0 branch: P(F\'\') slopes', [(str(s), L) for s, L in sb],
      '(4 in the gap)')

print('== VERDICT: %s (%d violations) ==' % ('GREEN' if VIOL == 0 else 'RED',
                                             VIOL))
sys.exit(0 if VIOL == 0 else 1)
