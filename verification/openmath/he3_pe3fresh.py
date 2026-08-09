#!/usr/bin/env python3
"""HE3 passPE3 FRESH ROUTE (hostile verifier's own instrument; disjoint from
PE1 legs A/B/C, PE2 FR-A/B/C/D, and the note's S8/S9' rows).

PREREGISTERED PREDICTIONS (derived by hand from the note's [r2] displays
BEFORE any run; PARI factorpadic/idealprimedec is the oracle on Z_p rows,
explicit construction is the oracle on the F_4[[t]] row):

FR1 THE LETTER-STARVED CORNER FAMILY -- the Psi-comparison display's own
    honest-scope geography ((Q,f1) in {(2,1),(3,1)}), never PARI-run as a
    starved-slope sigma family:
 1a (2,1) e1=1: Z_2, Phi' = x-2, f = (x-14)(x-22)(x-10): base slopes
    {2 (len 2, residual (Z-1)^2 ALPHA at the single letter), 3};
    recenter at C = n(2) = 4: measured above-2 length = 2, recentered
    above-2 slopes {3,4}, lambda-side of P(F'') length 1 residue 1
    (the collapse root -s = 1); PARI sigma = {(1,1)}^3.
 1b (2,1) e1=2: Z_2, Phi' = x^2-2 (D'h = 2, K^x = {1}), mu = 3,
    f = (x^2-2x-10)(x^2-2x-34)(x^2-2x-130): single side lam = 3 = D'h+1,
    d = 3, all three letters 1 (starved ALPHA, m_1 = 3); sub-block at
    Phi'' = x^2-2x-2 has slopes {6,10,14}; PARI sigma = {(2,1)}^3.
 1c (3,1) STARVED SLOPE + WRAP ADJUDICATOR AT f1 = 1 (new geography for
    the coherent seam; PE2's witness was f1 = 2): Z_3, Phi' = x^2+3
    (eta = res(theta^2/3) = -1, D'h = 2), mu = 2,
    f = Phi'^2 - 9 Phi' + 27 = x^4 - 3x^2 + 9 = (x^2-3x+3)(x^2+3x+3).
    Single side lam = 3 = D'h+1, pins (0,6),(2,0), middle pin lifted.
    NAIVE per-slot read: R = Z^2 + 1, irreducible over F_3 -> would
    predict sigma = {(2,2)} and m_s = 0 at both letters. COHERENT read
    (DEF 1 [r2]: W = (0,1,1), eta = -1): R~ = Z^2 - 1 up to scalar =
    -(Z-1)(Z+1), split at BOTH letters {1,2} (a genuinely starved slope:
    no generic letter in K^x = {1,2}) -> sigma = {(2,1),(2,1)},
    m_1 = m_2 = 1. PARI + measurement adjudicate (construction already
    knows: the two displayed quadratic factors are 3-Eisenstein).
 1d (3,1) e1=2 mu=3 starved-split: f = (x^2-3x-3)(x^2-6x-3)(x^2-12) at
    Phi' = x^2-3: slopes {3 (d=2, letters {1,2} = ALL of K^x), 4 (letter
    1)}; m_(3,1) = m_(3,2) = 1; PARI sigma = {(2,1)}^3.
FR2 MU = 3 COHERENT-READ FAMILY AT NEW (e1,f1) = (3,1): Z_3,
    Phi' = x^3+3 (e1 = 3, D' = 3, D'h = 3, eta = -1), lam = 4 line
    kappa0 = 12: W = (0,1,1,1) (non-affine).
    f = Phi'^3 - 3x Phi'^2 + 9x^2 Phi' - 81.
    NAIVE read a = (-1,1,-1,1): R = Z^3-Z^2+Z-1 = (Z-1)(Z^2+1) -> would
    predict sigma = {(3,1),(3,2)} and m_1 = 1. COHERENT read
    a~ = a * eta^W = (-1,-1,1,-1): R~ = -(Z^3-Z^2+Z+1), NO F_3-root ->
    irreducible cubic -> sigma = {(3,3)} (one nonic, e = 3, f = 3),
    m_1 = m_2 = 0. PARI + measurement adjudicate.
FR2b W-FORMULA DIRECT LEG (no slot formula, no W formula): the coherent
    coefficients res(A_k(theta) n(u)(theta)^k / n(kappa0)(theta)) computed
    by PARI nfeltval/nfmodpr, at BOTH the FR2 member (expect images of
    (-1,-1,1,-1) = (2,2,1,2) in F_3) and PE2's (2,2)-witness
    ma = Phi'^2 + 9x Phi' + 243 at Phi' = x^4+9 (expect (1, eta, eta) --
    the display of the S3 Remark [r2] witness block).
FR3 NON-PRIME q ON THE COHERENT DISPLAYS (equal char, BY CONSTRUCTION --
    no oracle shared with anything above): O = F_4[[t]], q = 4,
    Phi' = x^2 + w t (w = omega, F_4 = F_2(w)), e1 = 2, f1 = 1, h = 1,
    eta = res(theta^2/t) = w. f = g1 g2 with g1 = x^2 + tx + wt (letter 1),
    g2 = x^2 + wtx + wt (letter w): both slope-1/2 ramified quadratics, so
    sigma = {(2,1),(2,1)} IS KNOWN. Development: A1 = w^2 t x + w t^2,
    A0 = w^2 t^3, pins (0,6),(1,3),(2,0) all on the lam = 3 line.
    NAIVE read a = (w^2, w^2, 1): Z^2 + w^2 Z + w^2 has NO F_4-root ->
    naive would predict the INERT-over-stage type {(2,2)}. COHERENT read
    (W = (0,1,1), eta = w): a~ = (w^2, 1, w): wZ^2 + Z + w^2 =
    w(Z-1)(Z-w) -- split exactly at the two letters. Also checked: the
    direct symbolic residues in F_4[t][theta]/(theta^2 - wt) equal the
    W-formula values (decorrelated from the formula).

Exit 0 iff 0 violations. Z-rows exact (Bareiss/Sylvester); F_4 row exact
finite-field arithmetic.
"""
import json, subprocess, sys
from fractions import Fraction

VIOL = 0
def fail(msg):
    global VIOL; VIOL += 1; print('VIOLATION:', msg)

# ---------- exact integer-poly helpers (generic; as in the prior legs) ----
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

R = {}

# ================= FR1a: (2,1) e1=1 starved ALPHA ====================
print('== FR1a: (Q,f1)=(2,1), e1=1, Z_2, Phi\'=x-2, starved ALPHA ==')
K1 = [-2, 1]
f1a = pmul(pmul([-14, 1], [-22, 1]), [-10, 1])
_, s1a = polygon(f1a, K1, 3, 2, 1, 1)
if sorted((str(s), L) for s, L in s1a) != [('2', 2), ('3', 1)]:
    fail('FR1a base polygon %s != {2:2, 3:1}' % s1a)
m1a = above_line(f1a, [-6, 1], 3, 2, 2, 1, 1)      # Phi'' = x-6 (C = n(2) = 4)
if m1a != 2: fail('FR1a measured m_1 at slope 2 = %d != 2' % m1a)
_, s1ar = polygon(f1a, [-6, 1], 3, 2, 1, 1)
top = sorted(str(s) for s, _ in s1ar if s > 2)
if top != ['3', '4']: fail('FR1a sub-block slopes %s != {3,4}' % s1ar)
lamside = [(s, L) for s, L in s1ar if s == 2]
if lamside != [(Fraction(2), 1)]:
    fail('FR1a collapsed lambda-side %s != length 1' % lamside)
sg = gp_sig([f1a], 2)
if sg != [((1, 1), (1, 1), (1, 1))]: fail('FR1a PARI sigma %s' % sg)
print('   base', [(str(s), L) for s, L in s1a], '| m_1 =', m1a,
      '| recentered', [(str(s), L) for s, L in s1ar], '| sigma', sg)
R['FR1a'] = 'ok'

# ================= FR1b: (2,1) e1=2 mu=3 starved depth-2 =============
print('== FR1b: (Q,f1)=(2,1), e1=2, Phi\'=x^2-2, mu=3 starved ALPHA ==')
K2 = [-2, 0, 1]
blocks = [[-10, -2, 1], [-34, -2, 1], [-130, -2, 1]]
f1b = pmul(pmul(blocks[0], blocks[1]), blocks[2])
_, s1b = polygon(f1b, K2, 3, 2, 2, 1)
if [(str(s), L) for s, L in s1b] != [('3', 3)]:
    fail('FR1b base polygon %s != single side lam=3 len 3' % s1b)
m1b = above_line(f1b, [-2, -2, 1], 3, 3, 2, 2, 1)  # Phi'' = Phi' - 2x
if m1b != 3: fail('FR1b measured m_1 = %d != 3 (starved ALPHA)' % m1b)
_, s1br = polygon(f1b, [-2, -2, 1], 3, 2, 2, 1)
if sorted(str(s) for s, _ in s1br) != ['10', '14', '6']:
    fail('FR1b sub-block slopes %s != {6,10,14}' % s1br)
if not he31a(f1b, [-2, -2, 1], 2, 2, 2, 1): fail('FR1b HE3-1a at Phi\'\'')
sg = gp_sig([f1b], 2)
if sg != [((2, 1), (2, 1), (2, 1))]: fail('FR1b PARI sigma %s' % sg)
print('   base', [(str(s), L) for s, L in s1b], '| m_1 =', m1b,
      '| sub-block', [(str(s), L) for s, L in s1br], '| sigma', sg)
R['FR1b'] = 'ok'

# ====== FR1c: (3,1) STARVED SLOPE + WRAP ADJUDICATOR AT f1 = 1 ========
print('== FR1c: (Q,f1)=(3,1), Phi\'=x^2+3, naive INERT vs coherent SPLIT ==')
K3 = [3, 0, 1]
f1c = [9, 0, -3, 0, 1]                              # x^4 - 3x^2 + 9
chk = pmul([3, -3, 1], [3, 3, 1])
if f1c != chk: fail('FR1c member != (x^2-3x+3)(x^2+3x+3)')
dvs, s1c = polygon(f1c, K3, 2, 3, 2, 1)
if [(str(s), L) for s, L in s1c] != [('3', 2)]:
    fail('FR1c base polygon %s != single side lam=3 len 2' % s1c)
if dvs[1] + 3 <= 6: fail('FR1c middle pin NOT lifted (dv=%s)' % dvs[1])
# measured multiplicities at the two letters (C_1 = 3x, C_2 = 6x):
mm = {}
for s, C in ((1, [0, 3]), (2, [0, 6])):
    key = [K3[k] - (C[k] if k < len(C) else 0) for k in range(3)]
    mm[s] = above_line(f1c, key, 2, 3, 3, 2, 1)
    if not he31a(f1c, key, 2, 3, 2, 1): fail('FR1c HE3-1a at s=%d' % s)
if mm != {1: 1, 2: 1}:
    fail('FR1c measured m = %s: coherent says {1:1,2:1}, naive says 0s' % mm)
sg = gp_sig([f1c], 3)
if sg != [((2, 1), (2, 1))]:
    fail('FR1c PARI sigma %s != {(2,1)}^2 (naive predicts {(2,2)})' % sg)
print('   base', [(str(s), L) for s, L in s1c], '| measured m =', mm,
      '(naive Z^2+1 would give 0,0) | sigma', sg,
      '(naive would predict {(2,2)})')
R['FR1c'] = 'ok'

# ============ FR1d: (3,1) e1=2 mu=3 starved-split =====================
print('== FR1d: (Q,f1)=(3,1), Phi\'=x^2-3, mu=3, slope-3 side eats K^x ==')
K4 = [-3, 0, 1]
f1d = pmul(pmul([-3, -3, 1], [-3, -6, 1]), [-12, 0, 1])
_, s1d = polygon(f1d, K4, 3, 3, 2, 1)
if sorted((str(s), L) for s, L in s1d) != [('3', 2), ('4', 1)]:
    fail('FR1d base polygon %s != {3:2, 4:1}' % s1d)
mm = {}
for s, C in ((1, [0, 3]), (2, [0, 6])):
    key = [K4[k] - (C[k] if k < len(C) else 0) for k in range(3)]
    mm[s] = above_line(f1d, key, 3, 3, 3, 2, 1)
if mm != {1: 1, 2: 1}: fail('FR1d measured m at slope 3 = %s != 1,1' % mm)
sg = gp_sig([f1d], 3)
if sg != [((2, 1), (2, 1), (2, 1))]: fail('FR1d PARI sigma %s' % sg)
print('   base', [(str(s), L) for s, L in s1d], '| m at slope 3:', mm,
      '| sigma', sg)
R['FR1d'] = 'ok'

# ========== FR2: mu=3 coherent family at (e1,f1) = (3,1) ==============
print('== FR2: (3;3,1,3;1), Phi\'=x^3+3, lam=4, W=(0,1,1,1), eta=-1 ==')
K5 = [3, 0, 0, 1]
P2 = pmul(K5, K5); P3 = pmul(P2, K5)
f2 = [P3[k] for k in range(len(P3))]
for k, c in enumerate(pmul([0, -3], P2)): f2[k] += c       # -3x Phi'^2
for k, c in enumerate(pmul([0, 0, 9], K5)): f2[k] += c     # +9x^2 Phi'
f2[0] -= 81
dvs, s2 = polygon(f2, K5, 3, 3, 3, 1)
if [(str(s), L) for s, L in s2] != [('4', 3)]:
    fail('FR2 base polygon %s != single side lam=4 len 3' % s2)
if dvs[:3] != [12, 8, 4]: fail('FR2 pins %s != (0,12),(1,8),(2,4)' % dvs[:3])
mm = {}
for s, C in ((1, [0, 0, 0]), (2, [0, 0, 0])):
    # letter-carriers at height 4 = kappa: n(4) = 3x (i0(4)=1, a=1)
    Cc = [0, 3] if s == 1 else [0, 6]
    key = [K5[k] - (Cc[k] if k < len(Cc) else 0) for k in range(4)]
    mm[s] = above_line(f2, key, 3, 4, 3, 3, 1)
    if not he31a(f2, key, 3, 3, 3, 1): fail('FR2 HE3-1a at s=%d' % s)
if mm != {1: 0, 2: 0}:
    fail('FR2 measured m = %s: coherent irreducible says 0,0; naive'
         ' (Z-1)(Z^2+1) says m_1 = 1' % mm)
sg = gp_sig([f2], 3)
if sg != [((3, 3),)]:
    fail('FR2 PARI sigma %s != {(3,3)} (naive predicts {(3,1),(3,2)})' % sg)
print('   pins', dvs[:3], '| base', [(str(s), L) for s, L in s2],
      '| measured m =', mm, '(naive says m_1=1) | sigma', sg,
      '(naive would predict {(3,1),(3,2)})')
R['FR2'] = 'ok'

# ===== FR2b: W-formula DIRECT leg (nfeltval/nfmodpr, no W formula) =====
print('== FR2b: coherent coefficients by PARI residue arithmetic ==')
gp2 = r"""
nf = nfinit(x^3+3); P = idealprimedec(nf,3)[1];
mo = nfmodprinit(nf, P);
n12 = 81; n4 = 3*x;
A = [-81, 9*x^2, -3*x, 1];
{ for (k = 0, 3,
    num = nfeltmul(nf, A[k+1], nfeltpow(nf, n4, k));
    r = nfmodpr(nf, nfeltdiv(nf, num, n12), mo);
    print("cohA ", k, " ", lift(r))); }
nf2 = nfinit(x^4+9); Q = idealprimedec(nf2,3)[1];
mo2 = nfmodprinit(nf2, Q);
eta2 = nfmodpr(nf2, x^2/3, mo2); print("eta ", lift(lift(eta2)));
n10 = 243; n5 = 9*x;
B = [243, 9*x, 1];
{ for (k = 0, 2,
    num = nfeltmul(nf2, B[k+1], nfeltpow(nf2, n5, k));
    r = nfmodpr(nf2, nfeltdiv(nf2, num, n10), mo2);
    print("cohB ", k, " ", lift(lift(r)))); }
"""
out2 = gp_run(gp2)
print('\n'.join('   ' + l for l in out2.strip().splitlines()))
gA, gB, eta_s = {}, {}, None
for ln in out2.splitlines():
    t = ln.split(None, 2)
    if not t: continue
    if t[0] == 'cohA': gA[int(t[1])] = t[2].strip()
    if t[0] == 'cohB': gB[int(t[1])] = t[2].strip()
    if t[0] == 'eta': eta_s = t[1].strip()
# FR2 member: formula a~ = (-1,-1,1,-1) -> (2,2,1,2) in F_3
if [gA.get(k) for k in range(4)] != ['2', '2', '1', '2']:
    fail('FR2b direct coherent coeffs %s != formula (2,2,1,2)' % gA)
# ma witness: formula a~ = (1, eta, eta) in F_9 (eta as printed by PARI)
if not (gB.get(0) == '1' and gB.get(1) == gB.get(2) == eta_s):
    fail('FR2b ma witness direct coeffs %s != (1, eta, eta), eta=%s'
         % (gB, eta_s))
print('   FR2 member: direct = (2,2,1,2) = formula | ma witness: direct ='
      ' (1, %s, %s) = (1, eta, eta) [DEF 1 [r2] W=(0,1,1) confirmed]'
      % (gB.get(1), gB.get(2)))
R['FR2b'] = 'ok'

# ========== FR3: non-prime q = 4, equal char, BY CONSTRUCTION ==========
print('== FR3: O = F_4[[t]], q = 4, Phi\' = x^2 + wt, coherent vs naive ==')
# F_4 = {0,1,2,3} coded as bitpairs: 0, 1, w = 2, w^2 = 3 (w^2 = w+1).
FMUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def f4mul(a, b): return FMUL[a][b]
def f4add(a, b): return a ^ b
# polynomials in t over F_4: dict {deg: coeff}; polys in x: list of those.
def tmul(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            k = a + b; out[k] = f4add(out.get(k, 0), f4mul(ca, cb))
    return {k: c for k, c in out.items() if c}
def tadd(u, v):
    out = dict(u)
    for b, cb in v.items(): out[b] = f4add(out.get(b, 0), cb)
    return {k: c for k, c in out.items() if c}
def xmul(F, G):
    out = [{} for _ in range(len(F)+len(G)-1)]
    for i, u in enumerate(F):
        for j, v in enumerate(G): out[i+j] = tadd(out[i+j], tmul(u, v))
    return out
def xsub(F, G):  # char 2: sub = add
    n = max(len(F), len(G))
    return [tadd(F[i] if i < len(F) else {}, G[i] if i < len(G) else {})
            for i in range(n)]
w, w2 = 2, 3
Phi = [{1: w}, {}, {0: 1}]                       # x^2 + wt
g1 = [{1: w}, {1: 1}, {0: 1}]                    # x^2 + tx + wt   letter 1
g2 = [{1: w}, {1: w}, {0: 1}]                    # x^2 + wtx + wt  letter w
f3 = xmul(g1, g2)
# development of f3 at Phi (monic in x, deg 2): f3 = Phi^2 + A1 Phi + A0
A1exp = [{2: w}, {1: w2}]                        # w t^2 + w^2 t x
A0exp = [{3: w2}]                                # w^2 t^3
rec = xsub(xmul(Phi, Phi), xsub(xmul(A1exp, Phi), A0exp))  # char2: all adds
if [dict(c) for c in xsub(f3, rec)] != [{}]*5:
    fail('FR3 development identity f = Phi^2 + A1 Phi + A0 FAILS')
# pins: dv = 2*v_t + i*h on slots
def dvF4(A):
    best = 10**9
    for i, u in enumerate(A):
        for k in u: best = min(best, 2*k + i)
    return best
pins = (dvF4(A0exp), dvF4(A1exp), 0)
if pins != (6, 3, 0): fail('FR3 pins %s != (6,3,0)' % (pins,))
# naive per-slot read a_k = res(A_k / n(6-3k)): n(6)=t^3, n(3)=tx, n(0)=1
# slot arithmetic done by hand-checkable extraction:
a0 = A0exp[0].get(3, 0)              # coeff of t^3 in A0 (x-degree 0 slot)
a1 = A1exp[1].get(1, 0)              # coeff of t x in A1
a2 = 1
if (a0, a1, a2) != (w2, w2, 1): fail('FR3 naive read %s' % ((a0, a1, a2),))
naive_roots = [z for z in (1, 2, 3)
               if f4add(f4add(f4mul(f4mul(z, z), a2), f4mul(z, a1)), a0) == 0]
if naive_roots: fail('FR3 naive residual HAS F_4 roots %s (expected none:'
                     ' naive predicts inert {(2,2)})' % naive_roots)
# coherent: direct symbolic residue in F_4[t][theta]/(theta^2 = wt):
# elements a + b*theta, a,b in F_4[t]; residue of unit = const term of a.
def red_theta(A):
    """A(theta) for A = [c0(t), c1(t)] + higher x-slots reduced by
    theta^2 = wt: returns (aa, bb) with value aa(t) + bb(t)*theta."""
    aa, bb = {}, {}
    for i, u in enumerate(A):
        q, r = divmod(i, 2)
        tw = u
        for _ in range(q): tw = tmul(tw, {1: w})   # theta^2 -> wt
        if r == 0: aa = tadd(aa, tw)
        else: bb = tadd(bb, tw)
    return aa, bb
def coh_coeff(Ak, k):
    """res(A_k(theta) * n(3)(theta)^k / n(6)(theta)); n(3) = t*theta,
    n(6) = t^3. numerator = A_k(theta) * t^k * theta^k."""
    aa, bb = red_theta(Ak)
    # multiply by theta^k
    for _ in range(k):
        aa, bb = tmul(bb, {1: w}), aa               # (a+btheta)*theta
    # multiply by t^k, divide by t^3: net t^(k-3)
    shift = k - 3
    val = {d + shift: c for d, c in aa.items()}
    if any(d < 0 for d in val): fail('FR3 non-integral residue at k=%d' % k)
    if any(d < 0 for d in bb): pass
    return val.get(0, 0)
ac = (coh_coeff(A0exp, 0), coh_coeff(A1exp, 1), coh_coeff([{0: 1}], 2))
if ac != (w2, 1, w): fail('FR3 direct coherent read %s != (w^2, 1, w)' % (ac,))
# formula: a~_k = a_k * eta^W(k), W = (0,1,1), eta = w
form = (a0, f4mul(a1, w), f4mul(a2, w))
if form != ac: fail('FR3 W-formula %s != direct %s' % (form, ac))
coh_roots = sorted(z for z in (1, 2, 3)
                   if f4add(f4add(f4mul(f4mul(z, z), ac[2]),
                                  f4mul(z, ac[1])), ac[0]) == 0)
if coh_roots != [1, w]:
    fail('FR3 coherent roots %s != the letters {1, w}' % coh_roots)
print('   pins', pins, '| naive a = (w2,w2,1): NO F_4 root (would predict'
      ' {(2,2)}) | coherent = direct = (w2,1,w): roots {1,w} = the letters'
      ' | true sigma = {(2,1),(2,1)} by construction (g1,g2 slope-1/2'
      ' Eisenstein-type)')
# g1, g2 irreducibility: Newton polygon slope 1/2 over F_4((t))
for gi, nm in ((g1, 'g1'), (g2, 'g2')):
    vals = [min(u.keys()) if u else 10**9 for u in gi]
    if not (vals[0] == 1 and vals[1] >= 1 and vals[2] == 0):
        fail('FR3 %s not slope-1/2 irreducible shape: %s' % (nm, vals))
R['FR3'] = 'ok'

print()
if VIOL == 0:
    print('VERDICT GREEN -- 0 violations, all preregistered predictions'
          ' confirmed (coherent read adjudicated at (3,1), (3;3,1,3;1),'
          ' and non-prime q = 4; starved-corner family exact).')
else:
    print('VERDICT RED -- %d violations' % VIOL)
json.dump({'violations': VIOL, 'legs': R}, open(
    'he3_pe3fresh_results.json', 'w'), indent=1)
sys.exit(0 if VIOL == 0 else 1)
