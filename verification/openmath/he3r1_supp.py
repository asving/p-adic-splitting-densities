#!/usr/bin/env python3
"""HE3 r1 SUPPLEMENTARY LEG (additive; the sealed he3_checks.py battery and
its artifacts are BYTE-FROZEN and not touched).

What this run certifies, keyed to the [r1] repairs of HE3_PROOF_2026-08-08.md:

P1  THE REPAIRED PEEL AT THE PE1 COUNTER-INSTANCE (F1). Genre (3;1,2,3;1):
    O = Z_3, Phi' = x^2+9, K = F_9, D' = 2, D'h = 2. Member
    f = (Phi'-27)(Phi'-9x)(Phi'-18x): single side lam = 3, residual
    (Z-1)(Z-eta)(Z+eta) = PE1's {1, i, -i}. For EVERY letter s in F_9^x the
    LEMMA HE3-1L carrier C_s (a*3^3 + b*3^2*x for s = a+b*eta) is used with
    the [r1,F8] minus convention Phi'' = Phi' - C_s; measured m_s :=
    horizontal length of P(F'') strictly above lam. PREREGISTERED: m_s = 1
    at s in {1, eta, -eta}, m_s = 0 at the other 5 letters (incl. the
    OLD-display-unreachable K\F_3 letters), Sigma D'*m_s = 6 = deg f; PARI
    sigma = {(1,2)}^3. Also: the OLD letter family (shat in O, residues
    F_3^x = {1,2}) reaches only s = 1 here — displayed, not asserted.
P2  f1 = 2 SWEEP (PARI oracle): 8 members at Phi' = x^2+9 across residual
    genres — 3 rational letters (3 configs incl. a Frobenius-conjugate
    pair), irreducible quadratic (block (1,4)), irreducible cubic (block
    (1,6)), three CONSECUTIVE integer slopes 3,4,5 (the [r1-N1] geography)
    + its recenter-then-invert supplement demo (P(F'') slopes {3,4,>=6}:
    the gap at 5 appears), an ell = 2 side (block (2,2)), and a mixed
    member. Dictionary (e_s,f_s) -> (e1*e_s, f1*f_s) vs PARI sig.
P3  f1 = 3 SWEEP (PARI oracle): Phi' = x^3-9x+27 (K = F_27, D' = 3,
    D'h = 3), members at lam = 4: {1,2,eta}, the Frobenius orbit
    {eta, eta^3, eta^9} as three separate C-letter peels, an irreducible
    quadratic block (1,6), an irreducible cubic block (1,9). Repaired-peel
    profile m_s over ALL 26 letters of F_27^x on the first member
    (PREREGISTERED: 1 at the 3 residual roots, 0 at the other 23).
P4  LEMMA HE3-1L EXACT-SET CHECK at (1,2,1): for kappa in {0,1,2,3} the
    enumerated realized residues res(C(theta)/n(kappa)(theta)) equal the
    displayed span over T(kappa) (kappa = 0: F_3^x only; kappa >= 1 =
    (D'-1)h: all of F_9^x).
HE3-1a is asserted at every test key used (exact integer resultants via
Sylvester + fraction-free Bareiss, the sealed battery's route; no sympy —
[r2 2026-08-09, PE2 F-4: the earlier docstring line said "sympy", a slip;
the code below never imported it]).
CAVEAT [r2 2026-08-09, PE2 F-4]: P4 computes the "realized residues" BY the
slot-digit extraction the lemma itself derives (c0/c1 read off C's slots),
so P4 verifies the T(kappa) bookkeeping of LEMMA HE3-1L, NOT the residue
arithmetic — it is quasi-tautological as a residue check. The decorrelated
residue leg is he3_pe2fresh.py FR-C (PARI nfeltval heights + nfmodpr
residues at (2,2,1), kappa = 0..5, no slot formula), committed at PE2.
"""
import json, subprocess, sys
from fractions import Fraction
from itertools import product

OUT = {'P1': {}, 'P2': [], 'P3': [], 'P4': [], 'violations': 0}

def sylvester_res(f, g):
    """exact integer resultant Res(f, g), polys low->high, via the
    Sylvester matrix and fraction-free Bareiss elimination (the sealed
    battery's route; no sympy dependency)."""
    F, G = list(reversed(f)), list(reversed(g))     # high->low
    m, n = len(F)-1, len(G)-1
    N = m + n
    M = [[0]*N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(F): M[i][i+j] = c
    for i in range(m):
        for j, c in enumerate(G): M[n+i][i+j] = c
    det, prev, sign = 1, 1, 1
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

def v3(n):
    n = int(n)
    if n == 0: return 10**9
    v = 0
    while n % 3 == 0: n //= 3; v += 1
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

def pdivmod(f, g):
    """f, g integer polys (low->high), g monic; return (q, r)."""
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

def dev(f, key, mu):
    A, cur = [], f[:]
    for _ in range(mu):
        q, r = pdivmod(cur, key)
        A.append(r); cur = q
    return A

def dvA(A, h=1):
    """dv of A(theta), e1 = 1 frames: min_i (v3(a_i) + i*h)."""
    best = 10**9
    for i, c in enumerate(A):
        if c: best = min(best, v3(c) + i*h)
    return best

def hull(pts):
    pts = sorted(pts); H = [pts[0]]
    for p in pts[1:]:
        while len(H) >= 2 and (Fraction(H[-1][1]-H[-2][1], H[-1][0]-H[-2][0])
                               >= Fraction(p[1]-H[-1][1], p[0]-H[-1][0])):
            H.pop()
        H.append(p)
    return H

def polygon(f, key, mu):
    A = dev(f, key, mu)
    dvs = [dvA(a) for a in A] + [0]
    pts = [(j, dvs[j]) for j in range(mu+1) if dvs[j] < 10**8]
    H = hull(pts)
    sides = []
    for k in range(len(H)-1):
        (j1, m1), (j2, m2) = H[k], H[k+1]
        sides.append((Fraction(m1-m2, j2-j1), j2-j1))  # (slope, length)
    return A, sides

def above_len(sides, lam):
    return sum(L for s, L in sides if s > lam)

def above_line(f, key, mu, lam):
    """horizontal length of P(dev of f at key) strictly above slope lam,
    measured against the lam-supporting line (an INFINITE pin — the
    degenerate A_0' = 0 branch, key | f exactly — counts as above; cf.
    the [r1-N1] supplement's CASE A_0' = 0)."""
    dvs = [dvA(a) for a in dev(f, key, mu)] + [0]
    hF = min(dvs[j] + lam*j for j in range(mu+1))
    m = 0
    while m < mu and dvs[m] + lam*m > hF: m += 1
    return m

def he31a_check(f, key, Dp):
    """assert v3(Res(f,key)) == D' * dv(f mod key); at key | f both sides
    are +infinity (Res = 0, B_0 = 0) and the identity is read as inf=inf."""
    q, B0 = pdivmod(f, key)
    if not any(B0):
        return (v3(sylvester_res(f, key)) >= 10**8, 'inf', 'inf')
    lhs = v3(sylvester_res(f, key))
    rhs = Dp * dvA(B0)
    return lhs == rhs, lhs, rhs

GP_FUN = r"""
ef(g, p) = { if (poldegree(g)==1, return([1,1]));
  my(nf = nfinit([g,[p]]), dec = idealprimedec(nf, p)); [dec[1].e, dec[1].f] }
sig(f, p) = { my(d = poldisc(f), F); if (d==0, return([[-1,-1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i,1]), p))) }
"""
def gp_sig(polys):
    lines = ['print(sig(%s,3))' % ('+'.join('(%d)*x^%d' % (c, k)
             for k, c in enumerate(f) if c) or '0') for f in polys]
    r = subprocess.run(['gp', '-q'], input=GP_FUN + '\n'.join(lines) + '\n',
                       capture_output=True, text=True, timeout=900)
    sigs = []
    for ln in r.stdout.strip().splitlines():
        ln = ln.strip()
        if not ln.startswith('[['): continue     # gp -q echoes closures
        nums = [int(t) for t in ln.replace('[', ' ').replace(']', ' ')
                .replace(',', ' ').split()]
        sigs.append(tuple(sorted(zip(nums[0::2], nums[1::2]))))
    return sigs

def fail(msg):
    OUT['violations'] += 1
    print('VIOLATION:', msg)

# ---------------- F9 = F3(eta), eta^2 = -1 ----------------
F9 = [(a, b) for a in range(3) for b in range(3)]
F9X = [z for z in F9 if z != (0, 0)]
def carrier9(s, kap):
    """HE3-1L carrier for s = a+b*eta at integer height kap >= 1 (e1=f1h=..
    frame (1,2,1)): C = a*3^kap + b*3^(kap-1)*x."""
    a, b = s
    return [a * 3**kap, b * 3**(kap-1)]

KEY9 = [9, 0, 1]  # Phi' = x^2 + 9

# ---------------- P1: the repaired peel at PE1's counter-instance --------
print('== P1: repaired peel, genre (3;1,2,3;1), member {1, eta, -eta} ==')
f1 = pmul(pmul(psub(KEY9, [27]), psub(KEY9, [0, 9])), psub(KEY9, [0, 18]))
LAM = 3
A, sides = polygon(f1, KEY9, 3)
print('   entry polygon (slope, len):', [(str(s), L) for s, L in sides])
if sides != [(Fraction(3), 3)]: fail('P1 entry polygon not single side lam=3')
f1b = f1[:]; f1b[0] += 3**13     # junk-perturbed variant: no factor is a
                                 # literal key-translate (A_0' != 0 branch)
roots = {(1, 0): 1, (0, 1): 1, (0, 2): 1}
prof = {}
for tag, ff in [('exact', f1), ('junk', f1b)]:
    prof[tag] = {}
    for s in F9X:
        C = carrier9(s, LAM)
        key2 = psub(KEY9, C)                  # [r1, F8] minus convention
        ok, l, r = he31a_check(ff, key2, 2)
        if not ok: fail('P1(%s) HE3-1a at s=%s: %s != %s' % (tag, s, l, r))
        prof[tag][s] = above_line(ff, key2, 3, LAM)
    for s in F9X:
        want = roots.get(s, 0)
        if prof[tag][s] != want:
            fail('P1(%s) m_s at %s: got %s want %s'
                 % (tag, s, prof[tag][s], want))
    print('   [%s] m_s profile:' % tag,
          {str(k): int(v) for k, v in prof[tag].items()},
          '| Sigma D\'m =', 2*sum(prof[tag].values()), '(deg f = 6)')
prof = prof['junk']
print('   old-display reach (shat in O, res in F_3): letters {1,2} only ->'
      ' pins S_{Z-1} alone; letters eta, -eta = i, -i need HE3-1L carriers')
sigp = gp_sig([f1, f1b])
print('   PARI sigma (exact, junk):', sigp)
if any(s != ((1, 2), (1, 2), (1, 2)) for s in sigp):
    fail('P1 PARI sigma mismatch')
OUT['P1'] = {'profile': {str(k): int(v) for k, v in prof.items()},
             'sigma': sigp, 'sum_D_m': 2*sum(prof.values())}

# ---------------- P2: f1 = 2 sweep ----------------
print('== P2: f1 = 2 sweep (dictionary vs PARI) ==')
c14 = psub(pmul(KEY9, KEY9), [729, 243])          # Phi'^2 - (3^6 + 3^5 x)
# Z^3 + 2Z + 1 member: f = Phi'^3 + 2*3^6*Phi' + 3^9
t = pmul(pmul(KEY9, KEY9), KEY9)
c16 = [t[k] + (2*729*KEY9[k] if k < len(KEY9) else 0) for k in range(len(t))]
c16[0] += 19683
l2 = psub(pmul(KEY9, KEY9), [2187])               # Phi'^2 - 3^7 (lam = 7/2)
members2 = [
  ('{1,eta,-eta} (P1)', f1, ((1,2),(1,2),(1,2))),
  ('{1,2,eta}', pmul(pmul(psub(KEY9,[27]), psub(KEY9,[54])),
                     psub(KEY9,[0,9])), ((1,2),(1,2),(1,2))),
  ('{eta,1+eta,2+eta}', pmul(pmul(psub(KEY9,[0,9]), psub(KEY9,[27,9])),
                             psub(KEY9,[54,9])), ((1,2),(1,2),(1,2))),
  ('(Z-1)(Z^2-(1+eta)) -> (1,2)+(1,4)', pmul(psub(KEY9,[27]), c14),
   ((1,2),(1,4))),
  ('Z^3+2Z+1 irred -> (1,6)', c16, ((1,6),)),
  ('3 consecutive slopes 3,4,5', pmul(pmul(psub(KEY9,[27]), psub(KEY9,[81])),
                                      psub(KEY9,[243])), ((1,2),(1,2),(1,2))),
  ('ell=2 side lam=7/2 -> (2,2)', l2, ((2,2),)),
  ('mixed (1,2)+(2,2)', pmul(psub(KEY9,[0,9]), l2), ((1,2),(2,2))),
]
sigs = gp_sig([m[1] for m in members2])
for (name, f, pred), got in zip(members2, sigs):
    ok, l, r = he31a_check(f, KEY9, 2)
    tag = 'OK ' if (got == tuple(sorted(pred)) and ok) else 'BAD'
    if tag == 'BAD': fail('P2 %s: pred %s PARI %s he31a %s' % (name, pred, got, ok))
    print('   [%s] %-38s pred %s pari %s' % (tag, name, pred, got))
    OUT['P2'].append({'name': name, 'pred': pred, 'pari': got})
# [r1-N1] supplement demo on the consecutive-slope member: BOTH branches
fc = members2[5][1]
_, s0 = polygon(fc, KEY9, 3)
if sorted(str(a) for a, _ in s0) != ['3', '4', '5']:
    fail('N1 demo: base slopes not 3,4,5')
key_top = psub(KEY9, carrier9((1, 0), 5))    # recenter top slope 5 at s=1
# branch CASE A_0' = 0 (exact member: Phi'' | f):
A0p = pdivmod(fc, key_top)[1]
g = pdivmod(fc, key_top)[0]                  # g = f/Phi'' exactly
if any(A0p): fail('N1 demo: expected the A_0\'=0 branch on the exact member')
_, sg = polygon(g, key_top, 2)
if sorted(str(a) for a, _ in sg) != ['3', '4']:
    fail('N1 demo: quotient g polygon at Phi\'\' not slopes {3,4}')
# branch CASE A_0' != 0 (junk member):
fcb = fc[:]; fcb[0] += 3**15
_, s1 = polygon(fcb, key_top, 3)
sl1 = [a for a, _ in s1]
if any(a == 5 for a in sl1) or not any(a >= 6 for a in sl1) \
   or not all(a in sl1 for a in (3, 4)):
    fail('N1 demo: recentered slopes lack the gap shape {3,4,>=6}')
print('   [r1-N1] demo: P(F) slopes', [(str(a), L) for a, L in s0],
      '| A_0\'=0 branch: Phi\'\'|f exactly, quotient dev slopes',
      [(str(a), L) for a, L in sg],
      '| A_0\'!=0 branch: P(F\'\') slopes', [(str(a), L) for a, L in s1],
      '(the gap at 5 appears)')
OUT['P2N1'] = {'base': [(str(a), L) for a, L in s0],
               'quotient': [(str(a), L) for a, L in sg],
               'recentered': [(str(a), L) for a, L in s1]}

# ---------------- F27 = F3(eta), eta^3 = eta - 1 ----------------
def m27(x, y):
    a = [0]*5
    for i in range(3):
        for j in range(3): a[i+j] = (a[i+j] + x[i]*y[j]) % 3
    # reduce: eta^3 = eta - 1, eta^4 = eta^2 - eta
    a[1] += a[3]; a[0] -= a[3]; a[2] += a[4]; a[1] -= a[4]
    return (a[0] % 3, a[1] % 3, a[2] % 3)
def p27(x, n):
    r = (1, 0, 0)
    for _ in range(n): r = m27(r, x)
    return r
F27 = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
F27X = [z for z in F27 if z != (0, 0, 0)]
KEY27 = [27, -9, 0, 1]  # Phi' = x^3 - 9x + 27, psi = y^3 - y + 1
def carrier27(s, kap):
    """C = a*3^kap + b*3^(kap-1)x + c*3^(kap-2)x^2 for s = a+b eta+c eta^2,
    heights v+0, v+1, v+2 all = kap (frame (1,3,1)); needs kap >= 2 =
    (D'-1)h."""
    a, b, c = s
    return [a*3**kap, b*3**(kap-1), c*3**(kap-2)]

print('== P3: f1 = 3 sweep, Phi\' = x^3-9x+27 (K = F_27), lam = 4 ==')
eta, e3, e9 = (0, 1, 0), p27((0, 1, 0), 3), p27((0, 1, 0), 9)
def trans27(s, kap=4): return psub(KEY27, carrier27(s, kap))
m31 = pmul(pmul(trans27((1,0,0)), trans27((2,0,0))), pmul(trans27(eta), [1]))
m32 = pmul(pmul(trans27(eta), trans27(e3)), pmul(trans27(e9), [1]))
# quadratic block: first non-square c in F27^x (c^13 != 1)
csq = next(c for c in F27X if p27(c, 13) != (1, 0, 0))
K2 = pmul(KEY27, KEY27)
qblk = psub(K2, carrier27(csq, 8))
m33 = pmul(trans27((1,0,0)), qblk)
# cubic block: monic z^3 + a2 z^2 + a1 z + a0 over F27 with no F27 root
def evalc(cs, z):
    acc, zp = (0,0,0), (1,0,0)
    for c in cs:
        acc = tuple((acc[i]+m27(c, zp)[i]) % 3 for i in range(3)); zp = m27(zp, z)
    return acc
cub = None
for a1 in F27:
    for a0 in F27X:
        cs = [a0, a1, (0,0,0), (1,0,0)]
        if all(evalc(cs, z) != (0,0,0) for z in F27): cub = cs; break
    if cub: break
K3 = pmul(K2, KEY27)
m34 = K3[:]
for tdeg in range(3):
    coef = cub[tdeg]
    if coef == (0, 0, 0): continue
    Ct = carrier27(coef, (3-tdeg)*4)
    kp = [1]
    for _ in range(tdeg): kp = pmul(kp, KEY27)
    term = pmul(Ct, kp)
    m34 = [ (m34[k] if k < len(m34) else 0) + (term[k] if k < len(term) else 0)
            for k in range(max(len(m34), len(term))) ]
members3 = [
  ('{1,2,eta} -> (1,3)^3', m31, ((1,3),(1,3),(1,3))),
  ('Frobenius orbit {eta,eta^3,eta^9} -> (1,3)^3', m32, ((1,3),(1,3),(1,3))),
  ('(Z-1)(Z^2-nonsq) -> (1,3)+(1,6)', m33, ((1,3),(1,6))),
  ('irred cubic -> (1,9)', m34, ((1,9),)),
]
sigs3 = gp_sig([m[1] for m in members3])
for (name, f, pred), got in zip(members3, sigs3):
    ok, l, r = he31a_check(f, KEY27, 3)
    tag = 'OK ' if (got == tuple(sorted(pred)) and ok) else 'BAD'
    if tag == 'BAD': fail('P3 %s: pred %s PARI %s he31a %s' % (name, pred, got, ok))
    print('   [%s] %-44s pred %s pari %s' % (tag, name, pred, got))
    OUT['P3'].append({'name': name, 'pred': pred, 'pari': got})
# repaired-peel profile over ALL 26 letters on member 1
prof3, roots3 = {}, {(1,0,0): 1, (2,0,0): 1, eta: 1}
m31b = m31[:]; m31b[0] += 3**17    # junk variant (A_0' != 0 branch)
for s in F27X:
    key2 = psub(KEY27, carrier27(s, 4))
    ok, l, r = he31a_check(m31b, key2, 3)
    if not ok: fail('P3 HE3-1a at s=%s' % (s,))
    prof3[s] = above_line(m31b, key2, 3, 4)
bad = [s for s in F27X if prof3[s] != roots3.get(s, 0)]
if bad: fail('P3 peel profile wrong at %s' % bad)
print('   peel profile over F_27^x: m_s = 1 at %d letters (the residual'
      ' roots), 0 at %d letters; Sigma D\'m = %d (deg f = 9)'
      % (sum(1 for v in prof3.values() if v == 1),
         sum(1 for v in prof3.values() if v == 0), 3*sum(prof3.values())))
OUT['P3peel'] = {'ones': sum(1 for v in prof3.values() if v == 1),
                 'zeros': sum(1 for v in prof3.values() if v == 0)}

# ---------------- P4: HE3-1L exact set at (1,2,1) ----------------
print('== P4: HE3-1L exact reachable set at (e1,f1,h) = (1,2,1) ==')
for kap in range(4):
    realized = set()
    for a, b in product(range(3), repeat=2):
        # C = a*3^A + b*3^B x over digit positions A,B >= max(0,...)
        for A in range(kap, kap+2):
            for B in range(max(kap-1, 0), kap+1):
                C = [a * 3**A, b * 3**B]
                if dvA(C) != kap: continue
                # residue of C(theta)/n(kap)(theta), n = 3^kap (i0 = 0):
                c0 = (C[0] // 3**kap) % 3 if C[0] and v3(C[0]) == kap else 0
                c1 = (C[1] // 3**(kap-1)) % 3 \
                    if (kap >= 1 and C[1] and v3(C[1]) == kap-1) else 0
                if kap == 0 and C[1]: continue
                realized.add((c0, c1))
    realized.discard((0, 0))
    Tk = [t for t in range(2) if kap >= t]          # i0 = 0, h = 1
    span = set()
    for a, b in product(range(3), repeat=2):
        if (a and 0 not in Tk) or (b and 1 not in Tk): continue
        if (a, b) != (0, 0): span.add((a, b))
    tag = 'OK ' if realized == span else 'BAD'
    if tag == 'BAD': fail('P4 kappa=%d realized %s != span %s'
                          % (kap, sorted(realized), sorted(span)))
    print('   [%s] kappa=%d: |realized| = %d, T(k) = %s (full iff kappa >= 1'
          ' = (D\'-1)h)' % (tag, kap, len(realized), Tk))
    OUT['P4'].append({'kappa': kap, 'n_realized': len(realized), 'T': Tk})

print('== VERDICT: %s (%d violations) ==' %
      ('GREEN' if OUT['violations'] == 0 else 'RED', OUT['violations']))
with open('he3r1_supp_results.json', 'w') as fh:
    json.dump(OUT, fh, indent=1, default=str)
sys.exit(0 if OUT['violations'] == 0 else 1)
