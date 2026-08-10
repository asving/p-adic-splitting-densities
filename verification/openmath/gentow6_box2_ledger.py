#!/usr/bin/env python3
"""GENTOW6-BOX-2 machine leg: THEOREM GENTOW-6.6 (the window count
ledger pricing (f_S, g) |-> f_S*g) — sealed instrument, two-commit
seal (this docstring preregistered at commit 1, BEFORE the first
run). Note: lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md S7.

SELF-CONTAINED integer-exact primitives (no imports beyond stdlib):
Bareiss fraction-free determinant of MY Sylvester layout vs a
Euclidean-remainder resultant (a DIFFERENT algorithm — the in-file
decorrelated pair), a p-local Smith-profile reducer, a Fraction
Gaussian solver for the Hensel leg; + PARI/gp decorrelation
(polresultant, factorpadic shapes, poldisc).

THREE FRAMES:
  L1  p=3 avatar (level-1 cells, FULL ENUMERATION): B_S = {x^2+ax+b:
      v(a)>=1, b = -3 mod 9}, B_g = {x^2+cx+d: v(c)>=1, d = -6 mod 9}
      — same side slope 1/2, distinct residual roots z=1 vs z=2 of
      the (coefficient/-3)-residue. c_J = 2 (Res(x^2-3, x^2-6) = 9).
      H = 2, N_0 = c + max(c,H) + 1 = 5.
  L2  p=2 avatar (distinct slopes): B_S = {x+c0: c0 = 2 mod 4},
      B_g = {x^2+cx+d: v(c)>=1, d = 2 mod 4}. c_J = 1
      (Res(x+2, x^2+2x+2) = 2). H = 2, N_0 = 4.
  T1  the box's tower geography (FAM-P5 bouquet shape, Q3): Phi' =
      x^2-3, block key Phi2 = Phi'^2-18x (psi2-class, c-bar = 2),
      sibling key Phi2' = Phi'^2-9x (r-class, c-bar = 1); B_S = the
      GENTOW-1(a) budget box at mu2* = 2 (floors [6,5,4,4|3,3,2,1]
      on slots (j,(a,b)) with w = 2a+5b, e1e2 = 4), B_g = the box at
      m' = 1 (floors [3,3,2,1]). c_J = mu2'*m'*D2*E2/(e1e2) =
      2*1*4*10/4 = 20. deg f = 12.

PREREGISTERED PREDICTIONS (hand-ledger-derived from THEOREM
GENTOW-6.6 BEFORE any run; no pre-seal smoke of this file; a RED
run-1, if any, will be kept and disclosed per the arc's precedent):
 P-SYL   Bareiss det of MY Sylvester layout == the Euclidean-
   remainder resultant exactly (up to the classical sign), and ==
   |gp polresultant| on the gp-sampled rows: L1 x100, L2 x100,
   T1 x60 (in-file dual) / 3+3+6 (gp).
 P-RES   v_p(Res) constant = c_J on random in-box pairs (digits
   drawn to depth 12): L1: 2 at 100/100; L2: 1 at 100/100; T1: 20
   at 60/60.
 P-SNF   Smith divisors of the Sylvester matrix: sum of p-valuations
   = c_J, each <= c_J (the dm(O^d) >= pi^c lattice clause):
   L1/L2/T1 x3 pairs each.
 P-IMG   full-enumeration image counts (pairs -> distinct products
   mod pi^N): L1 at N=5: 3^12 = 531441 (N=3,4 EXPLORATORY, recorded
   without want — below N_0); L2 at N=4,5,6: 2^6, 2^9, 2^12.
 P-FIB   fiber uniformity at/above N_0: every image class has
   exactly q^{c_J} preimage pair-classes: L1-N5 all = 9; L2-N4/5/6
   all = 2.
 P-CEN   census identity: the image set == the congruence cell:
   L1 cell = {v(f3)>=1, v(f2)>=2, v(f1)>=2, f0 = 18 mod 27}, count
   3^{4N-8}; L2 cell = {v(f2)>=1, f1 = 2 mod 4, f0 = 4 mod 8},
   count 2^{3N-6}; checked as (count equality) + (500/300 random
   cell members lie in the measured image set) at L1-N5 and L2-N6.
 P-T1-BOX floors table computed from GENTOW-1(a)'s display ==
   the hand-pinned [6,5,4,4 | 3,3,2,1] and [3,3,2,1].
 P-T1-POLY for a sampled pair, f = f_S*g has level-1 lower hull =
   ONE side (0,15) -> (6,0) in (J, dv)-coordinates, dv(A_J) =
   min(2*v3(coeff) + xdeg-weighted...) = min slot 2v+a over A_J.
 P-T1-HEN quantitative-Hensel window stability: f' = f + 3^45*x^7
   refactors by Sylvester-Newton iteration: f_S'*g' == f' to mod
   3^90, f_S' == f_S mod 3^25, and (f_S', g') hold every box floor.
 P-T1-GP factorpadic(Phi2,3,30) and factorpadic(Phi2',3,30) each a
   single factor of degree 4; poldisc(f_S*g) != 0 at one sampled
   pair.
TEETH (mutant wants that MUST die; kill counts asserted):
 T-NOJ   ledger without the q^{-c_J} content factor (image =
   q^{sum free}) — dies at L1-N5 and L2-N4/5/6: 4 kills.
 T-FIB1  fiber = q^{c_J+1} — dies at the same 4 fiber rows: 4 kills.
 T-RESC  c_J + 1 at T1 (v(Res) = 21) — dies at the T1 constancy
   row (aggregated): 1 kill.
 T-CEN   census cell with the deepest congruence DROPPED (L1: f0
   residue-fix -> 3^{4N-7}; L2: f0 = 4 mod 8 -> 2^{3N-5}) — count
   mismatch vs measured image: 4 kills (L1-N5, L2-N4/5/6).
"""
import random, subprocess
from fractions import Fraction

random.seed(20260810)

# ---------- primitives ------------------------------------------------
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

def pdivmod(f, g):
    f = list(f)
    assert g[-1] == 1
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

def vpoly(f, p):
    return min(vp(c, p) for c in f if c) if pstrip(list(f)) else None

def sylvester(u, w):
    """columns x^i*u (i < deg w), x^j*w (j < deg u); rows = coeff of
    x^0..x^{d-1}; u, w monic dense lists."""
    du, dw = len(u) - 1, len(w) - 1
    d = du + dw
    M = [[0] * d for _ in range(d)]
    for i in range(dw):
        for k, c in enumerate(u):
            M[i + k][i] = c
    for j in range(du):
        for k, c in enumerate(w):
            M[j + k][dw + j] = c
    return M

# ---------- harness ---------------------------------------------------
NCHK = NVIO = 0
KILLS = {}
def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

def tooth(name, killed, msg):
    KILLS[name] = KILLS.get(name, 0) + (1 if killed else 0)
    chk('TEETH', killed, 'tooth %s NOT killed: %s' % (name, msg))

def bareiss_det(M):
    """exact integer determinant, fraction-free Bareiss."""
    A = [row[:] for row in M]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = next((i for i in range(k + 1, n) if A[i][k]), None)
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) \
                    // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]

def res_euclid(f, g):
    """resultant by the remainder recursion over Fractions (the
    decorrelated oracle vs the Sylvester determinant)."""
    f = [Fraction(c) for c in f]
    g = [Fraction(c) for c in g]
    df, dg = len(f) - 1, len(g) - 1
    if dg == 0:
        return g[0] ** df
    # remainder of f by g over Q
    r = list(f)
    while len(r) - 1 >= dg and any(r):
        d = len(r) - 1 - dg
        c = r[-1] / g[-1]
        for k in range(len(g)):
            r[d + k] -= c * g[k]
        while r and r[-1] == 0:
            r.pop()
    if not r:
        return Fraction(0)
    dr = len(r) - 1
    return (-1) ** (df * dg) * g[-1] ** (df - dr) * res_euclid(g, r)

def snf_profile(M, p, K):
    """p-valuations of the elementary divisors, computed by local
    reduction mod p^K (K must exceed the divisor sum)."""
    mod = p ** K
    A = [[x % mod for x in row] for row in M]
    n = len(A)
    prof = []
    for step in range(n):
        best = None
        for i in range(step, n):
            for j in range(step, n):
                if A[i][j] % mod:
                    v = vp(A[i][j] % mod, p)
                    if best is None or v < best[0]:
                        best = (v, i, j)
        assert best is not None, 'rank collapse mod p^K'
        v, bi, bj = best
        A[step], A[bi] = A[bi], A[step]
        for row in A:
            row[step], row[bj] = row[bj], row[step]
        piv = A[step][step]
        unit = piv // p ** v
        inv = pow(unit % mod, -1, mod)
        for i in range(step + 1, n):
            if A[i][step] % mod:
                fac = (A[i][step] // p ** v) * inv % mod
                for j in range(step, n):
                    A[i][j] = (A[i][j] - fac * A[step][j]) % mod
        for j in range(step + 1, n):
            if A[step][j] % mod:
                fac = (A[step][j] // p ** v) * inv % mod
                for i in range(step, n):
                    A[i][j] = (A[i][j] - fac * A[i][step]) % mod
        prof.append(v)
    return sorted(prof)

def fsolve(M, rhs):
    """solve M z = rhs over Fractions (M integer, nonsingular)."""
    n = len(M)
    A = [[Fraction(M[i][j]) for j in range(n)] + [Fraction(rhs[i])]
         for i in range(n)]
    for k in range(n):
        piv = next(i for i in range(k, n) if A[i][k] != 0)
        A[k], A[piv] = A[piv], A[k]
        for i in range(n):
            if i != k and A[i][k] != 0:
                fac = A[i][k] / A[k][k]
                for j in range(k, n + 1):
                    A[i][j] -= fac * A[k][j]
    return [A[i][n] / A[i][i] for i in range(n)]

def res_checks(tag, pairs, p, cwant, nsnf, gp_rows):
    snf_done = 0
    for idx, (u, w) in enumerate(pairs):
        M = sylvester(u, w)
        det = bareiss_det(M)
        r = res_euclid(u, w)
        assert r.denominator == 1
        r = int(r)
        chk('SYL', det == r or det == -r,
            '%s#%d det %s vs res %s' % (tag, idx, det, r))
        chk('RES', r != 0 and vp(r, p) == cwant,
            '%s#%d v(Res) = %s want %s'
            % (tag, idx, vp(r, p) if r else None, cwant))
        if tag == 'T1' and idx == 0:
            tooth('T-RESC', not (vp(r, p) == cwant + 1),
                  '%s#%d' % (tag, idx))
        if snf_done < nsnf:
            vals = snf_profile(M, p, cwant + 20)
            chk('SNF', sum(vals) == cwant and all(v <= cwant
                for v in vals),
                '%s#%d SNF %s' % (tag, idx, vals))
            snf_done += 1
        if idx < gp_rows:
            GP_JOBS.append((tag + 'R%d' % idx, 'polresultant',
                            (u, w), abs(r)))
    return

GP_JOBS = []

# ---------- L1 avatar -------------------------------------------------
print('== L1 avatar (p=3, c_J=2) ==')
p, c_J = 3, 2

def l1_pair():
    u = [(-3 + 9 * random.randrange(3**10)), 3 * random.randrange(3**10), 1]
    w = [(-6 + 9 * random.randrange(3**10)), 3 * random.randrange(3**10), 1]
    return u, w

res_checks('L1', [l1_pair() for _ in range(100)], 3, 2, 3, 3)

def l1_enum(N):
    q = 3 ** N
    blocks = [(a, b % q) for a in range(0, q, 3)
              for b in range(-3, -3 + 9 * (3 ** (N - 2)), 9)]
    sibs = [(cc, d % q) for cc in range(0, q, 3)
            for d in range(-6, -6 + 9 * (3 ** (N - 2)), 9)]
    img = {}
    for a, b in blocks:
        for cc, d in sibs:
            key = ((a + cc) % q, (b + d + a * cc) % q,
                   (a * d + b * cc) % q, (b * d) % q)
            img[key] = img.get(key, 0) + 1
    return len(blocks), len(sibs), img

for N in (3, 4):
    nb, ns, img = l1_enum(N)
    print('L1 EXPLORATORY N=%d: pairs %d image %d (3^%d slots free)'
          % (N, nb * ns, len(img), 4 * N - 8))

nb, ns, img = l1_enum(5)
q5 = 3 ** 5
chk('IMG', len(img) == 3**12,
    'L1-N5 image %d want %d' % (len(img), 3**12))
tooth('T-NOJ', len(img) != nb * ns, 'L1-N5 %d vs %d' % (len(img), nb*ns))
fibs = set(img.values())
chk('FIB', fibs == {9}, 'L1-N5 fibers %s' % sorted(fibs)[:5])
tooth('T-FIB1', fibs != {27}, 'L1-N5')
cen_count = 3 ** 12
chk('CEN', len(img) == cen_count, 'L1-N5 census count')
tooth('T-CEN', len(img) != 3 ** 13, 'L1-N5 census mutant')
ok = 0
for _ in range(500):
    f3 = 3 * random.randrange(3**4)
    f2 = 9 * random.randrange(3**3)
    f1 = 9 * random.randrange(3**3)
    f0 = (18 + 27 * random.randrange(9)) % q5
    ok += ((f3, f2, f1, f0) in img)
chk('CEN', ok == 500, 'L1-N5 cell members in image: %d/500' % ok)
del img

# ---------- L2 avatar -------------------------------------------------
print('== L2 avatar (p=2, c_J=1) ==')

def l2_pair():
    u = [2 + 4 * random.randrange(2**10), 1]
    w = [2 + 4 * random.randrange(2**10), 2 * random.randrange(2**10), 1]
    return u, w

res_checks('L2', [l2_pair() for _ in range(100)], 2, 1, 3, 3)

for N in (4, 5, 6):
    q = 2 ** N
    blocks = [c0 for c0 in range(2, q, 4)]
    sibs = [(cc, d) for cc in range(0, q, 2) for d in range(2, q, 4)]
    img = {}
    for c0 in blocks:
        for cc, d in sibs:
            key = ((c0 + cc) % q, (d + c0 * cc) % q, (c0 * d) % q)
            img[key] = img.get(key, 0) + 1
    want = 2 ** (3 * N - 6)
    chk('IMG', len(img) == want, 'L2-N%d image %d want %d'
        % (N, len(img), want))
    tooth('T-NOJ', len(img) != len(blocks) * len(sibs), 'L2-N%d' % N)
    fibs = set(img.values())
    chk('FIB', fibs == {2}, 'L2-N%d fibers %s' % (N, sorted(fibs)[:5]))
    tooth('T-FIB1', fibs != {4}, 'L2-N%d' % N)
    chk('CEN', len(img) == want, 'L2-N%d census count' % N)
    tooth('T-CEN', len(img) != 2 ** (3 * N - 5), 'L2-N%d census mutant' % N)
    if N == 6:
        ok = 0
        for _ in range(300):
            f2 = 2 * random.randrange(2**5)
            f1 = 2 + 4 * random.randrange(2**4)
            f0 = 4 + 8 * random.randrange(2**3)
            ok += ((f2, f1, f0) in img)
        chk('CEN', ok == 300, 'L2-N6 cell members in image: %d/300' % ok)

# ---------- T1 tower --------------------------------------------------
print('== T1 tower (FAM-P5 bouquet shape, c_J=20) ==')
PHI1 = [-3, 0, 1]
PHI2 = pstrip(padd(pmul([-3, 0, 1], [-3, 0, 1]), [0, -18]))
PHI2s = pstrip(padd(pmul([-3, 0, 1], [-3, 0, 1]), [0, -9]))
E2, ee, u2, h = 10, 4, 5, 1

def wab(a, b):
    return 2 * a + b * u2

def floors(mu):
    out = {}
    for j in range(mu):
        for a in range(2):
            for b in range(2):
                s = (mu - j) * E2 - wab(a, b)
                fl = -(-s // ee) + (1 if (s % ee == 0 and s >= 0) else 0)
                out[(j, a, b)] = fl
    return out

FS_FL = floors(2)
G_FL = floors(1)
chk('BOX', [FS_FL[(0, a, b)] for a, b in ((0,0),(1,0),(0,1),(1,1))]
    == [6, 5, 4, 4] and
    [FS_FL[(1, a, b)] for a, b in ((0,0),(1,0),(0,1),(1,1))]
    == [3, 3, 2, 1] and
    [G_FL[(0, a, b)] for a, b in ((0,0),(1,0),(0,1),(1,1))]
    == [3, 3, 2, 1], 'floors table %s %s' % (FS_FL, G_FL))

def draw_member(key, mu, fl, depth=12):
    """key-power plus one in-box digit per composed slot, each at
    floor + random extra depth (unit times 3-power)."""
    f = [1]
    for _ in range(mu):
        f = pmul(f, key)
    for (j, a, b), phi in fl.items():
        c = 3 ** (phi + random.randrange(3)) * \
            (1 + 3 * random.randrange(3 ** depth))
        term = pmul([c], [0] * a + [1])
        if b:
            term = pmul(term, PHI1)
        kterm = [1]
        for _ in range(j):
            kterm = pmul(kterm, key)
        f = padd(f, pmul(term, kterm))
    return f

def draw_pair():
    return draw_member(PHI2, 2, FS_FL), draw_member(PHI2s, 1, G_FL)

t1_pairs = [draw_pair() for _ in range(60)]
res_checks('T1', t1_pairs, 3, 20, 3, 6)

# polygon of f = f_S*g: level-1 hull
fS0, g0 = t1_pairs[0]
f0full = pmul(fS0, g0)
A = []
r = list(f0full)
for _ in range(7):
    r, rem = pdivmod(r, PHI1)
    A.append(rem)
assert not pstrip(r)
def dvA(c):
    return min(2 * vp(x, 3) + i for i, x in enumerate(c) if x) \
        if pstrip(list(c)) else None
hts = [dvA(list(c)) for c in A]
onside = all(hts[J] is not None and hts[J] >= 15 - (5 * J + 1) // 2
             for J in range(6)) if all(x is not None or J > 5
             for J, x in enumerate(hts)) else False
chk('POLY', hts[0] == 15 and hts[6] == 0 and
    all(h is None or 2 * h >= 5 * (6 - J)
        for J, h in enumerate(hts)),
    'T1 polygon heights %s' % hts)

# Hensel refactorization (window stability)
fpert = padd(f0full, [0]*7 + [3**45])
u, w = list(fS0), list(g0)
MOD = 3 ** 90
BIG = MOD * 3 ** 20
for it in range(8):
    rvec = padd(list(fpert), [-c for c in pmul(u, w)])
    if not rvec or all(c % MOD == 0 for c in rvec):
        break
    Msyl = sylvester(u, w)   # true Newton: refresh the Jacobian
    rhs = [(rvec[i] if i < len(rvec) else 0) for i in range(12)]
    sol = fsolve(Msyl, rhs)
    solint = []
    okden = True
    for z in sol:
        num, den = z.numerator, z.denominator
        if den % 3 == 0:
            # a 3-adically non-integral correction: iteration invalid
            okden = False
            break
        solint.append((num * pow(den, -1, BIG)) % BIG)
    if not okden:
        break
    # column layout of sylvester(u, w): first (deg w) columns multiply
    # u (that polynomial is beta, the correction ADDED TO w); the next
    # (deg u) columns multiply w (alpha, ADDED TO u)
    beta = solint[:4]
    alpha = solint[4:]
    u = [ (uu + (alpha[i] if i < 8 else 0)) % (MOD * 3**20)
          for i, uu in enumerate(u)]
    w = [ (ww + (beta[i] if i < 4 else 0)) % (MOD * 3**20)
          for i, ww in enumerate(w)]
resid = padd(list(fpert), [-c for c in pmul(u, w)])
chk('HEN', all(c % MOD == 0 for c in resid) if resid else True,
    'T1 Hensel: residual v3 %s'
    % (vpoly(resid, 3) if pstrip(list(resid)) else 'exact'))
diffS = padd(list(u), [-c for c in fS0])
chk('HEN', (not pstrip(list(diffS))) or vpoly(diffS, 3) >= 25,
    'T1 Hensel: f_S drift v3 %s' % (vpoly(diffS, 3)
    if pstrip(list(diffS)) else 'none'))

def inbox(f, key, mu, fl):
    r = [c % (3 ** 60) for c in f]
    coords = {}
    rr = list(r)
    devK = []
    for _ in range(mu):
        rr, rem = pdivmod(rr, key)
        devK.append(rem)
    for j, Cj in enumerate(devK):
        c1, rem = pdivmod(list(Cj), PHI1)
        for b, part in ((0, rem), (1, pstrip(c1))):
            for a in range(2):
                cc = part[a] if a < len(part) else 0
                if cc % 3 ** 60:
                    coords[(j, a, b)] = vp(cc % 3 ** 60, 3)
    return all(v >= fl[k] for k, v in coords.items())

chk('HEN', inbox(u, PHI2, 2, FS_FL) and inbox(w, PHI2s, 1, G_FL),
    'T1 Hensel: boxes hold')

# ---------- gp leg ----------------------------------------------------
def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'

lines = []
meta = []
for tag, kind, (u_, w_), want in GP_JOBS:
    lines.append('print("%s ", abs(polresultant(%s, %s)))'
                 % (tag, poly_str(u_), poly_str(w_)))
    meta.append((tag, want))
lines.append('print("FP2 ", matsize(factorpadic(%s,3,30))[1], " ",'
             ' poldegree(factorpadic(%s,3,30)[1,1]))'
             % (poly_str(PHI2), poly_str(PHI2)))
lines.append('print("FP2s ", matsize(factorpadic(%s,3,30))[1], " ",'
             ' poldegree(factorpadic(%s,3,30)[1,1]))'
             % (poly_str(PHI2s), poly_str(PHI2s)))
lines.append('print("DISC ", poldisc(%s))' % poly_str(f0full))
src = 'default(parisizemax, 2000000000);\n' + '\n'.join(lines) + '\nquit\n'
out = subprocess.run(['gp', '-q', '-f'], input=src, capture_output=True,
                     text=True, timeout=1800)
got = {}
for line in out.stdout.splitlines():
    parts = line.split(' ', 1)
    if len(parts) == 2:
        got[parts[0]] = parts[1].strip()
for tag, want in meta:
    chk('GP', tag in got and int(got[tag]) == want,
        'gp %s: %s want %s' % (tag, got.get(tag), want))
for t in ('FP2', 'FP2s'):
    chk('GP', t in got and got[t].split() == ['1', '4'],
        'gp %s: %s' % (t, got.get(t)))
chk('GP', 'DISC' in got and got['DISC'].lstrip('-').isdigit()
    and int(got['DISC']) != 0, 'gp DISC %s' % got.get('DISC'))

print('== SUMMARY == checks %d violations %d' % (NCHK, NVIO))
print('KILLS %s' % sorted(KILLS.items()))
print('VERDICT %s' % ('GREEN' if NVIO == 0 else 'RED'))
