#!/usr/bin/env python3
"""HE3 passPE1 FRESH ROUTE, legs A+B: the f1=2 genre (3; 1,2,3; h=1).

Genre: O = Z_3, Phi' = x^2 + 9  (roots +-3i, v=1, eta=+-i, psi = y^2+1
irreducible over F_3), D' = e1*f1 = 2, dv = v, S = e1*h = 1, D'h = 2.
deg f = 6.  K = F_9 = F_3(i).

LEG A (exact counter-instances to HE3's displayed statements):
  A1: kappa = 2 > S test keys Phi'' = Phi' + s*9, s in {1,2}: check
      irreducibility/(T1)/(T2) as HE3-1's parenthetical asserts.
  A2: the displayed node dv(A_j) >= (3-j)S+1 admits an OFF-LOCUS member
      whose face-value stage dictionary disagrees with PARI sigma.
LEG B (on-locus f1=2 mu=3 sweep, PARI oracle): stage read over F_9 by a
  FRESH reader (this file), dictionary (e_s,f_s) -> (e_s, 2 f_s), vs
  PARI sig(f,3).  Includes Frobenius-conjugate residual-root pairs (the
  note's finding-6 geography, vacuous at f1=1).
"""
import subprocess, itertools, sys
from fractions import Fraction

P = 3
# ---------------- F9 = F3(i), elements (a,b) = a + b*i, i^2 = -1
def f9mul(x, y):
    a, b = x; c, d = y
    return ((a*c - b*d) % 3, (a*d + b*c) % 3)
def f9add(x, y): return ((x[0]+y[0]) % 3, (x[1]+y[1]) % 3)
def f9neg(x): return ((-x[0]) % 3, (-x[1]) % 3)
F9 = [(a, b) for a in range(3) for b in range(3)]
F9X = [z for z in F9 if z != (0, 0)]
def f9pow(x, n):
    r = (1, 0)
    for _ in range(n): r = f9mul(r, x)
    return r
def frob(x): return f9pow(x, 3)

def polyroots9(cs):
    """roots in F9 of sum cs[k] Z^k (cs: list of F9 elts, low->high)."""
    out = []
    for z in F9:
        acc, zp = (0, 0), (1, 0)
        for c in cs:
            acc = f9add(acc, f9mul(c, zp)); zp = f9mul(zp, z)
        if acc == (0, 0): out.append(z)
    return out

def factor_type9(cs):
    """degrees of irreducible factors over F9 of a monic poly (deg<=3),
    None if not separable."""
    deg = len(cs) - 1
    roots = polyroots9(cs)
    # separability: check gcd with derivative via repeated-root count
    mult = {}
    for r in roots:
        # count multiplicity by synthetic division
        m, q = 0, cs[:]
        while True:
            # divide q by (Z - r)
            rem, out = (0, 0), [None]*(len(q)-1)
            for k in range(len(q)-1, -1, -1):
                if k == len(q)-1: out[k-1] = q[k]; rem = q[k]
                elif k > 0: out[k-1] = f9add(q[k], f9mul(rem, r)); rem = out[k-1]
                else: rem = f9add(q[0], f9mul(rem, r))
            if rem == (0, 0): m += 1; q = out
            else: break
            if len(q) == 1: break
        mult[r] = m
    if any(m > 1 for m in mult.values()): return None
    nl = deg - sum(mult.values())      # nonlinear part degree
    if nl == 0: return [1]*deg
    if nl == deg and deg == 2: return [2]
    if nl == deg and deg == 3: return [3]
    if nl == 2: return [1]*(deg-2) + [2]
    return None

# ---------------- Z_3 side: exact integer polys (low->high)
def v3(n):
    if n == 0: return 10**9
    v = 0
    while n % 3 == 0: n //= 3; v += 1
    return v
def pmul(f, g):
    out = [0]*(len(f)+len(g)-1)
    for a, ca in enumerate(f):
        for b, cb in enumerate(g): out[a+b] += ca*cb
    return out
def padd(f, g):
    n = max(len(f), len(g)); out = [0]*n
    for k in range(n):
        out[k] = (f[k] if k < len(f) else 0) + (g[k] if k < len(g) else 0)
    return out
KEY = [9, 0, 1]                     # Phi' = x^2 + 9
def build(A):                       # f = Phi'^3 + sum A[j] Phi'^j
    f, pw = [0], [1]
    for j in range(3):
        f = padd(f, pmul(A[j], pw)); pw = pmul(pw, KEY)
    return padd(f, pw)

def lift(c):                        # F9 elt -> integer pair (a + b*x rep)
    return c                        # handled at slot level below

def digit(m, c):
    """A-coordinate with K-residue c=(c0,c1) at dv-height m:
    a = c0*3^m, b = c1*3^(m-1)  (slot i=1 has dv = v(b)+1)."""
    a = c[0] * 3**m
    b = c[1] * 3**(m-1) if m >= 1 else 0
    return [a, b]

def resK(A, m):
    """K-residue of A = a + b x at height m (0 if above)."""
    a = A[0] if len(A) > 0 else 0
    b = A[1] if len(A) > 1 else 0
    c0 = (a // 3**m) % 3 if a and v3(a) >= m and v3(a) == m else ((a // 3**m) % 3 if a and v3(a) == m else 0)
    c0 = (a // 3**m) % 3 if (a and v3(a) == m) else 0
    c1 = (b // 3**(m-1)) % 3 if (b and m >= 1 and v3(b) == m-1) else 0
    return (c0, c1)

def dvA(A):
    a = A[0] if len(A) > 0 else 0
    b = A[1] if len(A) > 1 else 0
    return min(v3(a), (v3(b)+1) if b else 10**9) if (a or b) else 10**9

def hull(pts):
    pts = sorted(pts)
    h = [pts[0]]
    for p in pts[1:]:
        while len(h) >= 2 and (Fraction(h[-1][1]-h[-2][1], h[-1][0]-h[-2][0])
                               >= Fraction(p[1]-h[-1][1], p[0]-h[-1][0])):
            h.pop()
        h.append(p)
    return h

def stage_read(A):
    """depth-0 read: [(lam, [factor degrees])] or None if undecided."""
    dvs = [dvA(A[j]) for j in range(3)] + [0]
    pts = [(j, dvs[j]) for j in range(4) if dvs[j] < 10**8]
    H = hull(pts)
    out = []
    for k in range(len(H)-1):
        (j1, m1), (j2, m2) = H[k], H[k+1]
        lam = Fraction(m1-m2, j2-j1)
        ell, u = lam.denominator, lam.numerator
        d = (j2-j1)//ell
        cs = []
        for t in range(d+1):
            j = j1 + t*ell; hgt = m1 - t*u
            cs.append(resK(A[j], hgt) if j < 3 else ((1, 0) if hgt == 0 else (0, 0)))
        ft = factor_type9(cs)
        if ft is None: return None
        out.append((lam, ell, ft))
    return out

def pred_sigma(read):
    sig = []
    for lam, ell, ft in read:
        for dr in ft: sig.append((ell, 2*dr))
    return tuple(sorted(sig))

GP_FUN = r"""
ef(g, p) = { if (poldegree(g)==1, return([1,1]));
  my(nf = nfinit([g,[p]]), dec = idealprimedec(nf, p)); [dec[1].e, dec[1].f] }
sig(f, p) = { my(d = poldisc(f), F); if (d==0, return([[-1,-1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i,1]), p))) }
"""
def gp(lines):
    r = subprocess.run(['gp', '-q'], input=GP_FUN + '\n' + '\n'.join(lines) + '\n',
                       capture_output=True, text=True, timeout=600)
    return r.stdout

def pstr(f):
    return '+'.join('(%d)*x^%d' % (c, k) for k, c in enumerate(f) if c) or '0'

def parse_sig(txt):
    nums = [int(x) for x in txt.replace('[', ' ').replace(']', ' ')
            .replace(',', ' ').split()]
    return tuple(sorted(zip(nums[0::2], nums[1::2])))

def onlocus(f):
    """ambient side slope1 len6 + residual = (eta^2+1)^3 = eta^6+eta^4+... over F3?
    (y^2+1)^3 mod 3 = y^6 + 3y^4 + 3y^2 + 1 = y^6 + 1."""
    if any(v3(f[k]) < 6-k for k in range(6)): return False
    res = [0]*7
    for k in range(7):
        if k == 6: res[k] = 1
        elif v3(f[k]) == 6-k: res[k] = (f[k] // 3**(6-k)) % 3
    return res == [1, 0, 0, 0, 0, 0, 1]

def main():
    print('== LEG A1: test keys at kappa=2 (> S=1) at genre (3;1,2,3;1) ==')
    out = gp(['print(sig(x^2+9,3)); print(sig(x^2+18,3)); print(sig(x^2+27,3))',
              'print(factorpadic(x^2+18,3,20))'])
    print(out)
    print('== LEG A2: displayed-node OFF-LOCUS member ==')
    f_off = build([[729], [81], [9]])
    print('f_off =', f_off, 'node dv(A_j) =', [dvA([729]), dvA([81]), dvA([9])],
          '(displayed floors 4,3,2) on-locus:', onlocus(f_off))
    rd = stage_read([[729], [81], [9]])
    print('face-value stage read:', rd, '-> face-value sigma:',
          pred_sigma(rd) if rd else None)
    print(gp(['print(sig(%s,3))' % pstr(f_off)]))

    print('== LEG B: ON-LOCUS f1=2 mu=3 sweep (fresh reader vs PARI) ==')
    one, two, ii, mii = (1, 0), (2, 0), (0, 1), (0, 2)
    ip1, zeta = (1, 1), (1, 1)
    cubs = {
      'rat+conjpair {1,i,-i}': [f9neg(f9mul(f9mul(one, ii), mii))],  # build below
    }
    def cubic_from_roots(rs):
        cs = [(1, 0)];
        for r in rs:
            cs = [f9add((f9mul(cs[k-1], (1,0)) if k>0 else (0,0)),
                        f9neg(f9mul(cs[k], r))) if k < len(cs) else None for k in range(len(cs)+1)]
            cs = [c for c in cs]
            # rebuild properly
        # simpler: multiply (Z - r) iteratively
        cs = [(1, 0)]
        for r in rs:
            new = [(0, 0)]*(len(cs)+1)
            for k, c in enumerate(cs):
                new[k+1] = f9add(new[k+1], c)
                new[k] = f9add(new[k], f9neg(f9mul(c, r)))
            cs = new
        return cs[::-1] if False else cs  # cs low->high? built low->high below
    def mkcubic(rs):
        cs = [(1, 0)]
        for r in rs:
            new = [(0, 0)]*(len(cs)+1)
            for k, c in enumerate(cs):
                new[k+1] = f9add(new[k+1], c)       # Z * c Z^k
                new[k] = f9add(new[k], f9neg(f9mul(c, r)))
            cs = new
        return cs   # low->high, monic deg len-1
    jobs = []
    # config 1..3: single side lam=3 len3, residual cubic with given roots
    for name, rs in [('T:{1,i,-i}', [one, ii, mii]), ('T:{1,2,i}', [one, two, ii]),
                     ('T:{i,1+i,2+i}', [ii, (1, 1), (2, 1)])]:
        cs = mkcubic(rs)  # cs[t] = coeff of Z^t; residual coeff of A_j at h=9-3j is cs[j]
        A = [digit(9, cs[0]), digit(6, cs[1]), digit(3, cs[2])]
        jobs.append((name, A))
        # variant with junk higher digits
        A2v = [padd(digit(9, cs[0]), [3**11]), padd(digit(6, cs[1]), [0, 3**7]),
               padd(digit(3, cs[2]), [3**5])]
        jobs.append((name+'+junk', A2v))
    # config 4: (Z-1)*(Z^2 - (1+i))  irreducible quad (1+i nonsquare)
    q = [f9neg(ip1), (0, 0), one]           # Z^2 - (1+i)
    cs = [(0, 0)]*4
    # (Z-1)*q: multiply
    m = [(0, 0)]*4
    for k, c in enumerate(q):
        m[k+1] = f9add(m[k+1], c); m[k] = f9add(m[k], f9neg(c))
    jobs.append(('T:(Z-1)(Z^2-(1+i))', [digit(9, m[0]), digit(6, m[1]), digit(3, m[2])]))
    # config 5: irreducible cubic over F9 (search)
    found = None
    for c0 in F9X:
        for c1 in F9:
            cc = [c0, c1, (0, 0), one]
            if factor_type9(cc) == [3]: found = cc; break
        if found: break
    jobs.append(('T:irred-cubic', [digit(9, found[0]), digit(6, found[1]),
                                   digit(3, found[2])]))
    # config 6: two sides lam=3 len1 (j:3->2) + lam=4 len2 (j:2->0)
    #   dv(A2)=3 res c; dv(A1)=7 on line; dv(A0)=11; residual quad from A0,A1,A2
    for name, quad in [('2side:{i,-i}', mkcubic([ii, mii])),
                       ('2side:irredq', [f9neg(ip1), (0, 0), one])]:
        A = [digit(11, quad[0]), digit(7, quad[1]), digit(3, f9mul(quad[2], one))]
        jobs.append((name, A))
    # config 7: ell=2 side (3,0)->(1,7) + side (1,7)->(0,11): labels (2,1)&(1,1)
    jobs.append(('ell2+lin', [digit(11, one), digit(7, two), digit(4, (0, 0))]))
    # config 8: ell=3 single side (3,0)->(0,7): label (3,1): sigma {(3,2)}
    jobs.append(('ell3', [digit(7, ii), [0, 0], [0, 0]]))
    jobs.append(('ell3b', [digit(7, one), [3**5], [3**3]]))

    lines, metas = [], []
    for k, (name, A) in enumerate(jobs):
        A = [a if any(a) else [0] for a in A]
        f = build(A)
        rd = stage_read(A)
        ol = onlocus(f)
        pred = pred_sigma(rd) if rd else None
        metas.append((name, pred, ol))
        lines.append('print("R%d ", sig(%s,3))' % (k, pstr(f)))
    raw = gp(lines).strip().split('\n')
    out = {}
    for line in raw:
        if line.startswith('R') and ' ' in line:
            idx, rest = line.split(' ', 1)
            try: out[int(idx[1:])] = rest
            except ValueError: pass
    bad = 0
    for k, (name, pred, ol) in enumerate(metas):
        got = parse_sig(out[k])
        okmark = 'OK ' if pred == got else 'MISMATCH'
        if pred != got: bad += 1
        print('%-22s onloc=%d pred=%s pari=%s %s' % (name, ol, pred, got, okmark))
    print('LEG B: %d jobs, %d mismatches' % (len(metas), bad))

main()
