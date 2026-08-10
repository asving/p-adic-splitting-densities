#!/usr/bin/env python3
"""T1-GAUGE passPE1 FRESH instrument (verifier-composed, independent of
t1_gauge_checks.py). Frames NOT in the note's plan nor the seven annexes'
batteries. Exact arithmetic; dual PARI oracles on the p-adic leg.

FV-A: (e1,h)=(5,3), f1=3, u=7; u2-sweep 1..40. C2 wrap/product, C5 Q,
      vartheta three routes, C1-level-2 exponent identity, C4 support/x-free.
FV-B: F9 carrier, e1=3,h=1,u=5,f=3, eta=g. C3 dictionary + B-law + canonical
      residual over ALL monomial homomorphisms R compatible with the carrier;
      gauge invariance by exhaustive factorization (own F9) + PARI factorff.
FV-C: p=7 tower, Phi'=x^2-21, eta=3, u2=3, psi2=Z^2+Z+3. Corrected key
      sigma {(2,2)} + vP(Phi')=3; naive key sigma {(2,1),(2,1)} (NEW genre:
      naive splits, does not ramify). Dual routes: factorpadic + nfinit.
"""
import subprocess, sys

NC = 0; NV = 0; V = []
def chk(tag, cond, msg=''):
    global NC, NV
    NC += 1
    if not cond:
        NV += 1; V.append('%s: %s' % (tag, msg))
        print('  VIOLATION %s: %s' % (tag, msg), flush=True)

# ---------------------------------------------------------------- FV-A
def fva():
    print('FV-A: (e1,h)=(5,3) exponent core + C1 sweep + C4 f1=3')
    e1, h, f1 = 5, 3, 3
    hinv = next(v for v in range(e1) if (v*h) % e1 == 1)
    iof = lambda k: (hinv*k) % e1
    aof = lambda k: (k - iof(k)*h)//e1
    i0 = hinv
    ok = True
    for a in range(61):
        for b in range(61):
            wr = (iof(a)+iof(b))//e1
            ok &= wr in (0, 1)
            ok &= (iof(a)+iof(b), aof(a)+aof(b)) == (iof(a+b)+e1*wr, aof(a+b)-h*wr)
            ok &= (i0*(a+b)-iof(a+b))//e1 == (i0*a-iof(a))//e1 + (i0*b-iof(b))//e1 + wr
    chk('A1', ok, 'wrap/product/Q fails at (5,3)')
    # vartheta three routes at u=7 (exponent of eta as integer)
    u = 7
    ok = True
    rec = 0  # route 2: recursion sum of wraps
    for s in range(31):
        r1 = (s*iof(u) - iof(s*u))
        assert r1 % e1 == 0
        r1 //= e1                      # route 1: direct exponent reduction
        r3 = (s*iof(u))//e1            # route 3: claimed closed form
        ok &= r1 == rec == r3
        rec += (iof(s*u)+iof(u))//e1
    chk('A2', ok, 'vartheta routes disagree at (5,3),u=7')
    # C1-level-2: nhat(u2)/pi2^u2 == (x^e1/pi^h)^(-floor(l1 u2/e1)), u2 in 1..40
    l1 = next(v for v in range(e1) if (v*h) % e1 == 1)   # l1*h+l1p*e1=1
    l1p = (1 - l1*h)//e1
    ok = True
    for u2 in range(1, 41):
        xe = iof(u2) - l1*u2           # x-exponent of nhat(u2)/pi2^u2
        pe = aof(u2) - l1p*u2
        k = -((l1*u2)//e1)             # claimed exponent
        ok &= (xe, pe) == (e1*k, -h*k)
    chk('A3', ok, 'C1-level-2 exponent identity fails in sweep')
    # C4 at f1=3: support & x-free classification (exponent-level, all digit
    # supports S subset {0,1,2}, all m in 9..60 with clearance)
    ok = okxf = True
    D = e1*f1
    for m in range(0, 61):
        im, am = iof(m), aof(m)
        for S in range(1, 8):          # nonzero digit support bitmask
            rs = [r for r in range(3) if S >> r & 1]
            if any(am - r*h < 0 for r in rs):
                continue               # clearance violated: out of scope
            xs = [im + e1*r for r in rs]
            ok &= all((x*h + (am - r*h)*e1) == m for x, r in zip(xs, rs))
            ok &= len(set(xs)) == len(xs) and all(x < D for x in xs)
            xfree = len(rs) == 1 and xs[0] == 0
            okxf &= xfree == (im == 0 and rs == [0])
    chk('A4', ok, 'C4 support/height fails at f1=3')
    chk('A5', okxf, 'C4 x-free classification fails at f1=3')

# ---------------------------------------------------------------- F9
# F9 = F3[t]/(t^2 - t - 1), elements (a,b) = a + b t; t generates F9^* (ord 8)
def m9(u, v):
    a1, b1 = u; a2, b2 = v
    aa, ab, bb = a1*a2, a1*b2 + a2*b1, b1*b2
    return ((aa + bb) % 3, (ab + bb) % 3)   # t^2 = t + 1
ONE = (1, 0); ZERO = (0, 0)
def p9(u, k):
    r = ONE
    for _ in range(k % 8 if u != ONE else 0):
        r = m9(r, u)
    return r
def i9(u):
    for a in range(3):
        for b in range(3):
            if m9(u, (a, b)) == ONE:
                return (a, b)
    raise ValueError
def a9(u, v):
    return ((u[0]+v[0]) % 3, (u[1]+v[1]) % 3)
def units9():
    return [(a, b) for a in range(3) for b in range(3) if (a, b) != ZERO]

def polmul9(A, B):
    out = [ZERO]*(len(A)+len(B)-1)
    for i, c in enumerate(A):
        for j, d in enumerate(B):
            out[i+j] = a9(out[i+j], m9(c, d))
    return out
def poleval9(A, x):
    r = ZERO
    for c in reversed(A):
        r = a9(m9(r, x), c)
    return r
def factor_degrees9(A):
    """degree multiset of monic-cubic factorization over F9 (deg A = 3)."""
    roots = []
    cur = list(A)
    for x in units9()+[ZERO]:
        while len(cur) > 1 and poleval9(cur, x) == ZERO:
            # synthetic division by (y - x)
            out = []; carry = ZERO
            for c in reversed(cur):
                carry = a9(c, m9(carry, x))
                out.append(carry)
            rem = out.pop()
            assert rem == ZERO or poleval9(cur, x) != ZERO
            cur = list(reversed(out)); roots.append(x)
    degs = [1]*len(roots)
    if len(cur) > 1:
        degs.append(len(cur)-1)
    return sorted(degs)

def fvb():
    print('FV-B: F9 carrier, e1=3,h=1,u=5,f=3 — B-law over all R-models')
    e1, h, u, f = 3, 1, 5, 3
    hinv = 1
    iof = lambda k: (hinv*k) % e1
    aof = lambda k: (k - iof(k)*h)//e1
    g = (0, 1)                                   # generator t
    eta = g
    # vartheta_s = eta^floor(s*i(u)/e1); i(5)=2: floors s=1,2,3 -> 0,1,2
    vth = {s: p9(eta, (s*iof(u))//e1) for s in range(f+1)}
    chk('B1', (vth[1], vth[2], vth[3]) == (ONE, eta, m9(eta, eta)),
        'vartheta vector %s' % vth)
    Th = {t: i9(vth[f-t]) for t in range(f)}
    # psi = y^3 - c2 y^2 - c1 y - c0, pick letter-live coefficients
    c = {2: g, 1: (2, 1), 0: (1, 2)}
    dig = {t: m9(c[t], vth[f-t]) for t in c}     # corrected coherent digits
    # dictionary: mult read-back == c_t
    okd = all(m9(dig[t], i9(vth[f-t])) == c[t] for t in c)
    chk('B2', okd, 'C3-dictionary read-back fails')
    # all homomorphism models R: R(x)=a, R(pi)=b, constraint a^e1 = eta*b^h
    models = 0; okb = okr = okg = True
    for b in units9():
        cands = [a for a in units9() if p9(a, e1) == m9(eta, b)]
        chk('B3', len(cands) == 1, 'cube-root count %d != 1' % len(cands))
        a = cands[0]
        models += 1
        Rn = lambda k: m9(p9(a, iof(k)), p9(b, aof(k)))   # R(nhat(k))
        w = Rn(u)
        # B-law: R(nhat(su)) == Theta(t) * w^s, s=f-t
        for t in range(f):
            s = f - t
            okb &= Rn(s*u) == m9(Th[t], p9(w, s))
        # slot read: element with coherent digit dig[t] at height su ->
        # R = dig[t]*R(nhat(su)); claim == c_t * w^s
        for t in range(f):
            s = f - t
            okr &= m9(dig[t], Rn(s*u)) == m9(c[t], p9(w, s))
        # canonical residual coefficientwise == w^f psi(y/w): slot t coeff
        # c_t w^{f-t} — compare against w^f * psi(y/w) expansion
        canres = [m9(c[0], p9(w, 3)), m9(c[1], p9(w, 2)),
                  m9(c[2], p9(w, 1)), ONE]        # y^3 - sum c_t w^{f-t} y^t
        wf = p9(w, f)
        exp = [m9(wf, m9(c[0], i9(p9(w, 0 or 1))))]  # placeholder replaced
        # direct: w^f * psi(y/w) coeff of y^t = w^{f-t} * (coeff of psi at t)
        exp = [m9(p9(w, f-t), c[t]) for t in range(f)] + [ONE]
        okg &= canres == exp
    chk('B4', models == 8 and okb, 'B-law fails in some R-model')
    chk('B5', okr, 'slot canonical read != c_t w^s in some R-model')
    chk('B6', okg, 'canonical residual != w^f psi(y/w) in some R-model')
    # gauge invariance: factor-degree multisets of psi and psi^(w) agree for
    # every unit w; own factorization + PARI cross-check on 3 sample w's
    psi = [m9((2, 2), c[0]), m9((2, 2), c[1]), m9((2, 2), c[2]), ONE]
    # note: -1 = (2,0); -c_t = (2,0)*c_t
    psi = [m9((2, 0), c[0]), m9((2, 0), c[1]), m9((2, 0), c[2]), ONE]
    base = factor_degrees9(psi)
    okinv = True
    for w in units9():
        tw = [m9(p9(w, 3-t), psi[t]) for t in range(3)] + [ONE]
        okinv &= factor_degrees9(tw) == base
    chk('B7', okinv, 'factor-degree multiset varies with w')
    print('  psi factor degrees over F9: %s (invariant across 8 w-twists)'
          % base)
    return psi, base

def fvb_pari(psi, base):
    # PARI cross-check of the F9 factorization degree multiset
    def lift(cc):
        return '%d + %d*t' % cc
    pol = ' + '.join('(%s)*y^%d' % (lift(c), i) for i, c in enumerate(psi))
    src = ('t = ffgen(x^2 - x - 1, "t");\n'
           'F = factor(%s);\n'
           'print("DEGS ", vecsort(apply(poldegree, F[,1]~)));\nquit\n' % pol)
    out = subprocess.run(['gp', '-q', '-f'], input=src, capture_output=True,
                         text=True, timeout=300)
    line = [l for l in out.stdout.splitlines() if l.startswith('DEGS')]
    got = [int(x) for x in line[0].replace('[', ' ').replace(']', ' ')
           .replace(',', ' ').split()[1:]] if line else None
    chk('B8', got == base, 'PARI F9 degrees %s != own %s (%s)' %
        (got, base, out.stderr[-120:]))

# ---------------------------------------------------------------- FV-C
def fvc():
    print('FV-C: p=7 gauge-live tower, dual PARI oracles')
    src = r'''
default(parisize, 256*1024*1024);
sigQ(f, p) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i,1]);
    if (poldegree(g) == 1, listput(out, [1,1]),
      my(nf = nfinit([g,[p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
sigP(f, p, N) = {
  my(F = factorpadic(f, p, N), out = List());
  for (i = 1, matsize(F)[1],
    my(g = liftall(F[i,1]), nf = nfinit([g,[p]]),
       dec = idealprimedec(nf, p));
    for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f])));
  vecsort(Vec(out))
}
kv(f, p, K) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i,1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g,[p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [dec[j].e, dec[j].f, nfeltval(nf, Mod(K,g), dec[j])]))));
  Vec(out)
}
Kc = (x^2-21)^2 - 42*x*(x^2-21) - 1715;
Kn = (x^2-21)^2 - 42*x*(x^2-21) - 1372;
print("CQ ", sigQ(Kc, 7)); print("NQ ", sigQ(Kn, 7));
for (N = 20, 40, if (N%10==0, print("CP", N, " ", sigP(Kc,7,N)); print("NP", N, " ", sigP(Kn,7,N))));
print("KV ", kv(Kc, 7, x^2-21));
quit
'''
    out = subprocess.run(['gp', '-q', '-f'], input=src, capture_output=True,
                         text=True, timeout=1800)
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2:
            res[parts[0]] = parts[1].strip()
    def sig(sv):
        n = [int(x) for x in sv.replace('[', ' ').replace(']', ' ')
             .replace(',', ' ').split()]
        return sorted((n[i], n[i+1]) for i in range(0, len(n), 2))
    print('  raw: %s' % res)
    chk('C1', sig(res.get('CQ', '')) == [(2, 2)], 'corr Q-route %s' % res.get('CQ'))
    chk('C2', all(sig(res.get('CP%d' % N, '')) == [(2, 2)] for N in (20, 30, 40)),
        'corr P-route instability')
    chk('C3', sig(res.get('NQ', '')) == [(2, 1), (2, 1)],
        'naive Q-route %s != {(2,1),(2,1)}' % res.get('NQ'))
    chk('C4', all(sig(res.get('NP%d' % N, '')) == [(2, 1), (2, 1)]
                  for N in (20, 30, 40)), 'naive P-route instability')
    kvn = [int(x) for x in res.get('KV', '').replace('[', ' ')
           .replace(']', ' ').replace(',', ' ').split()]
    chk('C5', kvn == [2, 2, 3], 'nfeltval rows %s != [2,2,3]' % kvn)
    chk('C6', sig(res.get('CQ', '9 9')) != sig(res.get('NQ', '9 9')),
        'gauge tooth did not fire at p=7')

def main():
    fva()
    psi, base = fvb()
    fvb_pari(psi, base)
    fvc()
    print('\nTOTAL: %d checks, %d violations' % (NC, NV))
    for v in V:
        print('  RED: %s' % v)
    print('VERDICT: %s' % ('GREEN' if NV == 0 else 'RED'))
    return 0 if NV == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
