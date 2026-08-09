#!/usr/bin/env python3
"""HE3 passPE1 FRESH ROUTE leg C: equal-char cell at NON-PRIME base q=9.

O = F_9[[t]], genre E3 = (9; e1=2, f1=1, mu=3; h=1), key Phi' = x^2 - z t,
K = F_9, dv = 2v, S = 2.  MECHANISM-FREE sigma tie: f is CONSTRUCTED as a
product of three explicit Newton-slope-1/2 quadratics

    g_k = x^2 - a_k t x - z t   (a_k in F_9 distinct, z in F_9^x),

each irreducible over F_9((t)) with (e,f) = (2,1) [slope 1/2 forces e = 2],
so sigma(f) = {(2,1),(2,1),(2,1)} BY CONSTRUCTION -- no oracle, no reader
shared with the battery.  The check: the stage read of f at Phi' (polygon
of the Phi'-development in dv units + residual at the single side) is the
3-label type (1,1)^3 with residual roots exactly {a_1,a_2,a_3}, so THEOREM
HE3.A's dictionary (e1 e_s, f1 f_s) = (2,1) per label ties to the known
sigma.  Tests: the 3-label mu=3 type at p=3 (impossible at prime q=3;
|K^x| = 8 >= 3 here), equal characteristic, non-prime q.
"""
import itertools

# F9 = F3(i): elements (a,b) ~ a+bi, i^2 = -1
def m9(x, y):
    a, b = x; c, d = y
    return ((a*c - b*d) % 3, (a*d + b*c) % 3)
def a9(x, y): return ((x[0]+y[0]) % 3, (x[1]+y[1]) % 3)
def n9(x): return ((-x[0]) % 3, (-x[1]) % 3)
Z9, U9 = (0, 0), (1, 0)
F9 = [(a, b) for a in range(3) for b in range(3)]
F9X = [c for c in F9 if c != Z9]
def inv9(x):
    for y in F9X:
        if m9(x, y) == U9: return y

# F9[t][x]: poly in x with coeffs = dict{power_of_t: F9elt}
def tadd(p, q):
    out = dict(p)
    for k, v in q.items(): out[k] = a9(out.get(k, Z9), v)
    return {k: v for k, v in out.items() if v != Z9}
def tmul(p, q):
    out = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            out[k1+k2] = a9(out.get(k1+k2, Z9), m9(v1, v2))
    return {k: v for k, v in out.items() if v != Z9}
def xadd(f, g):
    n = max(len(f), len(g)); out = []
    for k in range(n):
        a = f[k] if k < len(f) else {}
        b = g[k] if k < len(g) else {}
        out.append(tadd(a, b))
    return out
def xmul(f, g):
    out = [{} for _ in range(len(f)+len(g)-1)]
    for i, a in enumerate(f):
        for j, b in enumerate(g): out[i+j] = tadd(out[i+j], tmul(a, b))
    return out
def xdivmod(f, key):
    # key monic in x (last coeff = {0: U9}); returns (quo, rem)
    f = [dict(c) for c in f]
    quo_rev = []
    while len(f) >= len(key):
        c = f[-1]
        shift = len(f) - len(key)
        for j, kc in enumerate(key):
            sub = {k: n9(v) for k, v in tmul(kc, c).items()}
            f[shift+j] = tadd(f[shift+j], sub)
        assert f[-1] == {}, f[-1]
        f.pop()
        quo_rev.append(c)
    return quo_rev[::-1], f

def vt(p):
    return min(p.keys()) if p else 10**9

def run(z, aa):
    tz = {1: z}                      # z*t
    key = [ {0: n9(Z9)} , {}, {0: U9} ]  # placeholder
    key = [ {1: n9(z)}, {}, {0: U9} ]    # x^2 - z t
    gs = []
    for a in aa:
        gs.append([{1: n9(z)}, {1: n9(a)}, {0: U9}])   # x^2 - a t x - z t
    f = gs[0]
    for g in gs[1:]: f = xmul(f, g)
    # develop f = sum A_j key^j
    A, rem = [], f
    for j in range(3):
        quo, r = xdivmod(rem, key)
        A.append(r); rem = quo
    # rem should be [ {0:(1,0)} ] (monic)
    assert len(rem) == 1 and rem[0] == {0: U9}, rem
    # dv values: dv(A) = min(2*vt(a0), 2*vt(a1) + 1)
    dvs = []
    for Aj in A:
        a0 = Aj[0] if len(Aj) > 0 else {}
        a1 = Aj[1] if len(Aj) > 1 else {}
        dvs.append(min(2*vt(a0), 2*vt(a1)+1))
    # expect single side slope 3 length 3: dv = 9,6,3 -> check hull
    node_ok = all(dvs[j] >= (3-j)*2 + 1 for j in range(3))
    # single side slope 3: endpoint (0,9) exact, interior pins ON or ABOVE
    side_ok = (dvs[0] == 9 and dvs[1] >= 6 and dvs[2] >= 3)
    # residual via coherent normalizer n(3) = x t (i=1,a=1); at theta:
    # theta^2 = z t => theta^3 t^3 = z t^4 theta; wrap constant z per step.
    # coefficient of Z^t_pow: res(A_j(theta) / n(3)(theta)^(3-j))
    # A_j(theta) = a0 + a1*theta; attaining slot at height 9-3j.
    # slot i=0 at even dv, i=1 at odd dv.  Heights: j=0: 9 (slot1: a1 t^4);
    # j=1: 6 (slot0: a0 t^3); j=2: 3 (slot1: a1 t^1).
    # n(3)(th)^1 = th t ; ^2 = th^2 t^2 = z t^3 ; ^3 = z t^4 th.
    def coefft(p, k): return p.get(k, Z9)
    r3 = []  # residual coeffs Z^0..Z^3
    # j=0: A0(th)/ (z t^4 th) : a1 t^4 th / (z t^4 th) = a1/z ... a1 = coeff of t^4 in A0[1]
    c = m9(coefft(A[0][1] if len(A[0]) > 1 else {}, 4), inv9(z))
    r3.append(c)
    # j=1: A1(th) / (z t^3): a0 part coeff t^3
    c = m9(coefft(A[1][0], 3), inv9(z))
    r3.append(c)
    # j=2: A2(th) / (th t): a1 part coeff t^1
    c = coefft(A[2][1] if len(A[2]) > 1 else {}, 1)
    r3.append(c)
    r3.append(U9)
    # roots of residual over F9
    roots = []
    for cand in F9:
        acc, zp = Z9, U9
        for cc in r3:
            acc = a9(acc, m9(cc, zp)); zp = m9(zp, cand)
        if acc == Z9: roots.append(cand)
    pred_labels = sorted(roots)
    want = sorted(aa)
    # known sigma by construction: {(2,1)}x3 iff a_k distinct (disc != 0)
    ok = node_ok and side_ok and len(roots) == 3 and pred_labels == want
    return ok, dvs, r3, roots

def main():
    z_choices = [(1, 0), (0, 1), (1, 1)]
    trip_pool = [ [(1,0),(2,0),(0,1)], [(0,1),(0,2),(1,0)], [(1,1),(2,2),(0,1)],
                  [(1,0),(1,1),(1,2)], [(2,1),(1,2),(0,2)] ]
    tot = bad = 0
    for z in z_choices:
        for aa in trip_pool:
            ok, dvs, r3, roots = run(z, aa)
            tot += 1
            if not ok:
                bad += 1
                print('FAIL z=%s aa=%s dvs=%s res=%s roots=%s' % (z, aa, dvs, r3, roots))
            else:
                print('OK   z=%s aa=%s dvs=%s residual-roots=%s == letters; '
                      'pred sigma {(2,1)}x3 == constructed sigma' % (z, aa, dvs, roots))
    print('LEG C: %d jobs, %d failures (each job: 3-label mu=3 stage at q=9, '
          'equal char, sigma known by construction)' % (tot, bad))

main()
