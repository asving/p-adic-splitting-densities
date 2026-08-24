# C.78 probe certification at (s2Tower, f5) over Z_2
# f5 = (x+1)(x^2-2)^2 + (4x+8) = x^5 + x^4 - 4x^3 - 4x^2 + 8x + 12
K = 60  # working precision 2^K
M = 1 << K

def v2(n):
    n = int(n) % M
    if n == 0: return K  # >= K
    v = 0
    while n % 2 == 0: n //= 2; v += 1
    return v

f5 = [12, 8, -4, -4, 1, 1]  # coeff list, low to high

def peval(p, x): 
    r = 0
    for c in reversed(p): r = (r*x + c) % M
    return r

def pmul(p, q):
    r = [0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): r[i+j] = (r[i+j] + a*b) % M
    return r

def psub(p, q):
    n = max(len(p), len(q)); r = []
    for i in range(n):
        a = p[i] if i < len(p) else 0
        b = q[i] if i < len(q) else 0
        r.append((a-b) % M)
    return r

# 1. Hensel root near 3
z = 3
for _ in range(10):
    fz = peval(f5, z)
    fpz = peval([8, -8, -12, 4, 5], z)  # f5'
    inv = pow(fpz, -1, M)
    z = (z - fz*inv) % M
print("root z mod 2^%d:" % K, z % 256, "= 3 mod 8?", z % 8 == 3, " f5(z) v2 >=", v2(peval(f5,z)))

# 2. cofactor g4 = f5 / (x - z) via synthetic division
g4 = [0]*5
g4[4] = f5[5]
for i in range(3, -1, -1):
    g4[i] = (f5[i+1] + z*g4[i+1]) % M
rem = (f5[0] + z*g4[0]) % M
print("g4 coeffs v2:", [v2(c) for c in g4[:4]], "monic:", g4[4]==1, "rem v2 >=", v2(rem))

# 3. w: composedKey Phi2 = (x^2-2)^2 - 4wx, w = resLift(1) -- any odd w. digits of f5 at Phi2:
# digit1 = x+1, digit0 = 4w x^2 + (4w+4) x + 8. Check pins for several odd w:
for w in [1, 3, 5, -1 % M]:
    d0 = [8, (4*w+4)%M, 4*w%M]
    # phi'-digits of d0: dev0 = (4w+4)x + (8w+8), dev1 = 4w
    dev0 = [(8+8*w)%M, (4*w+4)%M]
    dev1 = [(4*w)%M]
    def stage_h(p):  # min(2 v(c0), 2 v(c1)+1) for deg<=1 digit
        vals = []
        for a,c in enumerate(p):
            if c % M != 0: vals.append(2*v2(c) + a)
        return min(vals) if vals else 10**9
    h0, h1 = stage_h(dev0), stage_h(dev1)
    pin0 = min(2*h0 + 0, 2*h1 + 5)
    print("w=%s: stageH(dev0)=%s stageH(dev1)=%s pin0=%s" % (w if w<10 else -1, h0, h1, pin0))
# pin1: digit x+1 -> stage height 0 -> pin = 0

# 4. quadratic-split search: g4 = (x^2+ax+b)(x^2+cx+d) mod 2^k, BFS lifting
sols = [(0,0,0,0)]
k = 1
while k <= 40 and sols:
    k += 1
    m = 1 << k
    new = []
    for (a,b,c,d) in sols:
        for da in range(2):
            for db in range(2):
                for dc in range(2):
                    for dd in range(2):
                        A = a + da*(1<<(k-1)); B = b + db*(1<<(k-1))
                        C = c + dc*(1<<(k-1)); D = d + dd*(1<<(k-1))
                        p = pmul([B,A,1],[D,C,1])
                        if all((p[i]-g4[i]) % m == 0 for i in range(5)):
                            new.append((A,B,C,D))
    # dedupe by symmetry (swap factors)
    new = list(set(tuple(sorted([(a,b),(c,d)])) for (a,b,c,d) in new))
    new = [(x[0][0],x[0][1],x[1][0],x[1][1]) for x in new]
    sols = new
    if k <= 12 or not sols: print("k=%d: %d candidate quadratic splits" % (k, len(sols)))
print("quadratic split survives to 2^%d:" % k, bool(sols))

# 5. v2 of Res(f5, Phi2) with w=1: Phi2 = x^4 -4x^2 + 4 - 4x. Res = prod Phi2(roots of f5)
# compute via Res(f5, Phi2) = prod over roots — use resultant via Euclidean-free: Res = det Sylvester mod M
from itertools import product
def sylvester_det(p, q):
    n, mdeg = len(p)-1, len(q)-1
    N = n + mdeg
    rows = []
    for i in range(mdeg):
        rows.append([0]*i + list(reversed(p)) + [0]*(mdeg-1-i))
    for i in range(n):
        rows.append([0]*i + list(reversed(q)) + [0]*(n-1-i))
    # integer det via fraction-free Bareiss on Python ints (exact, then v2)
    import copy
    Amat = [ [int(x) for x in row] for row in rows]
    # exact integer det (small size 9x9): use sympy-free Bareiss
    nn = len(Amat); det = 1; sign = 1
    prev = 1
    for kk in range(nn-1):
        if Amat[kk][kk] == 0:
            for r in range(kk+1, nn):
                if Amat[r][kk] != 0:
                    Amat[kk], Amat[r] = Amat[r], Amat[kk]; sign = -sign; break
            else: return 0
        for i in range(kk+1, nn):
            for j in range(kk+1, nn):
                Amat[i][j] = (Amat[i][j]*Amat[kk][kk] - Amat[i][kk]*Amat[kk][j])//prev
        prev = Amat[kk][kk]
    return sign * Amat[nn-1][nn-1]

w = 1
Phi2 = [4, (-4*w), -4, 0, 1]
R = sylvester_det([int(c if c < M//2 else c-M) for c in f5], Phi2)
v = 0; RR = abs(R)
while RR % 2 == 0: RR //= 2; v += 1
print("v2(Res(f5, Phi2)) =", v, "(predicted 13 = 13/4 * 4 + 0)")
