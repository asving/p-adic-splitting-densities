#!/usr/bin/env python3
"""GENTOW5-W(i) passPE2 FRESH LEG -- ER3: the first e_{i+1} > 1 contact at
i >= 3 (the untested axis: LW3 had (e_4,f_4) = (1,2), FR4 had (e_5,f_5) =
(1,2); no committed or verifier frame has ever had e_{i+1} > 1 at i >= 3).

Fresh frame ER3 (verifier-constructed, NOT in any committed note):
  p = 3, stages (e,f) = (2,1),(2,1),(2,1),(2,2), u = (1,5,21,85).
  Floor chain: 5>4, 21>20, 85 > e_4*E_3 = 2*42 = 84; gcds (5,2)(21,2)(85,2)=1.
  Chain keys (the LW3 level-<=3 chain, letters z = (2,2,2), psi_1..3 = y-2):
        Phi1 = x^2-6, Phi2 = Phi1^2-18x, Phi3 = Phi2^2-162*Phi1.
  Level-3 recipe data at (e_4,f_4) = (2,2), u_4 = 85 (hand, derived twice):
        nhat_3(85)  = 3^8  * Phi2   (2m+21b=85: b=1,m=32; 2m+5b=32: b=0,m=16;
                                     a=8,i0=0)
        nhat_3(170) = 3^20 * Phi1   (b=0,m=85; 2m+5b=85: b=1,m=40; a=20,i0=0)
  Lattice (hand): M/N^2 = 3^20*Phi1/(3^16*Phi2^2) = 3^4*Phi1/Phi2^2
        = gamma_3^{-1} EXACTLY (split (0,0,-1) on (g1,g2,g3)), so
        theta_3(0) = z_3^{-1} = 2 in F_3^x -- LETTER-LIVE, and a DIFFERENT
        lattice geometry from LW3's (-1,-1,-1) split.
  psi_4 = y^2-y-1 (irreducible /F_3), c1 = c0 = 1; vartheta_{3,1} = 1,
        vartheta_{3,2} = res(N^2/M) = z_3 = 2; reciprocity 2*2 = 1 in F_3.
  Coherent key (slots at Phi3-exponents e_4*t = 0, 2; leading Phi3^4):
        Phi4  = Phi3^4 - 3^8*Phi2*Phi3^2 - 2*3^20*Phi1        (deg 32)
  Naive twin (digit c_0 = 1, no vartheta twist at slot 0):
        Phi4n = Phi3^4 - 3^8*Phi2*Phi3^2 -   3^20*Phi1
  Height mutant (k_0 height 19 not 20; hull re-solved by hand: one side of
  slope 81/16 through (0,81/4),(4,0), the j=2 vertex strictly above):
        Phi4h = Phi3^4 - 3^8*Phi2*Phi3^2 - 2*3^19*Phi1
  Hand polygon of Phi4: vertices (4,0),(2,85/8),(0,85/4) COLLINEAR -- one
  side of slope lam_4 = 85/16; e_4 = denominator over Gamma_3 = 2; residual
  length 4/2 = 2 = f_4. B-law residual = y^2 - c1*w*y - c0*w^2 (theta leg
  cancels), irreducible /F_3 at BOTH w = 1 (y^2-y-1) and w = 2 (y^2+y+2),
  so (e,f) = (16,2) is predicted W-BLIND; w's value is measured, never
  predicted. Twin residual = y^2 - w*y - 2w^2 = (y-2w)^2 REPEATED ROOT.

PREREGISTERED (verifier, before any run; teeth marked T):
  ER-1 own nhat recursion solver reproduces the hand monomials:
       nhat_3(85) = 3^8*Phi2, nhat_3(170) = 3^20*Phi1.
  ER-2 lattice split of M/N^2 on (g1,g2,g3) = (0,0,-1); theta_3(0) = 2
       (letter-live); reciprocity vartheta_{3,2}*theta_3(0) = 1 in F_3^x.
  ER-3 exact ladder v3(Res(Phi4,g)) = (16,40,84,170) for g =
       (x,Phi1,Phi2,Phi3), DUAL: own subresultant-PRS ints == gp
       polresultant ints (bit-equal).
  ER-4 (gauge-blindness of heights) v3(Res(Phi4n,Phi3)) = 170 (own PRS).
  ER-5 (T, height tooth) v3(Res(Phi4h,Phi3)) = 162 != 170 (own PRS; the
       hand hull's 32*81/16).
  ER-6 factorpadic(Phi4,3): ONE deg-32 factor; single prime; (e,f) =
       (16,2) -- FIRST e_{i+1} = 2 geometry at i = 3.
  ER-7 nfeltval ladder (x,Phi1,Phi2,Phi3) = (8,20,42,85), e(pr) = 16.
  ER-8 letters res(g1) = res(g2) = res(g3) = 2; T0 = res(M/N^2) = 2 LIVE.
  ER-9 THE LAW [GENTOW5-W(3)] at e_4 = 2: Y := res(Phi3^2/nhat_3(85))
       (the level-4 letter Lam_3 = Phi3^{e_4}/nhat_3(u_4)) generates F_9;
       w3 := tr(Y) in {1,2} (measured); norm(Y) = 2*w3^2 (= theta_3(0)*w3^2
       through the B-law algebra); psi_4^{(w3)}(Y) = Y^2 - w3*Y - w3^2 = 0.
  ER-10 (T) psi_4^{(w')}(Y) != 0 at the other unit w' != w3.
  ER-11 (T) norm(Y) != tr(Y)^2 (the theta-free power law dead at e_4 = 2).
  ER-12 (T, naive twin, disjunctive) Phi4n fails the coherent certificate:
       NOT(one deg-32 factor AND single prime AND (e,f) = (16,2)); the
       observed branch is RECORDED, not predicted.
"""
import subprocess, sys

def pnorm(a):
    while a and a[-1] == 0: a.pop()
    return a

def pmul(a, b):
    out = [0]*(len(a)+len(b)-1) if a and b else []
    for i, c in enumerate(a):
        if c:
            for j, d in enumerate(b):
                if d: out[i+j] += c*d
    return pnorm(out)

def psub(a, b):
    n = max(len(a), len(b))
    return pnorm([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
                  for i in range(n)])

def pscal(c, a): return pnorm([c*x for x in a])

def prem_scaled(f, g):
    f = f[:]; df, dg = len(f)-1, len(g)-1
    lg = g[-1]
    for _ in range(df - dg + 1):
        if len(f)-1 < dg or not f:
            f = pscal(lg, f)
            continue
        lf = f[-1]
        f = psub(pscal(lg, f), pscal(lf, [0]*(len(f)-1-dg) + list(g)))
    return f

def resultant_prs(f, g):
    if not f or not g: return 0
    if len(f)-1 < len(g)-1:
        s = (-1)**((len(f)-1)*(len(g)-1))
        return s*resultant_prs(g, f)
    a, b = f[:], g[:]
    gpow, hpow, s = 1, 1, 1
    while True:
        da, db = len(a)-1, len(b)-1
        delta = da - db
        if da % 2 == 1 and db % 2 == 1: s = -s
        r = prem_scaled(a, b)
        if not r: return 0
        a, b = b, [c // (gpow * hpow**delta) for c in r]
        gpow = a[-1]
        hpow = hpow if delta == 0 else (gpow**delta) // (hpow**(delta-1))
        if len(b) - 1 == 0:
            dA = len(a)-1
            res = hpow if dA == 0 else (b[0]**dA) // (hpow**(dA-1))
            return s*res

def v3(n):
    v = 0
    while n % 3 == 0: n //= 3; v += 1
    return v

# --- own nhat recursion solver (ER-1): e = (2,2,2), u = (1,5,21), h = 1 ---
def nhat3(k):
    """returns exponent tuple (a, i0, b1, b2) with nhat_3(k) =
    3^a x^{i0} Phi1^{b1} Phi2^{b2}."""
    es, us = [2, 2, 2], [1, 5, 21]      # e_1..e_3, u_1..u_3 (u_1 = h)
    bs = []
    for lev in (2, 1):                   # b_2 then b_1
        e, u = es[lev], us[lev]
        b = next(b for b in range(e) if (k - b*u) % e == 0)
        bs.append(b); k = (k - b*u)//e
    i0 = k % 2; a = (k - i0)//2
    return (a, i0, bs[1], bs[0])

x = [0, 1]
P1 = psub(pmul(x, x), [6])
P2 = psub(pmul(P1, P1), pscal(18, x))
P3 = psub(pmul(P2, P2), pscal(162, P1))
P3sq = pmul(P3, P3)
N  = pscal(3**8, P2)                          # nhat_3(85)
M  = pscal(3**20, P1)                         # nhat_3(170)
P4  = psub(psub(pmul(P3sq, P3sq), pmul(N, P3sq)), pscal(2, M))
P4n = psub(psub(pmul(P3sq, P3sq), pmul(N, P3sq)), M)
P4h = psub(psub(pmul(P3sq, P3sq), pmul(N, P3sq)), pscal(2*3**19, P1))

n = 0; bad = []
def chk(c, m):
    global n
    n += 1
    print(('  ok: ' if c else 'FAIL: ') + m)
    if not c: bad.append(m)

chk(len(P4)-1 == 32 and P4[-1] == 1, "Phi4 deg 32 monic")
chk(nhat3(85) == (8, 0, 0, 1), "ER-1 nhat_3(85) = 3^8*Phi2 (own recursion)")
chk(nhat3(170) == (20, 0, 1, 0), "ER-1 nhat_3(170) = 3^20*Phi1 (own recursion)")

# ER-2 lattice: M/N^2 as (A,B,C,D) exps of (3,x,Phi1,Phi2) = (4,0,1,-2);
# g1 = (-1,2,0,0), g2 = (-2,-1,2,0), g3 = (-4,0,-1,2); solve integrally.
target = (4, 0, 1, -2)
gam = [(-1, 2, 0, 0), (-2, -1, 2, 0), (-4, 0, -1, 2)]
split = None
for a in range(-3, 4):
    for b in range(-3, 4):
        for c in range(-3, 4):
            if all(a*gam[0][k] + b*gam[1][k] + c*gam[2][k] == target[k]
                   for k in range(4)):
                split = (a, b, c)
chk(split == (0, 0, -1), "ER-2 lattice split (0,0,-1): M/N^2 = gamma_3^{-1}")
z = (2, 2, 2)
# F_3^x power with negative exponents via inverse (2^-1 = 2 mod 3)
def fpow(base, e):
    inv = {1: 1, 2: 2}
    r = 1
    for _ in range(abs(e)): r = (r * (base if e >= 0 else inv[base])) % 3
    return r
theta0 = (fpow(z[0], split[0]) * fpow(z[1], split[1])
          * fpow(z[2], split[2])) % 3
chk(theta0 == 2, "ER-2 theta_3(0) = 2 in F_3^x (LETTER-LIVE at e_4 = 2)")
vth2 = fpow(theta0, -1)
chk((vth2 * theta0) % 3 == 1, "ER-2 reciprocity vartheta_{3,2}*theta_3(0) = 1")

own = []
for g, nm in ((x, 'x'), (P1, 'Phi1'), (P2, 'Phi2'), (P3, 'Phi3')):
    r = resultant_prs(P4, g)
    own.append(r)
    print("  own Res(Phi4,%s): v3 = %d" % (nm, v3(r)))
chk([v3(r) for r in own] == [16, 40, 84, 170],
    "ER-3 own-PRS ladder v3 = (16,40,84,170)")
chk(v3(resultant_prs(P4n, P3)) == 170,
    "ER-4 naive twin v3(Res(Phi4n,Phi3)) = 170 (heights gauge-blind)")
chk(v3(resultant_prs(P4h, P3)) == 162,
    "ER-5 TOOTH height mutant v3(Res(Phi4h,Phi3)) = 162 != 170")

GP = r"""
default(parisize, 1024000000);
P1 = x^2-6; P2 = P1^2-18*x; P3 = P2^2-162*P1;
N = 3^8*P2; M = 3^20*P1;
F  = P3^4 - N*P3^2 - 2*M;
Fn = P3^4 - N*P3^2 - M;
print("R-RX ", polresultant(F, x));
print("R-R1 ", polresultant(F, P1));
print("R-R2 ", polresultant(F, P2));
print("R-R3 ", polresultant(F, P3));
fp = factorpadic(F, 3, 500);
print("R-FP ", matsize(fp)[1], " ", poldegree(fp[1,1]));
K = nfinit([F, [3]]);
prs = idealprimedec(K, 3);
print("R-NPR ", #prs);
pr = prs[1];
print("R-EF ", pr.e, " ", pr.f);
xF = Mod(x,F); P1F = Mod(P1,F); P2F = Mod(P2,F); P3F = Mod(P3,F);
print("R-VALS ", nfeltval(K,xF,pr), " ", nfeltval(K,P1F,pr), " ", nfeltval(K,P2F,pr), " ", nfeltval(K,P3F,pr));
g1 = nfmodpr(K, xF^2/3, pr); g2 = nfmodpr(K, P1F^2/(9*xF), pr);
g3 = nfmodpr(K, P2F^2/(81*P1F), pr);
print("R-G ", g1 == 2, " ", g2 == 2, " ", g3 == 2);
NF = 3^8*P2F; MF = 3^20*P1F;
T0 = nfmodpr(K, MF/NF^2, pr);
print("R-T0 ", T0 == 2);
Y = nfmodpr(K, P3F^2/NF, pr);
print("R-YGEN ", Y^3 != Y);
trY = Y + Y^3; nmY = Y^4;
ws = if(trY == 1, 1, if(trY == 2, 2, -1));
print("R-W3 ", ws);
print("R-LAW1 ", nmY == 2*trY^2);
print("R-LAW2 ", Y^2 - trY*Y - trY^2 == 0);
wo = if(ws == 1, 2, 1);
print("R-TOOTH1 ", Y^2 - wo*Y - wo^2 != 0);
print("R-TOOTH2 ", nmY != trY^2);
fpn = factorpadic(Fn, 3, 500);
print("N-FP ", matsize(fpn)[1], " ", poldegree(fpn[1,1]));
Kn = nfinit([Fn, [3]]);
prn = idealprimedec(Kn, 3);
prn1 = prn[1];
print("N-EF ", #prn, " ", prn1.e, " ", prn1.f);
print("N-KILL ", (#prn != 1) || (prn1.e != 16) || (prn1.f != 2));
print("N-V3 ", nfeltval(Kn, Mod(P3, Fn), prn1));
print("GPDONE");
"""
r = subprocess.run(['gp', '-q', '-f'], input=GP, capture_output=True,
                   text=True, timeout=3000)
out = r.stdout
lines = {}
for ln in out.splitlines():
    ps = ln.strip().split()
    if ps: lines.setdefault(ps[0], []).append(ps[1:])
def one(t): return lines.get(t, [['?']])[0]
if 'GPDONE' not in out:
    chk(False, "gp leg completed"); print(out); print(r.stderr[-3000:])
else:
    gpres = [int(one(t)[0]) for t in ('R-RX', 'R-R1', 'R-R2', 'R-R3')]
    chk(gpres == own, "ER-3 DUAL: gp polresultant ints == own PRS ints (bit-equal)")
    chk(one('R-FP') == ['1', '32'], "ER-6 factorpadic: ONE deg-32 factor")
    chk(one('R-NPR') == ['1'], "ER-6 single prime over 3")
    chk(one('R-EF') == ['16', '2'], "ER-6 (e,f) = (16,2) [e_4 = 2 live: e(pr) = 16 needs the NEW stage-4 ramification]")
    chk(one('R-VALS') == ['8', '20', '42', '85'],
        "ER-7 nfeltval ladder (8,20,42,85)")
    chk(one('R-G') == ['1', '1', '1'], "ER-8 letters (2,2,2)")
    chk(one('R-T0') == ['1'], "ER-8 T0 = theta_3(0) = 2 (LIVE)")
    chk(one('R-YGEN') == ['1'], "ER-9 Y = res(Phi3^2/nhat_3(85)) generates F_9")
    chk(one('R-W3')[0] in ('1', '2'),
        "ER-9 w3 = tr(Y) in {1,2} (measured: %s)" % one('R-W3')[0])
    chk(one('R-LAW1') == ['1'], "ER-9 LAW norm(Y) = 2*w3^2 = theta_3(0)*w3^2")
    chk(one('R-LAW2') == ['1'], "ER-9 LAW psi_4^{(w3)}(Y) = 0")
    chk(one('R-TOOTH1') == ['1'], "ER-10 TOOTH psi_4^{(w')}(Y) != 0")
    chk(one('R-TOOTH2') == ['1'],
        "ER-11 TOOTH norm != tr^2 (theta-free law dead at e_4 = 2)")
    chk(one('N-KILL') == ['1'],
        "ER-12 TOOTH naive twin VERDICT KILL: NOT(single (16,2))"
        " (measured N-FP: %s; N-EF: %s)"
        % (' '.join(one('N-FP')), ' '.join(one('N-EF'))))
    print("  RECORD naive twin nfeltval(Phi_3) = %s" % ' '.join(one('N-V3')))

print("== ER3 FRESH SUMMARY: %d checks, %d violations ==" % (n, len(bad)))
for m in bad: print("  VIOLATION: " + m)
sys.exit(1 if bad else 0)
