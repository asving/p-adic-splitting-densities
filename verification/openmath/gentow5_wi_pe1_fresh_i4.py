#!/usr/bin/env python3
"""GENTOW5-W(i) passPE1 FRESH LEG -- an i = 4 LIVE contact (first anywhere).

Fresh frame FR4 (verifier-constructed, NOT in any committed note):
  p = 3, stages (e,f) = (2,1),(2,1),(2,1),(2,1),(1,2), u = (1,5,21,85,171).
  Floor chain: 5>4, 21>20, 85>84, 171>170; gcds (5,2)(21,2)(85,2)(171,1)=1.
  Keys: Phi1 = x^2-6, Phi2 = Phi1^2-18x, Phi3 = Phi2^2-162*Phi1,
        Phi4 = Phi3^2-3^8*Phi2  (stage-4 digit 1 -> z4 = 1),
  Hand nhat solves (level-by-level, done on paper by the verifier):
        nhat_4(171) = 3*x*Phi1*Phi2*Phi3   (2m+85b=171: b=1,m=43; chain)
        nhat_4(342) = 3^17*x*Phi1*Phi2     (b=0,m=171; 2m+21b=171: b=1,m=75;
                                            2m+5b=75: b=1,m=35; a=17,i0=1)
  Lattice (hand): nhat_4(342)/nhat_4(171)^2 = 3^15/(x Phi1 Phi2 Phi3^2)
        = g1^-1 g2^-1 g3^-1 g4^-1, letters z = (2,2,2,1),
        theta_4(0) = (2*2*2*1)^-1 = 2 in F_3^x  -- LETTER-LIVE at i = 4.
  psi_5 = y^2-y-1, c1 = c0 = 1; vartheta_{4,1} = 1, vartheta_{4,2} = 2.
  Phi5 = Phi4^2 - nhat_4(171)*Phi4 - 2*nhat_4(342)   (deg 32).

PREREGISTERED (verifier, before any run):
  FR-1 factorpadic(Phi5,3): ONE deg-32 factor; single prime, (e,f)=(16,2).
  FR-2 nfeltval ladder (x,Phi1,Phi2,Phi3,Phi4) = (8,20,42,85,171), v(pr 3)=16.
  FR-3 exact ladder v3(Res(Phi5,g)) = (16,40,84,170,342) DUAL:
       own subresultant-PRS ints == gp polresultant ints (bit-equal).
  FR-4 letters res(g1)=res(g2)=res(g3)=2, res(g4)=1; T0 = res(M/N^2) = 2.
  FR-5 THE LAW [GENTOW5-W(4)]: Y := res(Phi4/nhat_4(171)) generates F_9;
       w4 := tr(Y) in {1,2}; norm(Y) = 2*w4^2 (= theta_4(0)*w4^2);
       psi_5^{(w4)}(Y) = 0.
  FR-6 TEETH: psi_5^{(w')}(Y) != 0 at w' != w4; norm(Y) != tr(Y)^2
       (theta-free law dead at i = 4).
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
    """pseudo-remainder prem(f,g) with lc(g)^(deg f - deg g + 1) scaling."""
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
    """Resultant by the subresultant PRS algorithm (Cohen, Alg 3.3.7)."""
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

x = [0, 1]
P1 = psub(pmul(x, x), [6])
P2 = psub(pmul(P1, P1), pscal(18, x))
P3 = psub(pmul(P2, P2), pscal(162, P1))
P4 = psub(pmul(P3, P3), pscal(3**8, P2))
N  = pmul(pscal(3, x), pmul(P1, pmul(P2, P3)))       # nhat_4(171)
M  = pmul(pscal(3**17, x), pmul(P1, P2))             # nhat_4(342)
P5 = psub(psub(pmul(P4, P4), pmul(N, P4)), pscal(2, M))

n = 0; bad = []
def chk(c, m):
    global n
    n += 1
    print(('  ok: ' if c else 'FAIL: ') + m)
    if not c: bad.append(m)

chk(len(P5)-1 == 32 and P5[-1] == 1, "Phi5 deg 32 monic")

own = []
for g, nm in ((x,'x'), (P1,'Phi1'), (P2,'Phi2'), (P3,'Phi3'), (P4,'Phi4')):
    r = resultant_prs(P5, g)
    own.append(r)
    print("  own Res(Phi5,%s): v3 = %d" % (nm, v3(r)))
chk([v3(r) for r in own] == [16, 40, 84, 170, 342],
    "FR-3 own-PRS ladder v3 = (16,40,84,170,342)")

GP = r"""
default(parisize, 1024000000);
P1 = x^2-6; P2 = P1^2-18*x; P3 = P2^2-162*P1; P4 = P3^2-3^8*P2;
N = 3*x*P1*P2*P3; M = 3^17*x*P1*P2;
F = P4^2 - N*P4 - 2*M;
print("R-RX ", polresultant(F, x));
print("R-R1 ", polresultant(F, P1));
print("R-R2 ", polresultant(F, P2));
print("R-R3 ", polresultant(F, P3));
print("R-R4 ", polresultant(F, P4));
fp = factorpadic(F, 3, 500);
print("R-FP ", matsize(fp)[1], " ", poldegree(fp[1,1]));
K = nfinit([F, [3]]);
prs = idealprimedec(K, 3);
print("R-NPR ", #prs);
pr = prs[1];
print("R-EF ", pr.e, " ", pr.f);
xF = Mod(x,F); P1F = Mod(P1,F); P2F = Mod(P2,F); P3F = Mod(P3,F); P4F = Mod(P4,F);
print("R-VALS ", nfeltval(K,xF,pr), " ", nfeltval(K,P1F,pr), " ", nfeltval(K,P2F,pr), " ", nfeltval(K,P3F,pr), " ", nfeltval(K,P4F,pr));
g1 = nfmodpr(K, xF^2/3, pr); g2 = nfmodpr(K, P1F^2/(9*xF), pr);
g3 = nfmodpr(K, P2F^2/(81*P1F), pr); g4 = nfmodpr(K, P3F^2/(3^8*P2F), pr);
print("R-G ", g1 == 2, " ", g2 == 2, " ", g3 == 2, " ", g4 == 1);
NF = 3*xF*P1F*P2F*P3F; MF = 3^17*xF*P1F*P2F;
T0 = nfmodpr(K, MF/NF^2, pr);
print("R-T0 ", T0 == 2);
Y = nfmodpr(K, P4F/NF, pr);
print("R-YGEN ", Y^3 != Y);
trY = Y + Y^3; nmY = Y^4;
ws = if(trY == 1, 1, if(trY == 2, 2, -1));
print("R-W4 ", ws);
print("R-LAW1 ", nmY == 2*trY^2);
print("R-LAW2 ", Y^2 - trY*Y - trY^2 == 0);
wo = if(ws == 1, 2, 1);
print("R-TOOTH1 ", Y^2 - wo*Y - wo^2 != 0);
print("R-TOOTH2 ", nmY != trY^2);
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
    gpres = [int(one(t)[0]) for t in ('R-RX','R-R1','R-R2','R-R3','R-R4')]
    chk(gpres == own, "FR-3 DUAL: gp polresultant ints == own PRS ints (bit-equal)")
    chk(one('R-FP') == ['1','32'], "FR-1 factorpadic: ONE deg-32 factor")
    chk(one('R-NPR') == ['1'], "FR-1 single prime over 3")
    chk(one('R-EF') == ['16','2'], "FR-1 (e,f) = (16,2)")
    chk(one('R-VALS') == ['8','20','42','85','171'],
        "FR-2 nfeltval ladder (8,20,42,85,171)")
    chk(one('R-G') == ['1','1','1','1'], "FR-4 letters (2,2,2,1)")
    chk(one('R-T0') == ['1'], "FR-4 T0 = theta_4(0) = 2 (LIVE at i=4)")
    chk(one('R-YGEN') == ['1'], "FR-5 Y generates F_9")
    chk(one('R-W4')[0] in ('1','2'), "FR-5 w4 = tr(Y) in {1,2} (measured: %s)"
        % one('R-W4')[0])
    chk(one('R-LAW1') == ['1'], "FR-5 LAW norm(Y) = 2*w4^2 = theta_4(0)*w4^2")
    chk(one('R-LAW2') == ['1'], "FR-5 LAW psi_5^{(w4)}(Y) = 0")
    chk(one('R-TOOTH1') == ['1'], "FR-6 TOOTH psi_5^{(w')}(Y) != 0")
    chk(one('R-TOOTH2') == ['1'], "FR-6 TOOTH norm != tr^2 (theta-free dead at i=4)")

print("== FRESH SUMMARY: %d checks, %d violations ==" % (n, len(bad)))
for m in bad: print("  VIOLATION: " + m)
sys.exit(1 if bad else 0)
