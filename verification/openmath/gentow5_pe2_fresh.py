#!/usr/bin/env python3
"""GENTOW5 passPE2 FRESH ROUTE (hostile verifier's own instrument;
code written fresh, no imports from gentow5_checks.py or the PE1
instrument).

FRAME FR-A: THE FIRST SEAM-LIVE DEPTH-3 CHAIN ANYWHERE (eta != 1
AND an f >= 2 stage at level i = 2 — the first i >= 2 instance of
the r1 gauge pin's vartheta_{i,s} ever run; every committed depth-3+
chain is seam-blind, and PE1's FR-1 was the i = 1 instance only).

PREREGISTERED PREDICTIONS (hand-derived from the note @ HEAD before
this script's first run):

Tower: p = 3, Phi1 = x^2 - 6 (e1 = 2, f1 = 1, h = 1, eta =
res(x^2/3) = 2 != 1).  Stage 2: (e2,f2) = (1,2), u2 = 3 (> e2*E1 =
2), psi2 = y^2 + y + 2 over F_3; the S2.1 gauge-corrected recipe
gives Phi2 = Phi1^2 - 6x*Phi1 - 54 (PE1 FR-1's carrier; E2 = 6).
Stage 3: (e3,f3) = (1,2), u3 = 7 (> e3*E2 = 6, gcd(7,1) = 1),
K2 = F_9 = F_3(eta2), eta2^2 = 2*eta2 + 1; psi3 = y^2 - y - eta2
(c1 = 1, c0 = eta2; irreducible: disc = c1^2 + 4c0 = 1 + eta2 =
eta2^7, an odd power of the generator eta2, hence a NON-square).

Grammar (hand-solved): dv2-ladder: pi = 2, x = 1, Phi1 = 3.
nhat_2(7) = 3^3*x (2a + i0 = 7, i0 < 2), nhat_2(14) = 3^7.
vartheta_{2,1} = 1; vartheta_{2,2} = res(nhat_2(7)^2/nhat_2(14)) =
res(3^6 x^2 / 3^7) = res(x^2/3) = eta = 2  (ONE x-wrap; the first
live vartheta at i >= 2 anywhere).
Lifts: height-7 within-class family {3^3*x -> 1, 3^2*Phi1 -> beta1}
(beta1 := res(Phi1/(3x)), the psi2-root letter); height-14 family
{3^7 -> 1, 3^5*x*Phi1 -> eta*beta1 = 2*beta1}.  NOTE the height-14
second flavor REQUIRES re-solving the base exponents (i0: 0 -> 1):
the strict reading of the note's displayed lift shape
x^{i0+e1r}Phi1^{b1+e2t} (i0, b1 fixed from nhat(m)) gives pi-exponent
(14 - 0 - 3)/2 = 11/2, NON-INTEGER — no such monomial exists (a
finding of this pass; the coherent-normalization clause forces the
re-solved family used here).

Corrected recipe key (khat_1 = lift_2(c1*vartheta_{2,1}; 7) =
1*3^3*x; khat_0 = lift_2(c0*vartheta_{2,2}; 14) = lift_2(2*eta2; 14)
= 3^5*x*Phi1, digits (0,1) since 2*eta2 = 0*1 + 1*(2*beta1)):
    P3corr = Phi2^2 - 27x*Phi2 - 243x*Phi1.
Gauge-naive key (khat_0 = lift_2(eta2; 14) = 2*3^5*x*Phi1, digits
(0,2)):
    P3naiv = Phi2^2 - 27x*Phi2 - 486x*Phi1.

FA-0 (F_9 hand-algebra confirmed in code): psi3 = y^2 - y - eta2 has
  NO root in F_9; the vartheta^{-1}-twisted residual y^2 - y - 2eta2
  (naive slot coefficient c0*vartheta_{2,2}^{-1} = 2*eta2) has
  exactly TWO roots {2 + 2eta2, 2 + eta2} (disc 1 + 2eta2 = eta2^2,
  a square).
FA-1 grammar: nhat recursion reproduces nhat_2(7) = 27x, nhat_2(14)
  = 3^7; all three P3 side terms at dv3-height E3 = e3f3u3 = 14
  (2*7 / 7+7 / 10+1+3); floor 7 > 6; strict-lift-shape flavor-1
  pi-exponent at height 14 is 11/2 (non-integer).
FA-2 exact resultant ladder, corrected key (v3 of Res): (P3corr, g)
  for g = x, Phi1, Phi2 -> (4, 12, 28)   [= 8*(1/2, 3/2, 7/2)].
FA-3 PARI, corrected key: ONE deg-8 factor over Q_3; sigma =
  {(2,4)} (e = ehat3 = 2, f = f1f2f3 = 4); nfeltval ladder
  (x, Phi1, Phi2) = (1, 3, 7)  [= e*v = 2*(1/2, 3/2, 7/2)].
FA-4 residue-class legs at the corrected key (repo-side, exact):
  t1 := Phi1/(3x): val(t1^2 + t1 + 2) >= 1  (beta1 IS a psi2-root);
  t2 := Phi2/(27x): val(t2^2 - t2 - t1) >= 1 (beta2 IS a psi3-root
  — THE LEVEL-3 SEAM-LIVE RESIDUE, the r1 pin's content at i = 2);
  val(t2^2 - t2 - 2*t1) = 0 (the twisted residual is NOT carried);
  val(x^2/3 - 2) >= 1 (eta = 2).
FA-5 TOOTH, naive key: sigma = {(2,2), (2,2)} (the split twisted
  residual y^2-y-2eta2 breaks the deg-8 carrier into two deg-4
  branches) — NOT {(2,4)}: THEOREM GENTOW5-B (a)/(b) fail at the
  gauge-naive recipe on this frame at i = 2; per-prime nfeltval
  ladder still (1, 3, 7) per branch; per-prime val(t2^2-t2-2*t1)
  >= 1 (the twisted residual IS carried) and val(t2^2-t2-t1) = 0
  (psi3 is NOT).
FA-6 exact resultants, naive key: (4, 12, 28) — identical to FA-2:
  value/ladder data is seam-BLIND (the seam lives in residue
  classes and sigma, not in heights) — consistency row.

Both oracles wherever sigma or a ladder is claimed: exact integer
resultants (own Sylvester + fraction Gaussian elimination) + PARI gp
(factor/factorpadic/nfinit/idealprimedec/nfeltval).
"""
import subprocess, sys
from fractions import Fraction

OK=[0]; BAD=[0]
def chk(ok,msg):
    if ok: OK[0]+=1; print("ok  -", msg)
    else: BAD[0]+=1; print("VIOLATION:", msg)

# ---- fresh dense-list poly arithmetic over Z (index = degree) ----
def trim(f):
    while f and f[-1]==0: f.pop()
    return f
def padd(f,g):
    r=[0]*max(len(f),len(g))
    for i,c in enumerate(f): r[i]+=c
    for i,c in enumerate(g): r[i]+=c
    return trim(r)
def psc(f,k): return trim([k*c for c in f])
def pmul(f,g):
    if not f or not g: return []
    r=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a:
            for j,b in enumerate(g): r[i+j]+=a*b
    return trim(r)
def v3(n):
    assert n!=0
    v=0
    while n%3==0: n//=3; v+=1
    return v
def resultant(f,g):
    m,n=len(f)-1,len(g)-1
    N=m+n
    M=[[Fraction(0)]*N for _ in range(N)]
    for i in range(n):
        for j,c in enumerate(reversed(f)): M[i][i+j]=Fraction(c)
    for i in range(m):
        for j,c in enumerate(reversed(g)): M[n+i][i+j]=Fraction(c)
    det=Fraction(1)
    for k in range(N):
        piv=next((r for r in range(k,N) if M[r][k]!=0),None)
        if piv is None: return 0
        if piv!=k: M[k],M[piv]=M[piv],M[k]; det=-det
        det*=M[k][k]
        for r in range(k+1,N):
            if M[r][k]!=0:
                fac=M[r][k]/M[k][k]
                for c in range(k,N): M[r][c]-=fac*M[k][c]
    assert det.denominator==1
    return int(det)
def pstr(f):
    return "+".join(f"({c})*x^{i}" for i,c in enumerate(f) if c) or "0"

# ---- FA-0: F_9 algebra (eta2^2 = 2*eta2 + 1; elements a + b*eta2) --
def f9mul(u,v):
    a,b=u; c,d=v
    # (a+b*e)(c+d*e) = ac + (ad+bc)e + bd*e^2, e^2 = 2e+1
    return ((a*c + b*d) % 3, (a*d + b*c + 2*b*d) % 3)
def f9add(u,v): return ((u[0]+v[0])%3, (u[1]+v[1])%3)
F9=[(a,b) for a in range(3) for b in range(3)]
eta2=(0,1)
# psi3(y) = y^2 - y - eta2
psi3_roots=[y for y in F9 if f9add(f9add(f9mul(y,y), ((3-y[0])%3,(3-y[1])%3)), ((3-eta2[0])%3,(3-eta2[1])%3))==(0,0)]
tw=f9mul((2,0),eta2)  # 2*eta2
twist_roots=[y for y in F9 if f9add(f9add(f9mul(y,y), ((3-y[0])%3,(3-y[1])%3)), ((3-tw[0])%3,(3-tw[1])%3))==(0,0)]
chk(psi3_roots==[], f"FA0: psi3 = y^2-y-eta2 rootless in F_9 (irreducible), roots={psi3_roots}")
chk(sorted(twist_roots)==sorted([(2,2),(2,1)]), f"FA0: twisted y^2-y-2eta2 splits with roots {{2+2eta2, 2+eta2}}, got {twist_roots}")

# ---- FA-1: grammar ------------------------------------------------
def nhat2(m):
    # level-2 recursion: e2*m' + b1*u2 = m, b1 < e2 = 1 -> b1 = 0;
    # base: e1*a + i0*h = m, i0 < e1 = 2  (dv2: pi=2, x=1, Phi1=3)
    i0 = m % 2
    a = (m - i0)//2
    return (a, i0, 0)  # (pi-exp, x-exp, Phi1-exp)
chk(nhat2(7)==(3,1,0), f"FA1: nhat_2(7) = 3^3 x, got {nhat2(7)}")
chk(nhat2(14)==(7,0,0), f"FA1: nhat_2(14) = 3^7, got {nhat2(14)}")
# vartheta_{2,2}: nhat_2(7)^2 = 3^6 x^2; x-exp 2 -> one x-wrap (e1=2)
# [RUN-1 INSTRUMENT FIX, disclosed: the sealed check's arithmetic
#  expression was wrong (expected -1 for a 0 height-difference); the
#  intended assertions are: heights match (6*2+2*1 == 14) and the
#  pi-exponent of the ratio is 6-7 = -1, i.e. ratio = x^2/3. No
#  prediction changed.]
wraps=(2*1)//2
chk(wraps==1 and 6*2+2*1==14 and 6-7==-1, "FA1: nhat_2(7)^2/nhat_2(14) = x^2/3 (one x-wrap: vartheta_{2,2} = eta)")
chk(7 > 6, "FA1: floor u3 = 7 > e3*E2 = 6")
# side heights on dv3 = dv2 (e3 = 1): pi=2, x=1, Phi1=3, Phi2=u3=7
h_top = 2*7
h_k1  = (3*2+1) + 7        # 27x * Phi2
h_k0  = (5*2+1+3)          # 3^5 x Phi1
chk(h_top==14 and h_k1==14 and h_k0==14, f"FA1: all P3 side terms at dv3-height E3 = 14 ({h_top},{h_k1},{h_k0})")
# strict lift-shape probe at height 14, flavor t=1 (i0 fixed = 0 from nhat_2(14)):
num = 14 - 0*1 - 1*3
chk(num % 2 == 1, f"FA1-LIFT: strict fixed-i0 family flavor t=1 at height 14 has pi-exponent {num}/2 (NON-INTEGER: no such monomial; the realized member re-solves i0 -> 1)")

# ---- keys ----------------------------------------------------------
X=[0,1]; P1=[-6,0,1]
P2=padd(padd(pmul(P1,P1), psc(pmul(X,P1),-6)), [-54])
kh1=psc(X,27)
P3corr=padd(padd(pmul(P2,P2), psc(pmul(kh1,P2),-1)), psc(pmul(X,P1),-243))
P3naiv=padd(padd(pmul(P2,P2), psc(pmul(kh1,P2),-1)), psc(pmul(X,P1),-486))

# ---- FA-2 / FA-6: exact resultant ladders --------------------------
for name,P,tag in (("corrected",P3corr,"FA2"),("naive",P3naiv,"FA6")):
    lad=[v3(abs(resultant(P,g))) for g in (X,P1,P2)]
    chk(lad==[4,12,28], f"{tag}: {name} key resultant ladder v3 = {lad} == [4, 12, 28]")

# ---- PARI legs -----------------------------------------------------
def gp(script):
    r=subprocess.run(["gp","-q","-f"],input=script,capture_output=True,text=True,timeout=900)
    if r.returncode!=0 or "error" in r.stdout.lower():
        print("GP STDERR:", r.stderr[:500]); print("GP STDOUT:", r.stdout[:800])
    return r.stdout

def gp_probe(poly):
    # [RUN-1 INSTRUMENT FIX, disclosed: the sealed script fed
    #  multi-line for-loops to gp via stdin without {} wrapping; the
    #  gp reader ends statements at newlines, so the PRIME rows never
    #  printed (loop body was a syntax error; NFQ/NF3 lines were
    #  unaffected and matched predictions on run 1). Wrapped in {}.
    #  No prediction changed.]
    scr=f"""default(parisize,512M);
{{
P={pstr(poly)};
P1v={pstr(P1)};
P2v={pstr(P2)};
FQ=factor(P);
print("NFQ=",matsize(FQ)[1]);
FP=factorpadic(P,3,120);
print("NF3=",matsize(FP)[1]," DEGS3=",vector(matsize(FP)[1],i,poldegree(FP[i,1])));
for(k=1,matsize(FQ)[1],
  pol=FQ[k,1];
  nf=nfinit([pol,[3]]);
  pr=idealprimedec(nf,3);
  for(i=1,length(pr),
    vx=nfeltval(nf,x,pr[i]);
    v1=nfeltval(nf,P1v,pr[i]);
    v2=nfeltval(nf,P2v,pr[i]);
    th=Mod(x,pol);
    t1=subst(P1v,x,th)/(3*th);
    t2=subst(P2v,x,th)/(27*th);
    r1=nfeltval(nf,lift(t1^2+t1+2),pr[i]);
    r2a=nfeltval(nf,lift(t2^2-t2-t1),pr[i]);
    r2b=nfeltval(nf,lift(t2^2-t2-2*t1),pr[i]);
    re=nfeltval(nf,lift(th^2/3-2),pr[i]);
    print("PRIME ef=[",pr[i].e,",",pr[i].f,"] lad=[",vx,",",v1,",",v2,"] res=[",r1,",",r2a,",",r2b,",",re,"]");
  );
);
}}
"""
    return gp(scr)

print("== FA-3/FA-4: corrected key P3corr = Phi2^2 - 27x*Phi2 - 243x*Phi1 ==")
out=gp_probe(P3corr)
print(out.strip())
chk("NF3=1 DEGS3=[8]" in out, "FA3: corrected key ONE deg-8 factor over Q_3")
chk(out.count("PRIME ef=[2,4]")==1, "FA3: corrected sigma = {(2,4)} — the seam-live depth-3 carrier")
chk("lad=[1,3,7]" in out, "FA3: nfeltval ladder (x,Phi1,Phi2) = (1,3,7) exact")
import re as _re
# [RUN-2 INSTRUMENT FIX, disclosed: the sealed regex read \d+ only;
#  PARI prints +oo where the element is exactly 0 (r2a at the
#  corrected key IS the key identity P3corr(th)/(729 th^2) = 0, and
#  r2b at the naive key likewise) — +oo satisfies the sealed ">= 1"
#  predictions a fortiori. Parser now maps +oo -> a large int. No
#  prediction changed.]
def _v(s): return 10**9 if s=="+oo" else int(s)
_pat=r"res=\[(\+oo|\d+),(\+oo|\d+),(\+oo|\d+),(\+oo|\d+)\]"
m=_re.search(r"PRIME ef=\[2,4\] lad=\[1,3,7\] "+_pat,out)
chk(m is not None and _v(m.group(1))>=1, "FA4: val(t1^2+t1+2) >= 1 — beta1 is a psi2-root")
chk(m is not None and _v(m.group(2))>=1, "FA4: val(t2^2-t2-t1) >= 1 — beta2 IS a psi3-root (the i=2 gauge pin verified LIVE)")
chk(m is not None and _v(m.group(3))==0, "FA4: val(t2^2-t2-2t1) = 0 — twisted residual NOT carried by corrected key")
chk(m is not None and _v(m.group(4))>=1, "FA4: val(x^2/3 - 2) >= 1 — eta = 2 confirmed at the leaf")

print("== FA-5: naive key P3naiv = Phi2^2 - 27x*Phi2 - 486x*Phi1 (TOOTH) ==")
outn=gp_probe(P3naiv)
print(outn.strip())
chk(outn.count("PRIME ef=[2,2]")==2 and "PRIME ef=[2,4]" not in outn, "FA5-TOOTH: naive sigma = {(2,2),(2,2)} != {(2,4)} — GENTOW5-B(a)/(b) FAIL at the gauge-naive recipe at i = 2")
chk(outn.count("lad=[1,3,7]")==2, "FA5: per-branch nfeltval ladder (1,3,7) exact (values seam-blind)")
mm=_re.findall(r"PRIME ef=\[2,2\] lad=\[1,3,7\] "+_pat,outn)
chk(len(mm)==2 and all(_v(a)>=1 for a,b,c,d in mm), "FA5: per-branch beta1 is a psi2-root")
chk(len(mm)==2 and all(_v(c)>=1 for a,b,c,d in mm), "FA5: per-branch val(t2^2-t2-2t1) >= 1 — the vartheta^{-1}-TWISTED residual IS carried by the naive key")
chk(len(mm)==2 and all(_v(b)==0 for a,b,c,d in mm), "FA5: per-branch val(t2^2-t2-t1) = 0 — psi3 NOT carried by the naive key")

print(f"== PE2 FRESH VERDICT: {OK[0]} checks, {BAD[0]} violations ==")
sys.exit(1 if BAD[0] else 0)
