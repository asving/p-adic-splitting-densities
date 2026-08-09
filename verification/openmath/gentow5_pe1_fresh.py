#!/usr/bin/env python3
"""GENTOW5 passPE1 FRESH ROUTE (hostile verifier's own instrument;
code written fresh, no imports from gentow5_checks.py).

PREREGISTERED PREDICTIONS (derived by hand from the note + the GENHN
gauge erratum 59c1966, BEFORE this script's first run):

FR-1 SEAM PROBE at DEF GENTOW5-1's key recipe (frame X of the GENHN
  erratum, transported to GENTOW5's letters): p=3, Phi1 = x^2-6
  (e1=2, f1=1, h=1, eta = res(x^2/3) = 2 != 1), stage (e2,f2)=(1,2),
  u2 = 3 (> e2*E1 = 2, gcd(3,1)=1), psi2 = y^2 + y + 2 over F_3
  (c_1 = -1 = 2, c_0 = -2 = 1).  DEF GENTOW5-1's displayed recipe
  khat_t := lift_1(c_t; u2(2-t)) gives the NAIVE key
      K_naive = Phi1^2 - 6x*Phi1 - 27
  (khat_1 = 2*n1hat(3) = 6x, khat_0 = 1*n1hat(6) = 27).  The GENHN
  erratum's corrected lifts (c_t*eta^{W(t)}, W(0)=1, W(1)=0) give
      K_corr  = Phi1^2 - 6x*Phi1 - 54.
  PREDICTIONS: K_corr is the composed carrier: factorpadic(K_corr,3)
  = ONE deg-4 factor, idealprimedec sigma (e,f) = (2,2), and
  nfeltval(Phi1) = 3 (= e * u2/(e1e2) = 2 * 3/2).  K_naive is NOT
  the carrier: sigma != {(2,2)} (erratum's frame X: {(4,1)}), i.e.
  THEOREM GENTOW5-B (a)/(b) FAIL at the note's displayed recipe on
  this frame (R != psi2 forces f=2; naive f=1 refutes).

FR-2 SLACK-FLOOR DEPTH-3 CHAIN q=2 (every prior witness floor was
  tight u_{i+1} = 4u_i + 1; here rungs 1-2 slack by 3): u = (1,)7,31,
  top 125.  Keys per DEF GENTOW5-1: Phi1 = x^2-2, Phi2 = Phi1^2-8x
  (n1hat(7) = 8x), Phi3 = Phi2^2 - 64*Phi1 (n2hat(31) = 64*Phi1),
  f16 = Phi3^2 - 1024*Phi1*Phi2 (n3hat(125) = 1024*Phi1*Phi2;
  NOTE the two-variable normalizer -- first witness anywhere with a
  composite-monomial top normalizer).  Floors: 7 > 4, 31 > 28,
  125 > 124.  PREDICTIONS (GENTOW5-B (b)+(e)): f16 irreducible/Q_2,
  (e,f) = (16,1); ladder v(x,Phi1,Phi2,Phi3) = (1/2,7/4,31/8,125/16);
  v2(Res(f16,g)) = (8,28,62,125); v2(Res(Phi3,g)) g=x,Phi1,Phi2 =
  (4,14,31).
FR-2T TOOTH: floor-BREACH mutant at rung 2: u3' = 27 < 28 = e3*E2
  (odd, gcd ok, but BELOW the floor): Phi3' = Phi2^2 - n2hat(27),
  n2hat(27): 2m+7b=27 -> b=1, m=10 -> n1hat(10)=32 -> 32*Phi1.
  Phi3' = Phi2^2 - 32*Phi1.  PREDICTION: the grammar's certificate
  fails -- Phi3' is NOT a depth-3 carrier with ladder value 27/8 at
  Phi2... concretely v2(Res(Phi3', Phi2)) != 27 OR sigma != (8,1)
  (disclosed: the tooth's exact failure shape is not pinned, only
  that the FR-2 read-offs do not all hold with 27 in place of 31).

FR-3 p=3 TIGHT DEPTH-3 CHAIN (char robustness; binomial spots live
  in char 3): Phi1 = x^2-3 (eta=1), u = (1,)5,21, top 85.
  Phi2 = Phi1^2 - 9x, Phi3 = Phi2^2 - 81*Phi1, f16 = Phi3^2 -
  6561*Phi2.  PREDICTIONS: f16 irreducible/Q_3, (e,f) = (16,1);
  ladder (1/2,5/4,21/8,85/16); v3(Res(f16,g)) = (8,20,42,85);
  v3(Res(Phi3,g)) g=x,Phi1,Phi2 = (4,14,... no: 8*(1/2,5/4,21/8) =
  (4,10,21).

Both oracles where sigma is claimed: integer resultants (fresh code
below) + PARI gp (factorpadic/nfinit/idealprimedec/nfeltval).
"""
import subprocess, sys
from fractions import Fraction

OK=[0]; BAD=[0]
def chk(ok,msg):
    if ok: OK[0]+=1; print("ok  -", msg)
    else: BAD[0]+=1; print("VIOLATION:", msg)

# fresh minimal poly arithmetic (dense int coeff lists, index=degree)
def trim(f):
    while f and f[-1]==0: f.pop()
    return f
def add(f,g):
    r=[0]*max(len(f),len(g))
    for i,c in enumerate(f): r[i]+=c
    for i,c in enumerate(g): r[i]+=c
    return trim(r)
def sc(f,k): return trim([k*c for c in f])
def mul(f,g):
    if not f or not g: return []
    r=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a:
            for j,b in enumerate(g): r[i+j]+=a*b
    return trim(r)
def vp(n,p):
    if n==0: return None
    v=0
    while n%p==0: n//=p; v+=1
    return v
def res_int(f,g):
    """Resultant by exact-fraction Gaussian elimination on Sylvester
    (independent of the note's Bareiss code)."""
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
        inv=M[k][k]
        for r in range(k+1,N):
            if M[r][k]!=0:
                fac=M[r][k]/inv
                for c in range(k,N): M[r][c]-=fac*M[k][c]
    assert det.denominator==1
    return int(det)

def pstr(f):
    return "+".join(f"({c})*x^{i}" for i,c in enumerate(f) if c) or "0"

def gp_sigma(poly, p, extra=""):
    """returns (nfactors, [deg], e, f, laddervals) via gp"""
    scr=f"""default(parisize,256M);
P={pstr(poly)};
F=factorpadic(P,{p},200);
print("NF=",matsize(F)[1]," DEGS=",vector(matsize(F)[1],i,poldegree(F[i,1])));
nf=nfinit([P,[{p}]]);
pr=idealprimedec(nf,{p});
print("SIG=",vector(length(pr),i,[pr[i].e,pr[i].f]));
{extra}
"""
    r=subprocess.run(["gp","-q","-f"],input=scr,capture_output=True,text=True,timeout=600)
    return r.stdout

# ---------- FR-1 seam probe -------------------------------------------
print("== FR-1: gauge-seam probe at DEF GENTOW5-1's recipe (p=3, eta=2) ==")
X=[0,1]; P1=[-6,0,1]
Knaive=add(add(mul(P1,P1), sc(mul(X,P1),-6)), [-27])
Kcorr =add(add(mul(P1,P1), sc(mul(X,P1),-6)), [-54])
out=gp_sigma(Kcorr,3,extra=f'print("LADP1=",nfeltval(nf,{pstr(P1)},pr[1]));')
print(out.strip())
chk("NF=1" in out and "DEGS=[4]" in out, "FR1: corrected key single deg-4 factor")
chk("SIG=[[2, 2]]" in out, "FR1: corrected key sigma = (2,2) -- the carrier")
chk("LADP1=3" in out, "FR1: corrected key nfeltval(Phi1) = 3 (= 2*u2/2)")
outn=gp_sigma(Knaive,3)
print(outn.strip())
chk("SIG=[[2, 2]]" not in outn, "FR1-TOOTH: naive (note-displayed) key is NOT the (2,2) carrier -- GENTOW5-B(a)/(b) fail at the displayed recipe")

# ---------- FR-2 slack-floor depth-3, q=2 -----------------------------
print("== FR-2: slack-floor depth-3 chain q=2 (u=7,31, top 125) ==")
P1=[-2,0,1]
P2=add(mul(P1,P1), sc(X,-8))
P3=add(mul(P2,P2), sc(P1,-64))
f16=add(mul(P3,P3), sc(mul(P1,P2),-1024))
lad=[vp(abs(res_int(f16,g)),2) for g in (X,P1,P2,P3)]
chk(lad==[8,28,62,125], f"FR2: resultant ladder {lad} == [8,28,62,125]")
lad3=[vp(abs(res_int(P3,g)),2) for g in (X,P1,P2)]
chk(lad3==[4,14,31], f"FR2: Phi3 ladder {lad3} == [4,14,31]")
out=gp_sigma(f16,2,extra=(f'print("LAD=",[nfeltval(nf,x,pr[1]),'
    f'nfeltval(nf,{pstr(P1)},pr[1]),nfeltval(nf,{pstr(P2)},pr[1]),'
    f'nfeltval(nf,{pstr(P3)},pr[1])]);'))
print(out.strip())
chk("NF=1" in out and "DEGS=[16]" in out, "FR2: f16 irreducible over Q_2")
chk("SIG=[[16, 1]]" in out, "FR2: sigma = (16,1)")
chk("LAD=[8, 28, 62, 125]" in out, "FR2: PARI nfeltval ladder exact (dual route)")
# FR-2T floor-breach tooth
P3b=add(mul(P2,P2), sc(P1,-32))
r=vp(abs(res_int(P3b,P2)),2)
outb=gp_sigma(P3b,2)
print(outb.strip())
tooth = (r!=27) or ("SIG=[[8, 1]]" not in outb)
chk(tooth, f"FR2-TOOTH: floor-breach u3'=27<28 caught (res v2={r}, sig line above)")

# ---------- FR-3 p=3 tight depth-3 ------------------------------------
print("== FR-3: p=3 tight depth-3 chain (u=5,21, top 85) ==")
P1=[-3,0,1]
P2=add(mul(P1,P1), sc(X,-9))
P3=add(mul(P2,P2), sc(P1,-81))
f16=add(mul(P3,P3), sc(P2,-6561))
lad=[vp(abs(res_int(f16,g)),3) for g in (X,P1,P2,P3)]
chk(lad==[8,20,42,85], f"FR3: resultant ladder {lad} == [8,20,42,85]")
lad3=[vp(abs(res_int(P3,g)),3) for g in (X,P1,P2)]
chk(lad3==[4,10,21], f"FR3: Phi3 ladder {lad3} == [4,10,21]")
out=gp_sigma(f16,3,extra=(f'print("LAD=",[nfeltval(nf,x,pr[1]),'
    f'nfeltval(nf,{pstr(P1)},pr[1]),nfeltval(nf,{pstr(P2)},pr[1]),'
    f'nfeltval(nf,{pstr(P3)},pr[1])]);'))
print(out.strip())
chk("NF=1" in out and "DEGS=[16]" in out, "FR3: f16 irreducible over Q_3")
chk("SIG=[[16, 1]]" in out, "FR3: sigma = (16,1)")
chk("LAD=[8, 20, 42, 85]" in out, "FR3: PARI nfeltval ladder exact (dual route)")

print(f"== FRESH VERDICT: {OK[0]} checks, {BAD[0]} violations ==")
sys.exit(1 if BAD[0] else 0)
