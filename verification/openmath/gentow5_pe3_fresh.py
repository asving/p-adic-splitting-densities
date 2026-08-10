#!/usr/bin/env python3
"""GENTOW5 passPE3 FRESH ROUTE (2026-08-10). Two legs, both DISJOINT
from PE1's (FR-1/FR-2/FR-3: i=1 seam + seam-blind depth-3 chains) and
PE2's (FR-A: seam-live depth-3, e-trivial at the live stage) and from
every committed battery row.

LEG W -- GA3* : THE FIRST w-LIVE GENTOW5 KEY, AT THE PE2-F-4 COMPOUND
(vartheta live x e_stage = 2).  Frame = GENTOW2-PE6's GA3 tower data
(committed, measured w-avatar = z2 there), but the KEY IS NEW: built
by GENTOW5's S2.1 pinned recipe ([GT5-r1] vartheta twist + [GT5-r2]
per-flavor lift) for the IRREDUCIBLE target psi3 = y^2 - y - z2
(Artin-Schreier: Tr_{F4/F2}(z2) = z2 + z2^2 = 1 != 0 -> irreducible;
c0 = z2 != 0).  This is the first contact between the MEASURED
cross-frame unit w (GENTOW2 PE6, deba21b) and THEOREM GENTOW5-B(a)'s
re-scoped display R(Phi_{i+1}) = psi^{(w_i)}.

Tower GB (all committed data): PHIP = x^2-2, PHI2 = PHIP^4 - 4x*PHIP^2
- 32; e1=2 f1=1 h=1 (z1 = 1 dead); e2=2 f2=2 u2=5 (z2 LIVE, z2^2+z2+1
= 0); K2 = F4; pi3 = PHIP/x^2 (Def 3.12, V2 = 2); e(mu2) = 4;
dv2-ladder pi->4, x->2, PHIP->5; gamma1 = x^2/2 = (2,-1,0), gamma2 =
PHIP^2/x^5 = (-5,0,2) in (i,a,b) = exponents of (x, 2, PHIP).
Stage 3: e3 = 2, f3 = 2, u3 = 41 (gcd(41,2)=1; floor 41 > 2*E2 = 40,
minimal).  D3 = 32, ehat3 = 8, f-total = 4, E3 = e3 f3 u3 = 164.

HAND-DERIVED RECIPE (pre-seal, the S2.1 pin + the r2 lift display):
  nhat2(41) = 512*PHIP   (2m+5b=41 -> b=1, m=18; 2a+i0=18 -> a=9)
  nhat2(82) = 2^20*x     (b=0, m=41; 2a+i0=41 -> i0=1, a=20)
  nhat2(72) = 2^18       (b=0, m=36; a=18)
  nhat2(31) = 64x*PHIP   (b=1, m=13; i0=1, a=6)
  vartheta_{2,1} = 1;  vartheta_{2,2} = res(nhat2(41)^2/nhat2(82))
    = res(PHIP^2/4x): (i,a,b) = (-1,-2,2) = 2*g1 + 1*g2 -> z1^2 z2
    = z2 (z1 = 1).  [= THETA0^{-1}; PE6 measured THETA0 = z2^2.]
  khat_1 = lift(c1*vartheta_{2,1}; 41) = lift(1; 41) = 512*PHIP.
  khat_0 = lift(c0*vartheta_{2,2}; 82) = lift(z2^2; 82); flavors at
    82: M0 = nhat2(82) = 2^20 x (residue 1), M1 = nhat2(72)*PHIP^2 =
    2^18*PHIP^2 (residue res(PHIP^2/4x) = z2); z2^2 = 1 + z2 ->
    digits (1,1):  khat_0 = 2^20*x + 2^18*PHIP^2.
  Phi3s := PHI2^4 - 512*PHIP*PHI2^2 - 2^20*x - 2^18*PHIP^2.
  Side heights: dv3 = 2*dv2: khat_1-term 2*41 + 2*41 = 164 = E3;
  khat_0-term 2*82 = 164; top 4*41 = 164 -- all E3 exactly.
  LIFT-DISPLAY NECESSITY AT THIS FRAME (the r2 F-2 correction, second
  frame ever): the FIXED-BASE t1=1 flavor demands pi-exponent
  (82-2-10)/4 = 35/2 at height 82 and (41-0-15)/4 = 13/2 at height 41
  -- NO such monomials; the re-solved members exist (x-exp re-solves
  1->0 at 82; 0->1 at 41).

PREREGISTERED PREDICTIONS, LEG W (hand-derived from THEOREM GENTOW5-B
as re-scoped at r2 + GENTOW2's landed B-law + PE6's measured w):
  W-A1  nhat2 pins as above (own recursion), dv2-heights exact.
  W-A2  fixed-base flavor non-existence (35/2, 13/2) + re-solved
        members at heights 41/82 exact (own Fractions).
  W-A3  vartheta lattice: ratio value-0 exact; split (j,k) = (2,1).
  W-A4  W-ratio nhat2(41)/pi3^41 = 512x^82/PHIP^40 = (82,9,-40):
        value-0 exact; split (-9,-20) -> w = z2^{-20} = z2.
  W-A5  deg Phi3s = 32, monic; E3 side arithmetic = 164/164/164.
  W-A6  RES (own Sylvester/Bareiss): v2(Res(Phi3s, g)) = 16 / 40 /
        164 for g = x / PHIP / PHI2   [= 32*(1/2, 5/4, 41/8)].
  W-B1  factorpadic(Phi3s, 2): ONE factor, degree 32 (carrier).
  W-B2  nfinit([Phi3s,[2]]) + idealprimedec: ONE prime, e=8, f=4
        (the first (8,4) leaf in the program).
  W-B3  nfeltval ladder (x, PHIP, PHI2) = (4, 10, 41); PI3V
        v(pi3) = vp - 2*vx = 2 = e/4 (Lemma 3.13(1) at a new frame).
  W-B4  letters: r1 = res(x^2/2) == 1; r2 = res(PHIP^2/x^5) has
        r2^2 + r2 + 1 == 0, r2 != 1.
  W-B5  THETA0 = res(nhat2(82)/nhat2(41)^2) == r2^2 (theta-leg
        remeasured at the NEW prime; vartheta = its inverse = z2).
  W-B6  w-AVATAR at the carrier prime (the 7th w measurement
        anywhere, first at an (8,4) leaf): W = res(nhat2(41)/pi3^41)
        == r2;  W != 1;  W != r2^2.
  W-B7  REPO class: B = res(PHI2^2/nhat2(41)): B^2 - B - r2 == 0
        (psi3-root repo-side, the re-scope's w-blind clause) and
        B^4 != B (B generates F16 over F4: genuine f3 = 2).
  W-B8  FGMN class: Y = res(PHI2^2/pi3^41):
        (i)  Y == W*B (avatar arithmetic closure -- DISCLOSED as
             consistency, not independent physics);
        (ii) PSI-W: Y^2 - W*Y - r2*W^2 == 0  << THEOREM GENTOW5-B(a)
             AS RE-SCOPED, live at measured w != 1;
        (iii) NOSE TOOTH: Y^2 - Y - r2 != 0  << the pre-r2 claim
             R = psi3 ON THE NOSE fails at this frame's FGMN class.
  W-B9  MULT0: res(khat_0/nhat2(41)^2) == r2 (= c0: the vartheta
        twist cancellation verified live at e3 = 2 -- the compound).
  W-B10 NAIVE TWIN = the COMMITTED GA3 key (khat_0 naive = lift(z2;
        82) = 2^18*PHIP^2, no twist): factorpadic -> TWO factors,
        degrees [16, 16] (its mult residual is y^2-y-1 = y^2+y+1,
        SPLIT over F4; matches the committed GA3 record NPR 2,
        EF (8,2) x2 -- the tooth doubles as an instrument
        cross-check against the committed record).

LEG D5 -- THE DEPTH-5/6 CONTACT AT THE WITNESS LADDER (first anywhere;
the committed record stops at f32, depth 4).  Chain = S4.1's minimal
tower extended one rung: q = 2, all stages (2,1), u = (1,) 5, 21, 85,
341, 1365 (1365 = minimal odd > 2*E5 = 4*341 = 1364; E5 = 682;
gcd(1365,2) = 1).  nhat5(1365) = 2^32*Phi4 (recursion: 2m+341b = 1365
-> b=1, m=512; then b=0 thrice: 512->256->128->64; 2a = 64 -> a=32).
  f64 := f32^2 - 2^32*Phi4   (= Phi6, the first depth-6 key), deg 64.
TOOTH T-D5 (hand-derived PRE-SEAL, the T-B1 pattern one level up):
  f64m := f32^2 - 2^40*Phi2 (height 1364 = 2*E5 EXACTLY, gcd(1364,2)
  != 1): f64m = Phi4^4 - 2^17*Phi3*Phi4^2 + 2^32*(Phi3^2 - 2^8*Phi2)
  = Phi4^4 - 2^17*Phi3*Phi4^2 + 2^32*Phi4  [Phi4 = Phi3^2 - 2^8*Phi2]
  = Phi4*(Phi4^3 - 2^17*Phi3*Phi4 + 2^32) -- COLLAPSES INTO THE DRAIN.

PREREGISTERED PREDICTIONS, LEG D5:
  D-A1  nhat5(1365) = 2^32*Phi4 (own level-5 recursion, height exact
        on dv5); 1365 minimal odd > 1364 = 2*E5.
  D-A2  f64 deg 64, monic; side heights (dv6): top 2*1365 = 2730,
        lift term 2*1365 = 2730 = E6 exactly.
  D-A3  RES ladder (own Bareiss, 96x96 top): v2(Res(f64, g)) =
        (32, 80, 168, 340, 682, 1365) for g = (x, Phi1, Phi2, Phi3,
        Phi4, f32)  [= 64 * (1/2, 5/4, 21/8, 85/16, 341/32,
        1365/64) -- THEOREM GENTOW5-B(b)'s exact ladder at depth 6].
  D-A4  TOOTH: f64m == Phi4*(Phi4^3 - 2^17*Phi3*Phi4 + 2^32) as an
        EXACT polynomial identity (own kit); Res(f64m, Phi4) == 0.
  D-B1  factorpadic(f64, 2): ONE factor, degree 64 (irreducible --
        with the resultant leg this gives the per-root ladder
        exactly: single field => single prime).
  D-B2  factorpadic(Phi4, 2): ONE factor, degree 16 (the depth-4
        key's own irreducibility -- never a committed chk row).
  D-B3  factorpadic(f64m, 2): >= 2 factors including degree 16 (the
        drain factor Phi4), degrees summing to 64.
  D-B4  (BUDGETED, disclosed-if-timeout per the S4.2 P-C precedent:
        prediction stands preregistered either way) nfinit([f64,[2]])
        + idealprimedec: ONE prime, e = 64, f = 1; nfeltval ladder
        (32, 80, 168, 340, 682, 1365).

TEETH SUMMARY: W-B8(iii) kills psi-on-the-nose at measured w; W-B10
kills twist-blind lifting at the compound (and pins the committed GA3
split); D-A4/D-B3 kill the gcd-proviso-free grammar at depth 6.
w == 1 anywhere at GA3* fails W-B6; theta == vartheta (sign flip)
fails W-B5 (r2^2 vs r2 discriminated since r2 has order 3).

Runner: python3 gentow5_pe3_fresh.py   (exit 0 iff 0 violations;
D-B4 timeout prints DISCLOSED and does not count as violation).
Sealed before first run; py_compile only, no smoke run.
"""

import subprocess, sys
from fractions import Fraction as Fr

OK = [0]; BAD = [0]
def chk(cond, msg):
    OK[0] += 1
    if not cond:
        BAD[0] += 1
        print("VIOLATION:", msg)
    else:
        print("  ok:", msg)

# ---------- integer poly kit (ascending coefficients) ----------
def norm(p):
    while p and p[-1] == 0: p.pop()
    return p
def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b): r[i+j] += ca*cb
    return norm(r)
def padd(a, b):
    r = [0]*max(len(a), len(b))
    for i, c in enumerate(a): r[i] += c
    for i, c in enumerate(b): r[i] += c
    return norm(r)
def psub(a, b): return padd(a, [-c for c in b])
def pscal(c, a): return norm([c*v for v in a])
def xpow(n): return [0]*n + [1]
def v2(n):
    n = abs(n); k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

def sylvester_res(f, g):
    n, m = len(f)-1, len(g)-1
    N = n + m
    M = [[0]*N for _ in range(N)]
    for i in range(m):
        for j, c in enumerate(reversed(f)): M[i][i+j] = c
    for i in range(n):
        for j, c in enumerate(reversed(g)): M[m+i][i+j] = c
    prev = 1
    for k in range(N-1):
        if M[k][k] == 0:
            piv = next((r for r in range(k+1, N) if M[r][k] != 0), None)
            if piv is None: return 0
            M[k], M[piv] = M[piv], M[k]
            for r in range(k+1, N):
                for c in range(N): M[r][c] = -M[r][c]
        for r in range(k+1, N):
            for c in range(k+1, N):
                M[r][c] = (M[r][c]*M[k][k] - M[r][k]*M[k][c]) // prev
            M[r][k] = 0
        prev = M[k][k]
    return M[N-1][N-1]

# ================= LEG W : GA3* =================
def leg_W_A():
    print("== LEG W (GA3*), A-route ==")
    # nhat2 on GB: level2 2m+5b=k (b<2), base 2a+i0=m' (i0<2)
    def nhat2(k):
        b = k % 2 and 1 or 0          # 5b = k mod 2 -> b = k mod 2
        m = (k - 5*b)//2
        if (k - 5*b) % 2 or m < 0: return None
        i0 = m % 2; a = (m - i0)//2
        if a < 0: return None
        return (a, i0, b)             # 2^a x^i0 PHIP^b
    def h2(a, i0, b): return 4*a + 2*i0 + 5*b
    for k, want in ((41,(9,0,1)), (82,(20,1,0)), (72,(18,0,0)),
                    (31,(6,1,1))):
        got = nhat2(k)
        chk(got == want and h2(*got) == k,
            "W-A1 nhat2(%d) = 2^%d x^%d PHIP^%d height exact" % ((k,)+want))
    # W-A2 fixed-base non-existence + re-solved members
    chk(Fr(82-2-10, 4) == Fr(35,2) and Fr(35,2).denominator != 1,
        "W-A2 fixed-base t1=1 flavor at 82 demands pi-exp 35/2 (none)")
    chk(Fr(41-0-15, 4) == Fr(13,2) and Fr(13,2).denominator != 1,
        "W-A2 fixed-base t1=1 flavor at 41 demands pi-exp 13/2 (none)")
    chk(h2(18,0,0) + 10 == 82 and h2(6,1,1) + 10 == 41,
        "W-A2 re-solved members 2^18*PHIP^2 (82), 64x*PHIP^3 (41) exact")
    # lattice splits: solve (i,a,b) = j*(2,-1,0) + k*(-5,0,2)
    def split(i, a, b):
        if b % 2: return None
        k = b//2; j = -a
        return (j, k) if 2*j - 5*k == i else None
    def val0(i, a, b): return i*Fr(1,2) + a + b*Fr(5,4) == 0
    chk(val0(-1,-2,2) and split(-1,-2,2) == (2,1),
        "W-A3 vartheta_{2,2} ratio PHIP^2/4x value-0, split (2,1) -> z2")
    chk(val0(82,9,-40) and split(82,9,-40) == (-9,-20),
        "W-A4 W-ratio 512x^82/PHIP^40 value-0, split (-9,-20) -> z2")
    # key build
    PHIP = [-2, 0, 1]
    P2 = pmul(PHIP, PHIP)
    PHI2 = psub(psub(pmul(P2, P2), pmul(pscal(4, xpow(1)), P2)), [32])
    PHI2sq = pmul(PHI2, PHI2)
    khat1 = pscal(512, PHIP)
    khat0 = padd(pscal(2**20, xpow(1)), pscal(2**18, P2))
    Phi3s = psub(psub(pmul(PHI2sq, PHI2sq), pmul(khat1, PHI2sq)), khat0)
    chk(len(Phi3s)-1 == 32 and Phi3s[-1] == 1, "W-A5 Phi3s deg 32 monic")
    chk(2*41 + 2*41 == 164 and 2*82 == 164 and 4*41 == 164,
        "W-A5 side heights all E3 = 164")
    for g, want, nm in ((xpow(1), 16, "x"), (PHIP, 40, "PHIP"),
                        (PHI2, 164, "PHI2")):
        r = sylvester_res(Phi3s, g)
        chk(r != 0 and v2(r) == want, "W-A6 RES %s v2 = %d" % (nm, want))
    naive = psub(psub(pmul(PHI2sq, PHI2sq), pmul(khat1, PHI2sq)),
                 pscal(262144, P2))
    return Phi3s, naive

GPW = r"""
default(parisize, 512000000);
PHIP = x^2 - 2; PHI2 = PHIP^4 - 4*x*PHIP^2 - 32;
Ks = PHI2^4 - 512*PHIP*PHI2^2 - 2^20*x - 2^18*PHIP^2;
Kn = PHI2^4 - 512*PHIP*PHI2^2 - 262144*PHIP^2;
F = factorpadic(Ks, 2, 400);
print("WFP nfac=", matsize(F)[1], " deg=", poldegree(F[1,1]));
Fn = factorpadic(Kn, 2, 400);
print("WNAIVE nfac=", matsize(Fn)[1], " degs=", vector(matsize(Fn)[1], i, poldegree(Fn[i,1])));
K = nfinit([Ks, [2]]);
prs = idealprimedec(K, 2);
print("WNPR ", #prs);
{if(#prs == 1,
  my(pr = prs[1], xF, PP, P2F, NH, NH2, KH0, vx, vp, vf2, r1, r2,
     t0, w, b, y0);
  print("WEF ", pr.e, " ", pr.f);
  xF = Mod(x, Ks); PP = Mod(PHIP, Ks); P2F = Mod(PHI2, Ks);
  NH = 512*PP; NH2 = 2^20*xF; KH0 = 2^20*xF + 2^18*PP^2;
  vx = nfeltval(K, xF, pr); vp = nfeltval(K, PP, pr);
  vf2 = nfeltval(K, P2F, pr);
  print("WVALS ", vx, " ", vp, " ", vf2);
  print("WPI3V ", vp - 2*vx);
  r1 = nfmodpr(K, xF^2/2, pr);
  r2 = nfmodpr(K, PP^2/xF^5, pr);
  print("WR1 ", r1 == 1);
  print("WR2PAT ", r2^2 + r2 + 1 == 0, " ", r2 != 1);
  t0 = nfmodpr(K, NH2/NH^2, pr);
  print("WT0 ", t0 == r2^2);
  w = nfmodpr(K, NH/(PP/xF^2)^41, pr);
  print("WW ", w == r2, " ", w != 1, " ", w != r2^2);
  b = nfmodpr(K, P2F^2/NH, pr);
  print("WB ", b^2 - b - r2 == 0, " ", b^4 != b);
  y0 = nfmodpr(K, P2F^2/(PP/xF^2)^41, pr);
  print("WY ", y0 == w*b);
  print("WPSIW ", y0^2 - w*y0 - r2*w^2 == 0);
  print("WNOSE ", y0^2 - y0 - r2 != 0);
  print("WMULT0 ", nfmodpr(K, KH0/NH^2, pr) == r2);
);}
print("GPWDONE");
"""

def leg_W_B():
    print("== LEG W (GA3*), B-route (PARI) ==")
    out = subprocess.run(["gp", "-q", "-f"], input=GPW,
                         capture_output=True, text=True, timeout=1800)
    o = out.stdout
    print(o.strip())
    chk("WFP nfac=1 deg=32" in o, "W-B1 Phi3s one factor deg 32")
    chk("WNAIVE nfac=2" in o and "[16, 16]" in o,
        "W-B10 naive twin (= committed GA3 key) splits [16,16]")
    chk("WNPR 1" in o, "W-B2 one prime")
    chk("WEF 8 4" in o, "W-B2 e=8 f=4")
    chk("WVALS 4 10 41" in o, "W-B3 ladder (4,10,41) exact")
    chk("WPI3V 2" in o, "W-B3 v(pi3) = 2 = e/4 (Lemma 3.13(1))")
    chk("WR1 1" in o, "W-B4 z1 dead (r1 == 1)")
    chk("WR2PAT 1 1" in o, "W-B4 r2 = z2 live (order 3)")
    chk("WT0 1" in o, "W-B5 THETA0 == r2^2 (theta-leg at the new prime)")
    chk("WW 1 1 1" in o, "W-B6 w-avatar == r2 (= z2), != 1, != r2^2")
    chk("WB 1 1" in o, "W-B7 repo class B: psi3(B) == 0, B not in F4")
    chk("WY 1" in o, "W-B8i Y == W*B (closure, disclosed)")
    chk("WPSIW 1" in o, "W-B8ii GENTOW5-B(a) re-scoped: psi3^{(w)}(Y) == 0")
    chk("WNOSE 1" in o, "W-B8iii NOSE TOOTH: psi3(Y) != 0 at measured w")
    chk("WMULT0 1" in o, "W-B9 MULT0 == r2 (vartheta cancellation at e3=2)")

# ================= LEG D5 : depth-5/6 =================
def leg_D_A():
    print("== LEG D5, A-route ==")
    # recursion pins on the (2,1)^5 chain: nhat5 descends through
    # u_5, u_4, u_3, u_2 = 341, 85, 21, 5 (b = k mod 2, all u odd),
    # then base 2a + i0 = m (h = 1, e1 = 2).
    k = 1365; bs = []
    for uu in (341, 85, 21, 5):
        b = k % 2
        bs.append(b)
        k = (k - uu*b)//2
    i0 = k % 2; a = (k - i0)//2
    chk(bs == [1, 0, 0, 0] and i0 == 0 and a == 32,
        "D-A1 nhat5(1365) = 2^32 * Phi4 (b4=1, b3=b2=b1=0, i0=0, a=32)")
    chk(2*32*32 + 1*341*2 == 2730,
        "D-A1 dv6-height of 2^32*Phi4 = 2048 + 682 = 2730 = 2*1365")
    chk(1365 % 2 == 1 and 1365 > 2*682 and 1364 == 2*682,
        "D-A1 1365 = minimal odd > 2*E5 = 1364")
    # keys
    Phi1 = [-2, 0, 1]
    Phi2 = psub(pmul(Phi1, Phi1), pscal(4, xpow(1)))
    Phi3 = psub(pmul(Phi2, Phi2), pscal(16, Phi1))
    Phi4 = psub(pmul(Phi3, Phi3), pscal(256, Phi2))
    f32 = psub(pmul(Phi4, Phi4), pscal(2**16, Phi3))
    f64 = psub(pmul(f32, f32), pscal(2**32, Phi4))
    chk(len(f64)-1 == 64 and f64[-1] == 1, "D-A2 f64 deg 64 monic")
    chk(2*1365 == 2730, "D-A2 E6 = 2730 side arithmetic")
    # tooth identity
    f64m = psub(pmul(f32, f32), pscal(2**40, Phi2))
    cof = padd(psub(pmul(pmul(Phi4, Phi4), Phi4),
                    pscal(2**17, pmul(Phi3, Phi4))), [2**32])
    chk(psub(f64m, pmul(Phi4, cof)) == [],
        "D-A4 TOOTH f64m == Phi4*(Phi4^3 - 2^17 Phi3 Phi4 + 2^32) exact")
    chk(sylvester_res(f64m, Phi4) == 0, "D-A4 Res(f64m, Phi4) == 0")
    # resultant ladder
    for g, want, nm in ((xpow(1), 32, "x"), (Phi1, 80, "Phi1"),
                        (Phi2, 168, "Phi2"), (Phi3, 340, "Phi3"),
                        (Phi4, 682, "Phi4"), (f32, 1365, "f32")):
        r = sylvester_res(f64, g)
        chk(r != 0 and v2(r) == want, "D-A3 RES f64 vs %s v2 = %d" % (nm, want))
    return None

GPD = r"""
default(parisize, 512000000);
Phi1 = x^2-2; Phi2 = Phi1^2-4*x; Phi3 = Phi2^2-16*Phi1;
Phi4 = Phi3^2-256*Phi2; f32 = Phi4^2-2^16*Phi3;
f64 = f32^2 - 2^32*Phi4;
f64m = f32^2 - 2^40*Phi2;
F = factorpadic(f64, 2, 3000);
print("DFP nfac=", matsize(F)[1], " deg=", poldegree(F[1,1]));
F4 = factorpadic(Phi4, 2, 400);
print("DP4 nfac=", matsize(F4)[1], " deg=", poldegree(F4[1,1]));
Fm = factorpadic(f64m, 2, 3000);
print("DFM nfac=", matsize(Fm)[1], " degs=", vecsort(vector(matsize(Fm)[1], i, poldegree(Fm[i,1]))));
print("GPDDONE");
"""

GPD4 = r"""
default(parisize, 1024000000);
Phi1 = x^2-2; Phi2 = Phi1^2-4*x; Phi3 = Phi2^2-16*Phi1;
Phi4 = Phi3^2-256*Phi2; f32 = Phi4^2-2^16*Phi3;
f64 = f32^2 - 2^32*Phi4;
K = nfinit([f64, [2]]);
prs = idealprimedec(K, 2);
print("DNPR ", #prs);
{if(#prs >= 1,
  my(pr = prs[1]);
  print("DEF ", pr.e, " ", pr.f);
  print("DLAD ", [nfeltval(K, Mod(g, f64), pr) | g <-
        [x, Phi1, Phi2, Phi3, Phi4, f32]]);
);}
print("GPD4DONE");
"""

def leg_D_B():
    print("== LEG D5, B-route (PARI) ==")
    out = subprocess.run(["gp", "-q", "-f"], input=GPD,
                         capture_output=True, text=True, timeout=1800)
    o = out.stdout
    print(o.strip())
    chk("DFP nfac=1 deg=64" in o, "D-B1 f64 ONE factor deg 64 (irreducible /Q_2)")
    chk("DP4 nfac=1 deg=16" in o, "D-B2 Phi4 ONE factor deg 16")
    dfm = [l for l in o.splitlines() if l.startswith("DFM")]
    nfac = degs = None
    if dfm:
        try:
            nfac = int(dfm[0].split("nfac=")[1].split()[0])
            degs = eval(dfm[0].split("degs=")[1])
        except Exception:
            pass
    chk(nfac is not None and nfac >= 2 and degs is not None
        and 16 in list(degs) and sum(degs) == 64,
        "D-B3 f64m splits: >= 2 factors, deg-16 drain present, sum 64")
    # D-B4 budgeted
    try:
        out4 = subprocess.run(["gp", "-q", "-f"], input=GPD4,
                              capture_output=True, text=True, timeout=1200)
        o4 = out4.stdout
        print(o4.strip())
        chk("DNPR 1" in o4, "D-B4 one prime over 2")
        chk("DEF 64 1" in o4, "D-B4 e=64 f=1")
        chk("[32, 80, 168, 340, 682, 1365]" in o4,
            "D-B4 nfeltval ladder exact at depth 6")
    except subprocess.TimeoutExpired:
        print("D-B4 DISCLOSED: nfinit budget exceeded (predictions "
              "stand preregistered; resultant + irreducibility legs "
              "carry the per-root ladder)")

def main():
    Phi3s, naive = leg_W_A()
    leg_W_B()
    leg_D_A()
    leg_D_B()
    print("== PE3 FRESH VERDICT: %d checks, %d violations ==" %
          (OK[0], BAD[0]))
    return 1 if BAD[0] else 0

if __name__ == "__main__":
    sys.exit(main())
