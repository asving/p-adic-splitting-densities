#!/usr/bin/env python3
"""GENTOW5 passPE5 FRESH ROUTE — sealed pre-run (predictions below are
hand-derived BEFORE any execution; py_compile only, no smoke run).

Disjoint from PE1 FR-1/2/3 (p=3 seam, q=2 + p=3 slack/tight chains),
PE2 FR-A (p=3 seam-live depth 3), PE3 legs W/D5 (GA3* p=2; f64 q=2),
PE4 legs CS-A/CS-B (p=2 (2,2)-stage entries; p=3 (2,2) content), and
the committed battery. NEW AXES: (1) the first p = 5 frame of this
arc and the FIRST full odd-p tower with a PROPER (e,f) = (2,2)
mid-stage carried to depth 3 AND depth 4 (PE4's CS-B stopped at the
T_2 entry); (2) the FIRST mu = 3 tower-entry (c)-read anywhere in
the program (every committed/fresh (c) row had mu = 2), with residual
CONTENT (y^2-2)^3 mod 5 — coefficients (1,4,2,2), three != 1,
unfakeable by support; (3) a T_1 leg stressing the rider's index-0
scope sentence (the UNCLAIMED instance instantiated true =
conservative); (4) a retired-(i+2)-pairing kill at the mu = 3
geometry. Frame is letter-dead (eta = 1) BY DESIGN — the mu/tower
axes are orthogonal to the gauge seam; seam coverage stays with
PE1/PE2/PE3's instruments.

FRAME FR5 (p = 5): Phi_1 = x^2 - 5 (e1 = 2, f1 = 1, h = 1, eta =
res(x^2/5) = 1, psi_1 = y - 1, E_1 = 2).
Stage 2 PROPER (e2, f2) = (2, 2): psi_2 = y^2 - 2 (2 a QNR mod 5,
irreducible; c_0 = 2 != 0), u_2 = 5 (> e2*E_1 = 4, gcd(5,2)=1).
RECIPE: vartheta_{1,2} = eta^{floor(2*i(u2)/e1)} = eta = 1 (n1hat(5)
= 25x so i(u2) = 1); khat_1 = 0 (c_1 = 0), khat_0 = lift_1(2; 10) =
2*n1hat(10) = 2*5^5. Phi_2 = Phi_1^4 - 2*5^5. D_2 = 8, E_2 = 20,
dv_2 = 4v.
Stage 3 (e3, f3) = (2, 1): psi_3 = y - 1, u_3 = 41 (> e3*E_2 = 40).
nhat_2(41) = 5^9*Phi_1 (2m+5b=41 -> b=1, m=18; n1hat(18) = 5^9).
Phi_3 = Phi_2^2 - 5^9*Phi_1. D_3 = 16, E_3 = 82, dv_3 = 8v.
Depth 4: u_4 = 165 (> 2*E_3 = 164, odd). nhat_3(165) = 5^15*x*Phi_2
(2m+41b=165 -> b=1, m=62; nhat_2(62) -> b=0, n1hat(31) = 5^15 x).
f32p = Phi_3^2 - 5^15*x*Phi_2, deg 32.
MU3 ENTRY at T_2: box = 3*E_2 + 1 = 61; nhat_2(61) = 5^14*Phi_1
(b=1, m=28, n1hat(28) = 5^14). f24 = Phi_2^3 - 5^14*Phi_1, deg 24.
T_1 LEG: box = 2*E_1 + 1 = 5; n1hat(5) = 25x. f4 = Phi_1^2 - 25x.

PREREGISTERED PREDICTIONS (all hand-derived; dual oracles wherever
sigma is claimed — own exact integer Bareiss resultants + PARI
factorpadic/nfinit/idealprimedec/nfeltval):

P-T1 (T_1 scope leg, f4 = Phi_1^2 - 25x): level-0 (x-adic, dv_1=2v)
  polygon points (0,4),(1,4),(2,2),(4,0): ONE side (0,4)->(4,0)
  slope 1 (kappa_1 = h/e1 = 1/2), j=1 strictly above (4 > 3),
  on-chord digits (j=4,2,0) = (1,3,1): residual y^2+3y+1 ==
  (y-1)^2 = psi_1^2 mod 5 EXACTLY; box: f4 - Phi_1^2 = -25x at
  weight 5 = 2E_1+1 clears. PARI: factorpadic ONE deg-4 factor;
  ONE prime (e,f) = (4,1); nfeltval (x, Phi_1) = (2, 5).
  RES: v5(Res(f4, x)) = 2, v5(Res(f4, Phi_1)) = 5.
P-T2 (Phi_2 the proper-stage key): stage read one side, support
  {0,4} (A_2 = 0), digit at 0 = -2 = 3 mod 5 -> residual y^2 + 3 ==
  psi_2 mod 5. PARI: ONE deg-8 factor; ONE prime (4,2); nfeltval
  (x, Phi_1) = (2, 5). RES: v5 = (4, 10).
P-T3 (Phi_3, FIRST odd-p depth-3 key over a proper (2,2) stage):
  PARI: ONE deg-16 factor; ONE prime (8,2); nfeltval (x, Phi_1,
  Phi_2) = (4, 10, 41). RES: v5 = (8, 20, 82).
P-T4 (f32p, FIRST odd-p depth-4 witness; (e,f) = (16,2)): PARI:
  ONE deg-32 factor; ONE prime (16,2); nfeltval (x, Phi_1, Phi_2,
  Phi_3) = (8, 20, 82, 165). RES: v5 = (16, 40, 164, 330).
P-M (f24, THE mu = 3 (c)-READ): level-1 (Phi_1-adic, dv_2 = 4v)
  pins [60, 56, inf, inf, 40, inf, inf, inf, 20, inf, inf, inf, 0]:
  ONE side (0,60)->(12,0) slope 5 (kappa_2 = 5/2, e_2-lattice),
  j = 1 strictly above (56 > 55), on-chord support EXACTLY
  {0, 4, 8, 12}, digits (j=12,8,4,0) = (1, 4, 2, 2) from
  Phi_2^3 = Phi_1^12 - 6*5^5 Phi_1^8 + 12*5^10 Phi_1^4 - 8*5^15:
  residual y^6 + 4y^4 + 2y^2 + 2 == (y^2 - 2)^3 = psi_2^3 mod 5
  COEFFICIENT-FOR-COEFFICIENT (first deg-6/mu-3 residual anywhere);
  box: f24 - Phi_2^3 = -5^14 Phi_1, single slot (a,b) = (0,1) at
  weight 4*14 + u_2 = 61 = 3E_2 + 1 -- clears. RHS+LHS both hold.
  PARI: ONE deg-24 factor; ONE prime (12,2); nfeltval (x, Phi_1,
  Phi_2) = (6, 15, 61). RES: v5 = (12, 30, 122).
P-RK (retired-pairing kill at mu = 3): f24's level-2 (Phi_2-adic)
  read is one side (0,61)->(3,0), slope 61/3 != kappa_3 = 41/2 and
  residual DEGREE 1 != 3 = mu*f_3 = deg psi_3^3 — the retired
  (i+2)-read clause fails at the mu = 3 geometry while the box
  holds (a third refutation species: committed rows were mu = 2
  all-f-1 towers; PE4's was f_2 = 2; this one is mu = 3).
T-1 TOOTH (box breach at the mu = 3 entry): f24x = f24 -
  5^13*x*Phi_1 (slot (1,1) at weight 59 < 61 -- box FAILS). A_1 =
  -5^14 - 5^13 x, p_1 = min(56, 54) = 54 < 55 = chord -> the side
  BREAKS (hull vertices {0, 1, 12}, slopes 6, 54/11) -> f24x NOT in
  T_2: biconditional's other direction. PARI: factorpadic degs
  [2, 22]. RES: v5(Res(f24x, Phi_1)) = 22*(27/22) + 2*(3/2) = 30;
  v5(Res(f24x, Phi_2)) = 22*(54/11) + 2*5 = 108 + 10 = 118 != 122;
  v5(Res(f24x, x)) = 12 (x-blind).
T-2 TOOTH (floor breach at stage 3): Phi_3m = Phi_2^2 - 5^8*x*Phi_1
  (u_3' = 39 < 40 = e_3 E_2). A_1 = -5^8 x, p_1 = 34 < 35 = chord
  -> hull vertices {0, 1, 8} (slopes 6, 34/7) -> NOT one side, the
  mutant key fails. PARI: factorpadic degs [2, 14]. RES:
  v5(Res(Phi_3m, x)) = 8, v5(Res(Phi_3m, Phi_1)) = 14*(17/14) +
  2*(3/2) = 20, v5(Res(Phi_3m, Phi_2)) = 14*(34/7) + 2*5 = 78
  != 82.

gp NOTE: single-line prints only (the documented gp-stdin trap).

RUN-1 DISCLOSURE (2026-08-10, committed before re-run): run 1 died
at the P-RK row with my own protective assert "tie in dv read" —
the run-1 dv reader took a min over RAW x-monomial heights, and
f24@Phi_2's C_0 = -5^14*Phi_1 = -5^14 x^2 + 5^15 has a raw-monomial
TIE (60 = 60) that only the Phi_1-LADDER-basis read resolves (true
dv_2 = 61 — the note's own class-separation point, GENHN-2'). The
12 checks that printed before the crash were ALL PASS; no
mathematical prediction is changed by this repair; dvcoef now
develops each coefficient in the Phi_1 basis (monomial heights
s*(v5 + a/2 + 5b/4), tie-assert retained). Run-1 record kept at
gentow5_pe5_fresh_output_run1_RED.txt.
"""
import subprocess, sys
from fractions import Fraction as F

# ---------- exact integer polynomial arithmetic ----------
def norm(f):
    while len(f) > 1 and f[-1] == 0: f = f[:-1]
    return f
def padd(f, g):
    n = max(len(f), len(g))
    return norm([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0) for i in range(n)])
def pscale(c, f): return norm([c*a for a in f])
def psub(f, g): return padd(f, pscale(-1, g))
def pmul(f, g):
    r = [0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a:
            for j,b in enumerate(g): r[i+j] += a*b
    return norm(r)
def pdivmod(f, g):  # g monic
    f = list(f); q = [0]*(max(len(f)-len(g)+1, 1))
    while len(norm(f)) >= len(g) and norm(f) != [0]:
        f = norm(f)
        if len(f) < len(g): break
        c = f[-1]; d = len(f)-len(g)
        q[d] += c
        for i,b in enumerate(g): f[d+i] -= c*b
        f = norm(f)
    return norm(q), norm(f)
def pdev(f, base):  # base-adic development, low to high
    out = []
    while True:
        q, r = pdivmod(f, base)
        out.append(r)
        if norm(q) == [0]: break
        f = q
    return out
def v5int(n):
    assert n != 0
    v = 0
    while n % 5 == 0: n //= 5; v += 1
    return v

def sylvester_res(f, g):
    m, n = len(f)-1, len(g)-1
    N = m+n
    M = [[0]*N for _ in range(N)]
    for i in range(n):
        for j,c in enumerate(reversed(f)): M[i][i+j] = c
    for i in range(m):
        for j,c in enumerate(reversed(g)): M[n+i][i+j] = c
    # fraction-free Bareiss
    prev = 1; sign = 1
    for k in range(N-1):
        if M[k][k] == 0:
            sw = next((r for r in range(k+1, N) if M[r][k] != 0), None)
            if sw is None: return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k+1, N):
            for j in range(k+1, N):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
            M[i][k] = 0
        prev = M[k][k]
    return sign*M[N-1][N-1]

# ---------- frame ----------
X = [0, 1]
P1 = [-5, 0, 1]                                   # x^2 - 5
P1_2 = pmul(P1, P1); P1_4 = pmul(P1_2, P1_2)
P2 = psub(P1_4, [2*5**5])                         # Phi_2 = Phi_1^4 - 2*5^5
P3 = psub(pmul(P2, P2), pscale(5**9, P1))         # Phi_3 = Phi_2^2 - 5^9 Phi_1
f32p = psub(pmul(P3, P3), pscale(5**15, pmul(X, P2)))
f24 = psub(pmul(pmul(P2, P2), P2), pscale(5**14, P1))
f4 = psub(pmul(P1, P1), pscale(25, X))
f24x = psub(f24, pscale(5**13, pmul(X, P1)))
P3m = psub(pmul(P2, P2), pscale(5**8, pmul(X, P1)))

CH = []
def chk(name, ok):
    CH.append((name, bool(ok)))
    print(("PASS" if ok else "FAIL"), "-", name)

# dv of a coefficient poly (deg < 8) at a node point (v(x)=1/2,
# v(Phi_1)=5/4), scale dv = s*v — read in the Phi_1 LADDER basis
# (run-1 repair: raw x-monomial reads tie under cancellation;
# the ladder basis is the note's own class-separation frame)
def dvcoef(c, s):
    if norm(c) == [0]: return None
    vals = []
    for b, cb in enumerate(pdev(c, P1)):
        for a, co in enumerate(cb):
            if co != 0:
                vals.append(F(s) * (v5int(co) + F(a, 2) + b * F(5, 4)))
    if not vals: return None
    assert len(set(vals)) == len(vals), "tie in dv read"
    return min(vals)

def pins(f, base, s):
    return [dvcoef(c, s) for c in pdev(f, base)]

def hull_vertices(pts):  # pts: list (j, h); lower convex hull vertex j's
    pts = [p for p in pts if p[1] is not None]
    hull = [pts[0]]
    rest = pts[1:]
    while hull[-1][1] != 0 or hull[-1][0] != pts[-1][0]:
        j0, h0 = hull[-1]
        best = None
        for (j, h) in rest:
            if j <= j0: continue
            sl = F(h - h0, j - j0)
            if best is None or sl < best[0] or (sl == best[0] and j > best[1][0]):
                best = (sl, (j, h))
        hull.append(best[1])
        if best[1] == pts[-1]: break
    return [j for j,_ in hull]

def digit(coefpoly, height4, nhat_pow):  # pure-5-power coef vs nhat = 5^k
    assert len(norm(coefpoly)) == 1
    c = coefpoly[0]
    return (c // 5**nhat_pow) % 5

# ---------- P-T1: the T_1 scope leg ----------
pf4 = pins(f4, X, 2)  # x-adic, dv_1 = 2v
chk("T1 pins [4,4,2,inf,0]", pf4 == [4, 4, 2, None, 0])
chk("T1 one side + j=1 above (4 > 3)", hull_vertices([(j,p) for j,p in enumerate(pf4)]) == [0, 4] and pf4[1] > 3)
d40 = digit(pdev(f4, X)[0], 4, 2); d42 = digit(pdev(f4, X)[2], 2, 1)
chk("T1 residual y^2+3y+1 == psi_1^2 mod 5", (1, d42, d40) == (1, 3, 1))
chk("T1 box slot -25x at weight 5 = 2E_1+1", 2*2 + 1 == 5)

# ---------- P-T2/T3/T4 + P-M own-arithmetic pins ----------
pP2 = pins(P2, P1, 4)
chk("Phi_2 stage pins [20,inf,inf,inf,0] support {0,4}", pP2 == [20, None, None, None, 0])
chk("Phi_2 residual y^2+3 == psi_2 mod 5", digit(pdev(P2, P1)[0], 20, 5) == 3)
pM = pins(f24, P1, 4)
chk("f24 pins [60,56,inf,inf,40,...,20,...,0]",
    pM == [60, 56, None, None, 40, None, None, None, 20, None, None, None, 0])
chk("f24 ONE side, j=1 strictly above (56 > 55)",
    hull_vertices([(j,p) for j,p in enumerate(pM)]) == [0, 12] and pM[1] > 55)
dev24 = pdev(f24, P1)
dM = (1, digit(dev24[8], 20, 5), digit(dev24[4], 40, 10), digit(dev24[0], 60, 15))
chk("f24 residual digits (1,4,2,2)", dM == (1, 4, 2, 2))
# psi_2^3 mod 5 expanded independently
psi23 = [(-2)**3 % 5, ((3*4) % 5), ((-6) % 5), 1]  # y^0, y^2, y^4, y^6
chk("residual == (y^2-2)^3 mod 5 coefficient-for-coefficient",
    (dM[3], dM[2], dM[1], dM[0]) == tuple(psi23))
chk("f24 box: single slot at weight 61 = 3E_2+1", 4*14 + 5 == 61)
# P-RK retired-pairing kill
pRK = pins(f24, P2, 4)
chk("RETIRED KILL: f24@Phi_2 pins [61,inf,inf,0], slope 61/3 != 41/2, residual deg 1 != 3",
    pRK == [61, None, None, 0] and F(61,3) != F(41,2))

# ---------- teeth, own arithmetic ----------
pTX = pins(f24x, P1, 4)
chk("TOOTH f24x p_1 = 54 < 55 (side breaks)", pTX[1] == 54)
chk("TOOTH f24x hull vertices {0,1,12}", hull_vertices([(j,p) for j,p in enumerate(pTX)]) == [0, 1, 12])
pTM = pins(P3m, P1, 4)
chk("TOOTH Phi_3m p_1 = 34 < 35 (floor breach breaks the side)", pTM[1] == 34)
chk("TOOTH Phi_3m hull vertices {0,1,8}", hull_vertices([(j,p) for j,p in enumerate(pTM)]) == [0, 1, 8])

# ---------- RES ladders (exact integer Bareiss) ----------
def resrow(name, f, gs, expect):
    got = tuple(v5int(sylvester_res(f, g)) for g in gs)
    chk(f"RES {name} v5 = {expect}", got == tuple(expect))
resrow("f4", f4, [X, P1], (2, 5))
resrow("Phi_2", P2, [X, P1], (4, 10))
resrow("Phi_3", P3, [X, P1, P2], (8, 20, 82))
resrow("f32p", f32p, [X, P1, P2, P3], (16, 40, 164, 330))
resrow("f24", f24, [X, P1, P2], (12, 30, 122))
resrow("f24x TOOTH", f24x, [X, P1, P2], (12, 30, 118))
resrow("Phi_3m TOOTH", P3m, [X, P1, P2], (8, 20, 78))

# ---------- PARI legs ----------
def gppoly(f): return "+".join(f"({c})*x^{i}" for i,c in enumerate(f) if c != 0)
def gp(cmd, timeout=600):
    r = subprocess.run(["gp", "-q"], input=cmd, capture_output=True, text=True, timeout=timeout)
    return r.stdout.strip()

def parileg(name, f, ladder, exp_degs, exp_ef=None, exp_val=None):
    fp = gppoly(f)
    out = gp(f"F={fp}; fa=factorpadic(F,5,100); print(apply(poldegree, Vec(fa[,1])~))")
    chk(f"PARI {name} factorpadic degs {exp_degs}", out == str(exp_degs).replace(" ", ", ").replace(",,", ","))
    print(f"  [{name} degs raw: {out}]")
    if exp_ef is not None:
        lad = ",".join(gppoly(g) for g in ladder)
        cmd = (f"F={fp}; nf=nfinit([F,[5]]); dec=idealprimedec(nf,5); "
               f"print(#dec,\" \",dec[1].e,\" \",dec[1].f); "
               f"v=[{lad}]; print(vector(#v, i, nfeltval(nf, Mod(v[i], F), dec[1])))")
        out2 = gp(cmd)
        lines = out2.splitlines()
        chk(f"PARI {name} one prime (e,f)={exp_ef}", lines and lines[0].split() == ["1", str(exp_ef[0]), str(exp_ef[1])])
        chk(f"PARI {name} nfeltval ladder {exp_val}", len(lines) > 1 and lines[1] == "[" + ", ".join(map(str, exp_val)) + "]")
        print(f"  [{name} pr raw: {out2}]")

parileg("f4", f4, [X, P1], [4], (4, 1), (2, 5))
parileg("Phi_2", P2, [X, P1], [8], (4, 2), (2, 5))
parileg("Phi_3", P3, [X, P1, P2], [16], (8, 2), (4, 10, 41))
parileg("f32p", f32p, [X, P1, P2, P3], [32], (16, 2), (8, 20, 82, 165))
parileg("f24", f24, [X, P1, P2], [24], (12, 2), (6, 15, 61))
parileg("f24x TOOTH", f24x, [], [2, 22])
parileg("Phi_3m TOOTH", P3m, [], [2, 14])

bad = sum(1 for _,ok in CH if not ok)
print(f"== PE5 FRESH VERDICT: {len(CH)} checks, {bad} violations ==")
if bad: print("VIOLATION count:", bad)
sys.exit(1 if bad else 0)
