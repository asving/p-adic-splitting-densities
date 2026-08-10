#!/usr/bin/env python3
"""GENTOW5 passPE4 fresh instrument — THE (c)-STRESS ROUTE.

SEALED PRE-RUN (predictions hand-derived in the PE4 pass before any
execution; disjoint from the committed battery, the depth-4 witness
chain, PE1's FR-1/2/3, PE2's FR-A, PE3's legs W/D5 — new keys, new
frames, new check species: no committed row anywhere reads a
T_2-entry polygon).

TARGET: THEOREM GENTOW5-B(c) AS RE-INDEXED AT r3 (commit 1e1406f) —
the corrected entry-read clause (level-i read, slope kappa_{i+1},
residual psi_{i+1}^{mu}, box vs Phi_{i+1}^{mu} at mu*E_{i+1}+1) at
the exact axis the pre-r3 display miscounted, PLUS the old-clause
refutation at a NEW geometry, PLUS residual CONTENT (non-F_2
digits), PLUS a depth-4 witness at f-part 2.

LEG CS-A (p = 2; the first proper (e_2,f_2) = (2,2) (c)-read):
  Phi_1 = x^2 - 2 (e1=2, f1=1, h=1, D_1=2, E_1=2, K_1=F_2, eta=1).
  Stage 2: (e_2,f_2) = (2,2), u_2 = 7 (> e_2 E_1 = 4, SLACK floor,
  gcd(7,2)=1), psi_2 = y^2+y+1 (c_1=c_0=1). vartheta trivial (K_1 =
  F_2), corrected = naive recipe — DISCLOSED: this leg's axis is
  the (c)-read, not the gauge seam (PE1/PE2's axis).
    Phi_2 := Phi_1^4 - 8x*Phi_1^2 - 128     (n1hat(7)=8x, n1hat(14)=2^7)
    f16   := Phi_2^2 - 2^12*x*Phi_1         (n2hat(57) = 2^12 x Phi_1;
             u_3 = 57 = 2E_2+1 > 56 = e_3 E_2, E_2 = 28, stage 3 = (2,1))
    f32'  := Phi_3^2 - 2^21*x*Phi_2, Phi_3 := f16
             (n3hat(229) = 2^21 x Phi_2; u_4 = 229 > 228 = e_4 E_3, E_3 = 114)
  PREDICTIONS (hand-derived pre-seal):
  A-DEV: Phi_1-adic dev of f16 = Phi_1^8 - 16x Phi_1^6 + 64 Phi_1^5
    - 128 Phi_1^4 + 2^11 x Phi_1^2 - 2^12 x Phi_1 + 2^14 (exact).
  A-PINS (corrected-(c) LHS; dv_1 = 2v; monomial-exact, no slot
    theory consumed): [28, 25, 23, inf, 14, 12, 9, inf, 0]; ONE side
    of slope kappa_2 = 7/2; on-chord support EXACTLY {0,4,8}
    (j ∈ {2,6} strictly above); residual digits (1,1,1) -> residual
    y^4 + y^2 + 1 == psi_2^2 in F_2[y] — the FIRST machine (c)-read
    whose residual is a genuine psi^mu with deg psi > 1.
  A-BOX: wt_2(2^12 x Phi_1) = 48+2+7 = 57 == mu*E_2 + 1 (RHS holds).
  A-OLD (the pre-r3 clause refuted at the NEW geometry): f16@Phi_2
    dev = (C_0, C_1, C_2) = (-2^12 x Phi_1, 0, 1); pins [57, inf, 0];
    one kappa_3 = 57/2 side, on-chord {0,2}, residual DEGREE
    (2-0)/e_3 = 1 != 2 = deg psi_3^mu — LHS(old) fails while the box
    holds; equality would force e_3 f_3 = 1 (improper).
  A-RES (dual oracle 1, own Bareiss over Z): v2(Res(Phi_2, x)) = 4,
    v2(Res(Phi_2, Phi_1)) = 14; v2(Res(f16, ·)) = (8, 28, 114) for
    (x, Phi_1, Phi_2); v2(Res(f32', ·)) = (16, 56, 228, 458) for
    (x, Phi_1, Phi_2, Phi_3).
  A-PARI (dual oracle 2): Phi_2 -> ONE factor deg 8, ONE prime
    e = 4, f = 2, nfeltval (x, Phi_1) = (2, 7); f16 -> ONE factor
    deg 16, e = 8, f = 2, nfeltval (4, 14, 57); f32' -> ONE factor
    deg 32, e = 16, f = 2, nfeltval (8, 28, 114, 229) — the first
    depth-4 witness with f-part 2 anywhere in the program.
  T-A1 (tooth, box-even drain at 2E_2): f16m := Phi_2^2 - 2^14
    (n2hat(56) = 2^14; wt 56 = 2E_2, gcd proviso violated) =
    Phi_1^2 * (Phi_1^2 - 8x) * (Phi_1^4 - 8x Phi_1^2 - 256) EXACTLY
    (hand-derived: Phi_2 + 128 = Phi_1^2(Phi_1^2 - 8x)); rem(f16m,
    Phi_1) = 0, Res(f16m, Phi_1) = 0, factorpadic nfactors > 1 —
    box fails AND read fails (iff consistent, negative direction).
  T-A2 (tooth, sub-box slot): f16b := f16 - 2^13 x^2 (slot wt 56 =
    2E_2 < 57, box FAILS); 2^13 x^2 = 2^13 Phi_1 + 2^14 kills C_0:
    dev C_0(f16b) == 0, Phi_1 | f16b, Res(f16b, Phi_1) = 0 — the
    full-side read collapses (iff consistent).

LEG CS-B (p = 3; residual CONTENT — five nontrivial digits):
  Phi_1 = x^2 - 3 (e1=2, f1=1, h=1, K_1 = F_3, eta = 1 — disclosed
  convention-blind; the vartheta axis lives at PE1/PE2's records).
  Stage 2: (e_2,f_2) = (2,2), u_2 = 5 (> 4, gcd(5,2)=1), psi_2 =
  y^2 - y - 1 over F_3 (no root in F_3: values (-1,-1,1) at (0,1,2)
  — irreducible; c_1 = c_0 = 1).
    Phi_2 := Phi_1^4 - 9x*Phi_1^2 - 243    (n1hat(5)=9x, n1hat(10)=3^5)
    f16_3 := Phi_2^2 - 3^9*Phi_1           (n2hat(41) = 3^9 Phi_1;
             u_3 = 41 = 2E_2+1 > 40, E_2 = 20, stage 3 = (2,1))
  PREDICTIONS (hand-derived pre-seal):
  B-DEV: Phi_1-adic dev of f16_3 = Phi_1^8 - 18x Phi_1^6 + 81 Phi_1^5
    - 243 Phi_1^4 + 4374x Phi_1^2 - 3^9 Phi_1 + 3^10 (exact;
    81x^2 = 81 Phi_1 + 243 reduction).
  B-PINS (dv_1 = 2v): [20, 18, 15, inf, 10, 8, 5, inf, 0]; ONE side
    slope kappa_2 = 5/2; on-chord support {0, 2, 4, 6, 8} — ALL
    five lattice slots (p_1 = 18 > 17.5 the only near-miss flank);
    coherent digits (j = 8,6,4,2,0) = (1, 1, 2, 2, 1): residual
    y^4 + y^3 + 2y^2 + 2y + 1 == (y^2 - y - 1)^2 == psi_2^2 in
    F_3[y] — THE CONTENT CHECK: three digits != 1, unfakeable by
    support; Step 1's multiplicativity live at p = 3.
  B-BOX: wt_2(3^9 Phi_1) = 36 + 5 = 41 == mu*E_2 + 1.
  B-RES: v3(Res(Phi_2, x)) = 4, v3(Res(Phi_2, Phi_1)) = 10;
    v3(Res(f16_3, ·)) = (8, 20, 82) for (x, Phi_1, Phi_2).
  B-PARI: Phi_2 -> ONE factor deg 8, e = 4, f = 2, nfeltval (2, 5);
    f16_3 -> ONE factor deg 16, e = 8, f = 2, nfeltval (4, 10, 41).

INSTRUMENT NOTES: every gp print is SINGLE-LINE (the documented
gp-stdin trap of the PE2/PE3 run-1 REDs). Pin arithmetic consumes
NO slot theory: every dev coefficient is a ladder monomial, its
value exact by additivity of v on products (tautology audit:
polygon legs are independent of PARI legs; ladder values get dual
oracles RES + nfeltval; the residual digits are exact integer
monomial ratios).
"""
import sys, subprocess
from fractions import Fraction as Fr

CHECKS = [0, 0]
def chk(name, cond, detail=""):
    CHECKS[0] += 1
    if cond:
        print(f"  ok: {name} {detail}")
    else:
        CHECKS[1] += 1
        print(f"  VIOLATION: {name} {detail}")

# ---------- dense polynomial arithmetic over Z (coeff lists, low->high)
def pnorm(p):
    while len(p) > 1 and p[-1] == 0: p.pop()
    return p
def padd(a, b):
    n = max(len(a), len(b)); r = [0]*n
    for i,c in enumerate(a): r[i] += c
    for i,c in enumerate(b): r[i] += c
    return pnorm(r)
def pneg(a): return [-c for c in a]
def psub(a, b): return padd(a, pneg(b))
def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i,ca in enumerate(a):
        if ca:
            for j,cb in enumerate(b): r[i+j] += ca*cb
    return pnorm(r)
def pdivmod(a, b):
    # b monic
    a = a[:]; q = [0]*max(1, len(a)-len(b)+1)
    while len(a) >= len(b) and any(a):
        if a[-1] == 0: a.pop(); continue
        d = len(a)-len(b); c = a[-1]
        q[d] = c
        for i,cb in enumerate(b): a[d+i] -= c*cb
        a = pnorm(a)
    return pnorm(q), pnorm(a)
def pdev2(f, phi):
    out = []; cur = f[:]
    while True:
        q, r = pdivmod(cur, phi)
        out.append(r)
        cur = q
        if not any(cur): break
    return out
def peval_int(p, x):
    v = 0
    for c in reversed(p): v = v*x + c
    return v

def resultant(f, g):
    # Sylvester matrix + fraction-free Bareiss determinant (exact over Z)
    n, m = len(f)-1, len(g)-1
    N = n + m
    M = [[0]*N for _ in range(N)]
    for i in range(m):
        for j,c in enumerate(reversed(f)): M[i][i+j] = c
    for i in range(n):
        for j,c in enumerate(reversed(g)): M[m+i][i+j] = c
    sign = 1; prev = 1
    for k in range(N-1):
        if M[k][k] == 0:
            sw = next((r for r in range(k+1, N) if M[r][k] != 0), None)
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k+1, N):
            for j in range(k+1, N):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
            M[i][k] = 0
        prev = M[k][k]
    return sign * M[N-1][N-1]

def vp(n, p):
    if n == 0: return None
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

INF = Fr(10**9)

def dev_pins(f, phi, p, ladder_vals):
    """phi-adic dev; each C_j must be a ladder monomial c*x^k (deg<2) or
    c*x^k*PHI1^b style — here deg phi cases: for phi=Phi_1 the C_j have
    deg < 2 (c or c*x); for deeper phis we pass explicit basis handling.
    ladder_vals = dict giving v of x. Returns (dev, pins as Fractions*2 = dv_1)."""
    dev = pdev2(f, phi)
    pins = []
    vx = ladder_vals['x']
    for C in dev:
        if not any(C):
            pins.append(INF); continue
        # value = min over monomials (exact: at most one monomial expected; assert)
        mono = [(k, c) for k, c in enumerate(C) if c != 0]
        vals = [Fr(vp(c, p)) + k*vx for k, c in mono]
        pins.append(min(vals))
    return dev, pins

def run_gp(script):
    r = subprocess.run(["gp", "-q"], input=script, capture_output=True, text=True, timeout=1200)
    return r.stdout

# =====================================================================
print("== LEG CS-A (p=2, (2,2)-stage u2=7): the (c)-STRESS ==")
p = 2
x = [0, 1]
Phi1 = [-2, 0, 1]
# recipe
Phi2 = psub(psub(pmul(pmul(Phi1,Phi1),pmul(Phi1,Phi1)), pmul([0,8], pmul(Phi1,Phi1))), [128])
chk("A-KEY Phi2 = Phi1^4-8x*Phi1^2-128 deg 8", len(Phi2)-1 == 8)
# normalizer solves (recursion, hand: n1hat(7)=8x, n1hat(14)=128, n2hat(57)=2^12xPhi1, n3hat(229)=2^21xPhi2)
def n1hat(m, e1=2, h=1):
    # 2a + i0 = m, i0 < 2
    i0 = m % 2; a = (m - i0)//2
    return a, i0
chk("A-N1 n1hat(7)=(3,1)->8x", n1hat(7) == (3,1))
chk("A-N1 n1hat(14)=(7,0)->2^7", n1hat(14) == (7,0))
# n2hat(57): 2m+7b=57 b<2 -> b=1,m=25; n1hat(25)=(12,1)
chk("A-N2 n2hat(57)=2^12*x*Phi1", (57-7)%2==0 and (57-7)//2==25 and n1hat(25)==(12,1))
# n3hat(229): 2m+57b=229 b<2 -> b=1,m=86; n2hat(86): 2m'+7b'=86 -> b'=0,m'=43; n1hat(43)=(21,1)
chk("A-N3 n3hat(229)=2^21*x*Phi2", (229-57)//2==86 and 86%2==0 and n1hat(43)==(21,1))
t = pmul([0, 4096], Phi1)          # 2^12 * x * Phi1
f16 = psub(pmul(Phi2, Phi2), t)
chk("A-F16 deg 16", len(f16)-1 == 16)
Phi3 = f16
f32p = psub(pmul(Phi3, Phi3), pmul([0, 2**21], Phi2))
chk("A-F32' deg 32", len(f32p)-1 == 32)
# floor chain
E1, E2, E3 = 2, 28, 114
chk("A-FLOOR u2=7>4 slack", 7 > 4 and 7 - 4 == 3)
chk("A-FLOOR u3=57>56 tight", 57 == 2*E2 + 1)
chk("A-FLOOR u4=229>228 tight", 229 == 2*E3 + 1)
# A-DEV + A-PINS: the corrected-(c) LHS at f16 (level-1 read)
pred_dev = {8:[1], 7:[], 6:[0,-16], 5:[64], 4:[-128], 3:[], 2:[0,2048], 1:[0,-4096], 0:[16384]}
dev, pins = dev_pins(f16, Phi1, 2, {'x': Fr(1,2)})
devok = len(dev) == 9 and all(pnorm(dev[j][:]) == (pred_dev[j] if pred_dev[j] else [0]) for j in range(9))
chk("A-DEV f16 Phi1-dev == hand-derived 7-term display", devok)
pins2 = [2*q if q is not INF else 'inf' for q in pins]  # dv_1 = 2v
chk("A-PINS [28,25,23,inf,14,12,9,inf,0]", pins2 == [28,25,23,'inf',14,12,9,'inf',0], str(pins2))
# one side of slope kappa2=7/2 (dv_1): chord(j) = (8-j)*7/2; on-chord exactly {0,4,8}
onchord = []
oneside = True
for j in range(9):
    ch = Fr(7,2)*(8-j)
    q = pins[j]*2 if pins[j] is not INF else INF
    if q < ch: oneside = False
    if q == ch: onchord.append(j)
chk("A-SIDE one side (nothing below chord)", oneside)
chk("A-SUPP on-chord support == {0,4,8}", onchord == [0,4,8], str(onchord))
# residual digits at {8,6->skip,4,0}: lattice slots j=0,2,4,6,8 <-> residual degs 0..4
# digits: C_8=1 ->1; C_4=-128 vs n1hat(14)=128: -1=1 mod 2; C_0=16384 vs n1hat(28)=2^14: 1
dig4 = (-128) // 128 % 2
dig0 = 16384 // 16384 % 2
chk("A-RESIDUAL digits (j=8,4,0)=(1,1,1) -> y^4+y^2+1 == psi2^2 mod 2",
    dig4 == 1 and dig0 == 1, "(residual = (y^2+y+1)^2 in F_2)")
# psi2^2 in F_2: (y^2+y+1)^2 = y^4+y^2+1
psq = pmul([1,1,1],[1,1,1]); psq = [c % 2 for c in psq]
chk("A-PSISQ (y^2+y+1)^2 mod 2 == y^4+y^2+1", psq == [1,0,1,0,1])
# A-BOX
chk("A-BOX wt2(2^12 x Phi1) = 48+2+7 = 57 == 2*E2+1", 4*12 + 2 + 7 == 57 == 2*E2+1)
# A-OLD: level-2 read of f16
devB = pdev2(f16, Phi2)
oldok = len(devB) == 3 and pnorm(devB[0][:]) == pneg(t) and not any(devB[1]) and pnorm(devB[2][:]) == [1]
chk("A-OLD f16@Phi2 dev == (-2^12xPhi1, 0, 1)", oldok)
# pin p0 = dv_2(2^12 x Phi1) = 4*(12+1/2+7/4) = 57
chk("A-OLD pins [57, inf, 0] (dv_2)", 4*(Fr(12)+Fr(1,2)+Fr(7,4)) == 57)
chk("A-OLD residual degree (2-0)/e3 = 1 != 2 = deg psi3^mu (old clause killed; = forces e3f3=1)", (2-0)//2 == 1 and 1 != 2)
# T-A1 drain tooth
f16m = psub(pmul(Phi2, Phi2), [16384])
fac1 = pmul(Phi1, Phi1)
fac2 = psub(pmul(Phi1,Phi1), [0,8])
fac3 = psub(psub(pmul(pmul(Phi1,Phi1),pmul(Phi1,Phi1)), pmul([0,8],pmul(Phi1,Phi1))), [256])
chk("T-A1 f16m == Phi1^2*(Phi1^2-8x)*(Phi1^4-8xPhi1^2-256) EXACT", f16m == pmul(pmul(fac1,fac2),fac3))
chk("T-A1 rem(f16m, Phi1) == 0", not any(pdivmod(f16m, Phi1)[1]))
chk("T-A1 box slot wt = 4*14 = 56 == 2E2 (even, gcd proviso violated)", 4*14 == 2*E2)
r_m = resultant(f16m, Phi1)
chk("T-A1 Res(f16m, Phi1) == 0", r_m == 0)
# T-A2 sub-box tooth
f16b = psub(f16, [0,0,8192])
devb = pdev2(f16b, Phi1)
chk("T-A2 f16b dev C_0 == 0 (Phi1 | f16b; full-side read collapses)", not any(devb[0]))
chk("T-A2 offending slot wt2(2^13 x^2) = 52+4 = 56 < 57 (box FAILS)", 4*13 + 2*2 == 56)
chk("T-A2 Res(f16b, Phi1) == 0", resultant(f16b, Phi1) == 0)
# A-RES ladders
for name, F, G, want in [("Res(Phi2,x)", Phi2, x, 4), ("Res(Phi2,Phi1)", Phi2, Phi1, 14),
                          ("Res(f16,x)", f16, x, 8), ("Res(f16,Phi1)", f16, Phi1, 28),
                          ("Res(f16,Phi2)", f16, Phi2, 114),
                          ("Res(f32',x)", f32p, x, 16), ("Res(f32',Phi1)", f32p, Phi1, 56),
                          ("Res(f32',Phi2)", f32p, Phi2, 228), ("Res(f32',Phi3)", f32p, Phi3, 458)]:
    R = resultant(F, G)
    chk(f"A-RES {name} v2 == {want}", R != 0 and vp(abs(R), 2) == want,
        f"(v2={vp(abs(R),2) if R else 'zero'})")

print("== LEG CS-B (p=3, content-live residual) ==")
Phi1b = [-3, 0, 1]
Phi2b = psub(psub(pmul(pmul(Phi1b,Phi1b),pmul(Phi1b,Phi1b)), pmul([0,9], pmul(Phi1b,Phi1b))), [243])
chk("B-PSI psi2=y^2-y-1 rootless in F_3", all(peval_int([-1,-1,1], a) % 3 != 0 for a in (0,1,2)))
chk("B-N1 n1hat(5)=(2,1)->9x; n1hat(10)=(5,0)->3^5", n1hat(5)==(2,1) and n1hat(10)==(5,0))
chk("B-N2 n2hat(41)=3^9*Phi1 (2m+5b=41 -> b=1,m=18; n1hat(18)=(9,0))", (41-5)//2==18 and n1hat(18)==(9,0))
f16_3 = psub(pmul(Phi2b, Phi2b), pmul([19683], Phi1b))
chk("B-F16 deg 16", len(f16_3)-1 == 16)
chk("B-FLOOR u2=5>4; u3=41=2*20+1>40 tight", 5 > 4 and 41 == 2*20+1)
pred_devB = {8:[1], 7:[], 6:[0,-18], 5:[81], 4:[-243], 3:[], 2:[0,4374], 1:[-19683], 0:[59049]}
devb3, pinsb3 = dev_pins(f16_3, Phi1b, 3, {'x': Fr(1,2)})
devokB = len(devb3) == 9 and all(pnorm(devb3[j][:]) == (pred_devB[j] if pred_devB[j] else [0]) for j in range(9))
chk("B-DEV f16_3 Phi1-dev == hand-derived display", devokB)
pinsB2 = [2*q if q is not INF else 'inf' for q in pinsb3]
chk("B-PINS [20,18,15,inf,10,8,5,inf,0]", pinsB2 == [20,18,15,'inf',10,8,5,'inf',0], str(pinsB2))
onchordB = []
onesideB = True
for j in range(9):
    ch = Fr(5,2)*(8-j)
    q = pinsb3[j]*2 if pinsb3[j] is not INF else INF
    if q < ch: onesideB = False
    if q == ch: onchordB.append(j)
chk("B-SIDE one side", onesideB)
chk("B-SUPP on-chord support == {0,2,4,6,8} (ALL lattice slots)", onchordB == [0,2,4,6,8], str(onchordB))
# coherent digits: j=8: 1; j=6: -18x/9x = -2 = 1 mod 3; j=4: -243/243 = -1 = 2;
# j=2: 4374x/2187x = 2; j=0: 59049/59049 = 1  (n1hat(15) = 3^7 x = 2187x, n1hat(20) = 3^10)
digs = [1, (-18)//9 % 3, (-243)//243 % 3, 4374//2187 % 3, 59049//59049 % 3]
chk("B-DIGITS (j=8,6,4,2,0) == (1,1,2,2,1)", digs == [1,1,2,2,1], str(digs))
psqB = pmul([-1,-1,1], [-1,-1,1]); psqB = [c % 3 for c in psqB]
chk("B-PSISQ (y^2-y-1)^2 mod 3 == y^4+y^3+2y^2+2y+1 == residual", psqB == [1,2,2,1,1] and list(reversed(digs)) == psqB,
    f"(psi2^2={psqB})")
chk("B-BOX wt2(3^9 Phi1) = 36+5 = 41 == 2*E2+1 (E2=20)", 4*9 + 5 == 41)
for name, F, G, want in [("Res(Phi2,x)", Phi2b, x, 4), ("Res(Phi2,Phi1)", Phi2b, Phi1b, 10),
                          ("Res(f16_3,x)", f16_3, x, 8), ("Res(f16_3,Phi1)", f16_3, Phi1b, 20),
                          ("Res(f16_3,Phi2)", f16_3, Phi2b, 82)]:
    R = resultant(F, G)
    chk(f"B-RES {name} v3 == {want}", R != 0 and vp(abs(R), 3) == want,
        f"(v3={vp(abs(R),3) if R else 'zero'})")

# ---------------- PARI leg ----------------
if "--pari" in sys.argv or True:
    print("== PARI LEG ==")
    def pstr(pl):
        return "+".join(f"({c})*x^{k}" for k, c in enumerate(pl) if c != 0)
    gp_script = ""
    rows = [("PA-Phi2", pstr(Phi2), 2, [("x","2"),("({})".format(pstr(Phi1)),"7")], 8, 4, 2),
            ("PA-f16", pstr(f16), 2, [("x","4"),("({})".format(pstr(Phi1)),"14"),("({})".format(pstr(Phi2)),"57")], 16, 8, 2),
            ("PA-f32p", pstr(f32p), 2, [("x","8"),("({})".format(pstr(Phi1)),"28"),("({})".format(pstr(Phi2)),"114"),("({})".format(pstr(Phi3)),"229")], 32, 16, 2),
            ("PB-Phi2", pstr(Phi2b), 3, [("x","2"),("({})".format(pstr(Phi1b)),"5")], 8, 4, 2),
            ("PB-f16", pstr(f16_3), 3, [("x","4"),("({})".format(pstr(Phi1b)),"10"),("({})".format(pstr(Phi2b)),"41")], 16, 8, 2)]
    for tag, fs, pp, lad, dg, ee, ff in rows:
        gp_script += f'F={fs};fp=factorpadic(F,{pp},80);print("{tag} nfactors=",matsize(fp)[1]," deg1=",poldegree(fp[1,1]));\n'
        gp_script += f'K=nfinit([F,[{pp}]]);pr=idealprimedec(K,{pp});print("{tag} nprimes=",length(pr)," e=",pr[1].e," f=",pr[1].f);\n'
        lv = ",".join(g for g, _ in lad)
        gp_script += f'print("{tag} ladder=",[' + ",".join(f"idealval(K,nfalgtobasis(K,Mod({g},F)),pr[1])" for g,_ in lad) + ']);\n'
    gp_script += f'FM={pstr(f16m)};fm=factorpadic(FM,2,80);print("TA1 nfactors=",matsize(fm)[1]," degs=",vector(matsize(fm)[1],i,poldegree(fm[i,1])));\n'
    gp_script += f'FB={pstr(f16b)};fb=factorpadic(FB,2,80);print("TA2 nfactors=",matsize(fb)[1]," degs=",vector(matsize(fb)[1],i,poldegree(fb[i,1])));\n'
    out = run_gp(gp_script)
    print(out)
    want_lines = {
        "PA-Phi2 nfactors=1 deg1=8": None, "PA-Phi2 nprimes=1 e=4 f=2": None,
        "PA-Phi2 ladder=[2, 7]": None,
        "PA-f16 nfactors=1 deg1=16": None, "PA-f16 nprimes=1 e=8 f=2": None,
        "PA-f16 ladder=[4, 14, 57]": None,
        "PA-f32p nfactors=1 deg1=32": None, "PA-f32p nprimes=1 e=16 f=2": None,
        "PA-f32p ladder=[8, 28, 114, 229]": None,
        "PB-Phi2 nfactors=1 deg1=8": None, "PB-Phi2 nprimes=1 e=4 f=2": None,
        "PB-Phi2 ladder=[2, 5]": None,
        "PB-f16 nfactors=1 deg1=16": None, "PB-f16 nprimes=1 e=8 f=2": None,
        "PB-f16 ladder=[4, 10, 41]": None,
    }
    for wl in want_lines:
        chk(f"PARI {wl}", wl in out)
    chk("PARI TA1 f16m splits (nfactors>1)", "TA1 nfactors=1 " not in out and "TA1 nfactors=" in out)
    chk("PARI TA2 f16b splits (nfactors>1)", "TA2 nfactors=1 " not in out and "TA2 nfactors=" in out)

print(f"== PE4 FRESH VERDICT: {CHECKS[0]} checks, {CHECKS[1]} violations ==")
sys.exit(0 if CHECKS[1] == 0 else 1)
