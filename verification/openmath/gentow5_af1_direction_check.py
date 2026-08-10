#!/usr/bin/env python3
"""GENTOW5 [GT5-r4] A-F1 isolated re-check (2026-08-10).

CODEX TOWERRAT2 RUN A finding A-F1 (CRITICAL, adjudicated REAL at
commit eeac45f6): S2.4's closing sentence read the note's own strict
floor-rung inequality BACKWARDS -- the converse rewriting
Phi_{j+1} = Phi_j^{l_{j+1}} - lifts is weight-NONINCREASING (strictly
lowering at interior rungs, preserved at the top rung), not
"weight-nondecreasing".

This is an ISOLATED repair-round re-check (not a sealed preregistered
battery): exact integer/Fraction arithmetic at the committed S4.1
depth-4 witness chain (q = 2, h = 1, all (e_i, f_i) = (2, 1),
u = (1, 5, 21, 85), ehat_i = 2^i, E_i = 2 u_i, keys
Phi_1 = x^2 - 2, Phi_2 = Phi_1^2 - 4x, Phi_3 = Phi_2^2 - 16 Phi_1,
Phi_4 = Phi_3^2 - 256 Phi_2).  The committed sealed artifacts
(gentow5_output_exact.txt @ dc499a49) carry the witness ladder; the
weight arithmetic below is recomputed from the S2.4 definition alone.

Checks:
  C1  floor rung 3 tight: u4 = 85 > e4*E3 = 84 (margin 1)
  C2  CONVERSE drop at the interior rung (grid 4, rung j+1 = 3):
      wt4(Phi_3) = 85 -> slots {Phi_2^2, 16 Phi_1} both at 84
      (= (ehat4/ehat3)*E3): strictly LOWER by the rung margin
  C3  TOP rung preserved (the lemma's own worked instance):
      wt4(Phi_4) = wt4(Phi_3^2) = wt4(2^8 Phi_2) = 170 = E4
  C4  FORWARD carry nondecreasing at the same interior rung:
      min-slot 84 -> min(85, 84) = 84
  C5  polynomial identity Phi_3 = Phi_2^2 - 16 Phi_1 and the
      canonical Phi_1-adic development of Phi_3:
      Phi_1^4 - 8x Phi_1^2 - 16 Phi_1 + 16 x^2  (exact in Z[x])
  C6  level-1 read of Phi_3: pins (10, 8, 7, -, 0), one-sided of
      slope lam = 5/2 (interior pins strictly above the chord), and
      descmin = min_m(pin_m + m*lam) = 10 = L3*lam (S11.1.1 instance)
  C7  rho-ladder at j = 1 (S11.1.2 instance): rho_1 = 0 <
      rho_2 = 1/8 = rho_3 (top per-degree price = deepest interior
      per-degree price; strictness rho_1 < rho_2 <=> floor rung 2)
  C8  S11.1.3 margin instance: B* = 10.75, deg_1 <= 4, so
      descmin >= 10.75 - (1/8)*4 = 10.25 > 10 = M*lam
"""
from fractions import Fraction as F

fails = []
def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    print(f"CHECK {name}: {tag} {detail}")
    if not cond:
        fails.append(name)

# --- witness frame -------------------------------------------------
h = 1
e = {1: 2, 2: 2, 3: 2, 4: 2}
f = {1: 1, 2: 1, 3: 1, 4: 1}
u = {1: 1, 2: 5, 3: 21, 4: 85}
ehat = {i: 2**i for i in range(1, 5)}
E = {i: e[i]*f[i]*u[i] for i in range(1, 5)}   # E_i = 2 u_i
l = {i: e[i]*f[i] for i in range(1, 5)}

def wt4(v, a, J):
    """wt_4 of pi^v x^a Phi_1^{J1} Phi_2^{J2} Phi_3^{J3} Phi_4^{J4},
    per the S2.4 definition (top variable Phi_4 at E_4)."""
    J1, J2, J3, J4 = J
    return (ehat[4]*v + a*(ehat[4]//e[1])*h
            + J1*(ehat[4]//ehat[2])*u[2]
            + J2*(ehat[4]//ehat[3])*u[3]
            + J3*(ehat[4]//ehat[4])*u[4]
            + J4*E[4])

# C1 floor rung 3
chk("C1-rung3", u[4] == e[4]*E[3] + 1 and u[4] > e[4]*E[3],
    f"u4={u[4]} e4*E3={e[4]*E[3]}")

# C2 converse drop at interior rung j+1 = 3 on grid 4
w_phi3   = wt4(0, 0, (0, 0, 1, 0))       # the single slot Phi_3
w_phi2sq = wt4(0, 0, (0, 2, 0, 0))       # Phi_2^2
w_16phi1 = wt4(4, 0, (1, 0, 0, 0))       # 16 Phi_1 = pi^4 * Phi_1
side3 = (ehat[4]//ehat[3])*E[3]
chk("C2-drop", (w_phi3, w_phi2sq, w_16phi1) == (85, 84, 84)
    and w_phi2sq == side3 and w_16phi1 == side3
    and w_phi3 - side3 == u[4] - e[4]*E[3],
    f"wt4(Phi3)={w_phi3} -> slots {w_phi2sq},{w_16phi1}"
    f" (side=(ehat4/ehat3)E3={side3}); drop={w_phi3-side3}")

# C3 top rung preserved: Phi_4 = Phi_3^2 - 2^8 Phi_2
w_phi4   = wt4(0, 0, (0, 0, 0, 1))
w_phi3sq = wt4(0, 0, (0, 0, 2, 0))
w_256ph2 = wt4(8, 0, (0, 1, 0, 0))
chk("C3-top", w_phi4 == w_phi3sq == w_256ph2 == E[4] == 170,
    f"{w_phi4},{w_phi3sq},{w_256ph2}")

# C4 forward nondecreasing at the interior rung
chk("C4-forward", min(w_phi3, w_16phi1) >= w_phi2sq,
    f"min({w_phi3},{w_16phi1}) >= {w_phi2sq}")

# C5 polynomial identities in Z[x]
def pmul(p, q):
    r = [0]*(len(p)+len(q)-1)
    for i_, pi_ in enumerate(p):
        for j_, qj in enumerate(q):
            r[i_+j_] += pi_*qj
    return r
def padd(p, q):
    n = max(len(p), len(q)); r = [0]*n
    for i_, x_ in enumerate(p): r[i_] += x_
    for i_, x_ in enumerate(q): r[i_] += x_
    return r
def pscale(c, p): return [c*x_ for x_ in p]
def ptrim(p):
    while len(p) > 1 and p[-1] == 0: p = p[:-1]
    return p

P1 = [-2, 0, 1]                                  # x^2 - 2
P2 = ptrim(padd(pmul(P1, P1), [0, -4]))          # Phi_1^2 - 4x
P3 = ptrim(padd(pmul(P2, P2), pscale(-16, P1)))  # Phi_2^2 - 16 Phi_1
# canonical Phi_1-adic development of Phi_3:
#   Phi_1^4 - 8x Phi_1^2 - 16 Phi_1 + 16 x^2
P1_2 = pmul(P1, P1); P1_4 = pmul(P1_2, P1_2)
dev = ptrim(padd(padd(P1_4, pmul([0, -8], P1_2)),
                 padd(pscale(-16, P1), [0, 0, 16])))
chk("C5-identity", ptrim(P3) == dev,
    f"Phi3={ptrim(P3)} == dev={dev}")

# C6 level-1 read of Phi_3: coefficients (m = Phi_1-degree)
#   m=0: 16 x^2 -> dv1 = 2*4 + 2 = 10 ; m=1: -16 -> 8 ;
#   m=2: -8x -> 7 ; m=3: 0 ; m=4: 1 -> 0     (dv1(pi^v x^a) = 2v + a)
pins = {0: 10, 1: 8, 2: 7, 4: 0}
lam = F(ehat[1]*u[2], ehat[2])                   # = 5/2
L3 = l[2]*l[3]                                   # = 4
onesided = all(F(pins[m]) > pins[0] - m*lam for m in (1, 2)) \
    and pins[4] == 0 and F(pins[0]) == L3*lam
descmin = min(F(pins[m]) + m*lam for m in pins)
chk("C6-polygon", onesided and descmin == L3*lam == 10,
    f"pins={pins} lam={lam} descmin={descmin}")

# C7 rho-ladder at j = 1, entered stage i+2 = 3
L = {1: 1, 2: l[2], 3: l[2]*l[3]}
price = {1: F(ehat[1]*u[2], ehat[2]),            # interior u2
         2: F(ehat[1]*u[3], ehat[3]),            # interior u3
         3: F(ehat[1]*E[3], ehat[3])}            # TOP price E3, scaled
rho = {k: price[k]/L[k] - lam for k in (1, 2, 3)}
rung2 = u[3] > e[3]*E[2]
chk("C7-rho", rho[1] == 0 and rho[1] < rho[2] and rho[2] == rho[3]
    and rho[2] == F(1, 8) and rung2,
    f"rho={dict((k, str(v)) for k, v in rho.items())} rung2={rung2}")

# C8 margin instance: box mu*E3 + 1 scaled by ehat1/ehat3
mu = 1
Bstar = F(ehat[1]*(mu*E[3] + 1), ehat[3])        # 10.75
M = mu*L[3]
chk("C8-margin", Bstar - rho[3]*M > M*lam,
    f"B*={Bstar} - rho*M={rho[3]*M} = {Bstar - rho[3]*M} > M*lam={M*lam}")

print()
if fails:
    print(f"VERDICT: RED ({len(fails)} failing: {fails})")
    raise SystemExit(1)
print("VERDICT: GREEN — 8 checks, 0 violations")
