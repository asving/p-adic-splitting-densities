#!/usr/bin/env python3
"""R3b countermodel check (2026-07-28, carry-bridge escalation round).

Verifies the numeric countermodel of the REV-3 obstruction record at
`lean/LeanUrat/HC1/V9_K1nonrec.lean` (mirrored at `lean/LeanUrat/HC2/K1_vertexPin.lean`
obstruction item 5): the kernel `K1_readVertexPin_nonrec`'s weight conclusion (R3b's
lower half) is NOT derivable from SideReads(i)+(ii)+(vi) + hOrd/hAnchor + the proved
V-frame engine (V1-V4) + hStretch/child_slotmin.

Setup: p = 2; sigma = the (1,1)-Gauss stage at Phi = X (U31's base stage:
w(sum a_i X^i) = min_i (v_2(a_i) + i), sigma.h = 1, sigma.s = 1, sigma.t = 0);
read pair (e*, h*) = (1, 2) (t* = 0; steep: e*.sigma.h = 1 < 2 = h*);
psi = z^2 + z + 1 (g = 2); recorded IsReadLift Phihat = X^2 + 4X + 16;
f = (X + 8)(Phihat^2 + 8 X^3).

Checks (all asserted):
  1. Read-i side data: gam = 10 attained EXACTLY at slots {1,3,5} (SideReads(i));
     pattern (1,0,1,0,1), Ranch = psi^2, mu = 2 (hOrd), anchor a = 1 (hAnchor).
  2. Phihat-development: B2 = X + 16, B1 = -384, B0 = 512X + 4096.
  3. V4-(VERTEX) at the regrade: wV(B2) = 2 = gam - mu*e*g*h (G_V = (11,11,10), BOX strict).
  4. Clause (vi) HOLDS: sigma-frame digit of B2 = zbar^1 = nu.vtx (a - mu*mhat = 1,
     vtxPoly = 1) -- digit equations carry no weight content.
  5. THE VIOLATION: sigma'.w(B2) = e*.sigma.w(B2) = 1 < 2 = STR.line.at(mu.childWidth):
     the kernel's weight conclusion is FALSE on these data (bottom-window law fails:
     inner window of B2 = X + 16 has l_min = 1).
  6. The sole violated ReadsOf clause is SideReads(iii)'s `sigma.R f` rendering:
     frame-min of f is the single slot 5 (sigma.R f = z^5, a monomial != T(1).psi^2).

Run:  python3 r3b_countermodel_check.py   (needs sympy; e.g. `uv run --with sympy ...`)
"""
import sympy as sp

X = sp.symbols('X')
p = 2
Phihat = X**2 + p**2 * X + p**4


def v2(n):
    n = int(n)
    assert n != 0
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def slots(poly):
    c = sp.Poly(poly, X).all_coeffs()[::-1]
    return [(j, a) for j, a in enumerate(c) if a != 0]


def w(poly):  # sigma.w : the (1,1)-Gauss stage weight
    return min(v2(a) + j for j, a in slots(poly))


def wV(poly, e=1, h=2):  # the read regrade childW at key X, pair (1,2)
    return min(e * v2(a) + j * h for j, a in slots(poly))


f = sp.expand((X + p**3) * (Phihat**2 + p**3 * X**3))
assert f == X**5 + 24*X**4 + 176*X**3 + 512*X**2 + 1280*X + 2048

# 1. side data (SideReads(i)): gam = 10 exactly at slots {1,3,5}
side = {j: v2(a) + 2 * j for j, a in slots(f)}
assert side == {0: 11, 1: 10, 2: 13, 3: 10, 4: 11, 5: 10}
gam, mu, e_star, g, h_star = 10, 2, 1, 2, 2
assert min(side.values()) == gam and [j for j, v in side.items() if v == gam] == [1, 3, 5]
# pattern digits at stride slots (all odd cofactors -> digit 1 in F_2): Ranch = 1+z^2+z^4 = psi^2
z = sp.symbols('z')
psi = sp.Poly(z**2 + z + 1, z, modulus=2)
Ranch = sp.Poly(z**4 + z**2 + 1, z, modulus=2)
q, r = sp.div(Ranch, psi**2)
assert r == sp.Poly(0, z, modulus=2) and q == sp.Poly(1, z, modulus=2)  # ord_psi = mu = 2, vtxPoly = 1
a_anchor = (1 - 0 * gam) // e_star  # hAnchor: e.a = s0 - t.gam, s0 = 1, t* = 0
assert a_anchor == 1

# 2. Phihat-development
q1, B0 = sp.div(f, Phihat, X)
q2, B1 = sp.div(q1, Phihat, X)
B2, rest = sp.div(q2, Phihat, X)[1], sp.div(sp.div(q2, Phihat, X)[0], Phihat, X)
assert sp.expand(B2 - (X + 16)) == 0 and B1 == -384 and sp.expand(B0 - (512*X + 4096)) == 0

# 3. V4-(VERTEX) at the regrade
G_V = {j: wV(b) + j * (e_star * g * h_star) for j, b in [(0, B0), (1, B1), (2, B2)]}
assert G_V == {0: 11, 1: 11, 2: 10}
assert wV(f) == gam and wV(B2) == gam - mu * e_star * g * h_star == 2

# 4. clause (vi): frame digit of B2 vs vtx -- both are zbar^1 (frame-min of X+16 at
#    inner slot 1: position 1*sigma.s - sigma.t*(...) = 1; vtx exponent a - mu*mhat = 1,
#    vtxPoly = 1). Digit equality holds; no weight content.
frame_vals_B2 = {j: v2(a) + j for j, a in slots(B2)}
assert frame_vals_B2 == {0: 4, 1: 1}  # min at inner slot 1 alone => sigma.R(B2) = z^1
assert a_anchor - mu * 0 == 1        # mhat = -t*.h*.g = 0 at t* = 0

# 5. the violation: sigma'.w(B2) = e*.sigma.w(B2) = 1 < 2 = the kernel's target
assert w(B2) == 1 and e_star * w(B2) < gam - mu * e_star * g * h_star + 1

# 6. SideReads(iii) is the sole blocker: frame-min of f = slot 5 alone (monomial)
frame = {j: v2(a) + j for j, a in slots(f)}
m = min(frame.values())
assert [j for j, v in frame.items() if v == m] == [5]

print("R3b countermodel VERIFIED: all six checks pass.")
print("  side values:", side, "| G_V:", G_V)
print("  sigma.w(B2) =", w(B2), "< target =", gam - mu * e_star * g * h_star,
      "= wV(B2) =", wV(B2))
print("  frame-min slots of f:", [j for j, v in frame.items() if v == m],
      "(SideReads(iii) demands {1,3,5})")
