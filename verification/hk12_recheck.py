#!/usr/bin/env python3
"""HK-12: the r3b countermodel RE-CHECK against the REPAIRED (HK-06 wave) semantics.

BP2 (notes/BRIDGE_BP2_HC2K1_2026-07-30.md) unit HK-12, mandated to run BEFORE
HK-52/HK-11a: re-examine the r3b sympy countermodel (verification/
r3b_countermodel_check.py, 2026-07-28) against the (S-a) two-step regrade keying
landed 2026-07-31 (MovesC.RegradeOf + child-pair TransitionCoreL + the RG-2
e-star = 1 recording fence; QUEUE_EXECUTION_2026-07-31.md sec Item 3).

Recap of the r3b instance (all data re-verified by the base script):
  p = 2; sigma = the (1,1)-Gauss stage at Phi = X (w = min_j (v2(a_j) + j));
  root read pair (e*, h*) = (1, 2), psi = z^2+z+1 (g = 2), Phihat = X^2+4X+16;
  f = (X+8)(Phihat^2 + 8X^3); side gam = 10 at slots {1,3,5}, mu = 2;
  Phihat-development B2 = X+16, B1 = -384, B0 = 512X+4096;
  wV := the (1,2)-slot-min over sigma.w (the read-regrade weight).
  Displayed kernel target at the vertex (V9_K1nonrec's RHS, i = 0):
  strFrame(1) * line_0.at(mu*childWidth) = 1 * (gam - mu*e*g*h) = 2.

THE FIVE RE-CHECK FINDINGS (each asserted below):

  F1 (RegradeOf layer does NOT exclude the data). RegradeOf sigma 1 2 sigmaV
     pins sigmaV.w as the (1,2)-slot-min over sigma.w — the value is FORCED
     (sigmaV.w = wV); every RegradeOf clause holds on the r3b data. BP2's
     "Expected: NO (its would-be sigma' fails the sigmaV residual laws)" is
     answered NOT-EXCLUDED at this layer: the D.7(i)-(v) sigmaV residual laws
     were never ratified (B2-FINAL pass-8 rejection) and are NOT in RegradeOf.
     Any exclusion must come from TransitionCoreL/SideReads-at-read-1
     inhabitation — not decidable numerically here.

  F2 (THE CURE at child pair e' = 1). Under (NEW), sigma'.wPrev = sigmaV.w
     (child_wPrev lands on the REGRADE, not the parent), so
     sigma'.w(B2) = e' * sigmaV.w(B2) = 1 * wV(B2) = 2 = the displayed target.
     The r3b countermodel NO LONGER violates the kernel conclusion at e' = 1:
     the re-key routes AROUND the bottom-window law (R3b DISSOLVES for V9's
     steep legs at unramified child pairs).

  F3 (HK-11a's DISPLAYED law stays refuted, and is no longer the right
     target). HK-11a as written in BP2 claims sigma'.wPrev(B mu) =
     nu_i.e * sigma_i.w(B mu). On the r3b data: sigma'.wPrev(B2) = wV(B2) = 2
     while nu_i.e * sigma.w(B2) = 1. STILL FALSE — but V9's conclusion never
     consumes it: the needed vertex value is sigmaV.w(B2) = gam - mu*e*g*h,
     which is V4-(VERTEX) at the recorded regrade (+ R3a anchor transport).
     HK-11a must be RE-POINTED at the sigmaV-vertex law; HK-52's forced-window
     recursion is NOT needed for V9's displayed form.

  F4 (THE NEW OBSTRUCTION: the child-pair stretch factor). Stage law
     hStretch + child_e + child_wPrev give, on EVERY (NEW)-coherent
     non-recentering step and every vertex coefficient B mu in C_Phihat:
         sigma'.w(B mu) = nu_{i+1}.e * sigmaV.w(B mu).
     strFrame(i+1) omits nu_{i+1}.e (it is the product of the PARENT-side read
     strides, all 1 under the RG-2 fence), so the DISPLAYED q-form is off by
     exactly nu_{i+1}.e: at a ramified TERMINAL child (nu_{i+1}.e >= 2 is
     recordable — node i+1's own leg never fires; compiled coherent carrier =
     HK23's H2ram at child pair (2,5)) with nonzero vertex value, the displayed
     equality FAILS (4 != 2 on the r3b numbers at e' = 2). All FOUR reopened V9
     sorries (K1/E1box, steep + corner) are TRUE only on the nu_{i+1}.e = 1
     sub-perimeter; at nu_{i+1}.e >= 2 they are FALSE-SUSPECT, residual to a
     full refutation = ReadsOf inhabitation at one ramified-terminal-child
     record (a Block-G-gate-scale build). Lean mechanism leaf:
     lean/LeanUrat/HC2/HK52_stretchGate.lean.

  F5 (INTERIOR-READ DEGENERATION). At i >= 1 with a non-recentering
     predecessor, child_e/child_h pin the frame pair TO the read pair
     (sigma_i.e = nu_i.e = 1 by the fence, sigma_i.h = nu_i.h), and the regrade
     slot-min at the frame pair is IDEMPOTENT at e = 1 (hStretch folds w into
     wPrev): sigmaV.w = sigma_i.w pointwise. Interior non-recentering reads
     carry NO regrade content; genuinely h-steep reads (h* > sigma.h) occur
     only at i = 0 or immediately after recenterings. HK-52's per-slot
     recursion "at sigmaV" is the IDENTITY at interior reads; the honest
     interior content is the frame-pair side structure (HK-08's restatement
     territory).

Run:  python3 hk12_recheck.py    (needs sympy)
"""
import random

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


def w(poly):
    """sigma.w — the (1,1)-Gauss stage weight at Phi = X."""
    return min(v2(a) + j for j, a in slots(poly))


def wpair(poly, e, h):
    """the (e,h)-slot-min over sigma.w at the key X (X-development = slots)."""
    return min(e * (v2(a)) + j * h for j, a in slots(poly))
    # NB at the key X the X-development coefficients are the constants a_j,
    # whose sigma.w is v2(a_j).


# ---- shared r3b data -------------------------------------------------------
f = sp.expand((X + p**3) * (Phihat**2 + p**3 * X**3))
gam, mu, e_star, g, h_star = 10, 2, 1, 2, 2
target = gam - mu * e_star * g * h_star          # strFrame(1)*line0.at(mu*cw) = 2
q1, B0 = sp.div(f, Phihat, X)
q2, B1 = sp.div(q1, Phihat, X)
B2 = sp.div(q2, Phihat, X)[1]
assert sp.expand(B2 - (X + 16)) == 0

sigmaV_w_B2 = wpair(B2, e_star, h_star)          # the FORCED regrade value

# ---- F1: RegradeOf layer does not exclude ---------------------------------
# clause list: Phi/e/h/K/FQ/reps ties (definitional re-dressing), wPrev = sigma.w
# (holds by construction of the regrade witness), IsSlotMinWeight (the forced value).
assert sigmaV_w_B2 == 2                          # slot-min forced: sigmaV.w(B2) = wV(B2) = 2
assert wpair(f, e_star, h_star) == gam           # sigmaV.w(f) = gam (V-frame attained)
print("F1  RegradeOf layer: r3b data NOT excluded (sigmaV.w forced = wV; no residual laws ratified).")

# ---- F2: the cure at e' = 1 -------------------------------------------------
child_w_B2_unram = 1 * sigmaV_w_B2               # hStretch + child_e(=1) + child_wPrev
assert child_w_B2_unram == target == 2
print("F2  CURE at e' = 1: sigma'.w(B2) = 1*sigmaV.w(B2) =", child_w_B2_unram,
      "= displayed target", target, "-- r3b no longer violates the kernel.")

# ---- F3: HK-11a's displayed law stays refuted ------------------------------
hk11a_lhs = sigmaV_w_B2                          # sigma'.wPrev(B2) = sigmaV.w(B2)
hk11a_rhs = e_star * w(B2)                       # nu_i.e * sigma_i.w(B2)
assert w(B2) == 1 and hk11a_lhs == 2 and hk11a_rhs == 1 and hk11a_lhs != hk11a_rhs
print("F3  HK-11a displayed law REFUTED verbatim under (NEW):",
      hk11a_lhs, "!=", hk11a_rhs, "-- and V9 never consumes it (re-point at the sigmaV-vertex law).")

# ---- F4: the child-pair stretch obstruction --------------------------------
e_child_ram = 2                                  # HK23 H2ram's child pair (2,5)
child_w_B2_ram = e_child_ram * sigmaV_w_B2
assert child_w_B2_ram == 4 and child_w_B2_ram != target
print("F4  NEW OBSTRUCTION at e' >= 2: sigma'.w(B2) =", child_w_B2_ram, "!=", target,
      "= displayed target -- the q-form is off by nu_{i+1}.e (FALSE-SUSPECT at ramified terminal children).")

# ---- F5: interior idempotency (sigmaV.w = sigma.w at the frame pair, e = 1) --
random.seed(0)
for _ in range(200):
    deg = random.randint(0, 6)
    poly = sum(random.randint(-2**10, 2**10) * X**j for j in range(deg + 1))
    if poly == 0 or sp.Poly(poly, X).all_coeffs()[0] == 0:
        continue
    # frame pair of the Gauss stage is (1,1); the interior regrade reads (1, sigma.h) = (1,1)
    assert wpair(poly, 1, 1) == w(poly)
print("F5  interior idempotency: (1, sigma.h)-slot-min over sigma.w == sigma.w on 200 random samples")
print("    (interior non-recentering regrades are weight-identities; h-steep reads live at i = 0 / post-recentering only).")

print()
print("HK-12 VERDICT: r3b is CURED at e' = 1 (F2) but the displayed V9 q-form gains the")
print("nu_{i+1}.e stretch obstruction (F4); HK-11a re-points at the sigmaV-vertex law (F3);")
print("HK-52's sigmaV recursion is the identity at interior reads (F5). Full record:")
print("lean/notes/HK12_RECHECK_2026-07-31.md + the HK52_stretchGate.lean leaf.")
