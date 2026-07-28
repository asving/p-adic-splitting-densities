#!/usr/bin/env python3
"""V10 transition check (2026-07-28, V10 transcription round).

Numeric mirror of the machine-checked finding in
`lean/LeanUrat/HC1/V10_transportWindow.lean` (`V10_forcedKeyWeight` +
`V10_readTransition_incompatible`, both Lean-core), and the disposition of the
r3b countermodel (`r3b_countermodel_check.py`) against the V10-completed chain.

THE FINDING.  For a recorded non-recentering read transition (HistoryCoherent's
non-recentering leg: `TransitionCoreL` keyed at the READ pair (e*, h*) on the READ
lift, plus the child sigma' being a lawful Stage with the recorded Bezout ties
sigma'.s = s*, sigma'.t = t*), with read steepness e*.sigma.h < h* and e*.g >= 2:

  (1) FORCED KEY WEIGHT: the child-stage laws force  h* = e*^2 . g . sigma.h
      (hence e* = 1, t* = 0, s* = 1, h* = g.sigma.h);
  (2) INCOMPATIBILITY: sigma'.R(Phihat) = T(sigma'.s) = T(1)  [hRPhi + the tie]
      while hRlt/hRmul/hS5' through the read lift give
      sigma'.R(Phihat) = C(c^g).T(g * (-t* . sigma.h)) = C(c^g).T(0)
      -- monomials at positions 1 vs 0: NO lawful sigma' exists.

DISPOSITION OF THE R3B COUNTERMODEL (the charged confirmation): the countermodel
(p = 2, (1,1)-Gauss sigma at X, (e*, h*) = (1, 2), t* = 0, s* = 1, g = 2,
psi = z^2+z+1, Phihat = X^2+4X+16) SATISFIES the forced equation (1) -- 2 = 1.2.1
-- and DIES at (2): position 1 != 0.  So it cannot be extended to a full `ReadsOf`
instance, and the V10-completed chain never accepts it.  The route consumes NO
SideReads clause -- in particular NOT clause (iii)'s sigma.R f rendering (the
U31-fenced seam): the fence is respected.

Checks (all asserted):
  1. The countermodel's parameters satisfy the forced-key-weight equation (1).
  2. The read lift's slot weights make the tau-slot strictly deeper than the
     parent-key-power slot in the child grading (the hRlt gate of (2)).
  3. The position clash of (2): s* = 1 != 0 = g * (-t* . sigma.h).
  4. The r3b countermodel script's own six checks still pass (imported run) --
     its pool claims are unchanged; only its EXTENSION to ReadsOf is refuted.

Run:  python3 v10_transition_check.py   (check 4 needs sympy, as r3b does)
"""

# countermodel parameters (r3b_countermodel_check.py)
e_star, h_star, s_star, t_star = 1, 2, 1, 0
g, sigma_h = 2, 1          # psi = z^2+z+1 over F_2; the (1,1)-Gauss frame
# IsReadLift slot weights sigma.w(t_k) = h*(g-k): t_1 = 4 (w=2), t_0 = 16 (w=4)

# 1. the forced key-weight equation (V10_forcedKeyWeight)
assert h_star == e_star * e_star * g * sigma_h, "forced key weight violated"
assert e_star == 1 and t_star == 0 and s_star == 1

# 2. the hRlt gate: sigma'.w(tau) = sigma.w(tau) >= h* + (g-1)sigma.h > h* = sigma'.w(Phi^g)
w_tau_lower = min(h_star * (g - k) + e_star * k * sigma_h for k in range(g))
assert w_tau_lower >= h_star + e_star * (g - 1) * sigma_h
assert h_star + e_star * (g - 1) * sigma_h > g * e_star * sigma_h  # strict at g >= 2

# 3. the position clash (V10_readTransition_incompatible)
pos_hRPhi = s_star                      # sigma'.R(Phihat) = T(sigma'.s)
pos_lift = g * (-t_star * sigma_h)      # = C(c^g) . T(g.(-t*.sigma.h))
assert pos_hRPhi != pos_lift, "no clash?!"
assert (pos_hRPhi, pos_lift) == (1, 0)

# 4. the r3b countermodel's own checks are unchanged (pool claims intact).
#    Needs sympy (as r3b does); SKIPPED (environmental) when unavailable.
import subprocess, sys, os
_r3b = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "r3b_countermodel_check.py")
r = subprocess.run([sys.executable, _r3b], capture_output=True, text=True)
if r.returncode == 0:
    check4 = "pass"
elif "No module named 'sympy'" in (r.stdout + r.stderr):
    check4 = "SKIPPED (no sympy in this interpreter; run `uv run --with sympy`)"
else:
    raise AssertionError("r3b script regressed: " + r.stdout + r.stderr)

print("V10 transition finding VERIFIED: checks 1-3 pass; check 4:", check4)
print("  forced key weight: h* = e*^2.g.sigma.h ->", h_star, "=",
      e_star * e_star * g * sigma_h)
print("  position clash: T(s*) at", pos_hRPhi, "vs C(c^g).T(.) at", pos_lift,
      "-> no lawful sigma' over the countermodel; SideReads(iii) not consumed.")
