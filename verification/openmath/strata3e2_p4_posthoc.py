#!/usr/bin/env python3
"""strata3e2_p4_posthoc.py — POST-HOC classification of the single RED row
of the sealed TWIST-3 probe run (strata3e2_probe.py, seal 76513f8): the P4'
SECONDARY clause "key-divergence criterion" mismatched on 10/24 towers
(observed True, predicted False), while the PRIMARY P4' clause (the
coefficient law gmn3(Phi3)_k == z2^(-theta2*k*e2)*psi2_k) passed 24/24.

ROOT CAUSE (established here, post-run; NOT a sealed prediction): the
sealed criterion kdiv_pred compared the wrong objects twice —
  (a) the observed comparison fp_norm(gco) != fp_norm(psi2) is LITERAL
      polynomial inequality (includes the non-monic LEADING coefficient
      z2^(-theta2*g2*e2)), while
  (b) the sealed formula ranged over k < g2 only (bottom-weighted,
      excluding the leading slot) — so towers whose ONLY visible slot is
      the leading one (g2 = 1 rows R2D/R2F; R2B at p = 3 where the
      interior weights are ord-invisible) came out predicted-False /
      observed-True.
Under the (now measured-exact) coefficient law, the CORRECT displays are:
  LITERAL divergence  <=> exists k <= g2: psi2_k != 0 and
                          z2^(theta2*k*e2) != 1;
  CLASS divergence (monic representatives — the KEY0/ORD-INV notion)
                      <=> exists k < g2: psi2_k != 0 and
                          z2^(theta2*(g2-k)*e2) != 1.
This script recomputes all three per tower and checks:
  (1) corrected LITERAL formula == the run's observed kdiv, 24/24;
  (2) CLASS divergence per tower reported (the ORD-INV-relevant count).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import strata3_probe as S3
from strata3e2_probe import ROSTER3E2, theta2_of

ok = True
nlit = ncls = 0
for kind, p in [("Zp",2),("Zp",3),("Fpt",2),("Fpt",3)]:
    for tag, d0, r0, r1, r2 in ROSTER3E2:
        T3 = S3.Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
        K2, th2 = T3.K2, theta2_of(T3)
        s, d, gco, on, _, _, _ = S3.gmn3(T3, T3.Phi3)
        from grb_order2_check import fp_norm
        observed = fp_norm(K2, gco) != fp_norm(K2, T3.psi2)
        lit = any(not K2["isz"](c)
                  and K2["pow"](T3.z2, th2*k*T3.e2) != K2["one"]
                  for k, c in enumerate(T3.psi2))
        cls = any(not K2["isz"](c)
                  and K2["pow"](T3.z2, th2*(T3.g2-k)*T3.e2) != K2["one"]
                  for k, c in enumerate(T3.psi2) if k < T3.g2)
        sealed = any(not K2["isz"](c)
                     and K2["pow"](T3.z2, th2*k*T3.e2) != K2["one"]
                     for k, c in enumerate(T3.psi2) if k < T3.g2)
        tick = "OK " if lit == observed else "BAD"
        if lit != observed: ok = False
        nlit += lit; ncls += cls
        print(f"{tick} {kind},p={p},{tag}: observed={observed} "
              f"corrected-literal={lit} class-div={cls} sealed-pred={sealed}")
print(f"corrected literal formula matches observed: "
      f"{'24/24 CONFIRMED' if ok else 'MISMATCH'}; "
      f"literal-divergent {nlit}/24, CLASS-divergent {ncls}/24")
