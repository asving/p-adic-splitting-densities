#!/usr/bin/env python3
"""grb_order2_gate_rev2.py — REVISION-2 gate (G3) for GRB_ORDER2_2026-08-05.md.

Pass-1 critical C1: rev 0's S1.3 claimed the FGMN->project slope rescaling factor
e(mu_r)/E_{i+1} = 1; the corrected display (REVISION 2, (TR-1-corr)) is

    lambda^GMN = -h_i/e_i = -E_i * lambda_r^FGMN,   lambda_r^FGMN = h_i/E_{i+1}

(the E_i = PREVIOUS-level dilation w_i = E_i * mu_{r-1} is the missing factor;
FGMN print lambda_i = h_i/(e_0...e_i) at fgmn.txt:1060).  G3 checks, in exact
rational arithmetic over random clouds (shared abscissas; FGMN ordinates
mu_{r-1}(a_s phi^s) = U_s/E_i vs project/GMN ordinates U_s = w_i-values, both
papers' clouds include the phi-content, fgmn.txt:469 / gmn.txt:1826):

  (a) CORRECTED dictionary: the FGMN cut at parameter lambda_r = h_i/E_{i+1}
      (line L_{-lambda_r} touching from below, fgmn.txt:504/577) selects the SAME
      minimizing slot set as the project side of slope -h_i/e_i on the w_i-cloud.
      PREDICTION: 0 violations.
  (b) REV-0's ratio-1 reading REFUTED: cutting the FGMN cloud at parameter
      h_i/e_i (= |lambda^GMN|, what "factor 1" asserts) selects a DIFFERENT slot
      set for generic clouds whenever E_i > 1, and never differs when E_i = 1.
      PREDICTION: >0 mismatches on the E_i>1 stratum; 0 on E_i = 1.
  (c) exponent identities: E_i*lambda_r == h_i/e_i and E_{i+1}*lambda_r == h_i
      (the S2.1 augmentation scaling — consistency of TR-5/S2 with (TR-1-corr)).
      PREDICTION: exact, all samples.
  (d) augmentation-value agreement (Lemma RESCALE consistency at the step):
      E_{i+1}*(mu_{r-1}(phi_r) + lambda_r) == e_i*w_i(Phi_i) + h_i = gamma_{i+1},
      and on whole developments E_{i+1}*mu_r(f) == min_j(e_i*U_j + j*h_i)
      == w_{i+1}(f).  PREDICTION: exact, all samples.

Preregistered 2026-08-01 (REVISION 2 fold of pass-1), run before the revision
text was finalized.
"""
import random
from fractions import Fraction
from math import gcd

random.seed(20260801)

N = 20000
viol_a = 0          # corrected-dictionary mismatches (predict 0)
mism_b_ram = 0      # rev-0-reading mismatches on E_i > 1 stratum (predict > 0)
mism_b_unram = 0    # rev-0-reading mismatches on E_i = 1 stratum (predict 0)
n_ram = 0
fail_c = 0
fail_d = 0

def argmin_set(vals):
    m = min(vals.values())
    return frozenset(s for s, v in vals.items() if v == m)

for _ in range(N):
    i = random.randint(1, 3)                      # state order i+1 in {2,3,4}
    es = [random.randint(1, 4) for _ in range(i)] # e_0..e_{i-1}
    Ei = 1
    for x in es:
        Ei *= x
    e_i = random.randint(1, 4)
    h_i = random.choice([h for h in range(1, 13) if gcd(h, e_i) == 1])
    Eip1 = Ei * e_i
    lam_fgmn = Fraction(h_i, Eip1)                # printed lambda_r (fgmn:1060)
    lam_gmn_abs = Fraction(h_i, e_i)              # |project/GMN side slope|

    # (c) exponent identities
    if not (Ei * lam_fgmn == lam_gmn_abs and Eip1 * lam_fgmn == h_i):
        fail_c += 1

    # cloud: abscissas 0..n-1 (random subset kept), project ordinates U_s in Z
    n = random.randint(3, 8)
    slots = sorted(random.sample(range(n + 2), n))
    U = {s: random.randint(0, 40) for s in slots}

    # (a) corrected dictionary: same component
    fgmn_cut = argmin_set({s: Fraction(U[s], Ei) + s * lam_fgmn for s in slots})
    proj_cut = argmin_set({s: Fraction(U[s]) + s * lam_gmn_abs for s in slots})
    if fgmn_cut != proj_cut:
        viol_a += 1

    # (b) rev-0 ratio-1 reading: FGMN cut at parameter h_i/e_i
    rev0_cut = argmin_set({s: Fraction(U[s], Ei) + s * lam_gmn_abs for s in slots})
    if Ei > 1:
        n_ram += 1
        if rev0_cut != proj_cut:
            mism_b_ram += 1
    else:
        if rev0_cut != proj_cut:
            mism_b_unram += 1

    # (d) augmentation-value agreement
    W = random.randint(0, 30)                     # w_i(Phi_i) in Z
    gamma = e_i * W + h_i
    if Eip1 * (Fraction(W, Ei) + lam_fgmn) != gamma:
        fail_d += 1
    lhs = Eip1 * min(Fraction(U[s], Ei) + s * (Fraction(W, Ei) + lam_fgmn)
                     for s in slots)
    rhs = min(e_i * U[s] + s * gamma for s in slots)
    if lhs != rhs:
        fail_d += 1

print(f"G3(a) corrected dictionary (lambda^GMN = -E_i*lambda_r): "
      f"{viol_a}/{N} violations (predicted 0)")
print(f"G3(b) rev-0 ratio-1 reading: {mism_b_ram}/{n_ram} mismatches on the "
      f"E_i>1 stratum (predicted >0); {mism_b_unram}/{N - n_ram} on E_i=1 "
      f"(predicted 0)")
print(f"G3(c) exponent identities E_i*lam=h/e, E_(i+1)*lam=h: {fail_c}/{N} "
      f"failures (predicted 0)")
print(f"G3(d) augmentation/RESCALE value agreement: {fail_d}/{N} failures "
      f"(predicted 0)")
ok = (viol_a == 0 and mism_b_ram > 0 and mism_b_unram == 0
      and fail_c == 0 and fail_d == 0)
print("VERDICT: G3", "PASS (corrected TR-1 confirmed; rev-0 reading refuted "
      "on stacked ramification)" if ok else "FAIL")
