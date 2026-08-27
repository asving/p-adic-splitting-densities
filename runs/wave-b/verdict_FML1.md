# FML1 verdict — lift-side tails (MLIFT-1 general n; MLIFT-2 MSF+SR)

**Unit:** FML1 (FABLE math tier, examples-first), 2026-08-27.  Amends
`docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md` at the `[FML1 2026-08-27]` markers.
Certificate extension: `verification/openmath/h116b4_lift_cert.py` C11–C15 (all previous
checks C1–C10 kept and green); fresh log `runs/wave-b/out_FML1_cert.log`
(`==== ALL CHECKS PASSED ====`, exit 0).  No Lean, battery, or signed statement touched.

## Per-open disposition

| Open | Verdict | What is now proved | What remains |
|---|---|---|---|
| MLIFT-1 (sibling uniformity, n ≥ 4) | **PARTIAL — one level closed, statement reshaped** | **THEOREM U4 (§5.5): U(4\|F) for every target, every frame set, every r, over every DVR.**  Lemma WASH (the convolution engine); Lemma BP/BP′ (§6.2c): the fibre multiset of ω_n is computed from any single fibre point, so MLIFT-1 is EQUIVALENT to a target-free per-base-point statement — the C6/C8 quantifier question is settled.  §5.6 fence: uniformity FAILS for μ = 1 frames (q=3 fibres 9:18), so μ_p ≥ 2 is load-bearing and enters U4's proof at exactly one point (the washer column E_{p,μ−2}). | n ≥ 5.  The identified mechanism is WASH-n (§6.2d route 1: codepth ladders + one-grade-deeper washers; grade-shift pairing conjecture); alternative for large n: CRT route via REM+RES. |
| MLIFT-2 deep part (MSF + SR, n ≥ 3) | **PARTIAL — boundary proved, block reduced** | Lemma MSF-LOW (§6.2d): V_j(D) = V_j(T_x) for j ≤ 2 for ANY map ≡ T_x mod π² — so MSF's genuinely open range is j ≥ 3, matching SCHED-LOW's n ≤ 2 exactly.  Lemma REM (§6.2d): the cofactor block is eliminated — S_n(F) bijects with the child divisibility tower and ω_n is a remainder digit.  Lemma RES: v(Res(P_p,P_p′)) = μμ′min(k,k′) exactly, b-independent (the CRT separation constant). | MSF at j ≥ 3 and SR.  C13 (below) is the sharpest evidence yet; no proof. |

The unconditional H.116b4 count still needs: MLIFT-1 at n ≥ 5, MSF (j ≥ 3) + SR, and MSMITH.

## Evidence upgrades (finite-instance, all green)

* **C12 counterexample hunt came up EMPTY under adversarial design.**  All previous
  uniformity scans were q = 2, where squares are affine (c² ≡ c) — structurally blind to
  the quadratic-residue skew that breaks the μ = 1 fence at q = 3.  Nine complete scans
  (every reachable target class × every level): H1 q3 μ2k1r1 N=6; H2 q3 = CELL-2 all
  targets; H3 q3 μ3 r1; H4 q3 k2 r1 N=6; H5 q5; H6 q2 μ3 r1; H7 q3 r2 (the cell U4's
  proof singles out as quadratic-free — confirmed); X1/X2 reproduce C8.  Zero
  non-uniform buckets.
* **C13**: mixed-secant flags AND truncated Smith lists agree with the terminal tangent
  at ALL grades j < N, every sampled fibre depth, all three cells (359 fibre points) —
  strictly stronger than C10.  Suggests MSF may hold lift-robustly at all grades on
  fibre pairs.
* **C11/C14/C15**: BP pointwise (57,606 pairs), REM bijection + digit histograms exact,
  RES exact on random samples.

## What was tried and honestly remains

The q=3/q=5 hunt was a genuine refutation attempt derived from the proof structure (the
grade-4 quadratic Q̃ = [e₂ − σ²·1_{r=1}]·X^{m−2} mod W); its failure to refute forced the
discovery of the washer mechanism, which became U4.  At n = 5 the classification acquires
cross-level bilinears and codepth-3 directions whose washers pair coefficients with their
quadratics (observed conspiracy, conjectured grade-shift pairing on (1.6)) — stated as
OPEN LEMMA WASH-n, not claimed.  The CRT route (REM + RES + b-independent cokernel) is
recorded with its exact open transfer step.

**OVERALL: PARTIAL** (one new unconditional theorem, U4; both opens reshaped and
reduced; no false closure claimed).
