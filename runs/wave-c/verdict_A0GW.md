# UNIT A0GW — VERDICT (IN PROGRESS): node A0G-RW, the rational weights

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG13.lean` (NEW).

STATUS: FINISHER PASS COMPLETE UNDER THE THREE-ROUND RULE.  Eight of fourteen original
holes are closed; six retain `sorry` with their exact stopping subgoals recorded below.

## Per-hole status

* `coneSum_summable`: STOPPED after three repair rounds; `sorry` retained.  The comparison
  reduces the target to the finite-tuple geometric family, but the successor step timed
  out at `whnf` / `synthesize pending MVars` for `Fin.succFunEquiv`.  The exact remaining
  third-round subgoal was:

      case zero
      x : ℝ
      hx0 : 0 ≤ x
      hx1 : x < 1
      ⊢ Summable fun v => 1

* `loopFactor_eq`: STOPPED after three repair rounds; `sorry` retained.  The reduction
  through `coneSum_single` reached the intended singleton geometric series, but the
  constrained simplifier did not eliminate its `if True` before rewriting the loop
  exponent.  The exact remaining third-round subgoal was:

      q ^ m * (q - 1) *
          ((∑ x ∈ if True then {1} else ∅,
              q⁻¹ ^ skeletonExp (loopSkeleton m) (fun _ => x)) /
            (1 - q⁻¹ ^ (m * (m + 1) / 2))) =
        (q - 1) / (q ^ bigTLoop m - 1)

* `n2_gate_split`: STOPPED after three repair rounds; `sorry` retained.  The specialized
  degree-two single-face and two-degree-one-face cone identities both compile.  After
  substituting them and the loop law, the exact remaining third-round subgoal was:

      ⊢ -1 - q * (-q + q ^ 3)⁻¹ + q ^ 2
            + q ^ 3 * (-q + q ^ 3)⁻¹ = q ^ 2

* `n3_recovery_ram`: CLOSED.  Uses the fifth component of
  `IFC7.genuineDensity_three_exact`, unfolds `PhiR`, and applies `n3_gate_ram` at the
  cast residue-cardinality bound `q ≥ 2`.
* `n3_recovery_split`: CLOSED by the analogous first component and `n3_gate_split`.
* `n2_gate_inert`: CLOSED.  The degree-two irreducible face gives
  `x^5/(1-x^3)`; all loop and geometric denominators are proved nonzero from `q ≥ 2`,
  and the resulting identity closes by `field_simp; ring`.
* `n2_gate_ram`: CLOSED from the denominator-two face formula `x^3/(1-x^3)` with the
  same explicit nonvanishing gates.
* `n3_gate_inert`: CLOSED from the cubic-residual cone `x^9/(1-x^6)` and the mass-three
  loop denominator; all denominators are nonzero for `q ≥ 2`.
* `n3_gate_ram`: CLOSED from the denominator-three unit-class decomposition
  `(x^4+x^6)/(1-x^6)`.
* `n3_gate_linInert`: CLOSED.  Uses `n2_gate_inert`, the `(1,2)` staircase
  `x^12/((1-x^6)(1-x^3))`, its `(2,1)` reverse `x^10/((1-x^6)(1-x))`, and explicit
  nonvanishing gates.
* `n3_gate_split`: CLOSED.  In addition to the preceding cone laws, this proves and uses
  the three-face staircase `x^13/((1-x^6)(1-x^3)(1-x))`; the result is exactly the landed
  split cubic form.
* `coneSum_single`: STOPPED after three repair rounds.  Unit-class decomposition,
  `h = b*t+u`, and the per-class geometric ratio were established on paper, but the
  dependent equivalence between `ConeType [f]` and the filtered unit-class product did
  not elaborate without a large transport proof.  Exact remaining subgoal:

      coneSum x [f] =
        (∑ u ∈ (Finset.Icc 1 f.1).filter (fun u => Nat.Coprime u f.1),
            x ^ skeletonExp [f] (fun _ => u)) /
          (1 - x ^ (f.1 * (faceResDeg f * (faceLen f + 1)) / 2))

* `coneSum_unit_denominators`: STOPPED after three repair rounds.  The affine coefficients
  and all specialized length-two/length-three instances used by the gates now compile,
  but the arbitrary-length staircase equivalence remained.  Exact remaining subgoal:

      coneSum x s = x ^ skeletonExp s (fun k => k.1 + 1) /
        ∏ k : Fin s.length,
          (1 - x ^ ((∑ j ∈ Finset.univ.filter
            (fun j : Fin s.length => k ≤ j), expCoeffD s j) / 2))

* `n3_gate_linRam`: STOPPED after three repair rounds.  The obstruction is exactly the
  two recorded mixed-denominator cone identities, for which neither general closed-form
  theorem above applies:

      coneSum x [((1 : ℕ), rp11), ((2 : ℕ), rp11)]
        = x^10 / ((1-x^6)*(1-x^3))
      coneSum x [((2 : ℕ), rp11), ((1 : ℕ), rp11)]
        = x^6 / ((1-x^6)*(1-x))

  Once substituted, the gate is a routine denominator-safe rational identity.  The exact
  theorem subgoal retained is:

      n3Density 0 (clusterP2 shallow2Ram q) (clusterP3 shallow3LinRam q) q =
        q * (q ^ 3 + q + 1) /
          ((q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1))

No other original holes remain pending.

## Design (fixed, hand-verified before any Lean)

For a skeleton `s` (faces `(bᵢ, patᵢ)` in increasing slope order, IFCG5 bank) at
numerators `h` (IFCG7 `ValidSlopeParams`), the realization cell measure is
`(∏ᵢ N_patᵢ(q)) · q^(−E)` with

    E(s, h) = Σᵢ [ ℓᵢ·Y_{i−1} + bᵢhᵢdᵢ(dᵢ−1)/2 + dᵢ(hᵢ−1)(bᵢ−1)/2 + dᵢhᵢ + ℓᵢ ],
    Y_{i−1} = Σ_{k<i} d_k h_k   (right-tail cumulative height),

doubled affine law `2E = Σ(ℓ_k + d_k) + Σ_k h_k·d_k(2·tail_k + ℓ_k + 1)`; loop pin
`E(loop_m, h) = h·T_m + m` (IFCG3's `q^(1−T_m)` anchor).

HAND VERIFICATION (pre-Lean falsifiers, all passed): (i) the five mass-2 skeleton
measures sum to exactly `q⁻²` (the full recentred box); (ii) cases `(2,(1,1))` (Eisenstein)
and the two-face staircase verified by direct valuation counts; (iii) the assembled n=2
densities from the weights = the landed G51 laws `q/(2(q+1)), q/(2(q+1)), 1/(q+1)`.

## File plan / status

* §1 exponent calculus (RW0 core): defs and proofs CLOSED, including the loop exponent pin.
* §2 census interface (`UnitPatternCensus`/`PatternCensus` — the carried FF remainder,
  FF2 discharges): stated.
* §3 cone sums (RW1): specialized closed forms required by the closed gates are proved;
  the three general statements retain the stops recorded above.
* §5 gates: n=2 inert/ramified CLOSED; split stopped.  n=3 split/linear-inert/inert/ramified
  CLOSED; linear-ramified stopped on the two mixed cone identities.  Both by-name
  recoveries against `IFC7.genuineDensity_three_exact` are CLOSED.
* §4 executable mirror (n=4 vs blueprint §8 table): TODO.
* §6 RW2 package (`RatWeight`, q ≥ 2 denominator gate): structure landed, nonvanish lemma
  stated.

## Recorded remainders (honest boundary)

1. General mixed-denominator multiface closed form (Presburger classes) — single-face +
   all-`b=1` laws cover the symbolic gate; mirror covers m = 4 numerically.
2. Census instances beyond pinned low degrees — the FF2 unit.
3. The formal box-cardinality census tying `skeletonExp` to `MBoxN` level counts — A0G-FP0's
   socket (the loop instance is pinned against IFCG3's landed weight law).

## AxCheck

Target: Lean core only on §1/§3/§5/§6 (cover import is carrier binding only).
Current: the file compiles; declarations downstream of the six retained holes carry
`sorryAx`.  All closed arithmetic/exponent and denominator arguments use Lean core only.
