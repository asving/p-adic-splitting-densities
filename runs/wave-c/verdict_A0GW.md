# UNIT A0GW — VERDICT (IN PROGRESS): node A0G-RW, the rational weights

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG13.lean` (NEW).

STATUS: SKELETON LANDED, elaborating with sorries (21 statements type-checked against the
landed corpus on first pass; single fix pending: classical `DecidableEq` for
`fieldPattern`'s `normalizedFactors`).

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

* §1 exponent calculus (RW0 core): defs LANDED; proofs PENDING (this increment).
* §2 census interface (`UnitPatternCensus`/`PatternCensus` — the carried FF remainder,
  FF2 discharges): stated.
* §3 cone sums (RW1): `coneSum` def landed; summability + general single-face closed form
  (any `b`, unit-class decomposition `h = bt + u`) + all-`b=1` staircase closed form: stated.
* §5 gates: n=2 (3 theorems, vs G51 forms) and n=3 (5 theorems, vs IFC7 §9 forms) SYMBOLIC
  statements landed; by-name recovery `n3_recovery_ram`/`n3_recovery_split` against
  `IFC7.genuineDensity_three_exact` stated.  n=3 needs two additional mixed-denominator
  pair closed forms (to add).
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
Current: skeleton footer prints `sorryAx` (expected mid-unit).
