# UNIT A0GW — VERDICT (IN PROGRESS): node A0G-RW, the rational weights

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG13.lean` (NEW).

STATUS: **NODE LANDED (A0GW4 close-out, 2026-08-29).  ALL SIX RETAINED HOLES CLOSED.
ZERO `sorry`.  AxCheck footer prints PURE LEAN CORE `{propext, Classical.choice,
Quot.sound}` on every printed declaration — all three general cone laws, the loop pin,
all five n=2/n=3 gate families, AND both by-name recoveries against
`IFC7.genuineDensity_three_exact` (no cite appears at all; on top of that, every
`native_decide` in the file — the finisher's landed ones included — was downgraded to
kernel-checked `decide`, so no compiler-trust axioms remain).**  All six theorem
statements byte-unchanged; only proofs and private helpers were added.

## How each hole closed (A0GW4)

* `coneSum_summable`: hand-rolled `consE : ℕ × (Fin r → ℕ) ≃ (Fin (r+1) → ℕ)`
  structure literal (avoids `Fin.succFunEquiv` whnf blowup) + `summable_piGeom`
  induction (`Summable.mul_of_nonneg` with EXPLICIT `f`/`g` — elaborating nonneg
  proofs against the Pi-order `0 ≤ f` implicitly is the whnf trap) + comparison
  `x^E ≤ x^{∑num} = ∏ x^{num k}` through `Summable.subtype`.
* `coneSum_single`: explicit `unitClassEquiv : ↑(unit classes) × ℕ ≃ ConeType [f]`
  (`h = b·t + u`, div/mod roundtrips by omega — omega atomizes variable products) +
  affine shift `E(bt+u) = E(u) + t·A` via `skeletonExp_affine` with the empty-filter
  `expCoeffD [f]` computation + `Equiv.tsum_eq`/`Summable.tsum_prod'`/geometric.
  THE RECORDED WHNF BOMB: a `_` hole in `Summable.mul_left _` — with the constant
  explicit both `rw` and `refine …trans` work instantly.  Standing rule: NO `_` holes
  in Summable-combinator arguments in this file.
* `coneSum_unit_denominators`: `monoPeel : ℕ × M(r) ≃ M(r+1)` (strictly monotone
  positive tuples, `Fin.cons` peel, all roundtrips omega) + `monoGeom` induction
  (`∑ ∏ yₖ^{vₖ} = ∏ᵢ Pᵢ/(1−Pᵢ)`, tail products via the `Finset.prod_filter` +
  `Fin.prod_univ_succ` + `Fin.succ_le_succ_iff` reindex) + val-preserving
  `ConeType s ≃ M` (rfl inverses) + the halved affine law (`expCoeffD` even when
  `b = 1`) + the `Finset.sum_comm'`/`Fin.card_Iic` exchange for the base exponent.
* `loopFactor_eq`: `coneSum_single` at the loop face; unit Finset `{1}` by `decide`;
  `skeletonExp_loopSkeleton` pins `E = T_m + m`; `field_simp` closes the rational
  identity.
* `n2_gate_split`: exactly the n2_gate_inert template + `cone_b1d1_pair` + the
  BOTH-orderings nonvanishing facts (`0 < q³−q` AND `0 < −q+q³` — the recorded
  field_simp stop was the missing commuted form).
* `n3_gate_linRam`: NEW `coneSum_of_reindex` (ℕ² affine-exponent grid ⇒ double
  geometric) + two explicit reindex equivs: `mixedEquiv12 (i,j) ↦ (i+1, 2i+3+2j)`
  with `E = 10+6i+3j` giving `x¹⁰/((1−x⁶)(1−x³))`, and `mixedEquiv21
  (i,j) ↦ (2i+1, i+1+j)` with `E = 6+6i+j` giving `x⁶/((1−x⁶)(1−x))` (both
  hand-verified; the gate checked numerically at q=2: both sides 22/93 before
  formalizing) + the linInert-template algebra (`hP2` cancellation needed
  `linear_combination` + `mul_left_cancel₀`, not linarith).

Verification: `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG13.lean`
— zero errors, zero warnings, 15 `#print axioms` lines all pure Lean core.
The campaign's remaining nodes (CL/AS/DS/ALL) are pure assembly on this file.

Previous live-status record (kept for the log):
* `coneSum_summable`: **CLOSED** (A0GW4).  Hand-rolled `consE : ℕ × (Fin r → ℕ) ≃
  (Fin (r+1) → ℕ)` structure literal (avoids the recorded `Fin.succFunEquiv` whnf
  blowup) + `summable_piGeom` (induction, `Summable.mul_of_nonneg` with EXPLICIT
  `f`/`g` implicits — implicit elaboration against the Pi-order `0 ≤ f` was the whnf
  trap) + comparison `x^E ≤ x^(∑ num) = ∏ x^(num k)` through `Summable.subtype`.
* `coneSum_single`: IN PROGRESS on disk.  `unitClassEquiv : ↑(unit classes) × ℕ ≃
  ConeType [f]` (h = b·t+u) COMPILES, as do the affine-law shift `hshift`
  (E(bt+u) = E(u) + t·A via `skeletonExp_affine` + empty-filter `expCoeffD`), the
  `Equiv.tsum_eq` reindex, `tsum_congr hpt`, and the product summability `hsum2`
  (direct `Summable.mul_of_nonneg` on finite × geometric — do NOT transport through
  `Equiv.summable_iff`, that path whnf-times-out).  Remaining: the
  `rw [Summable.tsum_prod' hsum2 …]` step whnf-times-out — tail kept in a BISECT3
  comment in the file; next angle: `Eq.trans` with an explicitly-typed slice
  summability `have`, avoiding `rw` motive machinery and `_`-holes.
* Remaining four holes untouched so far this pass: `coneSum_unit_denominators`,
  `loopFactor_eq`, `n2_gate_split`, `n3_gate_linRam` (plan: monoGeom induction on
  strictly-monotone tuples; loop/gate algebra; two mixed-denominator cone reindexes
  (1,r)(2,r): E = 10+6i+3j and (2,r)(1,r): E = 6+6i+j — both hand-verified, and the
  linRam gate checked numerically at q=2: both sides 22/93).

Previous finisher status (kept for the record): eight of fourteen original
holes closed; six retained `sorry` with their exact stopping subgoals recorded below.

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
FINAL (2026-08-29, A0GW4): **met, and stronger than target** — the footer prints
`[propext, Classical.choice, Quot.sound]` for `skeletonExp_loopSkeleton`, all three
cone laws, `loopFactor_eq`, all n = 2 and n = 3 gates, and both recoveries
(`n3_recovery_ram`/`n3_recovery_split`); no cite and no `native_decide` compiler-trust
axiom appears anywhere (all decisions kernel-`decide`d).
