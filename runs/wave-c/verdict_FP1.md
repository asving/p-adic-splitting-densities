# UNIT FP1 — VERDICT: the cardinality bridge

STATUS FIRST: **★★★ `decidedSliceAt_all` DID NOT FIRE.  The widest honest FP1 form is
LANDED, zero `sorry`: (1) the named remainder is re-expressed as an equivalent PER-GENRE
census interface (`RationalNonloopCensusAt`), with the reduction, the converse, and the
audit iff all proved; (2) FP0's item-4 gap — no injectivity / surjectivity /
product-cardinality theorem for the class-level fold — is CLOSED in binary residue-layer
form: finite-precision Hensel uniqueness, class-level `mulClass` injectivity and
surjectivity on coprime strata, and the exact stratum product count
`#stratum(g₁·g₂) = #stratum(g₁) · #stratum(g₂)` at every finite level.**

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG16.lean` (NEW, 649 lines).
Verification:

    cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG16.lean

Result: **exit 0, zero errors, zero warnings, zero `sorry`**.  All 15 printed
declarations report exactly Lean core `[propext, Classical.choice, Quot.sound]`; the
C.33 cite does NOT occur.  Repo footprint: exactly this file + this verdict; no landed
file edited; no git mutation.

## Re-grounding (what this unit was)

FP0 (`IFCG15.lean`) reduced IFCG14's socket `ClusterRecursionAt m` — hence the ★★★
capstone `decidedSliceAt_all` — to ONE named remainder, `RationalNonloopRemainderAt m`:
the canonical non-loop cell sequence `nonloopBaseSeq O m σ` (= target decided density at
level `M+m` minus the exactly-counted loop image) tends to ONE rational function of `q`
uniformly over every complete DVR.  FP0's audit items 1–4 recorded that the corpus
exports NO finite-level classifier, cell measure, split bijection, or fold count, so the
remainder could not be discharged by assembly.  FP1's charge: build the cardinality
bridge; honest partials (bijection halves, named census gap) sanctioned.

## What landed

### §2–§4: the named per-genre census gap and the audit iff

`RationalNonloopCensusAt m` (the NEW named gap): given the smaller value laws, each
witnessed degree-`m` label has a FINITE, `O`-INDEPENDENT genre bank — rational weight
pairs `w i` (polynomial denominator nonzero + nonzero at every residue cardinality) and
children lists `ch i` with every entry of degree `k < m` — such that at every `(O, π)`:

* exact finite-level partition: `Nat.card (nonloopDecidedSet π m σ M) = ∑ i, C i M`;
* per-genre asymptotics: `C i M / q^(m(M+m)) → w_i(q) · ∏_{children} decidedDensity`.

Proved: `rationalNonloopRemainderAt_of_census` (the reduction: finite bank sum passes to
the limit, children products become rational by the smaller laws, the bank assembles to
one `Polynomial ℚ` pair with both denominator obligations), the converse
`census_of_rationalNonloopRemainderAt` (one-genre bank, empty children), and hence

    rationalNonloopRemainderAt_iff_census (hm : 0 < m) :
      RationalNonloopRemainderAt m ↔ RationalNonloopCensusAt m

— FP0's audit style: the interface is neither weaker nor stronger.  Uniformly:
`uniformNonloopRemainder_iff_census`, and the new widest honest capstone

    decidedSliceAt_all_of_census :
      UniformRationalNonloopCensus → ∀ n : ℕ, DecidedSliceAt n

(through IFCG15's equivalence and IFCG14's assembly).  Value of the exchange: the
obligation is now localized per genre — a future discharge builds the cells from the
strong cover's skeletons (classifier GC0 + cell measure RW0 + cone sums RW1 + census
FF1 + base change CL1) one genre at a time, and everything downstream is already wired.

### §1, §5: the assembly calculus and limit helpers (all reusable, Lean-core)

`exists_ratPair_childProd` (children products of smaller decided densities are ONE
rational function of `q` uniformly over `O`, both denominator obligations),
`exists_ratPair_sum` (ℚ-level common-denominator bank assembly),
`tendsto_decidedSeq_comp` (child counts at any diverging level map converge to the child
density), `tendsto_list_prod` (finite products of convergent sequences).

### §6: finite-precision Hensel uniqueness — FP0 item 4's missing injectivity core

    factor_sub_mem_of_mul_sub_mem :
      A, A', B, B' monic, same degrees, same residual reductions, Ā coprime B̄,
      A·B ≡ A'·B' (mod 𝔪^N)  ⟹  A ≡ A' and B ≡ B' (mod 𝔪^N)

by the classical Newton filtration climb (at each level the corrector satisfies
`Ū·B̄ + V̄·Ā = 0` with degree bounds, so coprimality kills it).  This is the
finite-precision companion of the landed exact `Uniformity.Hensel.monic_factorization_unique`
and was verified absent from the corpus.  Plus the DVR dictionary
`mem_coeffIdeal_pow_iff` (`coeffIdeal (𝔪^t)` membership = `C (π^t)` divisibility).

### §7: the class-level split bijection and THE exact product count

* `mulClass_stratified_inj` — the coprime fold is injective on stratified class pairs
  (INJECTIVITY half, from §6).
* `levelZeroStratum_mul_eq_image2` — over a complete DVR the product stratum is EXACTLY
  the `mulClass` image of the factor strata (SURJECTIVITY half, from the landed
  `Uniformity.Hensel.exists_monic_factorization`).
* `card_image2_mulClass` — the fold image of stratified subsets has exactly the product
  cardinality.
* ★★ `card_levelZeroStratum_mul` — at every level `N ≥ 1` and coprime monic residuals:

      Nat.card (levelZeroStratum O (n₁+n₂) N (g₁·g₂))
        = Nat.card (levelZeroStratum O n₁ N g₁) * Nat.card (levelZeroStratum O n₂ N g₂)

  — the first landed finite-level, MEASURE-PRESERVING split/count bridge into the
  `Coeff` cells: the binary residue-layer instance of exactly the bridge the unit brief
  requested.  (Checked against the corpus: H124c uses stratum cards only in
  inequalities; no prior product law exists — consistent with FP0's audit.)

## Why ★★★ still does not fire

The remaining content of `RationalNonloopCensusAt m` at masses `m ≥ 4` is the NP-layer
(deep-cluster) part of the bridge: FP0's items 1–3 stand — IFCG12's cover is
polynomial-level existence over a `KeyFrame` (no classifier from coefficient classes,
with genuinely subtle loop/non-loop boundary behaviour at finite precision), IFCG13
exports no `q^{-skeletonExp}` cell measure, and the general census interfaces
(`UnitPatternCensus`/`PatternCensus`) have no instances.  §§6–7 close the RESIDUE-layer
(coprime-split) leg; the per-skeleton leg needs the classifier (blueprint rows GC0/RW0),
for which no landed signature exists.  Asserting any unconditional census instance would
have required inventing that classifier or adding an axiom; neither was done.

## Suggested next decomposition (from what §§6–7 make possible)

1. **FP2 (first-layer census):** with `card_levelZeroStratum_mul` + IFCG4's irreducible
   census + the H124c stratum bank, the multi-distinct-residual-point genres of
   `nonloopDecidedSet` (≥ 2 coprime blocks) now have their exact finite counts in reach —
   the n-ary extension of §7 by peeling with `isCoprime_gProd_of_forall`, then the
   decided-refinement (a product class is decided iff each factor class is, via the §6/§7
   bijection + `typeOf_of_residual_coprime`).
2. **The genuinely open leg:** the single-rational-point non-loop genres (recentred
   fractional-slope clusters) — needs the class-level classifier against
   `StrongRealizesSkeletonAt` (GC0) and the `q^{-skeletonExp}` cell measure (RW0).

## AxCheck

15/15 printed declarations: exactly `[propext, Classical.choice, Quot.sound]`.
No new axiom; the C.33 dissection cite does not occur in this file.

## AMENDMENT (2026-08-29, orchestrator, from FP2's dedup pass)

FP2's corpus re-read found that H.102 ALREADY exported `card_levelZeroStratum_mul` /
`bijOn_mulClass`-strength statements; this verdict's §7 claim "no prior product law
exists" is WRONG (the H124c-only search was too narrow). IFCG16's §§6–7 are therefore a
re-derivation, not a first landing — harmless duplication (both Lean-core, both green),
but the novelty claim is retracted. Downstream units should cite H.102's originals or
IFCG16's copies interchangeably.
