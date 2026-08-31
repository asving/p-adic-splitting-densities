# UNIT FP2 — VERDICT: the multi-point genres' exact-count machinery

STATUS FIRST: **The full reduction (`UniformRationalNonloopCensus ⟸ FP2 ∧ single-point
remainder`) did NOT close in this unit.  What LANDED, zero `sorry`, is the complete
EXACT-COUNT layer for the multi-residual-point genres — every finite-level counting
theorem the reduction needs: ★ the decided-refinement (the converse the F-1 fence does
not forbid), ★ the binary per-type count convolution over coprime residual splits, ★ the
census product law in a commutative monoid algebra (the n-ary fold = ring
multiplication), the full UFD primary-pattern layer, ★ THE DOUBLE COUNT
(labelled/unlabelled exchange with the multiplicity factor), and ★ THE EXACT COLLISION
PEEL for distinct-tuple aggregates.  The remaining assembly (fiber lemma, limit calculus,
named remainder, final census) is fully designed with all ingredients landed — recorded
below as the next unit's worklist, with the single-point remainder's final exact shape
displayed.**

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG17.lean` (NEW, 1158 lines,
banked by the orchestrator mid-unit after a 529 interruption).  Verification:

    cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG17.lean

Result: **exit 0, zero errors, zero `sorry`** (~2 min wall; the one heavy declaration,
`VAgg_cons_eq`, carries a local `set_option maxHeartbeats 2000000` — a deep but
terminating `congr` whnf over the monoid algebra, not a loop).  The AxCheck footer prints
8 declarations (§0–§3), all exactly Lean core `[propext, Classical.choice, Quot.sound]`;
the C.33 cite does not occur anywhere in the file (nothing consumes the cover).  The
§4–§6 declarations compile in the same run; extending the footer to them is a one-edit
follow-up (they consume only Lean-core landed inputs + mathlib).

## Re-grounding (what this unit was)

FP0 (`IFCG15`) reduced the campaign's socket to ONE remainder: the canonical non-loop
cell sequence `nonloopBaseSeq` (target decided density at level `M+m` minus the
exactly-counted loop image) tends to one rational function of `q` uniformly over every
complete DVR.  FP1 (`IFCG16`) re-expressed it as the per-genre census interface
`RationalNonloopCensusAt m` and landed the binary coprime stratum product count.  FP2's
charge: the multi-point genres (residual polynomial with ≥ 2 distinct irreducible
factors) get their exact counts; land the widest honest form + the reduction to a named
single-point remainder.

## What landed (all sorry-free; names in `Uniformity.Density.IFCG17`)

### §1 — the stratum-refined decided count
* `stratDecCount O n σ N g` := #(σ-decided level-`N` classes inside the level-0 stratum
  of `g`) — the refined census cell.
* `mem_residuePatternFinset_of_stratDecCount_ne` — a nonzero refined count forces `σ`
  into the O-INDEPENDENT finite bank `IFCG0.residuePatternFinset n` (the type bank and
  the pattern bank are the same combinatorial object: multisets of positive pairs with
  weighted sum `n`).
* `decidedCount_eq_sum_stratDecCount` — the global decided count partitions over the
  monic residuals (fiberwise along the landed `stratumPoly`).

### §2 — ★ THE DECIDED-REFINEMENT (`exists_decided_factors`)
If `mulClass c₁ c₂` is `σ`-decided then `c₁, c₂` are decided outright, at types with
`σ₁.data + σ₂.data = σ.data`.  **Pure `typeOf_mul` + multiset cancellation — NO Hensel,
NO coprimality, NO completeness, NO strata.**  H.103's F-1 fence blocks recovering the
summands from the sum; it does not block this converse, which is what makes the per-type
refinement of H.102's bijection exact.

### §3 — ★ THE BINARY COUNT CONVOLUTION (`stratDecCount_mul`)
Over a coprime monic residual split, at EVERY finite level `N ≥ 1`:

    #dec_σ(strat(g₁·g₂)) = Σ_{s ∈ powerset σ.data} #dec_⟨s⟩(strat g₁) · #dec_⟨σ.data−s⟩(strat g₂)

via the set-level disjoint decomposition `decidedSet_inter_stratum_mul_eq` (§2 + FP1's
`levelZeroStratum_mul_eq_image2` + H.102's no-precision-loss injectivity).  This is the
per-TYPE sharpening of the H.102/FP1 product count.

### §4 — the type algebra (`TypeAlg := AddMonoidAlgebra ℚ (Multiset (ℕ × ℕ))`)
* `mul_apply_powerset` — product coefficients are powerset convolutions (Multiset
  addition is cancellative + canonically ordered).
* `stratPoly O n N g` — the whole refined census as ONE ring element; `stratPoly_apply`
  (coefficient formula, unconditional); `stratPoly_zero_one` (`stratPoly 0 N 1 = 1`).
* ★ `stratPoly_mul` — `stratPoly (g₁·g₂) = stratPoly g₁ * stratPoly g₂` over coprime
  splits: §3 as a ring identity.  **The n-ary fold over pairwise-coprime residual factors
  is now `prod` in a commutative ring — order-independence and all assignment-indexing
  combinatorics come free.**

### §5 — the primary-pattern layer (UFD bookkeeping over the residue field)
`patternOf g` (multiset of (component degree, multiplicity) pairs via
`normalizedFactors`), `patternOf_pow_mul` (coprime prime-power peel prepends its `(δ,e)`
block), `exists_primary_decomposition` (any component peels off as an exact prime power
times a monic coprime cofactor), `count_patternOf`, `count_normalizedFactors_pow_mul`,
plus the monic/normalized dictionary (`monic_of_mem_normalizedFactors`,
`prod_normalizedFactors_of_monic`, `mem_normalizedFactors_iff_dvd`).

### §5b — ★ THE DOUBLE COUNT (`sum_sigma_fiber_eq`)
With avoidance fibers `fiberFinset K n π A` (monic degree-`n`, pattern `π`, not divisible
by any point of `A`) and `irredFinset K δ`:

    Σ_{p₀ ∈ irred_δ \ A} Σ_{g' ∈ fiber(n', π, A ∪ {p₀})} F(p₀^e · g')
      = (π.count(δ,e) + 1) • Σ_{g ∈ fiber(δe + n', (δ,e) ::ₘ π, A)} F(g)

— the labelled/unlabelled exchange, for ANY target monoid `F`: each target polynomial is
hit once per `(δ,e)`-component.  This is the multiplicity bookkeeping that every genre
census must pay, discharged once and for all.

### §6 — the distinct-tuple aggregates and ★ THE EXACT COLLISION PEEL
Super-blocks `SBlock` (`δ`, exponent list `E`); `tupleFinset` (distinct irreducibles
matching a block system, avoiding `A`); `blockPoly`; the aggregates
`VAgg O N B A = Σ_{distinct tuples} ∏_i blockPoly (t i)` and the single-point aggregate
`SPAgg O N b A = Σ_{p ∈ irred_δ \ A} blockPoly p E`.  Structural theorems:
* `tuple_sum_succ` — the avoidance head-peel (head summed off `A`, tail avoiding
  `A ∪ {head}`), the engine for the fiber lemma's induction;
* `tuple_sum_collision` — a fresh point either misses the tuple or equals exactly ONE
  coordinate of matching degree (no inclusion-exclusion cascade);
* ★ `VAgg_cons_eq` —

      SPAgg b A * VAgg B A = VAgg (cons b B) A + Σ_{j : δ_j = b.δ} VAgg (merge_j B) A

  the EXACT collision peel: it reduces every distinct-tuple aggregate, in finitely many
  ring-identity steps, to products of single-point aggregates — mass is conserved, block
  count strictly drops, merged blocks stay ≤ total mass.

## THE NAMED SINGLE-POINT REMAINDER (the campaign's LAST kernel — final exact shape)

Not yet declared in Lean (see worklist); its content is now pinned by the landed objects.
Two clauses:

**(A) `SinglePointAggregateLaw`** — for every `δ ≥ 1` and nonempty exponent list `E`
(entries ≥ 1) and every data-multiset `s`: there is one rational pair `(num, den)`,
`den ≠ 0`, with, for every complete DVR `O` with finite residue field of cardinality `q`,

    den(q) ≠ 0  ∧  (SPAgg O N ⟨δ, E⟩ ∅) s / q^(δ·(ΣE)·N)  →  num(q)/den(q)   (N → ∞).

**(B) `DeepLinearClusterLaw`** — the loop-corrected top-mass clause: for `4 ≤ m`,
witnessed `σ` of degree `m`, one rational pair with, uniformly over `O` (and `π`),

    [ (SPAgg O (M+m) ⟨1, [m]⟩ ∅) σ.data − q·decidedCount(m,σ,M)·q^{κ_m} ] / q^{m(M+m)}
      →  num(q)/den(q)   (M → ∞)

(the subtrahend is FP0's exact loop-image count `card_range_loopClassN`; the loop image
sits inside the `(X+Cγ)^m` strata by `IFCG3.map_residue_monicPoly_loopMapN`, i.e. inside
exactly the `{(1,m)}` pattern cell).

Everything else about `RationalNonloopCensusAt m` is now finite ring/count bookkeeping
from the landed theorems.  Clause (A) at `e = 1` is Gauss's irreducible census (necklace
polynomial) — known math, δ ≤ 4 instances landed in IFCG4; clause (B) is the recentred
fractional-slope cluster recursion — the genuinely open leg FP1 already named.

## Remaining assembly (all ingredients landed; ~3 lemma groups)

1. **§6b `VAgg_eq_fiber`**: on simple blocks (singleton `E`),
   `VAgg B A = multB B • Σ_{g ∈ fiber(mass, pattern, A)} stratPoly g`.
   Induction on the block count: `tuple_sum_succ` peels the head; `stratPoly_mul`
   (coprimality from avoidance) assembles `blockPoly · stratPoly = stratPoly` of the
   product; `sum_sigma_fiber_eq` exchanges the (point, cofactor) sum for the
   multiplicity-weighted fiber sum; bases `fiberFinset_zero` + `stratPoly_zero_one`.
   (`multB` defined by the recursion `multB (cons b B') = (pattern(B').count b + 1) ·
   multB B'`.)
2. **§7 the `URseq` calculus + `V_tendsto`**: closure of "one rational pair, uniform
   over `O`" under +, ×, −, Finset sums, ℚ-scaling (FP1's §1 style plus subtraction);
   then strong induction on block count through `VAgg_cons_eq` + `mul_apply_powerset`
   propagates clause (A) to every `VAgg` coefficient.
3. **§8 the census**: cells := `nonloopDecidedSet ∩ (patternOf ∘ stratumPoly)⁻¹(π)` over
   the bank `residuePatternFinset m` (partition is `natCard_eq_sum_fiber`, already
   landed); non-`{(1,m)}` cells' counts = fiber sums (loop image disjoint by the
   residual computation); the `{(1,m)}` cell = fiber sum − loop count (clause (B));
   multi-point limits = `(1/multB)`·V-limits; single-block-cell limits = clause (A)
   directly; assemble `RationalNonloopCensusAt m`, then
   `decidedSliceAt_all_of_census` fires the capstone chain.

## Findings

* **DEDUP**: `Uniformity.Density.Induction.card_levelZeroStratum_mul` and
  `bijOn_mulClass` were ALREADY LANDED at H.102 (2026-08-16).  FP1's §7
  `IFCG16.card_levelZeroStratum_mul` re-derives them (verdict_FP1.md's "no prior product
  law exists" is incorrect as stated).  Harmless duplication; FP2 consumes H.102/H.103
  forms where possible.
* **The charge's δ ≥ 5 question — ANSWER: pattern-level identities suffice; no separate
  `I_δ` (necklace) hypothesis is needed at any mass.**  The irreducible-census
  rationality is subsumed in clause (A) (the aggregate over irreducibles of degree δ IS
  the remainder's object); the falling-factorial configuration counts never appear —
  distinctness is handled exactly by the collision peel, and repeated-block symmetry by
  the double count's `count + 1` factor.
* **The F-1 fence is one-sided**: H.103 proved no per-type iff is attachable to
  `decidedAt_mulClass` (the multiset sum doesn't determine its summands).  §2 shows the
  OTHER direction is a theorem: decidedness of the product forces decidedness of the
  factors, with the type-sum constraint.  The census needs only this direction plus
  disjointness over the sub-multiset index — which is why the per-type convolution is
  exact despite the fence.
* Engineering: `AddMonoidAlgebra` is a semireducible `Finsupp` synonym — use
  `AddMonoidAlgebra.ext`, a private finset-sum-apply lemma, and explicit `(α := ...)`
  on `Fin.cons_zero`/`Fin.tail_cons` (dependent-family unification fails otherwise);
  `congr 1` on monoid-algebra sums needs a heartbeat bump (deep whnf, terminates).

## AxCheck

Footer (8 declarations, §0–§3): exactly `[propext, Classical.choice, Quot.sound]` each.
No new axiom; no `sorry`; the C.33 cite does not occur in the file.  Follow-up unit
should extend the footer over §4–§6 when it reopens the file (banked read-only this
unit).
