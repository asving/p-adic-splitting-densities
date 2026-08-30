# UNIT DRN — VERDICT: `DrainageAt n` dissected; σ-free equivalence landed; general-n NOT reachable (named remainder pinned)

**Status: DONE — honest partial, exactly per charge.**
File: `leanfinal/Uniformity/ChapI/IFCG45.lean` — compiles clean (zero errors/warnings),
targeted `lake build Uniformity.ChapI.IFCG45` green (8615 jobs), ALL 8 printed footprints
Lean core `{propext, Classical.choice, Quot.sound}` only. Aggregator import added to
`Uniformity/ChapI.lean` (after IFCG44, sanctioned). IFCG44 untouched.

## §1 THE PIN (charge item 1)

`DrainageAt n` (`Density/Statement.lean:118`):

```
∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ σ : FactorizationType, UndecidedVanishes O n σ
```

`UndecidedVanishes O n σ := Tendsto (gapSeq O n σ) atTop (𝓝 0)` (`GenuineDensity.lean:335`),
`gapSeq = possibleSeq − decidedSeq` = the proportion of level-N coefficient classes with a
σ-lift that are NOT forced. So a2 quantifies **exhaustiveness-in-the-limit of the decided
strata**, per (O, σ): equivalently `genuineDensity O n σ = decidedDensity O n σ` (landed both
directions). NOT per-class eventual decision; NOT directly sum-to-1 (`TotalMassOne` follows
from it).

**What n = 2 used** (`drainage_two`, `Drainage.lean:838`): a degree-2 tangency count making
`undecidedSeq O 2 (2M) → 0`, fed into the n-UNIFORM plumbing `drainage_of_undecided_comp`
(`DensityAPI.lean:213`, CN-11): any `undecidedSeq O n (φ M) → 0` along φ → atTop drains every
σ at that n. **n = 3 is ALSO landed** — `drainageAt_three` (`ChapH/H97b.lean:236`),
unconditional Lean-core, via the H97r4 recursion u(M+3) ≤ q^(2(M+3)) + q⁴·u(M).
⚠ **PROJECT_STATE §4 line 116 ("only `drainageAt_two` exists") is STALE** — please fold in.

## §2 Why `drainageAt_all` is NOT provable from landed machinery (charge item 2, refused half)

* The only landed general-n route is `drainage_of_package` (`ChapH/H98.lean:148`) from
  `∀ n, InductionPackage n`; the induction step (`ChapH/H124c.lean`,
  `inductionPackage_of_clusterRates`) CARRIES `FullClusterRateBound n` — its dischargers are
  the named open gates HYP.36/30/32/33 (+HYP.81 at μ≥3, HYP.82 at n≥8; d≥2 leaf reads
  B-BOX-1). Bases landed: `package_two` (H96), `package_three` (H97b). n ≥ 4 open.
* The IFCG census chain (IFCG0–44 + IFC0–7) was swept declaration-by-declaration
  (fresh-context Explore agent): **ZERO occurrences** of `undecidedSeq`/`undecidedCount`/
  `gapSeq`/`possibleSeq`/`UndecidedVanishes`/`RateSpecies`/`InductionPackage` in the whole
  chain. All 19 conditional headlines conclude `∀ n, DecidedSliceAt n` (the a0 leg —
  decided-side rationality). The genre cover IFCG12 (`finiteGenreCoverAt_strong_all`) is
  exhaustive/disjoint/decreasing over POLYNOMIAL factorization skeletons, never converted to
  a partition touching `possibleSet`. The census partitions (IFCG15/18/20/24/34/40/41/44)
  all intersect with `decidedSet`. IFC6's `menuLawAt_all` lift = hoisting an O-independent
  finite Sym-grid menu witness out of the ∀O binder + content-free A1 label cells — **no
  analogue exists for drainage** (nothing finite to hoist for a vanishing rate).
  So the a0 and a2 fields are genuinely ORTHOGONAL legs; nothing in the census reaches a2.

## §3 What LANDED in IFCG45.lean (namespace `Uniformity.Density.IFCG45`)

1. **Instances** — `drainageAt_zero : DrainageAt 0`, `drainageAt_one : DrainageAt 1`
   (gap levelwise 0; n=0 via new `possibleSet_zero_eq`), + `example` regression pins for
   n = 2 (from `drainage_two`) and n = 3 (`drainageAt_three`). **a2 is now closed at
   n = 0, 1, 2, 3.**
2. **★ The σ-free equivalence (the unit's content).** NEW counting core:
   * `undecidedCount_add_sum_decidedCount_le : undecidedCount O n N + Σ_{σ∈S} decidedCount
     ≤ q^(nN)` — undecided classes (decided for NO type) and per-type decided classes
     (pairwise disjoint) pack disjointly into the level-N box (Sum/Sigma injection extending
     the landed `sum_decidedCount_le` pattern);
   * `undecidedSeq_le_sum_gapSeq` (over any `CoveringMenu`): subtract the packing from the
     landed cover `card_le_sum_possibleCount` — `undecidedSeq ≤ Σ_{σ∈S} gapSeq σ`;
   * `undecided_tendsto_zero_of_vanishes`: per-type drainage ⟹ the scalar rate (menu from
     CN-22 `exists_coveringMenu`; finite sum of draining gaps drains; squeeze).
   * `def UndecidedDrainAt n := ∀ O [same bundle], Tendsto (undecidedSeq O n) atTop (𝓝 0)`
     — σ-FREE; and **`drainageAt_iff_undecidedDrain : ∀ n, DrainageAt n ↔ UndecidedDrainAt n`**
     (← is CN-11 at φ = id; → is the new counting). The σ-quantifier is never the frontier.
3. **Per-degree package bridge** — `drainageAt_of_package : InductionPackage n → DrainageAt n`
   (H.98's ∀n conditional extracted degree-by-degree; its private analytic step replicated
   locally as `tendsto_rateBound_zero'`). Any future `package_n` lands a2 at that n alone.
4. **★ The exact named remainder** — `drainageAt_all_iff_undecidedDrain_from_four :
   (∀ n, DrainageAt n) ↔ (∀ n, 4 ≤ n → UndecidedDrainAt n)`. The capstone's full a2 supply
   IS the σ-free scalar rate at degrees ≥ 4 — nothing more, nothing less.

## §4 Honesty ledger

* `DrainageAt` byte-untouched; no statement weakened; every new theorem uniform in n or an
  explicit instance; the iff makes the reduction lossless in BOTH directions (no strength
  hidden in the named remainder).
* Axioms: Lean core only, machine-printed for all 8 public declarations (footer).
* OPEN, exactly: `UndecidedDrainAt n` for each n ≥ 4 — equivalently (via §3.3 + landed
  `exists_coveringMenu`) an O-uniform `RateSpecies` on `undecidedSeq O n`, which is the
  H.124/`FullClusterRateBound` frontier (HYP.36/81/82, B-BOX-1). No unit currently assigned.

## §5 Next-lane pointers (from the sweep, for whoever takes n ≥ 4)

The one census locus quantitative enough to feed a rate: IFCG41/42's resultant-depth engine —
`natCard_pairNbhd = q^v` (Smith-normal-form/Sylvester, general m) + `liftsFactor_of_not_dvd_resultant`
(depth-v Hensel) + the gap lemmas (`factor_perturbation_gap`, `mulClass_inj_of_coprime`).
Ambiguity lives at deep resultant depth; exact q^v fibers + a Hensel criterion is the right
shape for bounding `undecidedCount O n M` at general n. Also reusable: IFCG38's box-majorant
`card_splitSectorInv_le` (window-pin pigeonhole, doesn't use decidedness) and the
`tendsto_decidedSeq_comp` reindexer (IFCG16:309) as the decided-side twin of CN-11.
