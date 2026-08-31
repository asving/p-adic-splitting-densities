# UNIT SDJ — VERDICT: THE SECTOR × DEPTH JOINT CENSUS RE-BASED ONTO THE
DECIDED-TYPE-PINNED SLICE AND THE COLLISION TOTAL GRADED IN CLUSTER CURRENCY — the
joint-census/cluster bridge is EXACT (`q^v·Σ_c #clusters(c)` over ALL cells `=
#tableSlice(N−v, v)·q^{mv}` — the census over decided × decided at fixed types IS
the assembly's own currency), the row's cluster family splits EXACTLY as
{type-pinned joint census − stray-cluster census} with sector membership entering
ONLY through the strays, per-depth values for those two named censuses (shared
geometric modulus) assemble to `VisEntryClusterGeom` outright, the per-cell
block-grouping decomposition `pairDepthFiber = q^v·#clusters + #late` and the exact
collision identity `collision + #vis = Σ_v visDepthMass` land, weight-mismatched
parts FIRE outright (empty decided sets), and all three masters recompute with the
entry premise trimmed to the WEIGHT-MATCHED parts — while the VALUES of the joint
census and the stray census honestly do NOT land (the conditional gcd-filtration at
fixed decided types + the sector-membership census are the exact named remainder;
GCV's two refuted framings were NOT re-attempted) (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG74.lean` (863 lines, ZERO sorries,
zero errors, zero warnings; 19 AxCheck footer rows).  **Axiom fence,
machine-exact:** FOURTEEN rows PURE Lean core `{propext, Classical.choice,
Quot.sound}` — all of §§1–3 (the joint-census carrier layer, the cluster bridge,
the sector split), the weight-mismatch/type-degree fires, §5's reduction theorem,
and §6's per-cell/per-entry cluster-late layer.  FOUR rows Lean core + EXACTLY the
owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization`
(inherited, never re-consumed): `visEntryClusterGeom_of_card_le_one` (through VCL's
type-support forcing), `genreCollisionTotal_add_card` (through SDL's/PCD's
`1 ≤ multCount` on visible cells), `visCensusLaw_of_clusterGeom_matched`,
`decidedSliceAt_all_of_clusterGeom_matched` (through GCV's masters).  The capstone
master additionally inherits exactly `Uniformity.Density.Tower.agnprw_termination`
(ID12's, previously declared).  **C.33 and `AX_cellRecursion` do NOT occur.**  New
definitions: `strayClusterCount`/`jointSliceFam`/`strayClusterFam`/`lateFiber` —
finite counters and normalized families of landed objects, no new trust surface.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG74.lean`
(9 increments, each GREEN before the next — 6 first-attempt, 3 with one mechanical
repair; final run: exactly the 19 footprint infos); targeted
`lake build Uniformity.ChapI.IFCG74` GREEN; sanctioned aggregator import inserted
after IFCG73's line, aggregator `lake env lean Uniformity/ChapI.lean` GREEN.
IFCG72.lean untouched.  NO git operations.

## ★★ THE HEADLINES

    theorem sum_card_tableSlice :                     -- ★ THE JOINT CENSUS FACTORIZES
      Σ_{v ≤ L} #tableSlice(τ₁, τ₂, L, v) = decidedCount(τ₁)·decidedCount(τ₂)
                                                      -- the "product of decided
                                                      -- counts" side, exact
    theorem qpow_mul_sum_clusterCount_univ :          -- ★★ THE CLUSTER BRIDGE
      q^v · Σ_{ALL c} #clusters(c) = #tableSlice(N−v, v) · q^{(n₁+n₂)v}
                                                      -- the joint census IS the
                                                      -- assembly's currency
    theorem qpow_mul_cluster_split / clusterEntryFam_add_stray :  -- ★★ THE SECTOR SPLIT
      clusterEntryFam g + strayClusterFam g = jointSliceFam      -- EXACT at 2v+1 ≤ N
    theorem visEntryClusterGeom_of_joint_stray :      -- ★★ THE ROW'S CLUSTER AXIS,
      per-depth ZcVal for jointSliceFam + strayClusterFam        -- RE-BASED
        (shared modulus X^a) ⟹ VisEntryClusterGeom g n₁ n₂ σ part
    theorem pairDepthFiber_eq_cluster_add_late :      -- ★ THE BLOCK-GROUPING CENSUS
      pairDepthFiber p c v = q^v·#clusters(c) + #late(c)         -- per cell, exact
    theorem genreCollisionTotal_add_card :            -- ★ THE EXACT COLLISION IDENTITY
      genreCollisionTotal g + #vis(g) = Σ_{v ≤ M+m} visDepthMass g v
                                                      -- the double count, both genres
    theorem visEntryClusterGeom_of_degree_ne :        -- ★ THE WEIGHT-MISMATCH FIRE
      ⟨part⟩.degree ≠ n₁ ∨ ⟨σ.data−part⟩.degree ≠ n₂ ⟹ VisEntryClusterGeom (value 0)
    theorem visCensusLaw_of_clusterGeom_matched / decidedSliceAt_all_of_clusterGeom_matched
      / capstoneHypotheses_of_clusterGeom_matched :   -- ★★ ALL THREE MASTERS,
      -- entry premise trimmed to WEIGHT-MATCHED parts (other premises byte-identical)

## The three charge items, disposition

**(1) THE JOINT CENSUS — the exact statement derived and its structural layer landed;
the VALUES honestly do not.**  The decided-type-pinned depth census turned out to
already have its carrier in the corpus: KDW's `tableSlice(τ₁, τ₂, L, v)` =
`decidedPairSet ∩ depthPairSet` (IFCG56) — no new carrier was invented.  What was
missing and landed here:
* ★ `sum_card_tableSlice` — the depth strata partition the decided box EXACTLY:
  `Σ_{v ≤ L} #tableSlice = decidedCount(n₁, τ₁, L)·decidedCount(n₂, τ₂, L)` (the
  charge's "product of decided counts × conditional depth distribution", exact at
  every level; `mixDepth ≤ L` pins the range).  Lean-core.
* `card_tableSlice_le_card_depthPairSet` — domination by the full depth stratum
  (so GCV's unconditional drain bounds the DECIDED deep tail too).
* ★★ `card_shiftedSlice_eq_sum_fiber` + `qpow_mul_sum_clusterCount_univ` — THE
  BRIDGE: the shifted slice partitions along `mulClass` into the shifted-decided
  fibers; per-cell tiling (KDW's `natCard_shiftedDepthFiber`) and the cylinder count
  (KDW's `card_shiftedSlice`) then give `q^v·Σ_{ALL c} #clusters(c) =
  #tableSlice(N−v, v)·q^{(n₁+n₂)v}` — the cluster census summed over all product
  cells IS the joint census at the shifted level.  Lean-core.
* The CONDITIONAL depth distribution at fixed ramified types (`#tableSlice` values —
  the gcd-filtration story conditioned on decidedness) did NOT land and is the named
  remainder: the mod-π reduction of a decided cell is NOT pinned by its type (e.g. a
  generator `θ = π_L·u` of an `e=2, f=2` field reduces to `X⁴`, not `φ²` — the deep
  tower), so GNA's pattern-graded assembly does not restrict to a sub-sum — exactly
  GCV's refutation, honored as a fence.  What survives of the charged insight is the
  EXACT factorization (`sum_card_tableSlice`) and the exact currency identification
  (the bridge), not the values.

**(2) THE GROUPING — landed as the per-cell cluster/late decomposition + the exact
double-count identity; the multiplicity is (grouping, cluster-root) incidences,
never a per-σ combinatorial constant.**
* ★ `pairDepthFiber_eq_cluster_add_late` (per cell, exact at `2v+1 ≤ N`):
  `pairDepthFiber p c v = q^v·#clusters(c) + #late(c)` — the depth-graded fiber over
  ANY product cell partitions into CSL's `q^v`-clusters plus the new `lateFiber`
  (decided pairs whose shifted truncation is not yet decided — drains by KDW's
  ambiguity bound).  Lean-core.
* ★ `sum_pairDepthFiber_vis_eq_cluster_add_late` (vis-summed form) and
  ★ `pairFiber_eq_cluster_late_deep` (the per-entry grouping decomposition:
  `pairFiber p c = Σ_{2v+1 ≤ N}(q^v·clusters + late) + Σ_{2v+1 > N} pairDepthFiber`
  — the deep remainder NAMED, dominated by GCV's draining deep box).  Lean-core.
* ★ `genreCollisionTotal_add_card` (genre-uniform, exact at every level):
  `genreCollisionTotal g + #vis(g) = Σ_{v ≤ M+m} visDepthMass g v` — the collision
  total is EXACTLY the double count over `(entry, depth, cell)` minus the cell count,
  i.e. exact bookkeeping over the same cluster censuses the row's entry values
  consume.  With `multCount c = Σ_p pairFiber p c` (SDL) each visible cell's
  multiplicity is the number of `(mass split, part)`-groupings × their cluster
  weights — the (1,3)/(2,2)/(3,1) multi-grouping is carried per (p, cluster-root),
  never assumed away.  (B.42 through SDL's/PCD's `1 ≤ multCount` on visible cells.)
* NOT claimed: the charged "grouping multiplicity = a finite combinatorial factor
  per σ over convPairs".  Honest finding: the number of table entries hitting a
  fixed cell is NOT a function of σ alone — it depends on the cell's actual factor
  configuration (which groupings admit decided pairs, and at which depths); the
  exact per-cell object is the incidence decomposition above.  The finite convPairs
  index bounds it, but the exact identity is the honest form.

**(3) FIRES + THE MASTERS — what closes, exactly.**
* ★ `decidedSet_eq_empty_of_degree_ne` (a σ-decided set at the wrong degree is
  EMPTY) ⟹ ★ `visEntryClusterGeom_of_degree_ne`: at every weight-mismatched part
  the entry's cluster family is identically zero and the row's entry premise holds
  OUTRIGHT (witness `(0, 1)`).  Also `typeDegree_add_of_le` (type degrees add along
  a sub-multiset split) ⟹ `visEntryClusterGeom_of_type_degree_ne` (at
  `σ.degree ≠ n₁ + n₂` EVERY part fires).  Lean-core.
* ★ `visEntryClusterGeom_of_card_le_one` — the singleton-type fire of the cluster
  values (VCL's sector emptiness; B.42-inherited).
* ★★ `visEntryClusterGeom_of_joint_stray` — THE REDUCTION: explicit per-depth
  `ZcVal` witnesses for `jointSliceFam` and `strayClusterFam` with ONE shared
  geometric modulus `X^a` from `v₀` on assemble (difference witnesses
  `(nnJ·ddS − nnS·ddJ)/(ddJ·ddS)`) to `VisEntryClusterGeom` — Lean-core.
* ★★ THE MASTERS: `visCensusLaw_of_clusterGeom_matched` (the row),
  `decidedSliceAt_all_of_clusterGeom_matched` (the census master),
  `capstoneHypotheses_of_clusterGeom_matched` (the capstone master) — GCV's masters
  with the cluster-value premise required ONLY at parts with
  `⟨part⟩.degree = n₁ ∧ ⟨σ.data − part⟩.degree = n₂`; all other premises
  byte-identical.  `VisCensusLaw` at ramified non-singleton σ does NOT fire (needs
  the two census VALUES) — honestly not claimed.

## THE CONVOLUTION ROW AFTER THIS FILE (the exact residue)

`∀ g, VisCensusLaw g m σ` at each ramified non-singleton `(e ≥ 5, σ)` under the
`< e` value laws rests on exactly:
1. **The joint-census values**: per-depth `ZcVal` witnesses for
   `jointSliceFam n₁ n₂ ⟨part⟩ ⟨σ.data − part⟩ v` — the normalized
   `#tableSlice(τ₁, τ₂, L, v)/q^{(n₁+n₂)L}` limits — at the WEIGHT-MATCHED parts
   only, with eventual geometric structure in `v` (the conditional gcd-filtration
   at fixed decided types: the deep-tower census).
2. **The stray-cluster values**: matching witnesses for `strayClusterFam` (which
   cluster roots land outside the genre's visible cells — decidedness-transfer /
   sector-membership content), same modulus.
3. **The two collision limits** (`CollisionLaw` + power `ZcURLim`) — now graded
   exactly by `genreCollisionTotal_add_card` + the cluster/late decomposition into
   the SAME cluster censuses plus the draining late/deep masses.
Axes 1+2 feed `visEntryClusterGeom_of_joint_stray` → the matched masters; nothing
else remains of the cluster axis.

## File map (`leanfinal/Uniformity/ChapI/IFCG74.lean`)

§0 kit (private copies: `natCard_set_eq_card_filter`, `natCard_eq_sum_fiber_of_mem`,
`natCard_prod_set`, `toFinset_card_eq_natCard`) ·
§1 ★ `sum_card_tableSlice`, `card_tableSlice_le_card_depthPairSet`,
`decidedSet_eq_empty_of_degree_ne` ·
§2 `card_shiftedSlice_eq_sum_fiber`, ★★ `qpow_mul_sum_clusterCount_univ`,
`strayClusterCount`, ★★ `qpow_mul_cluster_split` ·
§3 `jointSliceFam`, `strayClusterFam`, ★★ `clusterEntryFam_add_stray` ·
§4 `visEntryClusterGeom_of_zero` (private), ★ `visEntryClusterGeom_of_degree_ne`,
★ `visEntryClusterGeom_of_card_le_one` ·
§5 ★★ `visEntryClusterGeom_of_joint_stray` ·
§6 `lateFiber`, ★ `pairDepthFiber_eq_cluster_add_late`,
★ `sum_pairDepthFiber_vis_eq_cluster_add_late`, ★ `pairFiber_eq_cluster_late_deep`,
★ `genreCollisionTotal_add_card` ·
§7 `typeDegree_add_of_le`, ★ `visEntryClusterGeom_of_type_degree_ne`,
★★ `visCensusLaw_of_clusterGeom_matched`,
★★ `decidedSliceAt_all_of_clusterGeom_matched`,
★★ `capstoneHypotheses_of_clusterGeom_matched` · AxCheck footer (19 rows).
Imports: Mathlib + IFCG73 (everything else transitive).  Aggregator: one import
line after IFCG73's (the sanctioned touch).

## Design decisions (recorded)

* **No new joint-census carrier**: the survey found KDW's `tableSlice` IS the
  decided-type-pinned depth census (and `card_shiftedSlice` its level-shift) — SDJ
  adds the partition, the bridge, and the split rather than duplicating carriers.
* **The reduction demands a SHARED geometric modulus `a`**: the difference of two
  eventually-geometric sequences with different moduli need not be geometric, so
  separate moduli would be a dishonest statement; the expected structure has one
  modulus and the hypotheses carry it jointly.
* **The family identity holds only for `2v+1 ≤ M + m`**, so the reduction transports
  values through `Tendsto.congr'` with an `eventually_atTop` window rather than a
  family-level `funext` — no statement weakened.
* **`lateFiber` as an explicit set difference** (decided-at-N but not shifted
  decided) keeps the per-cell decomposition additive in ℕ (no truncated
  subtraction); its drain is KDW's ambiguity bound, noted but not re-packaged.
* **The deep remainder in `pairFiber_eq_cluster_late_deep` is a NAMED range**
  (`2v+1 > N`), not an analytic claim — its drain is GCV's, to be consumed by the
  value unit.

## Repair log (3 mechanical rounds; every theorem landed as designed)

1. `rw [decidedPairSet, natCard_prod_set]` needed the `decidedCount` unfolds
   appended; a dead `sum_congr` block after a defeq-closing `rw` removed.
2. `congr 1` on `Nat.card ↑A = Nat.card ↑B` hits type-level ext when the sets are
   not defeq — replaced by an explicit set-equality `have` + `rw` (and in §3, the
   ℕ-exponent rewrite hit the type-dependency motive trap — RDC's log-4 genre —
   replaced by rewriting the ℝ-power via a standalone `hpow`).
3. `div_eq_div_iff` in this pin takes `≠ 0` (not `<`); `linear_combination` needs
   the ℕ identity cast to ℝ first (`congrArg Nat.cast` + `push_cast`); the ℚ value
   identity must be proved BEFORE casting (field_simp cannot see ℚ-nonzeroness
   through `Rat.cast`); `field_simp` closed it (trailing `ring` dead).

## Cross-checks

* The axiom split confirms the design: the bridge and the split never touch B.42
  (pure counting); B.42 enters exactly at {VCL's sector emptiness, SDL's/PCD's
  visible-hit lower bound, GCV's masters} — all inherited, never re-consumed.
* `sum_card_tableSlice` at `L = 0`: both sides are the full pair box (`mixDepth = 0`
  is the only stratum, decidedness at level 0 degenerate) — consistent.
* The bridge at `v = 0`: `#clusters = #tableSlice(N, 0)` — level-exact injectivity
  of the cluster map at depth 0, coherent with CSL's singleton-neighborhood law.
* GCV's fences: the residual-pattern framing appears NOWHERE (the joint census is
  graded by decided types throughout); no one-cluster-per-cell identity is stated
  (the per-cell decomposition carries the full incidence structure).
