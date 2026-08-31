# UNIT RCD — VERDICT: THE DRAINAGE TILING AND THE ROOT-COUNT INSTRUMENTS BOTH LAND, PURE LEAN-CORE — the shifted-decided depth-`v` fiber is machine-checked as `q^v` disjoint `pairNbhd`-clusters; the depth strata are proved N-FREE level-`(v+1)` digit boxes (with the classical `(1−1/q)q^{−v}` law machine-checked at `(1,1)`); CSL's DRAINAGE PREMISE IS CLOSED UNCONDITIONALLY through KDW; and the split front is RE-BASED: `SplitSectorLaw m σ` now rests on the `< m` value laws + ONE named Prop (`VisCountLaw`), with `CollisionLaw`/`StrayLaw` resting on the pair (`VisCountLaw`, `VisWeightLaw`) and FIRED at every `(m, σ)` except `m ≥ 4` ramified (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG56.lean` (1132 lines, ZERO sorries,
zero warnings, zero errors; 28 AxCheck footer rows — EIGHTEEN pure Lean core
`{propext, Classical.choice, Quot.sound}` including EVERYTHING in §§1–4 (the tiling,
the root counts, both drainage-limit theorems) AND the split-front re-base
(`splitConvolutionDefectLaw_of_visCountLaw`, `splitSectorLaw_of_visCountLaw`,
`collisionLaw_of_mass_le_three`, the mass-≤3 emptiness); TEN carry Lean core PLUS
exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through SDL's
`one_le_multCount_of_vis`/`convCount_eq_card_vis_add_totals` and IFCG33's
unramified emptiness — never re-consumed).  The C.33 cites and `AX_cellRecursion`
do NOT occur.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG56.lean` (final: exactly the 28
footprint infos, nothing else); targeted `lake build Uniformity.ChapI.IFCG56` GREEN
(8962 jobs); sanctioned aggregator import appended to `Uniformity/ChapI.lean` after
IFCG55's line, aggregator `lake env lean Uniformity/ChapI.lean` GREEN (exit 0);
IFCG55.lean untouched.  NO git operations.

## ★★★ THE HEADLINES

1. **★★ THE DRAINAGE TILING** (charge 1 — `natCard_shiftedDepthFiber`, §2, Lean-core):
   at exact mixing depth `v` with `2v+1 ≤ N`, the SHIFTED-DECIDED fiber over any
   product class `c` — the pairs whose level-`(N−v)` truncations are
   `(σ₁,σ₂)`-decided, with `mulClass = c` and `mixDepth = v` — has cardinality
   EXACTLY `q^v · #(level-(N−v) truncation image)`.  The mechanism
   (`shiftedDepthFiber_inter_eq_pairNbhd`): each truncation fiber inside the carrier
   IS a `pairNbhd` — CSL's `q^v`-cluster — because truncation agreement at `N−v`
   refines to `π^{v+1}`-congruence (`v+1 ≤ N−v`), while the gap engine pins
   `pairNbhd` members mod `π^{N−v}`; every census attribute (product class, depth,
   shifted decidedness) rides the SAME-LIFT cylinder.  Keyed to RDC's named object:
   `pairDepthFiber_eq_natCard` (cast-free set-currency bridge) and
   ★ `qpow_mul_card_le_pairDepthFiber` (`pairDepthFiber ≥ q^v · cluster-roots`
   at the pinned mass split `m = n₁ + n₂`) — the charge's "tiling where it closes",
   on `pairDepthFiber` itself.
2. **★★ THE DRAINAGE PREMISE, CLOSED UNCONDITIONALLY** (CSL fence item (ii) —
   `tendsto_slice_drainage_of_complete`, §4, Lean-core, NO drainage hypothesis):
   over every complete DVR with finite residue field, the normalized gap between the
   decided depth-`v` table slice at level `N` and its shifted-decided (tiled) part
   tends to 0 as `N → ∞` (`v` fixed).  Mechanism: the gap is covered by the two
   one-sided AMBIGUITY sets (level-`N` decided classes with still-ambiguous
   level-`(N−v)` truncation), whose counts are ≤ `(possibleCount − decidedCount)`
   at level `N−v` refined up (`card_tableSlice_le`), i.e. ≤ `gapSeq(N−v)` after
   normalization — and KDW's unconditional `drainageAt_all` (IFCG52) drains it.
   The shifted carrier EXHAUSTS the census in the limit: nothing about the tiling
   is conditional anymore.
3. **★ THE ROOT COUNTS ARE N-FREE DIGIT BOXES** (charge 2, CSL fence item (i) —
   `card_depthPairSet_levels`/`card_depthPairSetGE_levels`, §1, Lean-core): the
   depth-`v` pair stratum at level `N` is a FULL truncation cylinder over any level
   `L` with `v < L ≤ N` (`depthPairSet_eq_preimage`), so
   `#stratum(N) = #stratum(L)·q^{(n₁+n₂)(N−L)}` — the whole `|Res|`-distribution
   input reduces to the FIXED level-`(v+1)` box counts.  Engine: the SAME-LIFT
   cylinder trick (`mixDepth_proj_eq_iff`: below the cap, `mixDepth = v` reads
   `π^v ∣ Res ∧ π^{v+1} ∤ Res` on ANY lift — no resultant congruences needed).
   ★ THE CLASSICAL VALUE, machine-checked at `(1,1)`
   (`card_depthPairSet_one_one`): the level-`(v+1)` stratum of monic-linear pairs
   counts EXACTLY `(q−1)·q^{v+1}`, i.e. `P[v(Res) = v] = (1−1/q)·q^{−v}` — the
   classical Igusa `|Res|` law as a digit-box count (via
   `resultant_monicPoly_one_one`: the pinned `(1,1)` resultant is the difference of
   constant digits).  Uniform-in-`(n₁,n₂)` values are the named remainder (below).
4. **★ THE SUMMED TILING / LEVEL STABILIZATION** (`card_shiftedSlice`, §3,
   Lean-core, EXACT): the shifted-decided depth-`v` slice at level `N` equals the
   decided depth-`v` slice at level `N−v` times the exact cylinder factor
   `q^{(n₁+n₂)v}` — the decided census's level stabilization, with no error term.
   (Discovered en route: the SUMMED form needs no fiber law at all — it is a pure
   preimage-cylinder identity; the fiber law's `q^v` is load-bearing only per-cell.)
5. **★★ THE RE-BASE OF THE SPLIT FRONT** (charge 3, §5): with the two new named
   Props

       VisCountLaw m σ  := ZcURLim (#splitSectorVis / q^{m(M+m)})
       VisWeightLaw m σ := ZcURLim (Σ_{c ∈ vis} multCount c / q^{m(M+m)})

   the exact identities `collisionTotal = visWeight − #vis` (every vis cell hit ≥
   once — B.42 leg) and `strayTotal = convCount − visWeight` (RDC's decomposition)
   give: ★ `collisionLaw_of_visLaws` (CollisionLaw ⟸ both), ★
   `strayLaw_of_visWeightLaw` (StrayLaw ⟸ weight + `< m` value laws), ★★
   `splitConvolutionDefectLaw_of_visCountLaw` and ★★ `splitSectorLaw_of_visCountLaw`
   — **`SplitSectorLaw m σ` at EVERY mass and type now rests on the `< m` decided
   value laws plus the SINGLE Prop `VisCountLaw m σ`, and this re-base is PURE
   LEAN-CORE** (the defect is `conv − #vis` pointwise; the table law is IFCG38's).
6. **★ FIRST FIRES of the charged Props** (§5): `CollisionLaw m σ` outright at
   `m ≤ 3` (Lean-core!) and at every unramified σ (B.42); `StrayLaw m σ` at `m ≤ 3`
   and unramified σ under the `< m` value laws.  Combined with the re-base:
   **`CollisionLaw`/`StrayLaw` are now fired at every `(m, σ)` except `m ≥ 4`
   ramified, where they are equivalent to the pair (`VisCountLaw`,
   `VisWeightLaw`)** — the census laws' content is now exactly the two
   visible-sector censuses, nothing else.

## THE HONEST FENCE (what remains of the split front, exactly)

`VisCountLaw m σ` and `VisWeightLaw m σ` at `4 ≤ m`, σ ramified — NOT fired here.
Their content after this file:

1. **The discharge toolkit is complete on the PAIR side**: the weight census grades
   through `pairDepthFiber` (RDC's identities), each graded fiber is
   `q^v · (cluster roots)` on its shifted-decided part (headline 1), the shifted
   part exhausts the fiber in the `M → ∞` limit (headline 2, unconditional), and
   the cluster roots live at the N-free level-`(v+1)` boxes (headline 3).
2. **What the two Props still need is CELL-side structure**: which visible cells
   carry how many clusters — the block-decomposition census of the visible split
   sector (B.42's slope-factorization genre: a vis cell's clusters ↔ its ordered
   `(τ₁,τ₂)`-block groupings), plus the per-depth stratum VALUES at general
   `(n₁,n₂)` (the `(1,1)` value is landed; the general fixed-level box counts are
   finite objects per `(n₁,n₂,v)` — the uniform-in-`v` closed form is the Igusa
   rationality), plus the `Σ_v`-interchange (Tannery; the dominating series
   `Σ_v μ_v ≤ 1` is available from the disjointness of the strata — deliberately
   not asserted here).
3. NOT attempted (out of charge): `PowerSectorLaw`, `LeafSectorLaw`, the general
   `(n₁,n₂)` depth-stratum values, the Tannery assembly.

## File map (`leanfinal/Uniformity/ChapI/IFCG56.lean`, 1132 lines)

§0 supply: `pairFactor` (+`_apply`/`_proj`(rfl)/`_surjective`),
`card_preimage_pairFactor` (the pair-cylinder count), `proj_eq_proj_iff`, private
counting spines (`natCard_set_eq_card_filter`, `natCard_eq_sum_image_fiber`,
`natCard_prod_set`, `natCard_le_of_subset_union`) ·
§1 `mixDepth_proj_eq_iff` ★, `le_mixDepth_proj_iff`, `mixDepth_proj_levels`,
`le_mixDepth_proj_levels`, `depthPairSet`/`depthPairSetGE`,
★ `depthPairSet_eq_preimage` (+GE), ★ `card_depthPairSet_levels` (+GE),
`monicPoly_one_eq`, `resultant_monicPoly_one_one`, ★ `card_depthPairSet_one_one` ·
§2 `decidedPairSet`, `shiftedDepthFiber`, ★★ `shiftedDepthFiber_inter_eq_pairNbhd`,
★★ `natCard_shiftedDepthFiber`, `pairDepthFiber_eq_natCard`,
★ `qpow_mul_card_le_pairDepthFiber` ·
§3 `tableSlice`/`shiftedSlice`, `shiftedSlice_eq_preimage`, ★ `card_shiftedSlice`,
`shiftedSlice_subset_tableSlice`, ★ `card_tableSlice_le` ·
§4 ★ `tendsto_slice_drainage` (UV-hypothesis form, `Type*`),
★★ `tendsto_slice_drainage_of_complete` (Type-0, hypothesis-FREE via
`IFCG52.drainageAt_all`) ·
§5 `visWeight`, `VisCountLaw`, `VisWeightLaw`, `collisionTotal_cast`,
`strayTotal_cast`, `visWeight_eq_zero_of_empty`, `collisionTotal_eq_zero_of_empty`,
`splitSectorVis_eq_empty_of_mass_le_three` (Lean-core),
`splitSectorVis_eq_empty_unramified` (B.42 via IFCG33),
★ `collisionLaw_of_visLaws`, ★ `strayLaw_of_visWeightLaw`,
★★ `splitConvolutionDefectLaw_of_visCountLaw`, ★★ `splitSectorLaw_of_visCountLaw`,
★ `collisionLaw_of_mass_le_three`, ★ `strayLaw_of_mass_le_three`,
★ `collisionLaw_unramified`, ★ `strayLaw_unramified` ·
AxCheck footer (28 rows).  Imports: `Uniformity.ChapI.IFCG42` + `IFCG52` only
(SDL/RDC/CSL and the KDW drainage arrive through them).

## Design decisions (recorded)

* **Same-lift cylinder over resultant congruence**: every depth-transport in the
  file reads `mixDepth` conditions off ONE lift shared between levels (a lift of a
  class IS a lift of its truncation), so no `resultant_map_map` congruence is
  consumed anywhere — the transport kit is 4 small iffs.
* **Free-form first, keyed second**: the tiling machinery is stated at free
  `(n₁, n₂, σ₁, σ₂, N, v)` (consumable by any future census unit), with the
  `pairDepthFiber` keying done ONCE, cast-free, by pinning the mass split
  `m = n₁ + n₂` in the statement (`hpm := rfl`) instead of `▸`-transport.
* **Drainage as covering, not partition**: `card_tableSlice_le` bounds the
  shifted-vs-full gap by a 3-set covering (`natCard_le_of_subset_union`) — no exact
  error decomposition needed, since the squeeze only wants an upper bound.
* **Universe seam handled at the statement level**: `tendsto_slice_drainage` is
  `Type*` with `UndecidedVanishes` hypotheses; the Type-0 corollary consumes KDW's
  `DrainageAt` (whose `∀ O : Type` is the corpus convention) — no universe fight.
* **The re-base found a cite-free path**: `SplitSectorLaw ⟸ hDV + VisCountLaw`
  prints PURE Lean core (the B.42 legs sit only in the collision/stray GRADED
  refinement and the vis-nonemptiness genre), so the capstone-path split leg's
  remaining Prop is itself cite-free-consumable.

## Repair log (6 error rounds, all mechanical; every theorem landed as designed)

1. Skeleton (22 decls): compiled FIRST-PASS, zero statement repairs.
2. `rw [h2]` closed a calc step; trailing `ring` → "no goals" (deleted).
3. Prod-eta display trap (KDN #3 genre): `pairNbhd` witnesses typed against
   `(q₁, q₂).1` block `rw` — defeq-retyped `have hb₁' : proj … = q₁ := hb₁` + `show`
   before rewriting.
4. `card_tableSlice_le` under-determined implicits at a bare `have` → named
   `(n₁ := …) (n₂ := …)`; `push_cast at` no-op on a cast-free ℕ-inequality → restate
   the ℝ-form with hmain's exact associativity and `exact_mod_cast`.
5. `Nat.cast_one` needed before `mul_one` (the constant `1` in the collision sum is
   `((1:ℕ):ℝ)`); `Set.ncard_diff` deprecated → `Set.ncard_sdiff`.
6. `(1,1)` instance: `show (1:ℕ) = 1*1` rewrite = Fin-motive failure (deleted —
   never needed); `card_setOf_resOrd_eq` lives in IFCG24's namespace (open added);
   `Nat.lt_succ_self` leaks `v.succ` into exponents (→ `(by omega : v < v+1)`);
   duplicate `card_coeff` rewrite (both occurrences fire at once).
