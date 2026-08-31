# UNIT VCL — VERDICT: THE SINGLETON-TYPE FIRE CLOSES BOTH CONVOLUTION ROWS AT
`card σ.data ≤ 1` AND ALL THREE MASTERS RECOMPUTE — every visible split/power cell
provably forces `2 ≤ card σ.data` (so `VisCensusLaw g m σ` fires OUTRIGHT at every
singleton type, both genres, every mass); the CELL-SIDE COUNT lands exact at every
finite level (`#vis = Σ_v visDepthMass v − collision`); the triangle re-base closes
(`count ⟸ weight + collision`, both genres); and the CLUSTER BRIDGE lands pure
Lean-core (vis-summed tiling `= q^v·clusters`, drainage tendsto, per-depth ZcURLim
transfer) — while the full ramified fire honestly does NOT close (the cluster
values + summed rationality + collision structure are the exact named remainder,
as RCD/PCD/TBT fenced) (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG60.lean` (920 lines, ZERO sorries,
zero errors, zero warnings; 26 AxCheck footer rows).  **Axiom fence, machine-exact:**
NINE rows pure Lean core `{propext, Classical.choice, Quot.sound}` — ALL of §3's
grading identities (`sum_multCount_eq_sum_visDepthMass`,
`visWeight_eq_sum_visDepthMass`, `powerVisWeight_eq_sum_visDepthMass`) and ALL of §5
(the strata partition, the vis-summed cluster identity, the tiled lower bound, the
gap bound, the drainage tendsto, the ZcURLim transfer).  SIXTEEN rows Lean core +
EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through the two
refinement maps / SDL's casts / IFCG59's masters — never re-consumed): §1's fire
chain, the two slice masters, `card_visGenre_cast`, §4's triangle.  The capstone
master carries B.42 + exactly `Uniformity.Density.Tower.agnprw_termination` (ID12's,
previously declared).  **C.33 and `AX_cellRecursion` do NOT occur.**  New
definitions: only the ℕ counters `visDepthMass`/`genreCollisionTotal` (finite sums of
landed counters — no new trust surface).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG60.lean` (8 increments, each GREEN
before the next; final run: exactly the 26 footprint infos, nothing else); targeted
`lake build Uniformity.ChapI.IFCG60` GREEN (9036 jobs); sanctioned aggregator import
appended after IFCG59's line, aggregator `lake env lean Uniformity/ChapI.lean` GREEN
(exit 0).  NO git operations.

## ★★★ THE HEADLINES

    theorem two_le_card_of_visGenre :                 -- ★★★ THE TYPE-SUPPORT FORCING
      c ∈ visGenreSet g O π m σ M → 2 ≤ Multiset.card σ.data
                                                      -- BOTH genres, one statement
    theorem visCensusLaw_of_card_le_one :             -- ★★★ ROWS 3/4 AT SINGLETON σ
      Multiset.card σ.data ≤ 1 → ∀ g, VisCensusLaw g m σ   -- OUTRIGHT, every mass
    theorem card_visGenre_cast :                      -- ★ THE CELL-SIDE COUNT, EXACT
      (#visGenreSet g : ℝ) = Σ_{v ≤ M+m} visDepthMass g v − genreCollisionTotal g
    theorem decidedSliceAt_all_of_visCensus'' / _of_MASTER''' / capstoneHypotheses_of_MASTER''' :
      -- ★★★ ALL THREE MASTERS RECOMPUTED: EVERY sector row (split, power, leaf)
      -- now carries the guard `2 ≤ Multiset.card σ.data`
    theorem tendsto_visDepth_sub_clusters :           -- ★★ THE CLUSTER DRAINAGE
      (Σ_{c∈vis} pairDepthFiber p c v − q^v·Σ_{c∈vis} #clusters)/q^{m(M+m)} → 0
    theorem zcURLim_visDepth_of_clusters :            -- ★ THE PER-DEPTH RE-BASE
      ZcURLim (cluster census at (p,v)) → ZcURLim (visible depth-mass at (p,v))

## The three charge items, disposition

**(1) THE CELL-SIDE COUNT — landed in its honest exact form.**  The charged identity
`#vis = Σ_v (pairs at depth v)/q^v` is TRUE only with the collision correction: a
cell hit by `k` clusters is counted `k` times by the divided pair mass.  What lands:
* §3 `visDepthMass g v` (the depth-`v` table pair mass on the genre's visible cells)
  with ★ `sum_multCount_eq_sum_visDepthMass` — the weight census IS the depth-graded
  pair census (genre-uniform, Lean-core, exact at every finite level; instances
  `visWeight_eq_sum_visDepthMass`, `powerVisWeight_eq_sum_visDepthMass`), and
  ★ `card_visGenre_cast` — `#vis = Σ_v massᵥ − collision` exactly.
* §5 the `q^v` division where it is exact: ★ `sum_shiftedDepthFiber_vis_eq`
  (vis-summed RCD tiling: shifted pairs at depth `v` `= q^v · clusters`, EXACT),
  ★ `qpow_mul_clusters_le_visDepth` (the tiled lower bound on the true mass),
  ★ `visDepth_add_shiftedSlice_le` (the excess is at most the FULL slice gap — the
  two univ-partition identities `Σ_c pairDepthFiber = #tableSlice`,
  `Σ_c shiftedFiber = #shiftedSlice` run inside), ★★ `tendsto_visDepth_sub_clusters`
  (the gap DRAINS: per table entry, per genre, per depth — KDW's unconditional
  drainage through RCD's slice limit, composed onto `N = M + m`).
* THE URLIM PUSH, honest form: ★ `zcURLim_visDepth_of_clusters` — the per-depth mass
  census rests on the CLUSTER census (the vanishing gap is itself a `ZcURLim`-zero
  family, so no order/sandwich hypotheses needed).  The push does NOT extend to the
  summed census without new input: an infinite sum of per-depth rational values need
  not be a rational function of `q` — asserting `Σ_v` interchange into `ZcURLim`
  would be dishonest and is NOT stated (see the fence).
* Tannery instrument: ★ `sum_card_depthPairSet_eq` — the depth strata PARTITION the
  full pair box at every level (Lean-core), so stratum masses are dominated by total
  mass 1 uniformly.

**(2) THE DEPTH-STRATUM VALUES — honest partial.**  The general-`(n₁,n₂)` per-`v`
box values are the Igusa census and did NOT land (deriving honestly: the classical
`(1−1/q)q^{−v}` is the `(1,1)` law — IFCG56's `card_depthPairSet_one_one`, landed —
but at higher degrees the strata acquire gcd-degree ≥ 2 and higher-contact
configurations, so the per-`v` value is NOT `(1−1/q)q^{−v}`; the box values are
finite objects per `(n₁,n₂,v)` at the N-free level `v+1` by RCD's
`card_depthPairSet_levels`).  What this file adds structurally: the partition
identity above (the summability/domination input) and the reduction of everything
downstream to exactly these box values + the cluster combinatorics.

**(3) FIRE `VisCensusLaw g m σ` at all ramified `(m,σ)` — does NOT close; what fired
instead is the singleton-type axis, which no prior unit had.**
* ★★★ §1: `two_le_card_of_visGenre` — the refinement maps
  (`splitSector_refines_decided` / `powerSectorProper_refines_decided`) hand every
  visible split/power cell a decided factor pair of positive masses with
  `σ₁.data + σ₂.data = σ.data`; positive-mass decided types are nonempty
  (`typeOf_degree` through the new private reader `data_ne_zero_of_decided`).  Hence
  `visGenreSet_eq_empty_of_card_le_one` and the fires:
  ★★★ `visCensusLaw_of_card_le_one` (both genres, every mass, UNCONDITIONAL),
  `visWeightLaw_of_card_le_one`, `powerVisWeightLaw_of_card_le_one`,
  `collisionLaw_of_card_le_one` (all unconditional),
  `splitConvolutionDefectLaw_of_card_le_one`,
  `powerConvolutionDefectLaw_of_card_le_one` (under the `< m` value laws).
  This is the exact analogue for rows 3/4 of TBT's row-5 singleton fire — e.g. the
  totally ramified types `⟨{(m,1)}⟩` and all inert-tower types `⟨{(e,d)}⟩` leave the
  master's convolution premises entirely.
* ★★★ §2: THE MASTERS RECOMPUTED on all three spines —
  `decidedSliceAt_all_of_visCensus''` (PCD/TBT's census spine: the `∀ g, VisCensusLaw`
  premise now guarded by `2 ≤ Multiset.card σ.data`),
  `decidedSliceAt_all_of_MASTER'''` and `capstoneHypotheses_of_MASTER'''` (LSC's
  FC/Eis spine and the capstone form: BOTH defect premises guarded).  After this
  file EVERY sector row of the census master carries the non-singleton guard.
* ★ §4: THE TRIANGLE — `visCountLaw_of_weight_collision`,
  `powerVisCountLaw_of_weight_collision`, `visCensusLaw_of_weights_collisions`:
  with RCD's `collisionLaw_of_visLaws`, any two of {weight census, cell census,
  collision law} give the third — the cell censuses (the master's premises)
  officially rest on the weight censuses (§3-graded, §5-bridged per depth) plus the
  collision structure.

## THE HONEST FENCE (what remains of the convolution row, exactly)

`VisCensusLaw g m σ` at σ ramified AND `2 ≤ card σ.data` (`.split` at `4 ≤ m`,
`.power` at `5 ≤ m`) — NOT fired.  Its content after this file, in named axes:
1. **The cluster censuses per depth** (§5's re-base target): the cluster carrier
   lives at the N-free shifted level; its values need the general `(n₁,n₂)` box
   counts (Igusa genre) AND which visible cells the clusters land on.
2. **The summed rationality across depths**: `Σ_v` of per-depth rational limits into
   ONE rational function — the geometric structure in `v` (TBT's resultant pin
   `v = h·d·(m − e'·d)` predicts the ladder constants); the domination input is
   landed (`sum_card_depthPairSet_eq` + disjointness), the rationality is not.
3. **The collision structure** (B.42's block-grouping genre): §4 shows it is
   EXACTLY the gap between the weight and count censuses; equivalently the
   per-cell cluster multiplicities (how many ordered `(τ₁,τ₂)`-groupings a visible
   cell admits).
NOT attempted (out of charge): `PowerFullSpanLaw`, `LeafSubfaceLaw`'s remainder, the
general box values, the decidedness-transport converse (TBT's named open).  Nothing
weakened; every consumed statement byte-untouched; zero new axioms.

## File map (`leanfinal/Uniformity/ChapI/IFCG60.lean`, 920 lines)

§0 kit: `natCard_set_eq_card_filter` (private copy), `natCard_eq_sum_fiber_of_mem`
(the T-indexed fiber spine, new), `toFinset_card_eq_natCard` (private copy),
`data_ne_zero_of_decided` (private) ·
§1 ★★★ `two_le_card_of_visGenre`, ★★ `visGenreSet_eq_empty_of_card_le_one`,
★★★ `visCensusLaw_of_card_le_one`, `splitSectorVis_eq_empty_of_card_le_one`,
`powerSectorProperVis_eq_empty_of_card_le_one`, ★ `visWeightLaw_of_card_le_one`,
★ `powerVisWeightLaw_of_card_le_one`, ★ `collisionLaw_of_card_le_one`,
★★ `splitConvolutionDefectLaw_of_card_le_one`,
★★ `powerConvolutionDefectLaw_of_card_le_one` ·
§2 ★★★ `decidedSliceAt_all_of_visCensus''`, ★★★ `decidedSliceAt_all_of_MASTER'''`,
★★★ `capstoneHypotheses_of_MASTER'''` ·
§3 `visDepthMass`, `genreCollisionTotal`, ★ `sum_multCount_eq_sum_visDepthMass`,
`visWeight_eq_sum_visDepthMass`, `powerVisWeight_eq_sum_visDepthMass`,
★ `card_visGenre_cast` ·
§4 ★ `visCountLaw_of_weight_collision`, ★ `powerVisCountLaw_of_weight_collision`,
★ `visCensusLaw_of_weights_collisions` ·
§5 ★ `sum_card_depthPairSet_eq`, ★ `sum_shiftedDepthFiber_vis_eq`,
★ `qpow_mul_clusters_le_visDepth`, `natCard_shiftedDepthFiber_le_pairDepthFiber`
(private), ★ `visDepth_add_shiftedSlice_le`, ★★ `tendsto_visDepth_sub_clusters`,
★ `zcURLim_visDepth_of_clusters` · AxCheck footer (26 rows).
Imports: Mathlib + IFCG58 + IFCG59 (everything else transitive).  Aggregator: one
import line appended to `Uniformity/ChapI.lean` after IFCG59's (the one sanctioned
touch).

## Design decisions (recorded)

* **The count identity stated WITH the collision correction**: the charge's
  `#vis = Σ_v pairs_v/q^v` counts a `k`-cluster cell `k` times; the honest exact form
  is `#vis = Σ_v massᵥ − collision` (§3) with the `q^v` division per cluster (§5).
  The uncorrected identity is false and was not stated.
* **The summed-ZcURLim interchange deliberately NOT asserted**: `ZcURLim` demands ONE
  rational function of `q`; an infinite sum of per-depth rational values need not be
  rational, so the per-depth transfer (`zcURLim_visDepth_of_clusters`) is the honest
  URLim push, and the summed rationality is fenced as remainder axis (2).
* **The gap ZcURLim trick**: the per-depth transfer needs no order sandwich —
  the drainage tendsto makes the gap family a `ZcURLim` with `n = 0, d = 1`, and
  `ZcURLim.add + .congr` reassemble the mass family (avoids `ZcURLim.sandwich`'s
  ∀-M order hypotheses, which fail below the `2v+1 ≤ N` frame).
* **Genre uniformity via `visGenreSet g` throughout**: §1's forcing, §3's grading,
  §5's bridge are single statements over `VisGenre`, with the landed per-sector
  objects reached by iota-reduction (zero-cost bridges, PCD's design paid off).
* **`natCard_eq_sum_fiber_of_mem` generalized to any covering Finset** (not just the
  image or univ): one spine serves the strata partition (T = range (N+1)), and both
  univ-partition identities (T = univ under a local `Fintype.ofFinite`).

## Repair log (2 error rounds, both mechanical; every theorem landed as designed)

1. Case-arm continuation under-indented after `exact` (PCD's repair-log genre) —
   arm bodies moved to their own lines; `mixDepth_le` missing from the IFCG41 open.
2. `gcongr` on `(A−B)/D ≤ (T−S)/D` decomposed into the false subtrahend comparison —
   pinned the pattern `gcongr ?_ / _` (numerator as ONE hole); `div_add_div_same`
   does not exist in this pin (RDC's log) — `rw [← add_div]`.

## Cross-checks

* The singleton fire is sharp: at `(m, σ) = (5, ⟨{(4,1),(1,1)}⟩)` (LSC's hand-checked
  witness, `card σ.data = 2`) the masters' surviving premise still covers it, as it
  must — no stronger emptiness is available at non-singleton types (visible split
  cells exist there).
* Consistency with TBT: `card_ge_two_of_minFace_not_attained_zero` forces the same
  `2 ≤ card σ.data` on NON-full-span cells of any genre; §1's forcing covers the
  visible split/power cells INCLUDING full-span ones (the refinement maps do not
  need the polygon break) — the two constraints agree where they overlap.
* At unramified σ both §1 fires are implied by the landed unramified emptiness
  (IFCG56/58) — no conflict, strictly new content only at ramified singleton types
  (e.g. `⟨{(m,1)}⟩` totally ramified, `⟨{(e,d)}⟩` mixed towers).
