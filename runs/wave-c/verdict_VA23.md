# UNIT VA23 — VERDICT: THE ANALYTIC AXES OF THE CONVOLUTION ROW CLOSE — the depth
summation (axis 2: Tannery interchange + geometric-tail RATIONALITY) and the
cluster/collision assembly (axis 3: the `q^v`-corrected re-base through VCL's bridge)
are machine-checked end-to-end, so `VisCensusLaw g m σ` at EVERY mass and type, both
genres, now rests on EXACTLY {per-entry geometric CLUSTER values, `min ≥ 2` deep-box
drains, the two collision limits}; the deep-box drain FIRES OUTRIGHT at every mass
split touching 1 (exact geometric envelope `q^{−(V+1)}` via IGV's min = 1 law); both
masters are recomputed on the new base — while the charge's item-3 OUTRIGHT fire
honestly does NOT close (the genre-restricted cluster VALUES and the collision limits
are the exact named remainder) (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG71.lean` (1169 lines, ZERO sorries,
zero errors, zero warnings; 24 AxCheck footer rows).  **Axiom fence, machine-exact:**
TWENTY rows PURE Lean core `{propext, Classical.choice, Quot.sound}` — ALL of §§1–5
(the domination/envelope layer, the Tannery instrument, the geometric-tail value,
the per-entry assembly incl. the cluster transfer, the drain fires) AND — better than
fenced — the ENTIRE weight-census assembly (`zcURLim_visWeight_of_entryGeom`,
`visWeightLaw_of_entryGeom`, `powerVisWeightLaw_of_entryGeom` are Lean-core: the
grading identity they consume is VCL's Lean-core row).  FOUR rows carry exactly the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, inherited through VCL's cast/triangle — never re-consumed): the two census
capstones + the census master; the capstone master adds exactly
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).
**C.33 and `AX_cellRecursion` do NOT occur.**  New definitions: the explicit-witness
reader `ZcVal`, the two family readers `visEntryFam`/`clusterEntryFam` (verbatim the
IFCG60-§5 family shapes), the bundled value Props `VisEntryGeom`/
`VisEntryClusterGeom`, and the named drain `DeepStratumDrain` — hypothesis currency
only, no new trust surface.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG71.lean` (6 increments, each GREEN
before the next; final run: exactly the 24 footprint infos, nothing else); targeted
`lake build Uniformity.ChapI.IFCG71` GREEN (9042 jobs); sanctioned aggregator import
appended after IFCG70's line, aggregator `lake env lean Uniformity/ChapI.lean` GREEN
(exit 0).  IFCG72.lean untouched.  NO git operations.

## ★★★ THE HEADLINES

    theorem tendsto_depthSum_of_env :                 -- ★ AXIS 2a: THE INTERCHANGE
      per-depth limits + partial sums ≤ 1 + M-free vanishing tail envelope ⟹
      Summable L ∧ (Σ_{v ≤ M+m} f v M) → Σ' L        -- pure real analysis
    theorem tsum_of_geom_ratio :                      -- ★ AXIS 2b: THE RATIONALITY
      L eventually geometric (L(v+1) = L v/q^a from v₀) ⟹
      Σ' L = Σ_{v<v₀} L v + L v₀·q^a/(q^a − 1)       -- ONE rational function
    theorem zcURLim_visEntry_depthSum :               -- ★★ THE PER-ENTRY ASSEMBLY
      per-depth ZcVal (nn v, dd v) + POLYNOMIAL geometric ratio
      X^a·(nn_{v+1}·dd_v) = nn_v·dd_{v+1} + DeepStratumDrain n₁ n₂ ⟹
      ZcURLim (depth-SUMMED visible pair census at one table entry)
                                                      -- witness: head + (nn v₀·X^a)/(dd v₀·(X^a−1))
    theorem zcVal_visEntry_of_clusters :              -- ★★ AXIS 3: THE BRIDGE CLOSED
      cluster values ⟹ vis-mass values (VCL's tendsto_visDepth_sub_clusters)
    theorem visCensusLaw_of_clusterGeom_collisions :  -- ★★★ THE ROW'S NEW BASE
      VisEntryClusterGeom (all entries, both genres) + min≥2 drains +
      CollisionLaw + power-collision ZcURLim ⟹ ∀ g, VisCensusLaw g m σ
                                                      -- EVERY mass, EVERY type
    theorem deepStratumDrain_one_right/_left :        -- ★ THE DRAIN FIRES AT min = 1
      DeepStratumDrain 1 n₂ (and n₁ 1) OUTRIGHT       -- exact envelope q^{−(V+1)}
    theorem decidedSliceAt_all_of_clusterGeom / capstoneHypotheses_of_clusterGeom :
      -- ★★★ BOTH MASTERS RECOMPUTED on the new base (other rows byte-identical)

## The three charge items, disposition

**(1) AXIS 2, the summed rationality — CLOSED as an assembly.**  The subtlety VCL
fenced (an infinite sum of per-depth rationals need not be rational) is discharged
in two machine-checked halves: the INTERCHANGE (`tendsto_depthSum_of_env`: Tannery
with an M-free envelope — no q^{−v} pointwise envelope needed; monotone-bounded
partial sums + the deep-box tail suffice) and the RATIONALITY
(`tsum_of_geom_ratio` + the per-entry witness construction: the geometric hypothesis
enters at the POLYNOMIAL level `X^a·(nn_{v+1}·dd_v) = nn_v·dd_{v+1}`, so the summed
value is the single pair `(head + nn v₀·X^a, dd v₀·(X^a − 1))` — uniform in q by
construction, exactly the charge's "finite-shape sum of geometric tails").
Supporting Lean-core layer (§1): `sum_pairDepthFiber_le_card_depthPairSet` (vis
masses under the FULL strata), `card_depthPairSetGE_eq_sum` (GE = Σ exact strata,
hypothesis-free), `sum_card_depthPairSet_le` (partial sums ≤ box), and ★
`sum_pairDepthFiber_vis_tail_le` — THE DEEP-BOX ENVELOPE: the `v > V` tail of the
visible pair census ≤ the N-FREE level-`(V+2)` deep box × the exact cylinder factor
(RCD's GE-cylinder makes it window-independent; the charge's "the tail v > (N−1)/2
is bounded by the deep-box envelope", in its sharpest V-free-choice form).

**(2) AXIS 3, the cluster/collision assembly — CLOSED through IFCG60's bridge.**
`zcVal_visEntry_of_clusters` runs VCL's unconditional drainage
(`tendsto_visDepth_sub_clusters`) at the explicit-witness level, so CLUSTER census
values (the N-free shifted carrier — RCD/CSL's exact `q^v` tiling below half-window
is already inside the landed bridge) feed the whole §4 assembly unchanged
(`visEntryGeom_of_cluster` bundles it).  The collision correction enters exactly
once, through VCL's landed triangle (`visCensusLaw_of_weights_collisions`:
#vis = weight − collision pointwise): the two weight censuses are assembled here
(Lean-core!), the two collision limits are consumed as named hypotheses.

**(3) FIRE `VisCensusLaw` at all ramified multi-σ — does NOT close; what lands is
the complete RE-BASE plus the drain fires.**  The honest blocker (recorded in the
file's fence): GNA's axis-1 values are the FULL-box strata; the assembly needs the
per-depth CLUSTER censuses restricted to the GENRE'S VISIBLE CELLS (the
sector-membership × depth joint census — which visible cells the clusters land on),
and the collision limits (B.42's block-grouping genre).  Both are new content no
landed unit provides; asserting the fire would be dishonest.  What fires instead:
★ `DeepStratumDrain 1 n₂` / `n₁ 1` OUTRIGHT — via ★ `card_depthPairSetGE_one_right`:
the min = 1 deep box is EXACTLY `q^{(1+n₂)L − w}` (IGV's min = 1 law summed through
the additive ℕ-telescope `sum_geom_nat`, no truncated subtraction), so the envelope
is exactly `q^{−(V+1)}`; with `deepStratumDrain_of_min_two`, the drain hypothesis
survives ONLY at `2 ≤ min(n₁,n₂)` mass splits (at m = 4: only (2,2); at m = 5: only
(2,3)/(3,2)).

## THE CENSUS MASTER, RECOMPUTED EXACTLY (charge item 3's "state it exactly")

After this file, `∀ n, DecidedSliceAt n` rests (via `decidedSliceAt_all_of_clusterGeom`,
census spine) on:
1. **The convolution row (rows 3/4), NEW BASE**: at each ramified non-singleton
   `(e ≥ 5, σ)` under the `< e` value laws — (i) `VisEntryClusterGeom g n₁ n₂ σ part`
   for both genres at every admissible mass split/type part (per-depth cluster
   values, geometric in `v` at the polynomial level), (ii) the GLOBAL σ-free
   `DeepStratumDrain n₁ n₂` at `2 ≤ min` (⟺ `Σ_v zed(K,n,v)·q^{−v} = q^{2n}`, GNA's
   value-stack identity — the natural next unit), (iii) `CollisionLaw e σ` + the
   power collision `ZcURLim`.
2. `PowerFullSpanLaw` (row 2 leg), `LeafSubfaceLaw` at non-singleton σ (row 5, LSF/
   SFW's territory), the `e = 4` remainder laws — byte-identical to VCL's master.
On LSC's capstone spine (`capstoneHypotheses_of_clusterGeom`): {ladder/deepTwist
supply, FC_D (`FactorCorrespondenceAt`), `EisFullSpanRemainderLaw` (= EFR's
MixedFaceLaws re-base at composite m — the charge's "r ≥ 2 frames / h ≥ 2 carrier
gap / MixedFaceLaws" live HERE, unchanged by this unit), the row-1 base} + item 1
above + `LeafSubfaceLaw`.  The charge's prediction that the master collapses to
{FC_D, r ≥ 2 frames, h ≥ 2 gap, MixedFaceLaws} presupposed the convolution row's
outright fall; the honest recomputation keeps item 1 as its named residue.

## THE HONEST FENCE (the convolution row's remaining content, exactly)

1. **The genre-restricted per-depth cluster VALUES** (`VisEntryClusterGeom`): finite
   per-`(g, n₁, n₂, part, v)` quantities at the N-free shifted level; need (a) the
   sector-membership census of decided-pair products (which genre the product cell
   falls in, per depth) and (b) the geometric-in-`v` structure (TBT's resultant pin
   `v = h·d·(m − e'·d)` predicts the ladder; GNA's `patRate`/`primo` gives the
   full-box analogue).  GNA's landed values are the full box — the restriction is
   genuinely new.
2. **`DeepStratumDrain n₁ n₂` at `2 ≤ min`** — equivalent to the full-box strata
   masses summing to 1; reachable from GNA's stack via per-primary geometric sums of
   `primo` (Σ_v primo·q^{−v} closed forms), not landed.
3. **The two collision limits** (B.42's block-grouping genre) — unchanged from VCL's
   fence axis (iii).
NOT attempted (out of charge): `PowerFullSpanLaw`, `LeafSubfaceLaw`'s remainder, the
genre-restriction census itself.  Nothing weakened; every consumed statement
byte-untouched; zero new axioms; zero sorries.

## File map (`leanfinal/Uniformity/ChapI/IFCG71.lean`, 1169 lines)

§0 kit: `natCard_set_eq_card_filter`/`natCard_eq_sum_fiber_of_mem` (private copies),
`depthPairSet_eq_empty_of_lt`, `pairDepthFiber_eq_zero_of_lt`, `ZcVal` +
`ZcVal.zcURLim`, `sum_range_split` (private) ·
§1 `sum_pairDepthFiber_le_card_depthPairSet`, `card_depthPairSetGE_eq_sum`,
`sum_card_depthPairSet_le`, ★ `sum_pairDepthFiber_vis_tail_le` ·
§2 ★ `tendsto_depthSum_of_env` · §3 `L_geom_pow` (private), ★ `tsum_of_geom_ratio` ·
§4 `visEntryFam`, `clusterEntryFam`, `DeepStratumDrain`, ★★
`zcVal_visEntry_of_clusters`, ★★ `zcURLim_visEntry_depthSum` ·
§5 `sum_geom_nat` (private), ★ `card_depthPairSetGE_one_right`,
`card_depthPairSetGE_swap`, ★ `deepStratumDrain_one_right`/`_left`,
`deepStratumDrain_of_min_two` ·
§6 `VisEntryGeom`, `VisEntryClusterGeom`, ★ `visEntryGeom_of_cluster`, ★★★
`zcURLim_visWeight_of_entryGeom` (Lean-core), ★★ `visWeightLaw_of_entryGeom`,
★★ `powerVisWeightLaw_of_entryGeom`, ★★★ `visCensusLaw_of_entryGeom_collisions`,
★★★ `visCensusLaw_of_clusterGeom_collisions` ·
§7 ★★★ `decidedSliceAt_all_of_clusterGeom`, ★★★ `capstoneHypotheses_of_clusterGeom` ·
AxCheck footer (24 rows).  Imports: Mathlib + IFCG60 + IFCG61 (everything else
transitive).  Aggregator: one import line after IFCG70's (the sanctioned touch).

## Design decisions (recorded)

* **`ZcVal`, the explicit-witness reader**: `ZcURLim`'s existential witnesses cannot
  carry a cross-depth relation (choice-extracted pairs per v are incomparable), so
  the per-depth value data enters as explicit `(nn v, dd v)` with the geometric
  ratio a POLYNOMIAL identity — the uniform-in-q currency; `ZcVal.zcURLim` recovers
  the existential at each depth.
* **No pointwise q^{−v} envelope needed**: Tannery here runs on monotone-bounded
  partial sums (the strata partition) + the N-FREE deep-box tail (GE-cylinder), so
  the assembly does not wait on stratum-value asymptotics; the ONLY analytic residue
  is the drain (deep box → 0), named and minimized.
* **The drain fires additively**: `sum_geom_nat` states the ℕ-telescope as
  `Σ + q^{K−w} = q^K` (no truncated subtraction), and the deep-box value follows by
  `Nat` cancellation against the partition — subtraction-free throughout.
* **Head + tail as `ZcURLim.add`**: the depth sum splits pointwise at `v₀` (the cap
  vanishing pads the degenerate window), the head is `ZcURLim_sum` of the per-depth
  witnesses, the tail carries the single closed-form witness
  `(nn v₀·X^a, dd v₀·(X^a − 1))` — no sum-of-fractions polynomial gymnastics.
* **Genre uniformity via `visGenreSet g`** end-to-end; the `VisWeightLaw`/
  `PowerVisWeightLaw` instantiations are definitional (iota) — zero-cost, PCD's
  design again.
* **The drain Prop σ-free and global** in the masters — it is a pure box statement,
  so the master's premise shape does not multiply over types.

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. Pin renames: `le_or_lt`→`Nat.lt_or_ge`, `Finset.range_subset`→`_range`,
   `abs_add`→`abs_add_le`, `tendsto_finset_sum`→`tendsto_finsetSum`.
2. `congr 1` on `Nat.card` produced a Type-equality goal — the corpus's
   `congrArg Nat.card (congrArg Set.Elem _)` pattern.
3. `Metric.tendsto_atTop.mp` already yields the existential (no `eventually_atTop`).
4. ℕ-telescope: `omega` sees `q*x` and `x*q` as distinct atoms — orient `pow_succ'`
   first; `residueCard_pos` IS `1 ≤` in ℕ.
5. An unpinned geometric-ratio metavariable in the drain's limit — bind the
   `(1/q)^{V+1}` limit before `congr`; `gcongr` self-discharges its side goal.

## Cross-checks

* The min = 1 deep-box law regression: at `n₂ = 1, L = w` it reads
  `#GE = q^{2w − w} = q^w` — consistent with RDC's `(1,1)` stratum values summing
  to `q^{2w} − (q−1)(q^{2w−1} + ... )`; and the normalized envelope `q^{−(V+1)}`
  matches the classical `P[v(Res) ≥ w] = q^{−w}` at linear pairs.
* The axiom split confirms the design: everything up to and including the WEIGHT
  censuses is Lean-core; B.42 enters exactly where VCL's triangle consumes the
  "every vis cell hit ≥ once" leg (the census capstones), never earlier.
* Consistency with VCL's fence: axes (i)/(iii) survive verbatim as
  `VisEntryClusterGeom`/collision hypotheses; axis (ii) is GONE (this unit).
