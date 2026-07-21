# WILD_WAVE1_BLUEPRINT — first certified wild densities in the capstone menu

**Date: 2026-07-21. Directive (Asvin, 2026-07-21): formalize WILD-case uniformity conditional on
the Montes paper — paper-stated results importable as axioms under the standing faithfulness
discipline. Task selection delegated; this blueprint is the chosen package.** Successor to
`M9_REBASE_BLUEPRINT_2026-07-19.md` (complete). Grounded in the 2026-07-21 two-agent survey
(wild-assets map + Montes-citation inventory).

## §0. The load-bearing clarification (the "self-loop" homonym)

Two different objects share the name:
- **`ClassifierBridgeFiber.Tselfloop`** (misnomer): single-Newton-slope, all-μ=1
  (separable-residual), CHILDLESS, terminating shapes. Their counting limits are **PROVED**
  (`hnode_selfloop_over_Bclassify_R`, `hnode_selfloop_general`), *including genuinely wild
  ramification* (e.g. e=2 at p=2). Fiber characterization proved (`classify_eq_selfloop_iff`).
- **The recursive μ≥2 self-loop cell** (`Drainage.selfLoopCell`): the genuine wall. Five per-depth
  count routes REFUTED (`SELFLOOP_GENERALK_WALL.md`); the missing content is
  measure-theoretic (×q residue-translate equidistribution = Denef `AX_cellRecursion`), NOT
  Montes-paper-stated. Its `SelfLoopHNode` stays an honest hypothesis.

Consequence: **wild-stratum densities are certifiable NOW** by routing the terminating family into
the capstone menu; only the per-type H-tower resummation and exhaustiveness stay behind the wall.

## §1. Wave-1 goal and honest scope

**Goal.** Extend the σ-keyed capstone menu so ramified (wild) types get non-empty menus built from
the PROVED terminating order-1 shapes, and re-discharge the capstone chain — producing the first
machine-checked, non-vacuous, σ-keyed WILD density values in `montes_unconditional`.

**Scope (stated in every relevant docstring):**
- Covered: **constant-e ramified types** σ = {(e,f₁),…,(e,f_k)} with e ≥ 2, e·Σfᵢ = n — one
  CANONICAL stratum per σ (the minimal-H single-slope stratum: slope −H/n with
  e = n/gcd(H,n), all-μ=1 residual with parts (fᵢ); minimal admissible H). The certified value is
  the density of THAT decided stratum — the leading term of the type's density, not its H-tower sum.
- NOT covered (documented, unchanged): the per-type tower resummation across all H (the recursive
  self-loop wall / `countPivot` fixpoint); mixed-e types (multi-slope — provably not a single
  `omCount` menu shape, product form only, `PathShapeMultiSideTree`); order ≥ 2; exhaustiveness.

**No new axiom in Wave 1.** The σ-keying is definitional (`typeOfW` reads (e, f-parts) off the
shape payload); the counting legs are banked theorems. The Montes-paper axiom (`om_tree_unique`,
GMN Thm 3.1 + 3.7 + Cor 3.8 + Lem 3.11(3) + Def 3.10/eq.(37) + Cor 4.19; the project blueprint's
Lemma 7.9, never yet declared) is **Wave 2**: it upgrades the definitional keying to semantic
faithfulness ("fiber members genuinely have type σ"), declared over the genuine per-f tree (NEVER
a free `OMType`/`ClusterShape` — the U4/O1 lesson), with statement-map/mutation/non-vacuity audit
before merge. Explicit non-imports (machine-checked reasons): finite-level drainage (FALSE of the
truncated classifier — `Drainage.tendsto_undecidedDensity` → nonzero constant) and residual
equidistribution (no GMN counterpart — `M6_lemma.md`; must stay derived/proved).

## §2. Design (additive-then-swap, the proven W4 pattern)

New leaf modules; old chain untouched until the swap:
1. **`OM/WildMenu.lean`**: `ramShape n σ : Option ClusterShape` (the canonical Tselfloop literal
   for constant-e ramified σ; `none` otherwise), `typeOfW : ClusterShape → Option
   FactorizationType` (reads (e, f-parts) off head-tree + payload; on the order-0 image agrees with
   `unramType`-keying), `omMenuW n σ := sepShapesOf n σ ∪ (ramShape n σ).toFinset`, plus:
   injectivity of `ramShape` in σ, cross-family disjointness (a `sepShape` is never a `Tselfloop`
   literal — distinct head trees), cross-σ disjointness via `typeOfW`, degree lemma.
2. **`OM/WildMenuPrep.lean`**: the Prep-bank generalization — re-indexing over the enlarged type
   menu (`unramTypeMenu n ∪ constERamTypes n`), the box bound via `sum_card_fibers_le` over the
   union family (fibers of distinct shapes disjoint in the same box), level-≥1 constancy for the
   ramified legs (`DecidedOrder1.freeExp_eq_add_mul` route / the banked `stratumCount_selfloop_R`
   count identity), N=0 edge.
3. **`OM/RealInstanceW.lean`**: `realMW`/`realDW`/`realFW` over `omMenuW` (decided_tendsto legs:
   order-0 `hNodeLimit_unramified` + ramified `hnode_selfloop_over_Bclassify_R`; nonneg for the
   Tselfloop values), capstones `montes_unconditional_w`(+`_exhaustive`) — statements verbatim the
   current ones with `omMenuW` for `omMenu`.
4. **Gates (`OM/RealInstanceWGates.lean`)**: (G1W) **first wild non-vacuity**: certified value
   > 0 at n=2, σ=(2,1) (totally ramified quadratic), realP=2 — expected `(p−1)·p^{−k}` shape,
   through the real instance; (G2W) ramified σ-separation: (2,1) value ≠ unramified values, and two
   distinct ramified σ at some n get distinct values; (G3W) census: all new entries core-only,
   zero regression; (G4W) mutation: ramified-leg `C := 0` copy fails to compile; (G5W) Python brute
   force: ramified-stratum counts at p ∈ {2,3}, n ∈ {2,3} vs the certified values (the minimal-H
   Eisenstein-type strata are directly enumerable).
5. **Swap wave (separate)**: `omMenu := omMenuW` semantics take the canonical names; old order-0-only
   instance quarantined; docs/census updated. THEN Wave 2 (the `om_tree_unique` declaration +
   faithfulness theorem) and Wave 3+ (H-window extension; multi-slope product layer; the wall).

## §3. Risks / open design points (resolve in W1a before W1b)
- `MenuPath`/`ShapesFor` side conditions of the banked legs: the enumerator must emit only shapes
  where they discharge; minimal-H admissibility (gcd condition, all-μ=1 realizability of (fᵢ)
  parts over F_p — note the necklace-count emptiness pattern: some σ may have EMPTY canonical
  strata at small p; gates must include one such honest-empty case).
- `omCount_eq_mul` scope (single-configuration nodes) for the `decomposition` field on Tselfloop
  shapes — verify before wiring `realFW`.
- `decided_mono` for the union: order-0 legs constant for N ≥ 1; ramified legs constant only for
  N ≥ N₀(H) — monotonicity of the SUM needs the max cutoff; check the banked constancy forms.
- `Fact`-instance and `hn : 0 < n` threading as in RealInstanceV2.
