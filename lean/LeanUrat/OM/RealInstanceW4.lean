/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW3
import LeanUrat.OM.MultiSlopeMenu

/-!
# OM/RealInstanceW4 — the Wave-4 MIXED-e real instance (blueprint
`notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md` §2-W4b)

The mixed-e sibling of `OM/RealInstanceW3.lean` over the Wave-4 σ-keyed menu
`MultiSlopeMenu.omMenu4 n K σ = WildMenuW3.omMenuW3 n K σ ∪ (mixedShape n σ).toFinset`: the
whole Wave-3 window menu, PLUS — for mixed-e σ (all side-e's ≥ 2, pairwise distinct; blueprint
§0) — the ONE canonical multi-slope stratum `multiSideLit n (mixedPath σ) (mixedSh σ)`. Per σ
the menu is always ONE family (mixed σ are neither unramified nor constant-e, so their Wave-3
legs are EMPTY — `omMenu4_of_mixed`; non-mixed σ have an empty mixed branch —
`omMenu4_eq_of_not_mixed`).

**The coefficient is `C4`, NOT `omCount`** (unlike every prior wave): on the mixed literal the
density contribution is the PRODUCT over Newton sides of the re-scoped single-side engine
values `omCount (sideSubShape pr shape)` — one multi-side `ClusterShape` cannot carry the
product as a single `omCount` (`PathShapeMultiSideTree` header, candidate (c) refuted). The
count is `stratumCount4`: the GENUINE order-1 `stratumCount1`/`classify1` fiber count on the
mixed leg, the schematic `M8.stratumCount` on the old legs.

**Honest scope (blueprint §0/§3, stated on every capstone).** The mixed menu covers, per
mixed-e σ, EXACTLY ONE canonical stratum (minimal height k = 1 per side, ascending-`e`
steepest-first order, all-μ=1): the certified mixed value is the density of THAT decided
stratum — the leading term of the type's density, NOT any tower resummation. Constant-e types
keep their K-window scope from Wave 3 (`montes_w4_recovers`). e=1-mixing, same-e multi-side,
per-side K-windows, order ≥ 2, exhaustiveness: NOT covered.

Contents:
* helper bank: `omMenu4_eq_empty` (off-menu emptiness over the ENLARGED `typeMenu4`),
  `typeMenu4_degree`, `stratumCount4_level0`, `hNodeLimit_omMenu4` (the per-leg counting
  limits — the THREE-WAY case split: order-0 legs and constant-e window legs through the
  Wave-3 route `RealInstanceW3.hNodeLimit_omMenuW3`, mixed legs by the Wave-4a
  `stratum_tendsto_C4_mixed`), `totalDecided_le_box_W4` (box bound at every level, `N = 0`
  collapse included).
* per-side nonnegativity bank (`density_nonneg` feed on the mixed leg):
  `omCount_oneSideShape_nonneg` (the `oneSideShape` sibling of
  `WildMenuPrep.omCount_Tselfloop_nonneg`, same technique) + the `Forall₂` walk
  `prod_omCount_sideSub_nonneg`.
* the m×C split on the product coefficient: `mult4` (the multiplicity POLYNOMIAL — the
  per-side `omMultiplicity` product; see the `prodSC` note below), `vol4` (the per-side
  `omVolume` product), `C4_eq_mul_all` (per-factor `RealInstanceW.omCount_eq_mul_all` +
  the zipWith product/eval split `zipWith_omCount_split`).
* `realMW4 n K hn` — the Wave-4 counting model; `realDW4` (`C := C4`); `realFW4 K` — the
  Wave-4 real `DensityFoundation` (density = the σ-keyed menu sum of `C4`).
* capstones `montes_unconditional_w4` / `montes_unconditional_w4_exhaustive` — statements
  VERBATIM `RealInstanceW3.montes_unconditional_w3(_exhaustive)` with `omMenu4 n K` for
  `omMenuW3 n K` and `C4 T q'` for `omCount T q'` (the ONE coefficient change of this wave).
* `montes_w4_recovers` — the Wave-3 recovery gate: on every NON-mixed σ the Wave-4 instance's
  counting density IS Wave 3's (`omMenu4_eq_of_not_mixed` + `C4 = omCount` off the mixed
  family).

**The `prodSC`-polynomial question (blueprint §2-W4b, resolved).** `CellCard.prodSC p sh : ℕ`
is a `p`-DEPENDENT count (`∏_side shapeCount p`), NOT a polynomial-in-`q` object, so the
blueprint's "multiplicity polynomial from prodSC" cannot be taken literally without first
minting a `shapeCount`-as-polynomial-evaluation tie. No new lemma is needed: the banked
per-shape m×C split `RealInstanceW.omCount_eq_mul_all` (exact for EVERY shape) applied
per FACTOR gives the exact same split with `multiplicity := ∏_side omMultiplicity
(sideSubShape …)` (a genuine `Polynomial ℚ` product) and `clusterVolume := ∏_side omVolume
(sideSubShape …)` — the value `(mult4 T).eval p * vol4 T p` agrees with `prodSC p (mixedSh σ)
· p^{−(newtonExponent + Σ sideDeg)}` through `prod_omCount_eq_blockCardinality`, but the
interface split is discharged without routing through `prodSC` at all.

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.RealInstanceW4

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel Polynomial Filter Topology
open LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.MultiSlopeMenu
open LeanUrat.OM.PathShapeMultiSideTree (sideSubShape subPr sideDeg_subPr AllMuOne AllNonempty)
open LeanUrat.OM.OMCountV2 (omCount omMultiplicity omVolume)

/-! ## 1. Helper bank -/

/-- **Off-menu emptiness over the Wave-4 type menu**: a type outside `typeMenu4 n` has an EMPTY
Wave-4 menu at EVERY window bound `K` — the Wave-3 legs by `RealInstanceW3.omMenuW3_eq_empty`,
the mixed branch by `mem_mixedTypes` + `omMenu4_eq_of_not_mixed`. Discharges
`decidedCount_off_menu` and the off-menu leg of `upper_tail`. -/
theorem omMenu4_eq_empty (n K : ℕ) {σ : FactorizationType}
    (hσ : σ ∉ typeMenu4 n) : omMenu4 n K σ = ∅ := by
  rw [typeMenu4, Finset.mem_union, not_or] at hσ
  obtain ⟨h1, h2⟩ := hσ
  have hmix : ¬ mixedOK n σ := fun h => h2 (mem_mixedTypes.mpr h)
  rw [omMenu4_eq_of_not_mixed hmix]
  exact RealInstanceW3.omMenuW3_eq_empty n K h1

/-- Every Wave-4 menu type has degree `n` (`typeMenuW_degree` on the old branch, the `mixedOK`
degree clause on the mixed branch). -/
theorem typeMenu4_degree (n : ℕ) : ∀ σ ∈ typeMenu4 n, σ.degree = n := by
  intro σ hσ
  rw [typeMenu4, Finset.mem_union] at hσ
  rcases hσ with h | h
  · exact WildMenuPrep.typeMenuW_degree n σ h
  · exact (mem_mixedTypes.mp h).2.2.1

/-- **Level-0 vanishing on the whole Wave-4 menu**: old legs by
`RealInstanceV2.stratumCount_level0`, the mixed leg by its small-`N` vanishing
(`0 ≤ fSum σ`, so level 0 is below the mixed threshold). -/
theorem stratumCount4_level0 {n K : ℕ} (hn : 0 < n) {σ : FactorizationType}
    {T : ClusterShape} (hT : T ∈ omMenu4 n K σ) : stratumCount4 n T 0 = 0 := by
  rcases mem_omMenu4_cases hT with hold | ⟨hOK, rfl⟩
  · rw [stratumCount4_of_mem_omMenuW3 hold]
    exact RealInstanceV2.stratumCount_level0 n hn T
  · exact stratumCount4_mixed_smallN hOK (Nat.zero_le _)

/-- **The per-leg counting limit on the whole Wave-4 menu — the THREE-WAY case split**
(blueprint §2-W4b): per σ the menu is always ONE family, and every leg has a banked limit —
* order-0 legs and constant-e window legs: the Wave-3 route
  `RealInstanceW3.hNodeLimit_omMenuW3` (which itself splits `hNodeLimit_unramified` vs the
  banked H-generic window legs), with `stratumCount4 = M8.stratumCount` and `C4 = omCount` on
  these old shapes;
* mixed legs: the Wave-4a product limit `stratum_tendsto_C4_mixed`
  (`hnode_multiSideProduct` at `M9.realP`).
Discharges both `realMW4.decided_tendsto` and `realDW4.stratum_tendsto_C`. -/
theorem hNodeLimit_omMenu4 (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (T : ClusterShape) (hT : T ∈ omMenu4 n K σ) :
    Filter.Tendsto
      (fun N => stratumCount4 n T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (C4 T M9.realP)) := by
  rcases mem_omMenu4_cases hT with hold | ⟨hOK, rfl⟩
  · have hne1 : headOrd T ≠ 1 := by
      rw [headOrd_of_mem_omMenuW3 hold]; exact zero_ne_one
    rw [C4_of_headOrd_ne hne1]
    refine (RealInstanceW3.hNodeLimit_omMenuW3 n K hn σ T hold).congr fun N => ?_
    rw [stratumCount4_of_mem_omMenuW3 hold N]
  · exact stratum_tendsto_C4_mixed hOK

/-- **The total decided count is bounded by the box at EVERY level** (including `N = 0`, where
both sides collapse: decided `= 0` by `stratumCount4_level0`, box `= 1`). The `N ≥ 1` content
is the Wave-4a keystone `sum_stratumCount4_le_box` (pairwise-disjoint box subsets across the
two fiber notions). -/
theorem totalDecided_le_box_W4 (n K : ℕ) (hn : 0 < n) (N : ℕ) :
    (∑ σ ∈ typeMenu4 n, ∑ T ∈ omMenu4 n K σ, stratumCount4 n T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_eq_zero fun σ _ =>
      Finset.sum_eq_zero fun T hT => stratumCount4_level0 hn hT]
    exact le_of_lt (RealInstanceV2.realP_pow_pos _)
  · exact sum_stratumCount4_le_box n K N hn hN

/-! ## 2. Per-side nonnegativity (the `density_nonneg` feed on the mixed leg) -/

/-- The `cellChildren` of a single all-`μ=1` side shape is empty (local re-proof of the
`PathShape`-private lemma of the same name — 8 lines vs. de-privatizing a scratch module). -/
private theorem cellChildren_singleton_nil (s : ℕ) (shape : List (ℕ × ℕ))
    (hμ : ∀ q ∈ shape, q.2 = 1) :
    cellChildren s [shape] = [] := by
  rw [cellChildren]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.filterMap_eq_nil_iff]
  intro q hq
  rw [if_neg]
  rintro ⟨h2, -⟩
  rw [hμ q hq] at h2
  omega

/-- **Nonnegativity of the single-side engine value at EVERY natural `q'`** — the
`oneSideShape` sibling of `WildMenuPrep.omCount_Tselfloop_nonneg`, mirroring its technique:
at `q' = 0` the volume factor kills the value (`volExp ≥ sideDeg pr ≥ 1`); at `q' ≥ 1` the
face choice polynomial is a product of falling factorials of naturals
(`ffPoly_availPoly_eval_nonneg`) and the volume factor is an inverse of a nonnegative. -/
theorem omCount_oneSideShape_nonneg (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hμ : ∀ q ∈ shape, q.2 = 1)
    (hdeg : (shape.map Prod.fst).sum = sideDeg pr) (hne : shape ≠ []) (q' : ℕ) :
    0 ≤ omCount (PathShape.oneSideShape s pr shape) q' := by
  -- the volume exponent is ≥ sideDeg pr = Σ dᵢ ≥ 1
  have hvol : OMCountV2.volExp (mkCell s [pr.1, pr.2] [shape])
      = L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr := by
    rw [OMCountV2.volExp]
    congr 1
  have hsum_pos : 1 ≤ (shape.map Prod.fst).sum := by
    cases shape with
    | nil => exact absurd rfl hne
    | cons q t =>
        have hq := hpos q (List.mem_cons_self ..)
        simp only [List.map_cons, List.sum_cons]
        omega
  have hvol_pos : OMCountV2.volExp (mkCell s [pr.1, pr.2] [shape]) ≠ 0 := by
    omega
  -- reduce `omCount` to the single-configuration term (children collapse to `[]`)
  rw [OMCountV2.omCount, PathShape.configsOf_oneSideShape s pr shape hμ hdeg hne]
  have hchildren : (mkCell s [pr.1, pr.2] [shape]).children = [] := by
    show cellChildren s [shape] = []
    exact cellChildren_singleton_nil s shape hμ
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    hchildren, List.prod_nil, mul_one]
  rcases Nat.eq_zero_or_pos q' with rfl | hq'
  · -- `q' = 0`: the volume factor vanishes
    rw [show ((0 : ℕ) : ℚ) ^ OMCountV2.volExp (mkCell s [pr.1, pr.2] [shape]) = 0 from by
      rw [Nat.cast_zero]
      exact zero_pow hvol_pos]
    rw [inv_zero, mul_zero]
  · -- `q' ≥ 1`: choice polynomial ≥ 0, volume factor ≥ 0
    refine mul_nonneg ?_ (inv_nonneg.mpr (by positivity))
    have hlen : ([shape] : List (List (ℕ × ℕ))).length = (sidePairs [pr.1, pr.2]).length := rfl
    rw [CellCard.mCell_mkCell hlen q']
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    -- rewrite `shape` as an all-μ=1 map to fire `choicePoly_map_one`
    have hshape : shape = (shape.map Prod.fst).map (fun d => (d, 1)) := by
      rw [List.map_map]
      symm
      calc shape.map ((fun d => ((d, 1) : ℕ × ℕ)) ∘ Prod.fst)
          = shape.map id :=
            List.map_congr_left fun q hq => Prod.ext rfl (hμ q hq).symm
        _ = shape := List.map_id shape
    rw [hshape, OMCountV2.choicePoly_map_one, Polynomial.eval_prod]
    refine Finset.prod_nonneg fun d hd => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    refine mul_nonneg (by positivity) ?_
    have hd1 : 1 ≤ d := by
      rw [List.mem_toFinset, List.mem_map] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      exact hpos q hq
    exact RealInstanceV2.ffPoly_availPoly_eval_nonneg d _ q' hd1 hq'

/-- **Per-side product nonnegativity** over any `ShapesFor`-matched side list (the mixed-leg
`density_nonneg` walk — the `Forall₂` induction of
`PathShapeMultiSideTree.prod_sideFactor_eq_prod_omCount`, with `omCount_oneSideShape_nonneg`
fired per factor at `sideDeg (subPr pr) = sideDeg pr`). -/
theorem prod_omCount_sideSub_nonneg (q' : ℕ)
    (sp : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ)))
    (hF : List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr)) sh sp)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) :
    0 ≤ (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) q') sp sh).prod := by
  induction hF with
  | nil => norm_num
  | @cons shape pr shTail spTail hhead htail ih =>
      have hmem := mem_shapesOfDegree_iff.mp hhead
      have hpos : ∀ q ∈ shape, 1 ≤ q.1 := fun q hq => (hmem.2.1 q hq).1
      have hμh : ∀ q ∈ shape, q.2 = 1 := hμ shape List.mem_cons_self
      have hneh : shape ≠ [] := hne shape List.mem_cons_self
      have hdeg : (shape.map Prod.fst).sum = sideDeg (subPr pr) := by
        rw [sideDeg_subPr, ← hmem.2.2]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        show q.1 = q.1 * q.2
        rw [hμh q hq, Nat.mul_one]
      simp only [List.zipWith_cons_cons, List.prod_cons]
      refine mul_nonneg ?_ (ih (fun s hs => hμ s (List.mem_cons_of_mem _ hs))
        (fun s hs => hne s (List.mem_cons_of_mem _ hs)))
      exact omCount_oneSideShape_nonneg _ _ shape hpos hμh hdeg hneh q'

/-- The Wave-4 coefficient of the canonical mixed literal IS the per-side product (the decode
collapsed — the `C4`-side sibling of `stratum_tendsto_C4_mixed`'s internal rewrite). -/
theorem C4_multiSideLit (n : ℕ) (σ : FactorizationType) (q' : ℕ) :
    C4 (multiSideLit n (mixedPath σ) (mixedSh σ)) q'
      = (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) q')
          (sidePairs (mixedPath σ)) (mixedSh σ)).prod := by
  rw [C4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)), decodePath_multiSideLit,
    decodeShapes_multiSideLit (mixedSh_length_eq σ) (allMuOne_mixedSh σ)]

/-! ## 3. The m×C split on the product coefficient (the `realFW4.decomposition` feed) -/

/-- **The Wave-4 multiplicity polynomial**: on multi-slope literals the PRODUCT over sides of
the per-side `omMultiplicity` polynomials (a genuine `Polynomial ℚ`); `omMultiplicity`
unchanged on every other shape. See the module docstring for the `prodSC` resolution. -/
noncomputable def mult4 (T : ClusterShape) : Polynomial ℚ :=
  if headOrd T = 1 then
    (List.zipWith (fun pr shape => omMultiplicity (sideSubShape pr shape))
      (sidePairs (decodePath T)) (decodeShapes T)).prod
  else omMultiplicity T

/-- **The Wave-4 cluster volume**: on multi-slope literals the PRODUCT over sides of the
per-side `omVolume` factors (each a pure box-volume inverse `q^{−B}` — childless all-μ=1
cells); `omVolume` unchanged on every other shape. -/
noncomputable def vol4 (T : ClusterShape) (q' : ℕ) : ℚ :=
  if headOrd T = 1 then
    (List.zipWith (fun pr shape => omVolume (sideSubShape pr shape) q')
      (sidePairs (decodePath T)) (decodeShapes T)).prod
  else omVolume T q'

/-- The zipped per-side m×C split (one induction: per-factor
`RealInstanceW.omCount_eq_mul_all`, the product/eval commutation folded in). -/
private theorem zipWith_omCount_split (q' : ℕ) :
    ∀ (sp : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ))),
      (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) q') sp sh).prod
        = ((List.zipWith (fun pr shape => omMultiplicity (sideSubShape pr shape)) sp sh).prod).eval (q' : ℚ)
            * (List.zipWith (fun pr shape => omVolume (sideSubShape pr shape) q') sp sh).prod := by
  intro sp
  induction sp with
  | nil => intro sh; simp
  | cons pr sp ih =>
      intro sh
      cases sh with
      | nil => simp
      | cons shape sh =>
          simp only [List.zipWith_cons_cons, List.prod_cons, Polynomial.eval_mul, ih sh]
          rw [RealInstanceW.omCount_eq_mul_all (sideSubShape pr shape) q']
          ring

/-- **The m×C split for the Wave-4 coefficient on EVERY shape** (the `realFW4.decomposition`
discharge): `C4 T q' = (mult4 T).eval q' · vol4 T q'` — on old shapes this is exactly
`RealInstanceW.omCount_eq_mul_all`; on multi-slope literals it is the per-factor split
distributed over the side product. -/
theorem C4_eq_mul_all (T : ClusterShape) (q' : ℕ) :
    C4 T q' = (mult4 T).eval (q' : ℚ) * vol4 T q' := by
  by_cases h : headOrd T = 1
  · rw [C4, if_pos h, mult4, if_pos h, vol4, if_pos h]
    exact zipWith_omCount_split q' _ _
  · rw [C4_of_headOrd_ne h, mult4, if_neg h, vol4, if_neg h]
    exact RealInstanceW.omCount_eq_mul_all T q'

/-! ## 4. `realMW4` — the Wave-4 real counting model -/

/-- **The Wave-4 MIXED-e real counting model (blueprint §2-W4b, `realMW4`).** The σ-keyed
decided count is the fiber sum over the Wave-4 menu `omMenu4 n K σ` with the UNIFIED count
`stratumCount4` (genuine order-1 `classify1` fibers on the mixed leg, `B.classify` fibers on
the old legs — both subsets of the SAME box); the undecided count is the honest box residual
over the ENLARGED type menu `typeMenu4 n = typeMenuW n ∪ mixedTypes n`. Every field genuinely
discharged:
* `undecidedCount_nonneg` — the Wave-4a cross-classifier disjoint-fiber box bound
  `sum_stratumCount4_le_box` + level-0 vanishing;
* `decided_mono` — FULL monotonicity `normSum_omMenu4_mono` (the mixed leg is a single
  `0, …, 0, c, c, …` staircase joining at `N₀ = fSum σ + 1`; non-mixed σ inherit Wave 3);
* `decided_tendsto` — per-leg limits `hNodeLimit_omMenu4` (the three-way case split);
* `upper_tail` — per-σ increment ≤ total increment ≤ normalized undecided mass at `N`
  (the Wave-1/3 total-increment absorption verbatim, over the Wave-4a bank);
* cross-σ soundness — a Wave-4 menu shape names its type (`eq_of_mem_omMenu4`).

**Honest scope**: the mixed `densityVal` summand is the ONE canonical mixed stratum's density
(the leading term of the type's density); constant-e types keep the K-window scope. -/
noncomputable def realMW4 (n K : ℕ) (hn : 0 < n) : CountingModel M9.realP n where
  hq := by norm_num [M9.realP]
  decidedCount := fun σ N => ∑ T ∈ omMenu4 n K σ, stratumCount4 n T N
  undecidedCount := fun N => (M9.realP : ℚ) ^ (n * N)
    - ∑ σ ∈ typeMenu4 n, ∑ T ∈ omMenu4 n K σ, stratumCount4 n T N
  decidedCount_nonneg := by
    intro σ N
    exact Finset.sum_nonneg fun T _ => stratumCount4_nonneg n T N
  undecidedCount_nonneg := by
    intro N
    rw [sub_nonneg]
    exact totalDecided_le_box_W4 n K hn N
  typeMenu := typeMenu4 n
  typeMenu_degree := typeMenu4_degree n
  decidedCount_off_menu := by
    intro σ N hσ
    rw [omMenu4_eq_empty n K hσ, Finset.sum_empty]
  box_partition := by
    intro N
    ring
  decided_mono := fun σ => normSum_omMenu4_mono n K hn σ
  densityVal := fun σ => ∑ T ∈ omMenu4 n K σ, C4 T M9.realP
  decided_tendsto := by
    intro σ
    have hpush : (fun N => (∑ T ∈ omMenu4 n K σ, stratumCount4 n T N)
          / (M9.realP : ℚ) ^ (n * N))
        = fun N => ∑ T ∈ omMenu4 n K σ,
            stratumCount4 n T N / (M9.realP : ℚ) ^ (n * N) := by
      funext N; rw [Finset.sum_div]
    rw [hpush]
    exact tendsto_finsetSum (omMenu4 n K σ)
      (fun T hT => hNodeLimit_omMenu4 n K hn σ T hT)
  upper_tail := by
    intro σ N K' hNK
    have hBK := RealInstanceV2.realP_pow_pos (n * K')
    have hBN := RealInstanceV2.realP_pow_pos (n * N)
    -- normalized undecided mass at N = 1 − normalized total decided at N (box partition):
    have hundec : ((M9.realP : ℚ) ^ (n * N)
          - ∑ σ' ∈ typeMenu4 n, ∑ T ∈ omMenu4 n K σ', stratumCount4 n T N)
          / (M9.realP : ℚ) ^ (n * N)
        = 1 - (∑ σ' ∈ typeMenu4 n, ∑ T ∈ omMenu4 n K σ', stratumCount4 n T N)
            / (M9.realP : ℚ) ^ (n * N) := by
      rw [sub_div, div_self (ne_of_gt hBN)]
    by_cases hσ : σ ∈ typeMenu4 n
    · -- per-σ increment ≤ total increment (all σ'-summands monotone, `normSum_omMenu4_mono`):
      have hstep : ∀ σ' ∈ typeMenu4 n,
          (0 : ℚ) ≤ (∑ T ∈ omMenu4 n K σ', stratumCount4 n T K')
                / (M9.realP : ℚ) ^ (n * K')
            - (∑ T ∈ omMenu4 n K σ', stratumCount4 n T N)
                / (M9.realP : ℚ) ^ (n * N) := fun σ' _ =>
        sub_nonneg.mpr (normSum_omMenu4_mono n K hn σ' hNK)
      have hsingle := Finset.single_le_sum (f := fun σ' =>
          (∑ T ∈ omMenu4 n K σ', stratumCount4 n T K')
            / (M9.realP : ℚ) ^ (n * K')
          - (∑ T ∈ omMenu4 n K σ', stratumCount4 n T N)
            / (M9.realP : ℚ) ^ (n * N)) hstep hσ
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsingle
      -- total increment ≤ 1 − total_N norm (Wave-4 box bound at K'):
      have htotK : (∑ σ' ∈ typeMenu4 n,
            ∑ T ∈ omMenu4 n K σ', stratumCount4 n T K')
          / (M9.realP : ℚ) ^ (n * K') ≤ 1 :=
        (div_le_one hBK).mpr (totalDecided_le_box_W4 n K hn K')
      linarith
    · -- off-menu σ: decided ≡ 0, RHS = 0 + (nonnegative undecided mass):
      rw [omMenu4_eq_empty n K hσ]
      simp only [Finset.sum_empty, zero_div, zero_add]
      apply div_nonneg _ (le_of_lt hBN)
      rw [sub_nonneg]
      exact totalDecided_le_box_W4 n K hn N

/-! ## 5. `realDW4` — the abstract-coefficient V2 Montes data over `realMW4` -/

/-- **The Wave-4 MIXED-e real Montes data (`realDW4`).** `C := C4` — the FIRST wave whose
coefficient is NOT `omCount`: the per-side `omCount (sideSubShape …)` PRODUCT on the mixed
literal, `omCount` on every old shape. `C_isRational := C4_isRational` (THEOREM — the zipWith
product closure); `stratum_tendsto_C` = the three-way per-leg limits `hNodeLimit_omMenu4`;
`partition` definitional. -/
noncomputable def realDW4 (n K : ℕ) (hn : 0 < n) :
    LeanUrat.MontesV2.MontesDataV2 M9.realP n (realMW4 n K hn) where
  shapesOf := fun σ => omMenu4 n K σ
  stratumCount := stratumCount4 n
  partition := fun _ _ => rfl
  C := fun T q' => C4 T q'
  C_isRational := fun T => C4_isRational T
  stratum_tendsto_C := fun σ T hT => hNodeLimit_omMenu4 n K hn σ T hT

/-! ## 6. `realFW4` — the Wave-4 real density foundation -/

/-- **The Wave-4 MIXED-e real `DensityFoundation` (`realFW4 K`).** `density m σ q' :=
∑_{T ∈ omMenu4 m K σ} C4 T q'` — NOTE: the density sums the Wave-4 coefficient `C4`, NOT
`omCount` (unlike every prior wave — the mixed contribution is a per-side product that no
single `omCount` carries). UNGUARDED nonnegativity at EVERY natural `q'`: order-0/constant-e
legs as in Wave 3, the mixed leg as a product of per-side nonnegatives
(`prod_omCount_sideSub_nonneg`). The structural `decomposition` is the per-family m×C split
`C4_eq_mul_all` with `multiplicity := mult4` and `clusterVolume := vol4` (per-side products on
the mixed literal — see the module docstring for the `prodSC` resolution). -/
noncomputable def realFW4 (K : ℕ) : DensityFoundation where
  density := fun m σ q' => ∑ T ∈ omMenu4 m K σ, C4 T q'
  clusterVolume := fun T q' => vol4 T q'
  shapes := fun m σ => omMenu4 m K σ
  multiplicity := fun T => mult4 T
  decomposition := by
    intro m σ _ q' _
    exact Finset.sum_congr rfl fun T _ => C4_eq_mul_all T q'
  density_nonneg := by
    intro m σ q'
    refine Finset.sum_nonneg fun T hT => ?_
    rcases mem_omMenu4_cases hT with hold | ⟨hOK, rfl⟩
    · rw [C4_of_headOrd_ne (by rw [headOrd_of_mem_omMenuW3 hold]; exact zero_ne_one)]
      rcases mem_omMenuW3_cases hold with ⟨lam, rfl⟩ | ⟨hc, k, -, -, rfl⟩
      · exact RealInstanceV2.omCount_sepShape_nonneg m lam q'
      · exact WildMenuW3.omCount_ramShapeAt_nonneg hc k q'
    · rw [C4_multiSideLit m σ q']
      exact prod_omCount_sideSub_nonneg q' (sidePairs (mixedPath σ)) (mixedSh σ)
        (shapesFor_mixedPath hOK) (allMuOne_mixedSh σ) (allNonempty_mixedSh σ)

/-! ## 7. The Wave-4 capstones -/

/-- **`montes_unconditional_w4` — the Wave-4 MIXED-e capstone** (statement VERBATIM
`RealInstanceW3.montes_unconditional_w3` with the Wave-4 menu `omMenu4 n K` for `omMenuW3 n K`
and the Wave-4 coefficient `C4 T q'` for `omCount T q'` — the ONE coefficient change of this
wave; fired at the Wave-4 instance `(realMW4, realDW4, realFW4 K)`).

**What this certifies** (degree-`n` type `σ`, `n > 0`, window bound `K`):
* (R) UNCONDITIONAL uniform rationality of the Wave-4 σ-keyed engine density
  `g_σ(q') := ∑_{T ∈ omMenu4 n K σ} C4 T q'` — one `num/den`, denominator nonvanishing at
  every `q' > 1`;
* (V) the DECIDED-DENSITY TIE, UNCONDITIONAL: `(realMW4 n K hn).countingDensity σ` — the
  genuine `N → ∞` limit of the real normalized fiber counts over the Wave-4 menu (GENUINE
  order-1 `classify1` fibers on the mixed leg) — equals `num(realP)/den(realP)`. For
  **mixed-e σ** this is the FIRST machine-checked multi-slope density value in the capstone
  chain (gates G1/G2, `OM/RealInstanceW4Gates.lean`: `1/512 = (p−1)²·p⁻⁹` at
  `n = 5, σ = {(2,1),(3,1)}, realP = 2`);
* (P) palindromy `IsPalindromic num den` — CONDITIONAL on the explicit HYPOTHESIS `htameFE`
  (about `realFW4 K`; never an axiom).

**Honest scope (blueprint §0/§3 — what this does NOT claim):**
* the mixed menu covers ONLY mixed-e types with all side-e's ≥ 2 pairwise DISTINCT, ONE
  canonical stratum each (minimal per-side height k = 1, ascending-e steepest-first,
  all-μ=1): the certified mixed value is the density of THAT decided stratum — the LEADING
  TERM of the type's density, NOT any tower/window resummation; e=1-mixing, same-e
  multi-side, and per-side K-windows are deferred (blueprint §0);
* constant-e ramified types keep their Wave-3 K-window scope verbatim (`montes_w4_recovers`);
  order ≥ 2 shapes absent;
* NO exhaustiveness claim: `countingDensity` is the DECIDED limit; the undecided pool does
  not drain at any finite order (see `montes_unconditional_w4_exhaustive`);
* NOT unconditional palindromy: palindromy is exactly the content of `htameFE`.

`#print axioms` must be Lean core ONLY (`AxCheck` section): every tame/counting input is a
hypothesis or a theorem, never an axiom. -/
theorem montes_unconditional_w4 (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation (realFW4 K) n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ MultiSlopeMenu.omMenu4 n K σ, MultiSlopeMenu.C4 T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW4 n K hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hall, hval, hpalin⟩ :=
    LeanUrat.MontesV2.goal_theorem_montes (realMW4 n K hn) (realDW4 n K hn) σ (realFW4 K) hσ
      (fun _ _ => rfl) htameFE
  exact ⟨num, den, hden, hall, hval (by norm_num [M9.realP]), hpalin⟩

/-- **`montes_unconditional_w4_exhaustive` — the exhaustive companion of the Wave-4 MIXED-e
capstone** (statement VERBATIM `RealInstanceW3.montes_unconditional_w3_exhaustive` with
`omMenu4 n K`/`C4` for `omMenuW3 n K`/`omCount`). Adds the honest exhaustiveness input
`hExhaust` (the normalized undecided mass over the Wave-4 menu drains — an EXPLICIT
hypothesis, NOT discharged: the classifier does not drain at any finite order, and the Wave-4
menu carries one canonical stratum per mixed type + the K-window per constant-e type) and
concludes, on top of the `montes_unconditional_w4` clauses, the BRACKET-UNIQUENESS form of the
full-density tie: any `d` consistent with every level-`N ≥ 1` bracket equals
`(realMW4 n K hn).countingDensity σ`. Honest scope as in `montes_unconditional_w4`. -/
theorem montes_unconditional_w4_exhaustive (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation (realFW4 K) n σ)
    (hExhaust : Filter.Tendsto
      (fun N => (realMW4 n K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds 0)) :
    (∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ MultiSlopeMenu.omMenu4 n K σ, MultiSlopeMenu.C4 T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW4 n K hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        (realMW4 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N) ≤ d ∧
        d ≤ (realMW4 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
              + (realMW4 n K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N)) →
      d = (realMW4 n K hn).countingDensity σ := by
  refine ⟨montes_unconditional_w4 n K hn σ hσ htameFE, ?_⟩
  intro d hd
  have hlim : Filter.Tendsto
      (fun N => (realMW4 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds ((realMW4 n K hn).countingDensity σ)) :=
    (realMW4 n K hn).decided_tendsto σ
  have h1 : (realMW4 n K hn).countingDensity σ ≤ d := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).1
  have h2 : d ≤ (realMW4 n K hn).countingDensity σ := by
    have hlim2 : Filter.Tendsto
        (fun N => (realMW4 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
          + (realMW4 n K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop (nhds ((realMW4 n K hn).countingDensity σ)) := by
      simpa using hlim.add hExhaust
    refine ge_of_tendsto hlim2 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).2
  exact le_antisymm h2 h1

/-! ## 8. The Wave-3 recovery gate -/

/-- **`montes_w4_recovers` — the Wave-3 recovery gate (blueprint §2-W4b: "non-mixed σ must
recover Wave 3's values").** On every NON-mixed σ, at every degree and window bound, the
Wave-4 instance's counting density IS Wave 3's: both are DEFINED as their menu sums
(`densityVal`), the menus coincide (`omMenu4_eq_of_not_mixed`), and on every Wave-3 shape the
Wave-4 coefficient IS `omCount` (`C4_of_headOrd_ne` — the else-branches of
`stratumCount4`/`C4` are literally the Wave-3 forms). -/
theorem montes_w4_recovers (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : ¬ MultiSlopeMenu.mixedOK n σ) :
    (realMW4 n K hn).countingDensity σ
      = (RealInstanceW3.realMW3 n K hn).countingDensity σ := by
  show (∑ T ∈ omMenu4 n K σ, C4 T M9.realP)
    = ∑ T ∈ WildMenuW3.omMenuW3 n K σ, OMCountV2.omCount T M9.realP
  rw [omMenu4_eq_of_not_mixed hσ]
  exact Finset.sum_congr rfl fun T hT =>
    C4_of_headOrd_ne (by rw [headOrd_of_mem_omMenuW3 hT]; exact zero_ne_one) _

end LeanUrat.OM.RealInstanceW4

section AxCheck

-- Wave-4 gate (blueprint §2-W4b): the MIXED-e capstones' footprints must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
-- The tame content enters as the HYPOTHESIS `htameFE`; the mixed counting leg is the banked
-- THEOREM chain `stratum_tendsto_C4_mixed` ← `hnode_multiSideProduct` — no axiom anywhere on
-- the path.
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4_exhaustive
#print axioms LeanUrat.OM.RealInstanceW4.montes_w4_recovers

end AxCheck
