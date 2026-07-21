/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MontesV2
import LeanUrat.OM.RealInstanceV2Prep
import LeanUrat.OM.ConditionalDensity

/-!
# OM/RealInstanceV2 — the corrected real V2 instance (blueprint W2)

This module is **Wave 2 of `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`** (signed off 2026-07-19):
the CORRECTED, σ-KEYED real instance of the V2 spine (`LeanUrat/MontesV2.lean`), replacing the
old vacuous `M9.montes_unconditional` chain (order-0 decode ≡ 0, σ-independent; retired in W4a to
`quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`) with an instance whose
per-shape coefficient is the corrected engine evaluator `OMCountV2.omCount` over the σ-keyed menu
`OMCountV2.omMenu n σ` (= `Order0.sepShapesOf n σ` at R1).

Contents:
* `realM2` — the corrected real counting model: `decidedCount σ N := ∑_{T ∈ omMenu n σ}
  stratumCount (rawCount n) T N` (genuine `Nat.card` classifier-fiber counts over the M1 box),
  `undecidedCount := box − total decided`. All `CountingModel` fields genuinely discharged
  (menu disjointness, level-≥1 constancy, the box bound — `RealInstanceV2Prep`).
* `realD2` — the abstract-coefficient V2 Montes data over `realM2`: `C := omCount`,
  `C_isRational := omCount_isRational`, `stratum_tendsto_C := hNodeLimit_unramified` (the
  UNCONDITIONAL order-0 counting legs).
* `realF2` — the corrected real `DensityFoundation`: the FIRST non-trivial real instance.
  `density m σ q' := ∑_{T ∈ omMenu m σ} omCount T q'` (UNGUARDED: nonnegativity is proved at
  EVERY natural `q'`, via the all-naturals necklace integrality `Necklace.necklaceQ_eq_natCast`);
  `decomposition` via the m×C split `omCount_eq_mul`.
* `montes_unconditional` — THE all-orders capstone (honesty block in its docstring; renamed from
  `montes_unconditional_v2` in W4a, 2026-07-21, superseding the retired old vacuous
  `M9.montes_unconditional`).
* `montes_unconditional_exhaustive` — the bracket-uniqueness companion under `hExhaust` (renamed
  from `montes_unconditional_v2_exhaustive` in W4a).

Footprint gate (`AxCheck` section): both capstones must be Lean core ONLY — the tame functional
equation is a HYPOTHESIS (`htameFE`), never the axiom `M9.realDensity_tame_functionalEquation`
(blueprint D4; RETIRED in W4a, 2026-07-21 — it no longer exists in the tree, see
`quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceV2

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel Polynomial Filter Topology
open LeanUrat.OM

/-! ## 1. Local helper bank (level-0 vanishing, menu degree/off-menu facts, the per-σ box bound) -/

/-- **Level-0 vanishing**: the level-0 box is the monic degree-`n` box over `ZMod (realP^0) =
ZMod 1`, the trivial ring — EMPTY for `n > 0`, so every level-0 stratum count is `0`. (Local
re-proof of the fact inlined in `RealInstanceV2Prep.normSum_sepShapesOf_zero_le`, needed here
standalone for `undecidedCount_nonneg`/`upper_tail` at the `N = 0` edge.) -/
theorem stratumCount_level0 (n : ℕ) (hn : 0 < n) (T : ClusterShape) :
    M8.stratumCount (M9.rawCount n) T 0 = 0 := by
  haveI : IsEmpty {f : QuotientBox.monicBox M9.realP 0 n // M9.realClassify n 0 f = T} := by
    constructor
    rintro ⟨⟨f, hmon, hdeg⟩, -⟩
    haveI : Subsingleton (ZMod (M9.realP ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
    have hf : f = 0 := Polynomial.ext fun k => Subsingleton.elim _ _
    rw [hf, Polynomial.natDegree_zero] at hdeg
    omega
  show ((M9.rawCount n T 0 : ℕ) : ℚ) = 0
  rw [show M9.rawCount n T 0
      = Nat.card {f : QuotientBox.monicBox M9.realP 0 n // M9.realClassify n 0 f = T} from rfl,
    Nat.card_of_isEmpty]
  norm_num

/-- The unramified type of a partition of `n` has degree `n`: its `(e,f)` data is `(1,d)` per
part, so the degree is `∑ 1·d = ∑ parts = n` (`Nat.Partition.parts_sum`). Discharges the
`typeMenu_degree` field of `realM2`. -/
theorem unramType_degree (n : ℕ) (lam : Nat.Partition n) :
    (Order0.unramType n lam).degree = n := by
  show ((lam.parts.map (fun d => ((1 : ℕ), d))).map (fun p => p.1 * p.2)).sum = n
  rw [Multiset.map_map]
  simp only [Function.comp_apply, one_mul]
  rw [Multiset.map_id']
  exact lam.parts_sum

/-- **Off-menu emptiness**: a type outside the unramified type menu has an EMPTY σ-keyed order-0
shape menu (no partition's `unramType` matches). Discharges `decidedCount_off_menu`. -/
theorem sepShapesOf_eq_empty (n : ℕ) {σ : FactorizationType}
    (hσ : σ ∉ RealInstanceV2Prep.unramTypeMenu n) : Order0.sepShapesOf n σ = ∅ := by
  rw [Order0.sepShapesOf, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro lam _ heq
  subst heq
  exact hσ (Finset.mem_image_of_mem _ (Finset.mem_univ lam))

/-- The real prime is positive in `ℚ` (`realP = 2`). -/
theorem realPQ_pos : (0 : ℚ) < (M9.realP : ℚ) := by norm_num [M9.realP]

/-- Powers of the real prime are positive in `ℚ`. -/
theorem realP_pow_pos (k : ℕ) : (0 : ℚ) < (M9.realP : ℚ) ^ k := pow_pos realPQ_pos k

/-- **The per-σ box bound at every level**: the σ-keyed decided count is at most the box count
`realP^(nK)` — at `K = 0` both the count is `0` (level-0 vanishing) and the box is `1`; at
`K ≥ 1` the single-σ term of the nonnegative menu total is bounded by the total, which the Prep
bank bounds by the box (`sum_stratumCount_le_box`, disjoint classifier fibers). Feeds the
`N = 0` edge of `upper_tail`. -/
theorem decidedSum_le_box (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (K : ℕ) :
    (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T K)
      ≤ (M9.realP : ℚ) ^ (n * K) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [Finset.sum_eq_zero fun T _ => stratumCount_level0 n hn T]
    exact le_of_lt (realP_pow_pos _)
  · by_cases hσ : σ ∈ RealInstanceV2Prep.unramTypeMenu n
    · calc (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T K)
          ≤ ∑ σ' ∈ RealInstanceV2Prep.unramTypeMenu n,
              ∑ T ∈ Order0.sepShapesOf n σ', M8.stratumCount (M9.rawCount n) T K :=
            Finset.single_le_sum
              (f := fun σ' => ∑ T ∈ Order0.sepShapesOf n σ', M8.stratumCount (M9.rawCount n) T K)
              (fun σ' _ => Finset.sum_nonneg fun T _ => M8.stratumCount_nonneg _ T K) hσ
        _ ≤ (M9.realP : ℚ) ^ (n * K) := RealInstanceV2Prep.sum_stratumCount_le_box n K hK
    · rw [sepShapesOf_eq_empty n hσ, Finset.sum_empty]
      exact le_of_lt (realP_pow_pos _)

/-! ## 2. Block 1 — `realM2`, the corrected real counting model -/

/-- **The corrected real counting model (blueprint W2, `realM2`).** The σ-keyed decided count is
the genuine classifier-fiber sum over the corrected menu `omMenu n σ` (= `sepShapesOf n σ` at
R1); the undecided count is the honest box residual. Every field is genuinely discharged:
* `undecidedCount_nonneg`/`upper_tail` — Prep's disjoint-fiber box bound + level-0 vanishing;
* `decided_mono`/`decided_tendsto` — the normalized decided sequence is `0, c, c, c, …`
  (level-≥1 constancy `normSum_sepShapesOf_levelConst`), converging to the corrected engine
  value `∑_{T ∈ omMenu n σ} omCount T realP` by the UNCONDITIONAL order-0 counting legs
  `hNodeLimit_unramified`;
* `box_partition` — definitional (`undecided := box − total decided`);
* cross-σ soundness — a menu shape names its type (`eq_of_mem_sepShapesOf`), so distinct σ have
  disjoint menus and the type-menu total genuinely partitions the decided mass. -/
noncomputable def realM2 (n : ℕ) (hn : 0 < n) : CountingModel M9.realP n where
  hq := by norm_num [M9.realP]
  decidedCount := fun σ N => ∑ T ∈ OMCountV2.omMenu n σ, M8.stratumCount (M9.rawCount n) T N
  undecidedCount := fun N => (M9.realP : ℚ) ^ (n * N)
    - ∑ σ ∈ RealInstanceV2Prep.unramTypeMenu n,
        ∑ T ∈ OMCountV2.omMenu n σ, M8.stratumCount (M9.rawCount n) T N
  decidedCount_nonneg := by
    intro σ N
    exact Finset.sum_nonneg fun T _ => M8.stratumCount_nonneg _ T N
  undecidedCount_nonneg := by
    intro N
    rw [sub_nonneg]
    simp only [OMCountV2.omMenu_order0]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Finset.sum_eq_zero fun σ _ =>
        Finset.sum_eq_zero fun T _ => stratumCount_level0 n hn T]
      exact le_of_lt (realP_pow_pos _)
    · exact RealInstanceV2Prep.sum_stratumCount_le_box n N hN
  typeMenu := RealInstanceV2Prep.unramTypeMenu n
  typeMenu_degree := by
    intro σ hσ
    simp only [RealInstanceV2Prep.unramTypeMenu, Finset.mem_image] at hσ
    obtain ⟨lam, -, rfl⟩ := hσ
    exact unramType_degree n lam
  decidedCount_off_menu := by
    intro σ N hσ
    simp only [OMCountV2.omMenu_order0]
    rw [sepShapesOf_eq_empty n hσ, Finset.sum_empty]
  box_partition := by
    intro N
    ring
  decided_mono := by
    intro σ N M hNM
    simp only [OMCountV2.omMenu_order0]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rcases Nat.eq_zero_or_pos M with rfl | hM
      · exact le_refl _
      · calc (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 0)
              / (M9.realP : ℚ) ^ (n * 0)
            ≤ (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 1)
              / (M9.realP : ℚ) ^ (n * 1) :=
              RealInstanceV2Prep.normSum_sepShapesOf_zero_le n hn σ
          _ = (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T M)
              / (M9.realP : ℚ) ^ (n * M) :=
              (RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ M hM).symm
    · have hM : 0 < M := lt_of_lt_of_le hN hNM
      exact le_of_eq ((RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ N hN).trans
        (RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ M hM).symm)
  densityVal := fun σ => ∑ T ∈ OMCountV2.omMenu n σ, OMCountV2.omCount T M9.realP
  decided_tendsto := by
    intro σ
    have hpush : (fun N => (∑ T ∈ OMCountV2.omMenu n σ, M8.stratumCount (M9.rawCount n) T N)
        / (M9.realP : ℚ) ^ (n * N))
        = fun N => ∑ T ∈ OMCountV2.omMenu n σ,
            M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N) := by
      funext N; rw [Finset.sum_div]
    rw [hpush]
    exact tendsto_finsetSum (OMCountV2.omMenu n σ)
      (fun T hT => ConditionalDensity.hNodeLimit_unramified n hn σ T hT)
  upper_tail := by
    intro σ N K hNK
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · -- `N = 0`: RHS = 0/1 + (1 − 0)/1 = 1; LHS = decided σ K / box K ≤ 1.
      simp only [OMCountV2.omMenu_order0]
      have hd0 : (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 0) = 0 :=
        Finset.sum_eq_zero fun T _ => stratumCount_level0 n hn T
      have ht0 : (∑ σ' ∈ RealInstanceV2Prep.unramTypeMenu n,
          ∑ T ∈ Order0.sepShapesOf n σ', M8.stratumCount (M9.rawCount n) T 0) = 0 :=
        Finset.sum_eq_zero fun σ' _ =>
          Finset.sum_eq_zero fun T _ => stratumCount_level0 n hn T
      rw [hd0, ht0, Nat.mul_zero, pow_zero]
      norm_num
      rw [div_le_one (realP_pow_pos _)]
      exact decidedSum_le_box n hn σ K
    · -- `N ≥ 1`: LHS = level-1 constant = first RHS term; second RHS term nonnegative.
      have hK : 0 < K := lt_of_lt_of_le hN hNK
      simp only [OMCountV2.omMenu_order0]
      rw [RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ K hK,
        RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ N hN]
      have hund : (0 : ℚ) ≤ ((M9.realP : ℚ) ^ (n * N)
          - ∑ σ' ∈ RealInstanceV2Prep.unramTypeMenu n,
              ∑ T ∈ Order0.sepShapesOf n σ', M8.stratumCount (M9.rawCount n) T N)
          / (M9.realP : ℚ) ^ (n * N) := by
        apply div_nonneg _ (le_of_lt (realP_pow_pos _))
        rw [sub_nonneg]
        exact RealInstanceV2Prep.sum_stratumCount_le_box n N hN
      linarith

/-! ## 3. Block 2 — `realD2`, the abstract-coefficient V2 Montes data -/

/-- **The corrected real V2 Montes data (blueprint W2, `realD2`).** The abstract per-shape
coefficient is pinned to the corrected engine evaluator: `C := omCount` (D2 — instantiation, not
statement, carries the semantics), with `C_isRational := omCount_isRational` (uniform rationality,
THEOREM) and the per-shape counting limits `stratum_tendsto_C := hNodeLimit_unramified` (the
UNCONDITIONAL order-0 legs — the target of each leg is `omCount T realP`, exactly the V2 field
shape). The `partition` field is definitional: `realM2`'s decided count IS the menu-sum of
stratum counts. -/
noncomputable def realD2 (n : ℕ) (hn : 0 < n) :
    LeanUrat.MontesV2.MontesDataV2 M9.realP n (realM2 n hn) where
  shapesOf := fun σ => OMCountV2.omMenu n σ
  stratumCount := M8.stratumCount (M9.rawCount n)
  partition := fun _ _ => rfl
  C := fun T q' => OMCountV2.omCount T q'
  C_isRational := fun T => OMCountV2.omCount_isRational T
  stratum_tendsto_C := fun σ T hT => ConditionalDensity.hNodeLimit_unramified n hn σ T hT

/-! ## 4. Block 3 — the nonnegativity bank and `realF2`

`DensityFoundation.density_nonneg` demands `0 ≤ density m σ q'` at EVERY natural `q'` (including
`0`, `1`, and non-prime-powers). The corrected menu density is UNGUARDED here: nonnegativity is
genuinely provable at all naturals because
* at `q' = 0` (and `m > 0`) the volume factor `((0 : ℚ)^m)⁻¹ = 0` kills the count;
* at `q' ≥ 1` the choice polynomial evaluates to a product of falling factorials of NATURAL
  numbers (`availPoly d` evaluates to a natural at every natural `q' ≥ 1` — `q' − 1` at `d = 1`,
  the necklace count `necklaceQ d q'` at `d ≥ 2`, integrality at ALL naturals by
  `Necklace.necklaceQ_eq_natCast`), and a falling factorial of a natural is nonnegative. -/

/-- A falling factorial of a natural-number cast is nonnegative: either `k ≤ a` (all factors
positive) or the factor at `i = a` vanishes. -/
theorem ff_natCast_nonneg (a k : ℕ) :
    0 ≤ ∏ i ∈ Finset.range k, ((a : ℚ) - (i : ℚ)) := by
  rcases lt_or_ge a k with h | h
  · rw [Finset.prod_eq_zero (Finset.mem_range.mpr h) (by simp)]
  · refine Finset.prod_nonneg fun i hi => ?_
    have hia : (i : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) h)
    linarith

/-- **The pool polynomial evaluates to a NATURAL at every natural `q' ≥ 1`**: `q' − 1` at
`d = 1`; the necklace count `necklaceQ d q'` at `d ≥ 2` (a natural at ALL naturals — the
`Necklace.lean` integrality bank, not just at prime powers). -/
theorem availPoly_eval_natCast (d q' : ℕ) (hd : 1 ≤ d) (hq' : 1 ≤ q') :
    ∃ a : ℕ, (Order0.availPoly d).eval ((q' : ℚ)) = (a : ℚ) := by
  rcases eq_or_ne d 1 with rfl | hne
  · refine ⟨q' - 1, ?_⟩
    rw [Order0.availPoly, if_pos rfl]
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Nat.cast_sub hq',
      Nat.cast_one]
  · rw [Order0.availPoly, if_neg hne, Order0.necklacePoly_eval]
    exact Necklace.necklaceQ_eq_natCast d q' hd

/-- The per-degree falling-factorial choice factor is nonnegative at every natural `q' ≥ 1`. -/
theorem ffPoly_availPoly_eval_nonneg (d k q' : ℕ) (hd : 1 ≤ d) (hq' : 1 ≤ q') :
    0 ≤ (Order0.ffPoly (Order0.availPoly d) k).eval ((q' : ℚ)) := by
  obtain ⟨a, ha⟩ := availPoly_eval_natCast d q' hd hq'
  unfold Order0.ffPoly
  rw [Polynomial.eval_prod]
  have hcong : ∀ i ∈ Finset.range k,
      ((Order0.availPoly d - Polynomial.C ((i : ℚ))).eval ((q' : ℚ))) = (a : ℚ) - (i : ℚ) := by
    intro i _
    rw [Polynomial.eval_sub, Polynomial.eval_C, ha]
  rw [Finset.prod_congr rfl hcong]
  exact ff_natCast_nonneg a k

/-- **The `sepShape` choice polynomial is nonnegative at every natural `q' ≥ 1`** — the product
over distinct part degrees of `(1/k_d!)·ff(availPoly d, k_d)`, each factor nonnegative. -/
theorem nodeChoicePolyQ_sepShape_eval_nonneg (m : ℕ) (lam : Nat.Partition m) (q' : ℕ)
    (hq' : 1 ≤ q') :
    0 ≤ (Order0.nodeChoicePolyQ (M7.cellsOfShapeWF (Order0.sepShape m lam))).eval ((q' : ℚ)) := by
  unfold Order0.nodeChoicePolyQ
  rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
    Order0.nodeDelta_sepShape m lam, pow_one]
  unfold Order0.nodeChoicePoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_nonneg fun d hd => ?_
  have hd1 : 1 ≤ d := by
    rw [Order0.dSList_sepShape] at hd
    have hmem : d ∈ lam.parts := by
      have := List.mem_toFinset.mp hd
      rwa [Multiset.mem_sort] at this
    exact lam.parts_pos hmem
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  exact mul_nonneg (by positivity) (ffPoly_availPoly_eval_nonneg d _ q' hd1 hq')

/-- **The corrected per-shape count is nonnegative on the whole menu at EVERY natural `q'`**
(including `0`, `1`, and non-prime-powers — the UNGUARDED `density_nonneg` feed). At `q' = 0`
(and `m > 0`) the volume factor `(0^m)⁻¹ = 0` kills the product; at `q' ≥ 1` the choice
polynomial is nonnegative and the volume factor is an inverse of a nonnegative. The `m = 0`
degenerate shape has empty payload and `omCount = 1`. -/
theorem omCount_sepShape_nonneg (m : ℕ) (lam : Nat.Partition m) (q' : ℕ) :
    0 ≤ OMCountV2.omCount (Order0.sepShape m lam) q' := by
  rw [OMCountV2.omCount_sepShape_eq_rootCount m lam q']
  rw [Order0.rootCount]
  have h1 : ((M7.cellsOfShapeWF (Order0.sepShape m lam)).map (fun c =>
      (c.children.map (fun ch => clusterCount M7.cellsOfShapeWF M6.treeSize
        M7.cellsOfShapeWF_descend ch q')).prod)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Order0.sepShape_leaf m lam c hc]
    simp
  rw [h1, mul_one]
  rcases Nat.eq_zero_or_pos q' with rfl | hq'
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- `m = 0`: the payload is empty, the value is `1 · (0^0)⁻¹ = 1`.
      have hparts : lam.parts = 0 := by
        by_contra h
        obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h
        have hpos := lam.parts_pos ha
        have hsum := lam.parts_sum
        have hle : a ≤ lam.parts.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) a ha
        omega
      have hcells : M7.cellsOfShapeWF (Order0.sepShape 0 lam) = [] := by
        rw [Order0.cellsOfShapeWF_sepShape, hparts]
        simp
      rw [hcells]
      simp [Order0.nodeChoicePolyQ, Order0.nodeChoicePoly, Order0.dSList,
        Order0.nodeVolumeExp, Order0.nodeDelta]
    · -- `m > 0`, `q' = 0`: the volume factor `((0 : ℚ)^m)⁻¹ = 0` kills the product.
      rw [Order0.nodeVolumeExp_sepShape m hm lam]
      rw [Nat.cast_zero, zero_pow (by omega : m ≠ 0), inv_zero, mul_zero]
  · exact mul_nonneg (nodeChoicePolyQ_sepShape_eval_nonneg m lam q' hq')
      (inv_nonneg.mpr (by positivity))

/-- **The corrected real density foundation (blueprint W2, `realF2`) — the FIRST non-trivial real
`DensityFoundation` instance.** `density m σ q' := ∑_{T ∈ omMenu m σ} omCount T q'` — the σ-KEYED
corrected engine menu-sum, UNGUARDED (nonnegative at every natural `q'`, `omCount_sepShape_nonneg`).
The structural `decomposition` is the m×C split `omCount_eq_mul` (exact on the R1 menu:
single-node, single-configuration shapes), with `multiplicity := omMultiplicity` and
`clusterVolume := omVolume`. -/
noncomputable def realF2 : DensityFoundation where
  density := fun m σ q' => ∑ T ∈ OMCountV2.omMenu m σ, OMCountV2.omCount T q'
  clusterVolume := fun T q' => OMCountV2.omVolume T q'
  shapes := fun m σ => OMCountV2.omMenu m σ
  multiplicity := fun T => OMCountV2.omMultiplicity T
  decomposition := by
    intro m σ _ q' hq'
    exact Finset.sum_congr rfl fun T hT => OMCountV2.omCount_eq_mul m σ T hT q' hq'
  density_nonneg := by
    intro m σ q'
    refine Finset.sum_nonneg fun T hT => ?_
    rw [OMCountV2.omMenu_order0, Order0.sepShapesOf, Finset.mem_image] at hT
    obtain ⟨lam, -, rfl⟩ := hT
    exact omCount_sepShape_nonneg m lam q'

/-! ## 5. Block 3 — the W2 capstone -/

/-- **`montes_unconditional` — THE all-orders capstone (blueprint §2, hypothesis-minimal
form).**

**SUPERSESSION (W4a, 2026-07-21).** Renamed from `montes_unconditional_v2`: this theorem now CARRIES
the canonical capstone name, superseding the old vacuous `M9.montes_unconditional` (order-0 decode
≡ 0, σ-independent, conditional on false-for-the-instance hypotheses), which is retired to
`quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt` together with the axiom
`realDensity_tame_functionalEquation` (blueprint D4: the tame input is the HYPOTHESIS `htameFE`
below; the footprint is Lean core ONLY — a net trusted-base reduction).

**What this certifies** (for degree-`n` type `σ`, `n > 0`), firing the V2 Goal theorem
`goal_theorem_montes_v2` at the corrected real instance `(realM2, realD2, realF2)`:
* (R) UNCONDITIONAL uniform rationality of the σ-KEYED corrected engine density
  `g_σ(q') := ∑_{T ∈ omMenu n σ} omCount T q'` — one `num/den`, denominator nonvanishing at every
  `q' > 1` (`omCount_isRational`);
* (V) the DECIDED-DENSITY TIE, UNCONDITIONAL: `(realM2 n hn).countingDensity σ` — the genuine
  `N → ∞` limit of the real normalized classifier-fiber counts over the M1 box — equals
  `num(realP)/den(realP)` (order-0 legs `hNodeLimit_unramified`, no counting hypothesis left);
* (P) palindromy `IsPalindromic num den` — CONDITIONAL on `htameFE` (an explicit HYPOTHESIS about
  `realF2`, per blueprint D4: the old axiom `realDensity_tame_functionalEquation` is
  false-shaped for a PARTIAL decided density and is NOT consumed here — the faithful
  Del Corso–Dvornicich cite returns only with Phase-B exhaustiveness + the M1 projective bridge).

**What this does NOT claim** (honesty block, blueprint §0):
* NOT that `g_σ` is the FULL type-`σ` density `ρ(n,σ;q)`: `countingDensity` is the DECIDED limit;
  it equals the full density only given exhaustiveness/drainage of the undecided pool (see
  `montes_unconditional_exhaustive` for the honest bracket-uniqueness form; the classifier
  does not drain at any finite order — Phase B);
* NOT unconditional palindromy: the monic decided stratum is genuinely non-palindromic in
  general; palindromy here is exactly the content of the hypothesis `htameFE`;
* NOT any order-≥1 wild content: the R1 menu is the order-0 separable slice (`omMenu = sepShapesOf`);
  self-loop legs re-enter through the INSTANCE when the Phase-B menu grows.

Non-vacuity and σ-dependence are enforced against THIS instance by the W3 gates (certified value
`1/4 > 0` at `n = 2` inert; O1-reversal σ-separation). `#print axioms` must be Lean core ONLY
(see the `AxCheck` section): every tame/counting input is a hypothesis or a theorem, never an
axiom. -/
theorem montes_unconditional (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (htameFE : TameFunctionalEquation realF2 n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ OMCountV2.omMenu n σ, OMCountV2.omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realM2 n hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hall, hval, hpalin⟩ :=
    LeanUrat.MontesV2.goal_theorem_montes_v2 (realM2 n hn) (realD2 n hn) σ realF2 hσ
      (fun _ _ => rfl) htameFE
  exact ⟨num, den, hden, hall, hval (by norm_num [M9.realP]), hpalin⟩

/-! ## 6. Block 4 — the exhaustive companion (bracket uniqueness) -/

/-- **`montes_unconditional_exhaustive` — the exhaustive companion of THE all-orders capstone
(blueprint §2, W2 packaging refinement; renamed from `montes_unconditional_v2_exhaustive` in W4a,
2026-07-21 — see the supersession note on `montes_unconditional`).**
Adds the honest exhaustiveness input `hExhaust` (the normalized undecided mass
drains: `undecidedCount N / realP^(nN) → 0` — TRUE-shaped, numerics-confirmed, Phase-B target;
the classifier does NOT discharge it at any finite order) and concludes, on top of the
`montes_unconditional` clauses, the BRACKET-UNIQUENESS form of the full-density tie: any `d`
consistent with EVERY level-`N` bracket
`[decidedMeasure σ N, decidedMeasure σ N + undecidedMeasure N]` (for `N ≥ 1`) equals
`(realM2 n hn).countingDensity σ`. This is the only definable full-density tie short of the
semantic wall (no formal "true factorization type of `f` over `ℚ_p`" exists to compare against);
under `hExhaust` the bracket width vanishes, so the decided limit is the UNIQUE such `d`. -/
theorem montes_unconditional_exhaustive (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation realF2 n σ)
    (hExhaust : Filter.Tendsto
      (fun N => (realM2 n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds 0)) :
    (∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ OMCountV2.omMenu n σ, OMCountV2.omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realM2 n hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        (realM2 n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N) ≤ d ∧
        d ≤ (realM2 n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
              + (realM2 n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N)) →
      d = (realM2 n hn).countingDensity σ := by
  refine ⟨montes_unconditional n hn σ hσ htameFE, ?_⟩
  intro d hd
  have hlim : Filter.Tendsto
      (fun N => (realM2 n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds ((realM2 n hn).countingDensity σ)) :=
    (realM2 n hn).decided_tendsto σ
  -- the decided limit is ≤ d: every level-`N ≥ 1` decided measure is ≤ d (lower bracket).
  have h1 : (realM2 n hn).countingDensity σ ≤ d := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).1
  -- d is ≤ the decided limit: d ≤ decided + undecided at every level, and the RHS → limit + 0.
  have h2 : d ≤ (realM2 n hn).countingDensity σ := by
    have hlim2 : Filter.Tendsto
        (fun N => (realM2 n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
          + (realM2 n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop (nhds ((realM2 n hn).countingDensity σ)) := by
      simpa using hlim.add hExhaust
    refine ge_of_tendsto hlim2 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).2
  exact le_antisymm h2 h1

end LeanUrat.OM.RealInstanceV2

section AxCheck

-- Blueprint W2/D4 gate: the V2 capstones' footprints must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
-- In particular the tame content enters as the HYPOTHESIS `htameFE`; the old axiom
-- `LeanUrat.OM.M9.realDensity_tame_functionalEquation` was RETIRED in W4a (2026-07-21) and no
-- longer exists in the tree (`quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`).
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional
#print axioms LeanUrat.OM.RealInstanceV2.montes_unconditional_exhaustive

end AxCheck
