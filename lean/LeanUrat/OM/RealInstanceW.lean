/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MontesV2
import LeanUrat.OM.WildMenuPrep
import LeanUrat.OM.ConditionalDensity

/-!
# OM/RealInstanceW — the Wave-1 WILD real instance (blueprint
`notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md` §2 item 3)

The σ-keyed real instance of the V2 spine over the WILD-extended menu
`WildMenu.omMenuW n σ = sepShapesOf n σ ∪ (ramShape n σ).toFinset`: the order-0 separable menu
plus, for **constant-e ramified** σ, the ONE canonical minimal-H terminating wild stratum
(`Tselfloop n ((0, fSum σ), (n, 0)) (wShape σ)`). Mirrors `OM/RealInstanceV2.lean`
(`realM2`/`realD2`/`realF2`/capstones) with `omMenuW`/`typeMenuW` for `omMenu`/`unramTypeMenu`.

**Honest scope (blueprint §1, stated on every capstone).** Covered: constant-e ramified types
`σ = {(e,f₁),…,(e,f_k)}`, `e ≥ 2`, `e·Σfᵢ = n` — one CANONICAL stratum per σ (minimal-H
single-slope, all-μ=1). The certified ramified value is the density of THAT decided stratum —
the MINIMAL-H leading term of the type's density, NOT the per-type H-tower sum. NOT covered:
the H-tower resummation (the recursive self-loop wall), mixed-e (multi-slope) types, order ≥ 2,
exhaustiveness. No exhaustiveness claim is made anywhere in this module.

Contents:
* helper bank: `omMenuW_eq_empty` (off-menu emptiness over `typeMenuW`), `hNodeLimit_ramShape` /
  `hNodeLimit_omMenuW` (the per-leg counting limits: order-0 legs by
  `ConditionalDensity.hNodeLimit_unramified`, the wild leg by the banked UNCONDITIONAL
  `ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R` fired on the `ramShapeWitness` bundle),
  `omCount_eq_mul_all` (the m×C split for EVERY shape — `configsOf` is a singleton for all
  shapes, so the single-configuration split holds unconditionally; this is the sanctioned
  fallback for `OMCountV2.omCount_eq_mul`, whose statement demands `omMenu`-membership that
  `Tselfloop` shapes cannot supply).
* `realMW` — the Wave-1 counting model (`decidedCount σ N := ∑_{T ∈ omMenuW n σ} stratumCount`;
  `undecidedCount := box − total decided` over `typeMenuW n`). `upper_tail` is proved from FULL
  per-σ monotonicity (`WildMenuPrep.normSum_omMenuW_mono`) + the union box bound: the per-σ
  normalized increment from level `N` to `K` is at most the TOTAL increment (all other summands
  monotone), and the total at `K` is ≤ 1 while the total at `N` is `1 − undecided_N/q^{nN}`
  (box partition), so the increment is absorbed by the normalized undecided mass at `N`.
* `realDW` — the abstract-coefficient V2 Montes data over `realMW` (`C := omCount`).
* `realFW` — the Wave-1 real `DensityFoundation` (density = the σ-keyed `omMenuW` menu sum;
  nonnegativity at EVERY natural `q'` from `RealInstanceV2.omCount_sepShape_nonneg` +
  `WildMenuPrep.omCount_ramShape_nonneg`).
* `montes_unconditional_w` / `montes_unconditional_w_exhaustive` — the capstones, statements
  VERBATIM `RealInstanceV2.montes_unconditional(_exhaustive)` with `omMenuW` for `omMenu`.

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceW

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel Polynomial Filter Topology
open LeanUrat.OM

/-! ## 1. Helper bank -/

/-- **Off-menu emptiness over the Wave-1 type menu**: a type outside `typeMenuW n` has an EMPTY
wild menu — the unramified branch by `RealInstanceV2.sepShapesOf_eq_empty`, the ramified branch
by `WildMenuPrep.mem_constERamTypes` (not constant-e ramified ⟹ `ramShape = none`). Discharges
`decidedCount_off_menu` and the off-menu leg of `upper_tail`. -/
theorem omMenuW_eq_empty (n : ℕ) {σ : FactorizationType}
    (hσ : σ ∉ WildMenuPrep.typeMenuW n) : WildMenu.omMenuW n σ = ∅ := by
  rw [WildMenuPrep.typeMenuW, Finset.mem_union, not_or] at hσ
  obtain ⟨h1, h2'⟩ := hσ
  have h2 : ¬ WildMenu.constERam n σ :=
    fun hc => h2' (WildMenuPrep.mem_constERamTypes.mpr hc)
  rw [WildMenu.omMenuW, RealInstanceV2.sepShapesOf_eq_empty n h1,
    WildMenu.ramShape_of_not_constERam h2, Option.toFinset_none, Finset.union_empty]

/-- **The wild per-leg counting limit** (UNCONDITIONAL): on every `ramShape` output the real
normalized stratum counts converge to the engine value `omCount T realP` — the banked
`ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R` fired on the `ramShapeWitness`
hypothesis bundle (`H = fSum σ`, `N₀ = fSum σ + 1`, `P = wPath`, `shape = wShape`). -/
theorem hNodeLimit_ramShape {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : WildMenu.ramShape n σ = some T) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (OMCountV2.omCount T M9.realP)) := by
  have W := WildMenu.ramShapeWitness hT
  rw [W.hT]
  exact ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R n W.N₀ W.hN₀ W.hn W.H W.P W.hP
    W.hsingle W.shape W.hsh W.hpos W.hμ W.hne

/-- **The per-leg counting limit on the whole Wave-1 menu**: order-0 legs by the UNCONDITIONAL
`ConditionalDensity.hNodeLimit_unramified`, the wild leg by `hNodeLimit_ramShape`. Discharges
both `realMW.decided_tendsto` and `realDW.stratum_tendsto_C`. -/
theorem hNodeLimit_omMenuW (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (OMCountV2.omCount T M9.realP)) := by
  rw [WildMenu.omMenuW, Finset.mem_union] at hT
  rcases hT with h | h
  · exact ConditionalDensity.hNodeLimit_unramified n hn σ T h
  · rw [Option.mem_toFinset, Option.mem_def] at h
    exact hNodeLimit_ramShape h

/-- **The m×C split for EVERY shape** (the sanctioned `realFW.decomposition` fallback,
blueprint §3): `omCount T q = m_T(q) · C_T(q)` holds UNCONDITIONALLY because `configsOf T`
is a singleton for every `T` (`configsOf T = [configOf T]` definitionally), so the
sum-over-configs vs product-over-nodes commutation issue that scoped
`OMCountV2.omCount_eq_mul` to `omMenu`-membership never arises. Same proof body, membership
dropped; in particular it covers the `Tselfloop` shapes of the wild menu. -/
theorem omCount_eq_mul_all (T : ClusterShape) (q : ℕ) :
    OMCountV2.omCount T q
      = (OMCountV2.omMultiplicity T).eval (q : ℚ) * OMCountV2.omVolume T q := by
  rw [OMCountV2.omCount, OMCountV2.omMultiplicity, OMCountV2.omVolume]
  simp only [OMCountV2.configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [Polynomial.eval_list_prod, List.map_map]
  have hfaces : ((OMCountV2.configOf T).faces.map (Polynomial.eval (q : ℚ) ∘ fun F =>
      (OMCountV2.choicePoly F.punctured F.shape).comp (Polynomial.X ^ F.δ)))
      = (OMCountV2.configOf T).faces.map (fun F =>
          (OMCountV2.choicePoly F.punctured F.shape).eval ((q : ℚ) ^ F.δ)) := by
    refine List.map_congr_left fun F _ => ?_
    simp only [Function.comp_apply]
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hfaces]
  unfold OMCountV2.mCell
  ring

/-- **The total decided count is bounded by the box at EVERY level** (including `N = 0`, where
both sides collapse: decided `= 0` by level-0 vanishing, box `= 1`). The `N ≥ 1` content is
`WildMenuPrep.sum_stratumCount_le_box_W` (disjoint classifier fibers over the union family). -/
theorem totalDecided_le_box_W (n : ℕ) (hn : 0 < n) (N : ℕ) :
    (∑ σ ∈ WildMenuPrep.typeMenuW n,
        ∑ T ∈ WildMenu.omMenuW n σ, M8.stratumCount (M9.rawCount n) T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_eq_zero fun σ _ =>
      Finset.sum_eq_zero fun T _ => RealInstanceV2.stratumCount_level0 n hn T]
    exact le_of_lt (RealInstanceV2.realP_pow_pos _)
  · exact WildMenuPrep.sum_stratumCount_le_box_W n N hN

/-! ## 2. `realMW` — the Wave-1 real counting model -/

/-- **The Wave-1 WILD real counting model (blueprint §2 item 3, `realMW`).** The σ-keyed decided
count is the classifier-fiber sum over the WILD-extended menu `omMenuW n σ` (order-0 separable
strata ∪ the canonical minimal-H wild stratum for constant-e ramified σ); the undecided count is
the honest box residual over the Wave-1 type menu `typeMenuW n`. Every field genuinely
discharged:
* `undecidedCount_nonneg` — the union-family disjoint-fiber box bound + level-0 vanishing;
* `decided_mono` — FULL monotonicity `WildMenuPrep.normSum_omMenuW_mono` (wild legs are
  `0, …, 0, c, c, …` with the jump at `N₀ = fSum σ + 1`; order-0 legs `0, c', c', …`);
* `decided_tendsto` — per-leg limits `hNodeLimit_omMenuW` (order-0 UNCONDITIONAL legs + the
  banked UNCONDITIONAL wild self-loop leg);
* `upper_tail` — per-σ increment ≤ total increment ≤ normalized undecided mass at `N`
  (monotonicity of every σ′-summand + the box bound at `K` + the box partition at `N`);
* cross-σ soundness — a menu shape names its type (`WildMenu.eq_of_mem_omMenuW`).

**Honest scope**: the wild `densityVal` summand is the MINIMAL-H canonical-stratum density
(the leading term of the type's density), NOT the H-tower sum — blueprint §1. -/
noncomputable def realMW (n : ℕ) (hn : 0 < n) : CountingModel M9.realP n where
  hq := by norm_num [M9.realP]
  decidedCount := fun σ N => ∑ T ∈ WildMenu.omMenuW n σ, M8.stratumCount (M9.rawCount n) T N
  undecidedCount := fun N => (M9.realP : ℚ) ^ (n * N)
    - ∑ σ ∈ WildMenuPrep.typeMenuW n,
        ∑ T ∈ WildMenu.omMenuW n σ, M8.stratumCount (M9.rawCount n) T N
  decidedCount_nonneg := by
    intro σ N
    exact Finset.sum_nonneg fun T _ => M8.stratumCount_nonneg _ T N
  undecidedCount_nonneg := by
    intro N
    rw [sub_nonneg]
    exact totalDecided_le_box_W n hn N
  typeMenu := WildMenuPrep.typeMenuW n
  typeMenu_degree := WildMenuPrep.typeMenuW_degree n
  decidedCount_off_menu := by
    intro σ N hσ
    rw [omMenuW_eq_empty n hσ, Finset.sum_empty]
  box_partition := by
    intro N
    ring
  decided_mono := fun σ => WildMenuPrep.normSum_omMenuW_mono n hn σ
  densityVal := fun σ => ∑ T ∈ WildMenu.omMenuW n σ, OMCountV2.omCount T M9.realP
  decided_tendsto := by
    intro σ
    have hpush : (fun N => (∑ T ∈ WildMenu.omMenuW n σ, M8.stratumCount (M9.rawCount n) T N)
        / (M9.realP : ℚ) ^ (n * N))
        = fun N => ∑ T ∈ WildMenu.omMenuW n σ,
            M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N) := by
      funext N; rw [Finset.sum_div]
    rw [hpush]
    exact tendsto_finsetSum (WildMenu.omMenuW n σ)
      (fun T hT => hNodeLimit_omMenuW n hn σ T hT)
  upper_tail := by
    intro σ N K hNK
    have hBK := RealInstanceV2.realP_pow_pos (n * K)
    have hBN := RealInstanceV2.realP_pow_pos (n * N)
    -- normalized undecided mass at N = 1 − normalized total decided at N (box partition):
    have hundec : ((M9.realP : ℚ) ^ (n * N)
          - ∑ σ' ∈ WildMenuPrep.typeMenuW n,
              ∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T N)
          / (M9.realP : ℚ) ^ (n * N)
        = 1 - (∑ σ' ∈ WildMenuPrep.typeMenuW n,
              ∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N) := by
      rw [sub_div, div_self (ne_of_gt hBN)]
    by_cases hσ : σ ∈ WildMenuPrep.typeMenuW n
    · -- per-σ increment ≤ total increment (all σ'-summands monotone, `normSum_omMenuW_mono`):
      have hstep : ∀ σ' ∈ WildMenuPrep.typeMenuW n,
          (0 : ℚ) ≤ (∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T K)
                / (M9.realP : ℚ) ^ (n * K)
            - (∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T N)
                / (M9.realP : ℚ) ^ (n * N) := fun σ' _ =>
        sub_nonneg.mpr (WildMenuPrep.normSum_omMenuW_mono n hn σ' hNK)
      have hsingle := Finset.single_le_sum (f := fun σ' =>
          (∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T K)
            / (M9.realP : ℚ) ^ (n * K)
          - (∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N)) hstep hσ
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsingle
      -- total increment ≤ 1 − total_N norm (box bound at K):
      have htotK : (∑ σ' ∈ WildMenuPrep.typeMenuW n,
            ∑ T ∈ WildMenu.omMenuW n σ', M8.stratumCount (M9.rawCount n) T K)
          / (M9.realP : ℚ) ^ (n * K) ≤ 1 :=
        (div_le_one hBK).mpr (totalDecided_le_box_W n hn K)
      linarith
    · -- off-menu σ: decided ≡ 0, RHS = 0 + (nonnegative undecided mass):
      rw [omMenuW_eq_empty n hσ]
      simp only [Finset.sum_empty, zero_div, zero_add]
      apply div_nonneg _ (le_of_lt hBN)
      rw [sub_nonneg]
      exact totalDecided_le_box_W n hn N

/-! ## 3. `realDW` — the abstract-coefficient V2 Montes data over `realMW` -/

/-- **The Wave-1 WILD real Montes data (`realDW`).** `C := omCount` over the WILD-extended
σ-keyed menu; `C_isRational := omCount_isRational` (THEOREM); `stratum_tendsto_C` = the per-leg
counting limits `hNodeLimit_omMenuW` (order-0 legs + the banked UNCONDITIONAL wild self-loop
leg); `partition` definitional. -/
noncomputable def realDW (n : ℕ) (hn : 0 < n) :
    LeanUrat.MontesV2.MontesDataV2 M9.realP n (realMW n hn) where
  shapesOf := fun σ => WildMenu.omMenuW n σ
  stratumCount := M8.stratumCount (M9.rawCount n)
  partition := fun _ _ => rfl
  C := fun T q' => OMCountV2.omCount T q'
  C_isRational := fun T => OMCountV2.omCount_isRational T
  stratum_tendsto_C := fun σ T hT => hNodeLimit_omMenuW n hn σ T hT

/-! ## 4. `realFW` — the Wave-1 real density foundation -/

/-- **The Wave-1 WILD real `DensityFoundation` (`realFW`).** `density m σ q' :=
∑_{T ∈ omMenuW m σ} omCount T q'` — the WILD-extended σ-keyed engine menu-sum, UNGUARDED:
nonnegative at EVERY natural `q'` (order-0 shapes by `RealInstanceV2.omCount_sepShape_nonneg`,
wild shapes by `WildMenuPrep.omCount_ramShape_nonneg`). The structural `decomposition` is the
m×C split `omCount_eq_mul_all` (exact for every shape — single-configuration nodes), with
`multiplicity := omMultiplicity` and `clusterVolume := omVolume`. -/
noncomputable def realFW : DensityFoundation where
  density := fun m σ q' => ∑ T ∈ WildMenu.omMenuW m σ, OMCountV2.omCount T q'
  clusterVolume := fun T q' => OMCountV2.omVolume T q'
  shapes := fun m σ => WildMenu.omMenuW m σ
  multiplicity := fun T => OMCountV2.omMultiplicity T
  decomposition := by
    intro m σ _ q' _
    exact Finset.sum_congr rfl fun T _ => omCount_eq_mul_all T q'
  density_nonneg := by
    intro m σ q'
    refine Finset.sum_nonneg fun T hT => ?_
    rw [WildMenu.omMenuW, Finset.mem_union] at hT
    rcases hT with h | h
    · rw [Order0.sepShapesOf, Finset.mem_image] at h
      obtain ⟨lam, -, rfl⟩ := h
      exact RealInstanceV2.omCount_sepShape_nonneg m lam q'
    · rw [Option.mem_toFinset, Option.mem_def] at h
      exact WildMenuPrep.omCount_ramShape_nonneg h q'

/-! ## 5. The Wave-1 capstones -/

/-- **`montes_unconditional_w` — the Wave-1 WILD capstone** (statement VERBATIM
`RealInstanceV2.montes_unconditional` with the WILD-extended menu `omMenuW` for `omMenu`,
fired at the Wave-1 instance `(realMW, realDW, realFW)`).

**What this certifies** (degree-`n` type `σ`, `n > 0`):
* (R) UNCONDITIONAL uniform rationality of the WILD-extended σ-keyed engine density
  `g_σ(q') := ∑_{T ∈ omMenuW n σ} omCount T q'` — one `num/den`, denominator nonvanishing at
  every `q' > 1`;
* (V) the DECIDED-DENSITY TIE, UNCONDITIONAL: `(realMW n hn).countingDensity σ` — the genuine
  `N → ∞` limit of the real normalized classifier-fiber counts over the WILD-extended menu —
  equals `num(realP)/den(realP)`. For **constant-e ramified σ** this is the FIRST machine-checked
  non-vacuous WILD density value in the capstone chain (gates G1W/G2W,
  `OM/RealInstanceWGates.lean`);
* (P) palindromy `IsPalindromic num den` — CONDITIONAL on the explicit HYPOTHESIS `htameFE`
  (about `realFW`; never an axiom).

**Honest scope (blueprint §1 — what this does NOT claim):**
* the ramified menu covers ONLY constant-e ramified types, with ONE canonical stratum each (the
  minimal-H single-slope all-μ=1 terminating stratum): the certified ramified value is the
  density of THAT decided stratum — the LEADING TERM of the type's density, NOT the per-type
  H-tower sum (the recursive self-loop wall, `notes/SELFLOOP_GENERALK_WALL.md`, stands);
* mixed-e (multi-slope) types get NO ramified menu entry (their decided density is a product
  form, not a single `omCount` shape — `PathShapeMultiSideTree`); order ≥ 2 shapes absent;
* NO exhaustiveness claim: `countingDensity` is the DECIDED limit; the undecided pool does not
  drain at any finite order (see `montes_unconditional_w_exhaustive` for the honest
  bracket-uniqueness form under the explicit `hExhaust` hypothesis);
* NOT unconditional palindromy: palindromy is exactly the content of `htameFE`.

`#print axioms` must be Lean core ONLY (`AxCheck` section): every tame/counting input is a
hypothesis or a theorem, never an axiom. -/
theorem montes_unconditional_w (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (htameFE : TameFunctionalEquation realFW n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ WildMenu.omMenuW n σ, OMCountV2.omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW n hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hall, hval, hpalin⟩ :=
    LeanUrat.MontesV2.goal_theorem_montes (realMW n hn) (realDW n hn) σ realFW hσ
      (fun _ _ => rfl) htameFE
  exact ⟨num, den, hden, hall, hval (by norm_num [M9.realP]), hpalin⟩

/-- **`montes_unconditional_w_exhaustive` — the exhaustive companion of the Wave-1 WILD capstone**
(statement VERBATIM `RealInstanceV2.montes_unconditional_exhaustive` with `omMenuW` for `omMenu`).
Adds the honest exhaustiveness input `hExhaust` (the normalized undecided mass over the Wave-1
menu drains — an EXPLICIT hypothesis, NOT discharged: the classifier does not drain at any
finite order, and the Wave-1 wild menu carries only the canonical minimal-H strata) and
concludes, on top of the `montes_unconditional_w` clauses, the BRACKET-UNIQUENESS form of the
full-density tie: any `d` consistent with every level-`N ≥ 1` bracket equals
`(realMW n hn).countingDensity σ`. Honest scope as in `montes_unconditional_w`. -/
theorem montes_unconditional_w_exhaustive (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation realFW n σ)
    (hExhaust : Filter.Tendsto
      (fun N => (realMW n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds 0)) :
    (∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ WildMenu.omMenuW n σ, OMCountV2.omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW n hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        (realMW n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N) ≤ d ∧
        d ≤ (realMW n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
              + (realMW n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N)) →
      d = (realMW n hn).countingDensity σ := by
  refine ⟨montes_unconditional_w n hn σ hσ htameFE, ?_⟩
  intro d hd
  have hlim : Filter.Tendsto
      (fun N => (realMW n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds ((realMW n hn).countingDensity σ)) :=
    (realMW n hn).decided_tendsto σ
  have h1 : (realMW n hn).countingDensity σ ≤ d := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).1
  have h2 : d ≤ (realMW n hn).countingDensity σ := by
    have hlim2 : Filter.Tendsto
        (fun N => (realMW n hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
          + (realMW n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop (nhds ((realMW n hn).countingDensity σ)) := by
      simpa using hlim.add hExhaust
    refine ge_of_tendsto hlim2 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).2
  exact le_antisymm h2 h1

end LeanUrat.OM.RealInstanceW

section AxCheck

-- Wave-1 gate (blueprint §2 item 3): the WILD capstones' footprints must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
-- The tame content enters as the HYPOTHESIS `htameFE`; the wild counting legs are the banked
-- THEOREM `hnode_selfloop_over_Bclassify_R` — no axiom anywhere on the path.
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive

end AxCheck
