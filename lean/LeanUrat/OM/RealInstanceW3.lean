/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW
import LeanUrat.OM.WildMenuW3

/-!
# OM/RealInstanceW3 — the Wave-3 H-WINDOW real instance (blueprint
`notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 2)

The K-parameterized sibling of `OM/RealInstanceW.lean` over the WINDOWED wild menu
`WildMenuW3.omMenuW3 n K σ = sepShapesOf n σ ∪ ramShapes3 n K σ`: for constant-e ramified σ,
ONE `Tselfloop` stratum per admissible multiplier `k ∈ admissibleK (n/fSum σ) K` (height
`H = fSum σ · k`, `gcd(k, e) = 1`), instead of Wave 1's single `k = 1` stratum. Every proof is
the Wave-1 proof with the `WildMenuW3` bank substituted for the `WildMenu`/`WildMenuPrep` bank;
the type menu `WildMenuPrep.typeMenuW n` is UNCHANGED.

**Honest scope (blueprint §3, stated on every capstone).** Window-K certifies the K-TRUNCATED
decided density of each constant-e ramified type — a strictly larger leading sum than Wave 1
(machine-checked strict growth: `RealInstanceW3Gates.gate_w3_growth`), still NOT the full type
density: the geometric tail is the recursive self-loop wall (`notes/SELFLOOP_GENERALK_WALL.md`).
Mixed-e (multi-slope) types and order ≥ 2 unchanged. No exhaustiveness claim.

Contents:
* helper bank: `omMenuW3_eq_empty` (off-menu emptiness over the UNCHANGED `typeMenuW`),
  `hNodeLimit_ramShapeAt` / `hNodeLimit_omMenuW3` (the per-leg counting limits: order-0 legs by
  `ConditionalDensity.hNodeLimit_unramified`, EVERY window leg by the banked UNCONDITIONAL
  `ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R` fired on the per-k
  `WildMenuW3.ramShapeAtWitness` bundle — the legs are H-generic, so the window costs nothing),
  `totalDecided_le_box_W3` (box bound at every level, `N = 0` collapse included).
* `realMW3 n K hn` — the window-K counting model (`decidedCount σ N := ∑_{T ∈ omMenuW3 n K σ}
  stratumCount`; `undecidedCount := box − total decided` over the UNCHANGED `typeMenuW n`).
  `upper_tail` is the Wave-1 total-increment absorption verbatim: every σ′-summand is monotone
  (`WildMenuW3.normSum_omMenuW3_mono` — each window leg is a 0-then-constant staircase joining
  at its OWN threshold `N = F·k + 1`), the total at `K` is ≤ 1 (windowed box bound
  `sum_stratumCount_le_box_W3`), so the per-σ increment is absorbed by the normalized
  undecided mass at `N`.
* `realDW3` — the abstract-coefficient V2 Montes data over `realMW3` (`C := omCount`).
* `realFW3 K` — the window-K real `DensityFoundation` (density = the σ-keyed `omMenuW3 · K`
  menu sum; `DensityFoundation.density` has no K slot, so K is a PARAMETER of the foundation).
* `montes_unconditional_w3` / `montes_unconditional_w3_exhaustive` — the capstones, statements
  VERBATIM `RealInstanceW.montes_unconditional_w(_exhaustive)` with `omMenuW3 n K` for
  `omMenuW n` (and the instance triple at `(realMW3, realDW3, realFW3 K)`).
* `montes_w3_one_recovers` — the Wave-1 recovery gate: at `K = 1` the window instance's
  counting density IS Wave 1's (`omMenuW3_one`; both densities are the same menu sum).

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceW3

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel Polynomial Filter Topology
open LeanUrat.OM

/-! ## 1. Helper bank -/

/-- **Off-menu emptiness over the (unchanged) Wave-1 type menu**: a type outside `typeMenuW n`
has an EMPTY windowed menu at EVERY window bound `K` — the unramified branch by
`RealInstanceV2.sepShapesOf_eq_empty`, the ramified branch by
`WildMenuW3.ramShapes3_of_not_constERam`. Discharges `decidedCount_off_menu` and the off-menu
leg of `upper_tail`. -/
theorem omMenuW3_eq_empty (n K : ℕ) {σ : FactorizationType}
    (hσ : σ ∉ WildMenuPrep.typeMenuW n) : WildMenuW3.omMenuW3 n K σ = ∅ := by
  rw [WildMenuPrep.typeMenuW, Finset.mem_union, not_or] at hσ
  obtain ⟨h1, h2'⟩ := hσ
  have h2 : ¬ WildMenu.constERam n σ :=
    fun hc => h2' (WildMenuPrep.mem_constERamTypes.mpr hc)
  rw [WildMenuW3.omMenuW3, RealInstanceV2.sepShapesOf_eq_empty n h1,
    WildMenuW3.ramShapes3_of_not_constERam h2, Finset.union_empty]

/-- **The per-k wild counting limit** (UNCONDITIONAL): on every window leg `ramShapeAt n σ k`
(constant-e σ, admissible k) the real normalized stratum counts converge to the engine value
`omCount (ramShapeAt n σ k) realP` — the banked H-GENERIC
`ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R` fired on the per-k
`WildMenuW3.ramShapeAtWitness` hypothesis bundle (`H = fSum σ · k`, `N₀ = fSum σ · k + 1`,
`P = wPathAt n σ k`, `shape = wShape σ`). Mirrors `RealInstanceW.hNodeLimit_ramShape`. -/
theorem hNodeLimit_ramShapeAt {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M9.rawCount n) (WildMenuW3.ramShapeAt n σ k) N
        / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (OMCountV2.omCount (WildMenuW3.ramShapeAt n σ k) M9.realP)) := by
  have W := WildMenuW3.ramShapeAtWitness h hk1 hk
  rw [W.hT]
  exact ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R n W.N₀ W.hN₀ W.hn W.H W.P W.hP
    W.hsingle W.shape W.hsh W.hpos W.hμ W.hne

/-- **The per-leg counting limit on the whole window-K menu**: order-0 legs by the
UNCONDITIONAL `ConditionalDensity.hNodeLimit_unramified`, every window leg by
`hNodeLimit_ramShapeAt` (membership decomposed by `WildMenuW3.mem_ramShapes3` +
`mem_admissibleK`). Discharges both `realMW3.decided_tendsto` and `realDW3.stratum_tendsto_C`.
Mirrors `RealInstanceW.hNodeLimit_omMenuW`. -/
theorem hNodeLimit_omMenuW3 (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (T : ClusterShape) (hT : T ∈ WildMenuW3.omMenuW3 n K σ) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (OMCountV2.omCount T M9.realP)) := by
  rw [WildMenuW3.omMenuW3, Finset.mem_union] at hT
  rcases hT with h | h
  · exact ConditionalDensity.hNodeLimit_unramified n hn σ T h
  · rw [WildMenuW3.mem_ramShapes3] at h
    obtain ⟨hc, k, hk, rfl⟩ := h
    obtain ⟨⟨hk1, -⟩, hke⟩ := WildMenuW3.mem_admissibleK.mp hk
    exact hNodeLimit_ramShapeAt hc hk1 hke

/-- **The total decided count is bounded by the box at EVERY level** (including `N = 0`, where
both sides collapse: decided `= 0` by level-0 vanishing, box `= 1`). The `N ≥ 1` content is
`WildMenuW3.sum_stratumCount_le_box_W3` (disjoint classifier fibers over the windowed union
family). Mirrors `RealInstanceW.totalDecided_le_box_W`. -/
theorem totalDecided_le_box_W3 (n K : ℕ) (hn : 0 < n) (N : ℕ) :
    (∑ σ ∈ WildMenuPrep.typeMenuW n,
        ∑ T ∈ WildMenuW3.omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_eq_zero fun σ _ =>
      Finset.sum_eq_zero fun T _ => RealInstanceV2.stratumCount_level0 n hn T]
    exact le_of_lt (RealInstanceV2.realP_pow_pos _)
  · exact WildMenuW3.sum_stratumCount_le_box_W3 n K N hN

/-! ## 2. `realMW3` — the window-K real counting model -/

/-- **The Wave-3 H-WINDOW real counting model (blueprint §2 item 2, `realMW3`).** The σ-keyed
decided count is the classifier-fiber sum over the WINDOWED menu `omMenuW3 n K σ` (order-0
separable strata ∪ one `Tselfloop` stratum per admissible multiplier `k ≤ K`); the undecided
count is the honest box residual over the UNCHANGED type menu `typeMenuW n`. Every field
genuinely discharged:
* `undecidedCount_nonneg` — the windowed disjoint-fiber box bound + level-0 vanishing;
* `decided_mono` — FULL monotonicity `WildMenuW3.normSum_omMenuW3_mono` (each window leg is a
  `0, …, 0, c_k, c_k, …` staircase joining at its OWN threshold `N = F·k + 1`; order-0 legs
  `0, c', c', …`; a finite sum of monotone staircases is monotone);
* `decided_tendsto` — per-leg limits `hNodeLimit_omMenuW3` (order-0 UNCONDITIONAL legs + the
  banked UNCONDITIONAL H-generic wild self-loop leg, per k);
* `upper_tail` — per-σ increment ≤ total increment ≤ normalized undecided mass at `N`
  (monotonicity of every σ′-summand + the windowed box bound at `K` + the box partition at `N`);
* cross-σ soundness — a windowed menu shape names its type (`WildMenuW3.eq_of_mem_omMenuW3`).

**Honest scope**: the wild `densityVal` summand is the K-TRUNCATED window sum of the type's
density (the first ≤ K admissible-height strata), NOT the full H-tower sum — blueprint §3. -/
noncomputable def realMW3 (n K : ℕ) (hn : 0 < n) : CountingModel M9.realP n where
  hq := by norm_num [M9.realP]
  decidedCount := fun σ N => ∑ T ∈ WildMenuW3.omMenuW3 n K σ,
    M8.stratumCount (M9.rawCount n) T N
  undecidedCount := fun N => (M9.realP : ℚ) ^ (n * N)
    - ∑ σ ∈ WildMenuPrep.typeMenuW n,
        ∑ T ∈ WildMenuW3.omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N
  decidedCount_nonneg := by
    intro σ N
    exact Finset.sum_nonneg fun T _ => M8.stratumCount_nonneg _ T N
  undecidedCount_nonneg := by
    intro N
    rw [sub_nonneg]
    exact totalDecided_le_box_W3 n K hn N
  typeMenu := WildMenuPrep.typeMenuW n
  typeMenu_degree := WildMenuPrep.typeMenuW_degree n
  decidedCount_off_menu := by
    intro σ N hσ
    rw [omMenuW3_eq_empty n K hσ, Finset.sum_empty]
  box_partition := by
    intro N
    ring
  decided_mono := fun σ => WildMenuW3.normSum_omMenuW3_mono n K hn σ
  densityVal := fun σ => ∑ T ∈ WildMenuW3.omMenuW3 n K σ, OMCountV2.omCount T M9.realP
  decided_tendsto := by
    intro σ
    have hpush : (fun N => (∑ T ∈ WildMenuW3.omMenuW3 n K σ,
          M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N))
        = fun N => ∑ T ∈ WildMenuW3.omMenuW3 n K σ,
            M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N) := by
      funext N; rw [Finset.sum_div]
    rw [hpush]
    exact tendsto_finsetSum (WildMenuW3.omMenuW3 n K σ)
      (fun T hT => hNodeLimit_omMenuW3 n K hn σ T hT)
  upper_tail := by
    intro σ N K' hNK
    have hBK := RealInstanceV2.realP_pow_pos (n * K')
    have hBN := RealInstanceV2.realP_pow_pos (n * N)
    -- normalized undecided mass at N = 1 − normalized total decided at N (box partition):
    have hundec : ((M9.realP : ℚ) ^ (n * N)
          - ∑ σ' ∈ WildMenuPrep.typeMenuW n,
              ∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T N)
          / (M9.realP : ℚ) ^ (n * N)
        = 1 - (∑ σ' ∈ WildMenuPrep.typeMenuW n,
              ∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N) := by
      rw [sub_div, div_self (ne_of_gt hBN)]
    by_cases hσ : σ ∈ WildMenuPrep.typeMenuW n
    · -- per-σ increment ≤ total increment (all σ'-summands monotone, `normSum_omMenuW3_mono`):
      have hstep : ∀ σ' ∈ WildMenuPrep.typeMenuW n,
          (0 : ℚ) ≤ (∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T K')
                / (M9.realP : ℚ) ^ (n * K')
            - (∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T N)
                / (M9.realP : ℚ) ^ (n * N) := fun σ' _ =>
        sub_nonneg.mpr (WildMenuW3.normSum_omMenuW3_mono n K hn σ' hNK)
      have hsingle := Finset.single_le_sum (f := fun σ' =>
          (∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T K')
            / (M9.realP : ℚ) ^ (n * K')
          - (∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N)) hstep hσ
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsingle
      -- total increment ≤ 1 − total_N norm (windowed box bound at K'):
      have htotK : (∑ σ' ∈ WildMenuPrep.typeMenuW n,
            ∑ T ∈ WildMenuW3.omMenuW3 n K σ', M8.stratumCount (M9.rawCount n) T K')
          / (M9.realP : ℚ) ^ (n * K') ≤ 1 :=
        (div_le_one hBK).mpr (totalDecided_le_box_W3 n K hn K')
      linarith
    · -- off-menu σ: decided ≡ 0, RHS = 0 + (nonnegative undecided mass):
      rw [omMenuW3_eq_empty n K hσ]
      simp only [Finset.sum_empty, zero_div, zero_add]
      apply div_nonneg _ (le_of_lt hBN)
      rw [sub_nonneg]
      exact totalDecided_le_box_W3 n K hn N

/-! ## 3. `realDW3` — the abstract-coefficient V2 Montes data over `realMW3` -/

/-- **The Wave-3 H-WINDOW real Montes data (`realDW3`).** `C := omCount` over the WINDOWED
σ-keyed menu; `C_isRational := omCount_isRational` (THEOREM); `stratum_tendsto_C` = the per-leg
counting limits `hNodeLimit_omMenuW3` (order-0 legs + the banked UNCONDITIONAL H-generic wild
self-loop leg, per admissible k); `partition` definitional. -/
noncomputable def realDW3 (n K : ℕ) (hn : 0 < n) :
    LeanUrat.MontesV2.MontesDataV2 M9.realP n (realMW3 n K hn) where
  shapesOf := fun σ => WildMenuW3.omMenuW3 n K σ
  stratumCount := M8.stratumCount (M9.rawCount n)
  partition := fun _ _ => rfl
  C := fun T q' => OMCountV2.omCount T q'
  C_isRational := fun T => OMCountV2.omCount_isRational T
  stratum_tendsto_C := fun σ T hT => hNodeLimit_omMenuW3 n K hn σ T hT

/-! ## 4. `realFW3` — the window-K real density foundation -/

/-- **The Wave-3 H-WINDOW real `DensityFoundation` (`realFW3 K`).** `density m σ q' :=
∑_{T ∈ omMenuW3 m K σ} omCount T q'` — the WINDOWED σ-keyed engine menu-sum, UNGUARDED:
nonnegative at EVERY natural `q'` (order-0 shapes by `RealInstanceV2.omCount_sepShape_nonneg`,
window legs by `WildMenuW3.omCount_ramShapeAt_nonneg`). `DensityFoundation.density` has no K
slot, so the window bound K is a PARAMETER of the foundation. The structural `decomposition` is
the m×C split `RealInstanceW.omCount_eq_mul_all` (exact for every shape — single-configuration
nodes), with `multiplicity := omMultiplicity` and `clusterVolume := omVolume`. -/
noncomputable def realFW3 (K : ℕ) : DensityFoundation where
  density := fun m σ q' => ∑ T ∈ WildMenuW3.omMenuW3 m K σ, OMCountV2.omCount T q'
  clusterVolume := fun T q' => OMCountV2.omVolume T q'
  shapes := fun m σ => WildMenuW3.omMenuW3 m K σ
  multiplicity := fun T => OMCountV2.omMultiplicity T
  decomposition := by
    intro m σ _ q' _
    exact Finset.sum_congr rfl fun T _ => RealInstanceW.omCount_eq_mul_all T q'
  density_nonneg := by
    intro m σ q'
    refine Finset.sum_nonneg fun T hT => ?_
    rw [WildMenuW3.omMenuW3, Finset.mem_union] at hT
    rcases hT with h | h
    · rw [Order0.sepShapesOf, Finset.mem_image] at h
      obtain ⟨lam, -, rfl⟩ := h
      exact RealInstanceV2.omCount_sepShape_nonneg m lam q'
    · rw [WildMenuW3.mem_ramShapes3] at h
      obtain ⟨hc, k, -, rfl⟩ := h
      exact WildMenuW3.omCount_ramShapeAt_nonneg hc k q'

/-! ## 5. The Wave-3 capstones -/

/-- **`montes_unconditional_w3` — the Wave-3 H-WINDOW capstone** (statement VERBATIM
`RealInstanceW.montes_unconditional_w` with the WINDOWED menu `omMenuW3 n K` for `omMenuW n`,
fired at the window-K instance `(realMW3, realDW3, realFW3 K)`).

**What this certifies** (degree-`n` type `σ`, `n > 0`, window bound `K`):
* (R) UNCONDITIONAL uniform rationality of the WINDOWED σ-keyed engine density
  `g_σ(q') := ∑_{T ∈ omMenuW3 n K σ} omCount T q'` — one `num/den`, denominator nonvanishing
  at every `q' > 1`;
* (V) the DECIDED-DENSITY TIE, UNCONDITIONAL: `(realMW3 n K hn).countingDensity σ` — the
  genuine `N → ∞` limit of the real normalized classifier-fiber counts over the WINDOWED
  menu — equals `num(realP)/den(realP)`. For **constant-e ramified σ** and `K > 1` this
  certifies STRICTLY MORE of the type's density than Wave 1 (gates G1/G2,
  `OM/RealInstanceW3Gates.lean`: `9/64 > 1/8` at n = 2, K = 3, realP = 2);
* (P) palindromy `IsPalindromic num den` — CONDITIONAL on the explicit HYPOTHESIS `htameFE`
  (about `realFW3 K`; never an axiom).

**Honest scope (blueprint §3 — what this does NOT claim):**
* the ramified menu covers ONLY constant-e ramified types, each with the K-WINDOW of
  admissible single-slope all-μ=1 strata (`H = F·k`, `k ≤ K`, `gcd(k, e) = 1`): the certified
  ramified value is the K-TRUNCATED decided density — a strictly larger leading sum than
  Wave 1, still NOT the full type density (the geometric tail = the recursive self-loop wall,
  `notes/SELFLOOP_GENERALK_WALL.md`, stands);
* mixed-e (multi-slope) types get NO ramified menu entry; order ≥ 2 shapes absent;
* NO exhaustiveness claim: `countingDensity` is the DECIDED limit; the undecided pool does not
  drain at any finite order or window (see `montes_unconditional_w3_exhaustive` for the honest
  bracket-uniqueness form under the explicit `hExhaust` hypothesis);
* NOT unconditional palindromy: palindromy is exactly the content of `htameFE`.

`#print axioms` must be Lean core ONLY (`AxCheck` section): every tame/counting input is a
hypothesis or a theorem, never an axiom. -/
theorem montes_unconditional_w3 (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation (realFW3 K) n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ WildMenuW3.omMenuW3 n K σ, OMCountV2.omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW3 n K hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hall, hval, hpalin⟩ :=
    LeanUrat.MontesV2.goal_theorem_montes (realMW3 n K hn) (realDW3 n K hn) σ (realFW3 K) hσ
      (fun _ _ => rfl) htameFE
  exact ⟨num, den, hden, hall, hval (by norm_num [M9.realP]), hpalin⟩

/-- **`montes_unconditional_w3_exhaustive` — the exhaustive companion of the Wave-3 H-WINDOW
capstone** (statement VERBATIM `RealInstanceW.montes_unconditional_w_exhaustive` with
`omMenuW3 n K` for `omMenuW n`). Adds the honest exhaustiveness input `hExhaust` (the
normalized undecided mass over the window-K menu drains — an EXPLICIT hypothesis, NOT
discharged: the classifier does not drain at any finite order, and the window-K wild menu
carries only the first ≤ K admissible-height strata of each type) and concludes, on top of the
`montes_unconditional_w3` clauses, the BRACKET-UNIQUENESS form of the full-density tie: any `d`
consistent with every level-`N ≥ 1` bracket equals `(realMW3 n K hn).countingDensity σ`.
Honest scope as in `montes_unconditional_w3`. -/
theorem montes_unconditional_w3_exhaustive (n K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation (realFW3 K) n σ)
    (hExhaust : Filter.Tendsto
      (fun N => (realMW3 n K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds 0)) :
    (∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ WildMenuW3.omMenuW3 n K σ, OMCountV2.omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW3 n K hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        (realMW3 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N) ≤ d ∧
        d ≤ (realMW3 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
              + (realMW3 n K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N)) →
      d = (realMW3 n K hn).countingDensity σ := by
  refine ⟨montes_unconditional_w3 n K hn σ hσ htameFE, ?_⟩
  intro d hd
  have hlim : Filter.Tendsto
      (fun N => (realMW3 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds ((realMW3 n K hn).countingDensity σ)) :=
    (realMW3 n K hn).decided_tendsto σ
  have h1 : (realMW3 n K hn).countingDensity σ ≤ d := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).1
  have h2 : d ≤ (realMW3 n K hn).countingDensity σ := by
    have hlim2 : Filter.Tendsto
        (fun N => (realMW3 n K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
          + (realMW3 n K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop (nhds ((realMW3 n K hn).countingDensity σ)) := by
      simpa using hlim.add hExhaust
    refine ge_of_tendsto hlim2 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).2
  exact le_antisymm h2 h1

/-! ## 6. The Wave-1 recovery gate -/

/-- **`montes_w3_one_recovers` — the Wave-1 recovery gate (blueprint §2 item 2: "K = 1 must
recover Wave 1's values").** The window-1 instance's counting density IS Wave 1's, at every
degree and type: both are DEFINED as their menu sums (`densityVal`), and the menus coincide
(`WildMenuW3.omMenuW3_one`). -/
theorem montes_w3_one_recovers (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    (realMW3 n 1 hn).countingDensity σ = (RealInstanceW.realMW n hn).countingDensity σ := by
  show (∑ T ∈ WildMenuW3.omMenuW3 n 1 σ, OMCountV2.omCount T M9.realP)
    = ∑ T ∈ WildMenu.omMenuW n σ, OMCountV2.omCount T M9.realP
  rw [WildMenuW3.omMenuW3_one]

end LeanUrat.OM.RealInstanceW3

section AxCheck

-- Wave-3 gate (blueprint §2 item 2): the H-WINDOW capstones' footprints must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
-- The tame content enters as the HYPOTHESIS `htameFE`; every window counting leg is the banked
-- H-generic THEOREM `hnode_selfloop_over_Bclassify_R` — no axiom anywhere on the path.
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_w3_one_recovers

end AxCheck
