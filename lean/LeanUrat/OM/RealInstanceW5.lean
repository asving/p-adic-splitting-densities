/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW4
import LeanUrat.OM.ChainMenu

/-!
# OM/RealInstanceW5 — the Wave-5 DESCENT-CHAIN real instance (blueprint
`notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md` §2-W5b)

The depth-windowed chain sibling of `OM/RealInstanceW4.lean` over the Wave-5 σ-keyed menu
`ChainMenu.omMenu5 n D K σ = MultiSlopeMenu.omMenu4 n K σ ∪ chainShapes n D K σ`: the whole
Wave-4 menu, PLUS — at `n = 2` ONLY (the enumerator emits no other-degree chains; general-`n`
chains are the note's OPEN-D3/D5 territory) — the depth-`≤ D` recenter-descend chains
`chainLit ms leaf` with window slopes `m_t ∈ [1, K]` and window leaves (`ram H`, odd
`H ≤ 2K−1`; `inert m ≤ K`; `split k ≤ K`), keyed by leaf type.

**The count is `stratumCount5`**: on chain literals the GENUINE `Nat.card` of the `ChainCell`
digit fiber (W5a's staircase-transported (S1)∧(S2) chain conditions composed through
`descendPair`, ending in the leaf's digit conditions); the Wave-4 count on every other shape.
**The coefficient is `C5`**: the chain closed form
`chainC = (q−1)^depth · leafPool(q) · q^{−(3·Σms + eLeaf)}` on chain literals, `C4` else —
per the accepted note's §7 Case-A ledger (`OM/RealInstanceW5Gates.lean` pins the absolute
values `1/64, 1/512, 1/256, …` at `p = 2`).

**Honest scope (stated on every capstone).**
* The chain fibers are DIGIT-CONDITION fibers (the counting side); that the OM classifier's
  full-type read of these fibers is the leaf's type (translation invariance of factorization
  types under the recentering automorphism — [COUNT], note §1/§6) is **W5c's** faithfulness
  boundary (scope #4 + the boundary-#5 lift-invariance pin), NOT claimed here. `typeOf5`
  keying is definitional.
* The chain menu is a finite `(D, K)` window: the certified value is the decided density of
  the windowed chain strata — a PARTIAL SUM of the type's full tower (W6's series assembly
  takes `D → ∞`). No exhaustiveness claim (`hExhaust` stays an explicit hypothesis).
* At odd `p` the even-height split-residual leaf (pool `(q−1)(q−2)/2`) is deferred to W6; at
  the real prime `p = 2` its pool is empty (the ledger's honest-empty pool), so the `p = 2`
  Case-A tree is fully represented.
* Recovery: at `D = 0` the instance IS the Wave-4 instance (`montes_w5_recovers`).

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.RealInstanceW5

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel Polynomial Filter Topology
open LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.ChainMenu
open LeanUrat.OM.MultiSlopeMenu (omMenu4 typeMenu4 stratumCount4 C4)

/-! ## 1. Helper bank -/

/-- **Off-menu emptiness over the (unchanged) Wave-4 type menu**: the three chain types are
already menu types, so `typeMenu5 := typeMenu4` and off-menu σ have empty Wave-5 menus. -/
theorem omMenu5_eq_empty (n D K : ℕ) {σ : FactorizationType}
    (hσ : σ ∉ typeMenu4 n) : omMenu5 n D K σ = ∅ := by
  rw [omMenu5, RealInstanceW4.omMenu4_eq_empty n K hσ, chainShapes_eq_empty_off_menu hσ,
    Finset.union_empty]

/-- **Level-0 vanishing on the whole Wave-5 menu**: Wave-4 legs banked; chain legs are below
their thresholds (`N₀ ≥ 3 > 0`). -/
theorem stratumCount5_level0 {n D K : ℕ} (hn : 0 < n) {σ : FactorizationType}
    {T : ClusterShape} (hT : T ∈ omMenu5 n D K σ) : stratumCount5 n T 0 = 0 := by
  rcases mem_omMenu5_cases hT with h4 | ⟨hn2, ms, leaf, hms, hmsne, hleaf, rfl⟩
  · rw [stratumCount5_of_headOrd_ne (headOrd_of_mem_omMenu4 h4)]
    exact RealInstanceW4.stratumCount4_level0 hn h4
  · rw [stratumCount5_chainLit, card_chainCell_smallN M9.realP ms leaf
      (by have := one_le_leafNeed leaf; omega), Nat.cast_zero]

/-- **The per-leg counting limit on the whole Wave-5 menu** — Wave-4 legs by the banked
`hNodeLimit_omMenu4`, chain legs by the eventually-constant staircase
(`stratum_tendsto_C5_chain`). Discharges `realMW5.decided_tendsto` and
`realDW5.stratum_tendsto_C`. -/
theorem hNodeLimit_omMenu5 (n D K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (T : ClusterShape) (hT : T ∈ omMenu5 n D K σ) :
    Filter.Tendsto
      (fun N => stratumCount5 n T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (C5 T M9.realP)) := by
  rcases mem_omMenu5_cases hT with h4 | ⟨hn2, ms, leaf, hms, hmsne, hleaf, rfl⟩
  · have hne2 := headOrd_of_mem_omMenu4 h4
    rw [C5_of_headOrd_ne hne2]
    refine (RealInstanceW4.hNodeLimit_omMenu4 n K hn σ T h4).congr fun N => ?_
    rw [stratumCount5_of_headOrd_ne hne2]
  · subst hn2
    rw [C5_chainLit]
    exact stratum_tendsto_C5_chain ms leaf
      (fun x hx => (((mem_msMenu D K ms).mp hms).2 x hx).1) (of_mem_chainLeaves hleaf).1

/-- **The total decided count is bounded by the box at EVERY level** (`N = 0` collapse
included). -/
theorem totalDecided_le_box_W5 (n D K : ℕ) (hn : 0 < n) (N : ℕ) :
    (∑ σ ∈ typeMenu4 n, ∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_eq_zero fun σ _ =>
      Finset.sum_eq_zero fun T hT => stratumCount5_level0 hn hT]
    exact le_of_lt (RealInstanceV2.realP_pow_pos _)
  · exact sum_stratumCount5_le_box n D K N hn hN

/-! ## 2. The m×C split on the Wave-5 coefficient (the `realFW5.decomposition` feed) -/

/-- **The Wave-5 multiplicity polynomial**: `chainMult` (a genuine `Polynomial ℚ`:
`(X−1)^depth · leafMult`) on chain literals, `mult4` else. -/
noncomputable def mult5 (T : ClusterShape) : Polynomial ℚ :=
  if MultiSlopeMenu.headOrd T = 2 then chainMult (decodeMs T) (decodeLeaf T)
  else RealInstanceW4.mult4 T

/-- **The Wave-5 cluster volume**: the pure monomial inverse `q^{−chainVolExp}` on chain
literals, `vol4` else. -/
noncomputable def vol5 (T : ClusterShape) (q' : ℕ) : ℚ :=
  if MultiSlopeMenu.headOrd T = 2 then
    ((q' : ℚ) ^ chainVolExp (decodeMs T) (decodeLeaf T))⁻¹
  else RealInstanceW4.vol4 T q'

/-- **The m×C split for the Wave-5 coefficient on EVERY shape**: on chain literals `chainC`
IS `chainMult.eval · volExp-inverse` by definition; on the old shapes the banked
`C4_eq_mul_all`. -/
theorem C5_eq_mul_all (T : ClusterShape) (q' : ℕ) :
    C5 T q' = (mult5 T).eval (q' : ℚ) * vol5 T q' := by
  by_cases h : MultiSlopeMenu.headOrd T = 2
  · rw [C5, if_pos h, mult5, if_pos h, vol5, if_pos h]
    rfl
  · rw [C5_of_headOrd_ne h, mult5, if_neg h, vol5, if_neg h]
    exact RealInstanceW4.C4_eq_mul_all T q'

/-- Per-member nonnegativity of the Wave-4 coefficient (extraction of the
`realFW4.density_nonneg` case analysis, reusable per shape). -/
theorem C4_nonneg_of_mem {m K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu4 m K σ) (q' : ℕ) : 0 ≤ C4 T q' := by
  rcases MultiSlopeMenu.mem_omMenu4_cases hT with hold | ⟨hOK, rfl⟩
  · rw [MultiSlopeMenu.C4_of_headOrd_ne
      (by rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hold]; exact zero_ne_one)]
    rcases MultiSlopeMenu.mem_omMenuW3_cases hold with ⟨lam, rfl⟩ | ⟨hc, k, -, -, rfl⟩
    · exact RealInstanceV2.omCount_sepShape_nonneg m lam q'
    · exact WildMenuW3.omCount_ramShapeAt_nonneg hc k q'
  · rw [RealInstanceW4.C4_multiSideLit m σ q']
    exact RealInstanceW4.prod_omCount_sideSub_nonneg q' (sidePairs (MultiSlopeMenu.mixedPath σ))
      (MultiSlopeMenu.mixedSh σ) (MultiSlopeMenu.shapesFor_mixedPath hOK)
      (MultiSlopeMenu.allMuOne_mixedSh σ) (MultiSlopeMenu.allNonempty_mixedSh σ)

/-- Per-member nonnegativity of the Wave-5 coefficient at every natural `q'`. -/
theorem C5_nonneg_of_mem {m D K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu5 m D K σ) (q' : ℕ) : 0 ≤ C5 T q' := by
  rcases mem_omMenu5_cases hT with h4 | ⟨hn2, ms, leaf, hms, hmsne, hleaf, rfl⟩
  · rw [C5_of_headOrd_ne (headOrd_of_mem_omMenu4 h4)]
    exact C4_nonneg_of_mem h4 q'
  · rw [C5_chainLit]
    exact chainC_nonneg ms leaf q'

/-! ## 3. `realMW5` — the Wave-5 real counting model -/

/-- **The Wave-5 DESCENT-CHAIN real counting model (blueprint §2-W5b, `realMW5`).** The
σ-keyed decided count is the fiber sum over the Wave-5 menu `omMenu5 n D K σ` with the
unified count `stratumCount5` (genuine `ChainCell` digit fibers on the chain legs, the Wave-4
counts on the old legs — all subsets of the SAME box); the undecided count is the honest box
residual over the UNCHANGED type menu `typeMenu4 n`. Every field genuinely discharged:
* `undecidedCount_nonneg` — the Wave-5 keystone box bound `sum_stratumCount5_le_box`
  (pairwise-disjoint fibers across chains and both W4 classifiers) + level-0 vanishing;
* `decided_mono` — `normSum_omMenu5_mono` (W4 part banked; each chain leg a
  `0, …, 0, c, c, …` staircase joining at `N₀ = 2·Σms + leafNeed`);
* `decided_tendsto` — per-leg limits `hNodeLimit_omMenu5`;
* `upper_tail` — the Wave-1/3/4 total-increment absorption verbatim, over the Wave-5 bank;
* cross-σ soundness — a Wave-5 menu shape names its type (`eq_of_mem_omMenu5`).

**Honest scope**: the chain `densityVal` summands are the `(D, K)`-windowed chain strata's
decided densities (a partial sum of the descent tower; W6 resums); counting-side only —
per-fiber TYPE faithfulness is W5c's boundary. -/
noncomputable def realMW5 (n D K : ℕ) (hn : 0 < n) : CountingModel M9.realP n where
  hq := by norm_num [M9.realP]
  decidedCount := fun σ N => ∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N
  undecidedCount := fun N => (M9.realP : ℚ) ^ (n * N)
    - ∑ σ ∈ typeMenu4 n, ∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N
  decidedCount_nonneg := by
    intro σ N
    exact Finset.sum_nonneg fun T _ => stratumCount5_nonneg n T N
  undecidedCount_nonneg := by
    intro N
    rw [sub_nonneg]
    exact totalDecided_le_box_W5 n D K hn N
  typeMenu := typeMenu4 n
  typeMenu_degree := RealInstanceW4.typeMenu4_degree n
  decidedCount_off_menu := by
    intro σ N hσ
    rw [omMenu5_eq_empty n D K hσ, Finset.sum_empty]
  box_partition := by
    intro N
    ring
  decided_mono := fun σ => normSum_omMenu5_mono n D K hn σ
  densityVal := fun σ => ∑ T ∈ omMenu5 n D K σ, C5 T M9.realP
  decided_tendsto := by
    intro σ
    have hpush : (fun N => (∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N)
          / (M9.realP : ℚ) ^ (n * N))
        = fun N => ∑ T ∈ omMenu5 n D K σ,
            stratumCount5 n T N / (M9.realP : ℚ) ^ (n * N) := by
      funext N
      rw [Finset.sum_div]
    rw [hpush]
    exact tendsto_finsetSum (omMenu5 n D K σ)
      (fun T hT => hNodeLimit_omMenu5 n D K hn σ T hT)
  upper_tail := by
    intro σ N K' hNK
    have hBK := RealInstanceV2.realP_pow_pos (n * K')
    have hBN := RealInstanceV2.realP_pow_pos (n * N)
    have hundec : ((M9.realP : ℚ) ^ (n * N)
          - ∑ σ' ∈ typeMenu4 n, ∑ T ∈ omMenu5 n D K σ', stratumCount5 n T N)
          / (M9.realP : ℚ) ^ (n * N)
        = 1 - (∑ σ' ∈ typeMenu4 n, ∑ T ∈ omMenu5 n D K σ', stratumCount5 n T N)
            / (M9.realP : ℚ) ^ (n * N) := by
      rw [sub_div, div_self (ne_of_gt hBN)]
    by_cases hσ : σ ∈ typeMenu4 n
    · have hstep : ∀ σ' ∈ typeMenu4 n,
          (0 : ℚ) ≤ (∑ T ∈ omMenu5 n D K σ', stratumCount5 n T K')
                / (M9.realP : ℚ) ^ (n * K')
            - (∑ T ∈ omMenu5 n D K σ', stratumCount5 n T N)
                / (M9.realP : ℚ) ^ (n * N) := fun σ' _ =>
        sub_nonneg.mpr (normSum_omMenu5_mono n D K hn σ' hNK)
      have hsingle := Finset.single_le_sum (f := fun σ' =>
          (∑ T ∈ omMenu5 n D K σ', stratumCount5 n T K')
            / (M9.realP : ℚ) ^ (n * K')
          - (∑ T ∈ omMenu5 n D K σ', stratumCount5 n T N)
            / (M9.realP : ℚ) ^ (n * N)) hstep hσ
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsingle
      have htotK : (∑ σ' ∈ typeMenu4 n,
            ∑ T ∈ omMenu5 n D K σ', stratumCount5 n T K')
          / (M9.realP : ℚ) ^ (n * K') ≤ 1 :=
        (div_le_one hBK).mpr (totalDecided_le_box_W5 n D K hn K')
      linarith
    · rw [omMenu5_eq_empty n D K hσ]
      simp only [Finset.sum_empty, zero_div, zero_add]
      apply div_nonneg _ (le_of_lt hBN)
      rw [sub_nonneg]
      exact totalDecided_le_box_W5 n D K hn N

/-! ## 4. `realDW5` — the abstract-coefficient V2 Montes data over `realMW5` -/

/-- **The Wave-5 real Montes data (`realDW5`).** `C := C5` — chain closed forms on chain
literals (`chainC`, rationality by `(poly)·q^{−V}` closure), `C4` else;
`stratum_tendsto_C := hNodeLimit_omMenu5`; `partition` definitional. -/
noncomputable def realDW5 (n D K : ℕ) (hn : 0 < n) :
    LeanUrat.MontesV2.MontesDataV2 M9.realP n (realMW5 n D K hn) where
  shapesOf := fun σ => omMenu5 n D K σ
  stratumCount := stratumCount5 n
  partition := fun _ _ => rfl
  C := fun T q' => C5 T q'
  C_isRational := fun T => C5_isRational T
  stratum_tendsto_C := fun σ T hT => hNodeLimit_omMenu5 n D K hn σ T hT

/-! ## 5. `realFW5` — the Wave-5 real density foundation -/

/-- **The Wave-5 real `DensityFoundation` (`realFW5 D K`).** `density m σ q' :=
∑_{T ∈ omMenu5 m D K σ} C5 T q'`. The structural `decomposition` is the per-family m×C split
`C5_eq_mul_all` with `multiplicity := mult5` (the genuine polynomial `(X−1)^depth · leafMult`
on chains) and `clusterVolume := vol5` (`q^{−chainVolExp}` on chains). UNGUARDED
nonnegativity at every natural `q'` (`C5_nonneg_of_mem`). -/
noncomputable def realFW5 (D K : ℕ) : DensityFoundation where
  density := fun m σ q' => ∑ T ∈ omMenu5 m D K σ, C5 T q'
  clusterVolume := fun T q' => vol5 T q'
  shapes := fun m σ => omMenu5 m D K σ
  multiplicity := fun T => mult5 T
  decomposition := by
    intro m σ _ q' _
    exact Finset.sum_congr rfl fun T _ => C5_eq_mul_all T q'
  density_nonneg := by
    intro m σ q'
    exact Finset.sum_nonneg fun T hT => C5_nonneg_of_mem hT q'

/-! ## 6. The Wave-5 capstones -/

/-- **`montes_unconditional_w5` — the Wave-5 DESCENT-CHAIN capstone** (statement VERBATIM
`RealInstanceW4.montes_unconditional_w4` with the Wave-5 menu `omMenu5 n D K` for
`omMenu4 n K` and the Wave-5 coefficient `C5 T q'` for `C4 T q'`; fired at the Wave-5
instance `(realMW5, realDW5, realFW5 D K)`).

**What this certifies** (degree-`n` type `σ`, `n > 0`, depth window `D`, height window `K`):
* (R) UNCONDITIONAL uniform rationality of the Wave-5 σ-keyed engine density
  `g_σ(q') := ∑_{T ∈ omMenu5 n D K σ} C5 T q'` — one `num/den`, denominator nonvanishing at
  every `q' > 1` (chain legs are `(q−1)^{k}·pool·q^{−V}`, genuinely rational);
* (V) the DECIDED-DENSITY TIE, UNCONDITIONAL: `(realMW5 n D K hn).countingDensity σ` — the
  genuine `N → ∞` limit of the real normalized fiber counts over the Wave-5 menu (genuine
  `ChainCell` digit fibers on the chain legs) — equals `num(realP)/den(realP)`. For the
  `n = 2` types this includes the FIRST machine-checked DEPTH-`≥ 1` descent-chain masses
  (gates: the §7 Case-A ledger absolute values `1/64` (Case C), `1/512`, `1/256` at `p = 2`);
* (P) palindromy `IsPalindromic num den` — CONDITIONAL on the explicit HYPOTHESIS `htameFE`
  (about `realFW5 D K`; never an axiom).

**Honest scope (blueprint §1–§2, what this does NOT claim):**
* chain fibers are counting-side digit fibers; their per-fiber Montes TYPE faithfulness (the
  translation-invariance [COUNT] lemma + Cor 1.20 in the recentered frame) is W5c's
  boundary-#4/#5 business — `typeOf5` keying is definitional here;
* the chain menu is the finite `(D, K)` window: the certified value is a PARTIAL SUM of the
  descent tower (W6 resums `D → ∞` and discharges exhaustion); no exhaustiveness claim;
* at odd `p` the even-height split-residual leaf is deferred (empty pool at `realP = 2`);
* `n ≠ 2` degrees carry NO chains (the enumerator's n=2-only emission);
* NOT unconditional palindromy: palindromy is exactly the content of `htameFE`. -/
theorem montes_unconditional_w5 (n D K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation (realFW5 D K) n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ChainMenu.omMenu5 n D K σ, ChainMenu.C5 T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW5 n D K hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hall, hval, hpalin⟩ :=
    LeanUrat.MontesV2.goal_theorem_montes (realMW5 n D K hn) (realDW5 n D K hn) σ (realFW5 D K)
      hσ (fun _ _ => rfl) htameFE
  exact ⟨num, den, hden, hall, hval (by norm_num [M9.realP]), hpalin⟩

/-- **`montes_unconditional_w5_exhaustive` — the exhaustive companion** (statement VERBATIM
`RealInstanceW4.montes_unconditional_w4_exhaustive` with `omMenu5 n D K`/`C5` for
`omMenu4 n K`/`C4`). Adds the honest exhaustiveness input `hExhaust` (an EXPLICIT hypothesis,
NOT discharged — the `(D, K)` window does not drain the box; W6's envelope 3.4′(a) is the
planned discharge) and concludes the BRACKET-UNIQUENESS form of the full-density tie. -/
theorem montes_unconditional_w5_exhaustive (n D K : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation (realFW5 D K) n σ)
    (hExhaust : Filter.Tendsto
      (fun N => (realMW5 n D K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds 0)) :
    (∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ChainMenu.omMenu5 n D K σ, ChainMenu.C5 T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      ((realMW5 n D K hn).countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        (realMW5 n D K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N) ≤ d ∧
        d ≤ (realMW5 n D K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
              + (realMW5 n D K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N)) →
      d = (realMW5 n D K hn).countingDensity σ := by
  refine ⟨montes_unconditional_w5 n D K hn σ hσ htameFE, ?_⟩
  intro d hd
  have hlim : Filter.Tendsto
      (fun N => (realMW5 n D K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds ((realMW5 n D K hn).countingDensity σ)) :=
    (realMW5 n D K hn).decided_tendsto σ
  have h1 : (realMW5 n D K hn).countingDensity σ ≤ d := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).1
  have h2 : d ≤ (realMW5 n D K hn).countingDensity σ := by
    have hlim2 : Filter.Tendsto
        (fun N => (realMW5 n D K hn).decidedCount σ N / (M9.realP : ℚ) ^ (n * N)
          + (realMW5 n D K hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop (nhds ((realMW5 n D K hn).countingDensity σ)) := by
      simpa using hlim.add hExhaust
    refine ge_of_tendsto hlim2 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hd N hN).2
  exact le_antisymm h2 h1

/-! ## 7. The Wave-4 recovery gate -/

/-- **`montes_w5_recovers` — the Wave-4 recovery gate**: at depth window `D = 0` (no chains),
at EVERY degree, type, and height window, the Wave-5 instance's counting density IS Wave 4's —
the menus coincide (`omMenu5_zero`) and on every Wave-4 shape the Wave-5 coefficient IS `C4`. -/
theorem montes_w5_recovers (n K : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    (realMW5 n 0 K hn).countingDensity σ
      = (RealInstanceW4.realMW4 n K hn).countingDensity σ := by
  show (∑ T ∈ omMenu5 n 0 K σ, C5 T M9.realP) = ∑ T ∈ omMenu4 n K σ, C4 T M9.realP
  rw [omMenu5_zero]
  exact Finset.sum_congr rfl fun T hT => C5_of_headOrd_ne (headOrd_of_mem_omMenu4 hT) _

end LeanUrat.OM.RealInstanceW5

section AxCheck

-- Wave-5 gate (blueprint §2-W5b): the DESCENT-CHAIN capstones' footprints must be Lean core
-- ONLY (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line
-- event). The tame content enters as the HYPOTHESIS `htameFE`; the chain counting legs are
-- the banked THEOREM chain `stratum_tendsto_C5_chain` ← `card_chainCell` ←
-- `stratumPairEquiv` (W5a) — no axiom anywhere on the path.
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5_exhaustive
#print axioms LeanUrat.OM.RealInstanceW5.montes_w5_recovers

end AxCheck
