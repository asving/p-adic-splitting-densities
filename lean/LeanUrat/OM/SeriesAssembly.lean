/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW5
import LeanUrat.OM.RealInstanceW5Gates

/-!
# OM/SeriesAssembly — Wave 6: the n = 2 series assembly, the undecided envelope, and the
first FULL per-type density capstone (blueprint `notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md`
§2-W6; ground truth `notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` Lemma 3.4′(a) + §4)

## What this module proves (all at the real prime `p = M9.realP = 2`, `n = 2`)

1. **The full counting model `realMW6`** — the level-`N` decided counts of the COMPLETE
   `n = 2` stratum tree: the order-0 separable root reads (`SepSplitCell`/`SepInertCell`), and,
   at EVERY residue point `c ∈ F_2 = {0, 1}` (via the recentering translate
   `f(x) ↦ f(x + c)`, which on the coefficient pair is exactly `RecenterBox.affineEquiv` at
   levels `(N, N)`), ALL depth-`k ≥ 0` descend chains ending in every leaf kind — including the
   depth-0 even-height inert/split cluster leaves that no earlier wave's menu carried.

2. **The undecided envelope (note Lemma 3.4′(a), the ⟨stall containment + relaxed chain sum⟩
   proof transcribed)**: `undecided_envelope` —
   `undecidedCount6 N / p^{2N} ≤ (⌊N/2⌋ + 1) · p^{−(N−1)}` for every `N ≥ 1` (the note proved
   `N ≥ 4`; the Lean argument closes from `N ≥ 1`). Ingredients: the covering
   `cluster_covering` (every cluster pair either realizes a terminating chain stratum within
   budget or lies in an explicit `StallPair` stall stratum — the (3f) stall containment
   `v(a₀) ≥ B − 1` at some frame of its read), the stall count bound `card_stallPair_le`
   (`≤ (p−1)^k · p^{L₁ − Σm}` — budget recovery), and the ≤-relaxed chain sum
   `msW_half_le` (`Σ_{ms} (1/2)^{Σm} ≤ D + 1` over the depth-`≤ D` slope menu — the note's
   (3h) relaxation `Σ_{k ≤ N/2} r₂^k` with `r₂ = 1` critical).

3. **`hExhaust_n2`** — the envelope → 0: the FIRST unconditional discharge of the exhaustion
   hypothesis (pure counting; no axiom).

4. **The value ties by squeeze** (`fullDecided_tendsto`): each type's normalized decided count
   is ≤ its closed-form value (the per-step geometric fixpoint bound `msW_eighth_le`:
   `Σ_{ms} (1/8)^{Σm} ≤ 7/6 = 1/(1 − 1/7)`, `1/7 = Σ_m (q−1)q^{−3m}` at `q = 2` — the note §4's
   per-step descend ratio `1/(q²+q+1)`), and ≥ `1/3 − envelope` by the box partition; hence
   `→ 1/3` for each of the three degree-2 types. Note §7 ledger match: `β_ram = q/(q+1)`
   cluster-conditional, full-box ramified density `1/(q+1) = 1/3` at `q = 2` ✓; inert/split
   `q/(2(q+1)) = 1/3` at `q = 2` ✓; sum of the three = 1 ✓ (`gate_w6_checksum`).

5. **The capstone `montes_unconditional_n2_full`** — for every degree-2 type σ: uniform
   rationality of the closed-form density family (`fullValueFn`), the value tie
   `(realMW6).countingDensity σ = num(2)/den(2)`, palindromy conditional on `htameFE`, AND the
   bracket-uniqueness full-density clause fired OUTRIGHT (`hExhaust` supplied by
   `hExhaust_n2`, not hypothesized) — the program's first full-tower per-type density.

## The closed forms (the `q`-uniform family certified in clause (R); `q = 2` values in ⟨⟩)

* ramified `{(2,1)}` : `1/(q+1)` ⟨1/3⟩ — tower: `q · q^{−2} · β_ram`, `β_ram = q/(q+1)`;
* inert `{(1,2)}` : `q/(2(q+1))` ⟨1/3⟩ — order-0 `(q−1)/(2q)` + tower `1/(2q(q+1))`;
* split `{(1,1),(1,1)}` : `(q³ − q + 2)/(2q²(q+1))` ⟨1/3⟩ — order-0 `(q−1)/(2q)` + two-sided
  tower `1/(q²(q+1))`. NOTE: at general `q` the split closed form differs from the true split
  density `q/(2(q+1))` by `(q−2)/(2q²(q+1))` — the even-height split-residual family (pool
  `(q−1)(q−2)/2`), which is honestly EMPTY at the real prime `q = 2` and is not in this model's
  menu (deferred, as in Wave 5). The VALUE clause at `q = 2` is the true full density; the
  `q`-family is the `p = 2`-complete tree's family.

## Honest scope

* Counting-side only: the fibers are DIGIT-CONDITION fibers (`ChainPair` composed through
  `descendPair`, translated by `affineEquiv`); that the OM classifier's full-type read of each
  fiber is the leaf's named type is faithfulness-boundary content. Wave 5c's axiom scope #4
  covers the `omMenu5` fibers; the translate fibers (`c = 1`) and the depth-0 inert/split
  cluster leaves added here are NOT yet inside any declared axiom scope — their σ-keying is
  definitional in this module (a W6c-style scope extension is future work). NO axiom is
  consumed here: every capstone footprint must be Lean core only.
* The model `realMW6` bypasses the Finset-menu `MontesDataV2` spine for its DEFINITION (the
  full tree needs level-indexed stratum families; blueprint §3's model resolution) but is
  packaged as a genuine `CountingModel`, and a one-marker-shape-per-type `MontesDataV2`
  instance (`realDW6`) reuses `MontesV2.goal_theorem_montes` verbatim for the capstone. The
  markers are bookkeeping (the interface is deliberately weak, per its own docstring); the
  semantic content lives in the count definitions and the squeeze theorems here.
* `w5_window_mono` records the Wave-5 windowed family's monotonicity in the depth window `D`;
  the full model's `decided_tendsto` (the level-`N` window limit, monotone by
  `decided6_mono`) is this wave's window-limit theorem. The Wave-5 family's own `D → ∞` limit
  (which is NOT the full density: the W5 menu has one residue point and no depth-0
  inert/split cluster legs) is not computed here — see the module-end status note.

## Python cross-check dispatch (for the coordinator; not run here)

Exact values an external `p = 2, n = 2` census (mod `2^N`, `N ≤ 10`) should reproduce:
* per-type decided limits: ram → 1/3, inert → 1/3, split → 1/3 (each = the note's per-type
  totals; the census partial sums must approach from below);
* undecided mass at level `N`: `≤ (⌊N/2⌋ + 1) · 2^{−(N−1)}` (e.g. `N = 9`: ≤ 5·2^{−8} =
  5/256 ≈ 0.0195);
* per-stratum anchors already banked: depth-1 chain `(m=1) → ram 1` = 1/64 (Case C, `x²−12`),
  `(1,1) → ram 1` = 1/512, `(1) → inert 1` = 1/256, `(1) → split 1` = 1/256, depth-0
  `inert 1` (even-height, per residue point) = 1/32, `split 1` (two-sided) = 1/32,
  order-0 split = order-0 inert = 1/4.

No `sorry`, no new axiom. `AxCheck` at the end: Lean core only.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.SeriesAssembly

open scoped Classical
open LeanUrat LeanUrat.CountingModel LeanUrat.RatFn Polynomial Filter Topology
open LeanUrat.OM
open LeanUrat.OM.QuotientBox
open LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox
open LeanUrat.OM.ChainMenu

/-! ## §A. The geometric-sum bank (pure `ℚ` algebra)

The two ratios the wave needs: `1/8` (the per-step mass ratio `q^{−3m}`-with-`(q−1)`-pool at
`q = 2`, note §4's `Σ_m (q−1)q^{−3m} = 1/(q²+q+1) = 1/7`) and `1/2` (the budget-recovered
stall ratio, note (3g)'s critical `r₂ = 1` — whence the POLYNOMIAL factor `⌊N/2⌋ + 1`). -/

/-- Exact finite geometric sum at ratio `1/8`: `Σ_{m=1}^{K} (1/8)^m = (1 − (1/8)^K)/7`. -/
theorem sum_Icc_eighth (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 8) ^ m = (1 - (1 / 8 : ℚ) ^ K) / 7 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih, pow_succ]
      ring

theorem sum_Icc_eighth_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 8) ^ m ≤ 1 / 7 := by
  rw [sum_Icc_eighth]
  have h8 : (0 : ℚ) ≤ (1 / 8 : ℚ) ^ K := by positivity
  linarith

theorem sum_Icc_eighth_nonneg (K : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 8) ^ m :=
  Finset.sum_nonneg fun m _ => by positivity

/-- Exact finite geometric sum at ratio `1/2`: `Σ_{m=1}^{K} (1/2)^m = 1 − (1/2)^K`. -/
theorem sum_Icc_half (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 2) ^ m = 1 - (1 / 2 : ℚ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih, pow_succ]
      ring

theorem sum_Icc_half_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 2) ^ m ≤ 1 := by
  rw [sum_Icc_half]
  have h2 : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ K := by positivity
  linarith

/-- **The weighted slope-menu sum** `msW D K r = Σ_{ms ∈ msMenu D K} r^{Σms}` — the SHAPE-grouped
per-depth aggregation of the chain series (values `c̃` counted inside `r`'s pool factor). -/
noncomputable def msW (D K : ℕ) (r : ℚ) : ℚ := ∑ ms ∈ msMenu D K, r ^ ms.sum

theorem msW_zero (K : ℕ) (r : ℚ) : msW 0 K r = 1 := by
  unfold msW
  show ∑ ms ∈ ({[]} : Finset (List ℕ)), r ^ ms.sum = 1
  rw [Finset.sum_singleton]
  simp

/-- The depth recurrence `msW (D+1) = 1 + (Σ_{m≤K} r^m) · msW D` — the menu recursion
`msMenu (D+1) K = {[]} ∪ (Icc 1 K × msMenu D K).image cons` summed. -/
theorem msW_succ (D K : ℕ) (r : ℚ) :
    msW (D + 1) K r = 1 + (∑ m ∈ Finset.Icc 1 K, r ^ m) * msW D K r := by
  unfold msW
  show ∑ ms ∈ ({[]} : Finset (List ℕ))
      ∪ (Finset.Icc 1 K ×ˢ msMenu D K).image (fun x => x.1 :: x.2), r ^ ms.sum = _
  rw [Finset.sum_union (by
    refine Finset.disjoint_left.mpr fun _ms hms hms' => ?_
    rw [Finset.mem_singleton] at hms
    rw [Finset.mem_image] at hms'
    obtain ⟨x, -, hx⟩ := hms'
    rw [hms] at hx
    exact List.cons_ne_nil x.1 x.2 hx)]
  rw [Finset.sum_singleton, List.sum_nil, pow_zero]
  congr 1
  rw [Finset.sum_image (by
    intro x _ y _ hxy
    have h1 := List.head_eq_of_cons_eq hxy
    have h2 := List.tail_eq_of_cons_eq hxy
    exact Prod.ext h1 h2)]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun tl _ => ?_
  rw [List.sum_cons, pow_add]

theorem msW_nonneg (D K : ℕ) {r : ℚ} (hr : 0 ≤ r) : 0 ≤ msW D K r :=
  Finset.sum_nonneg fun _ms _ => pow_nonneg hr _

/-- **The fixpoint bound at ratio `1/8`**: `msW D K (1/8) ≤ 7/6 = 1/(1 − 1/7)` — the geometric
closure of the depth tower (note §4, Claim 4.4(ii) at `n = 2`, `q = 2`). -/
theorem msW_eighth_le (D K : ℕ) : msW D K (1 / 8 : ℚ) ≤ 7 / 6 := by
  induction D with
  | zero => rw [msW_zero]; norm_num
  | succ D ih =>
      rw [msW_succ]
      have hS := sum_Icc_eighth_le K
      have hS0 := sum_Icc_eighth_nonneg K
      have hW0 : 0 ≤ msW D K (1 / 8 : ℚ) := msW_nonneg D K (by norm_num)
      nlinarith

/-- **The critical-ratio bound**: `msW D K (1/2) ≤ D + 1` — the note (3h)'s relaxed chain sum
(each depth contributes ≤ 1; the ratio is exactly critical at `s = 2`). -/
theorem msW_half_le (D K : ℕ) : msW D K (1 / 2 : ℚ) ≤ (D : ℚ) + 1 := by
  induction D with
  | zero => rw [msW_zero]; norm_num
  | succ D ih =>
      rw [msW_succ]
      have hS := sum_Icc_half_le K
      have hS0 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 2) ^ m :=
        Finset.sum_nonneg fun m _ => by positivity
      have hW0 : 0 ≤ msW D K (1 / 2 : ℚ) := msW_nonneg D K (by norm_num)
      have hDpos : (0 : ℚ) ≤ (D : ℚ) + 1 := by positivity
      push_cast
      nlinarith

/-! ## §B. The chain coefficient at the real prime: factorization and leaf sums

`chainC ms leaf 2 = (1/8)^{Σms} · chainC [] leaf 2` — every pool is `1` at `q = 2` (the
`(q−1)`-pools and the inert `(q²−q)/2` pool), so the series is a pure product of powers of
`1/8`: the SHAPE grouping of blueprint §2-W6 item 1. -/

/-- The per-step factorization of the chain coefficient at the real prime. -/
theorem chainC_realP_factor (ms : List ℕ) (leaf : ChainLeaf) :
    chainC ms leaf M9.realP = (1 / 8 : ℚ) ^ ms.sum * chainC [] leaf M9.realP := by
  show chainC ms leaf 2 = (1 / 8 : ℚ) ^ ms.sum * chainC [] leaf 2
  rw [chainC, chainC, eval_chainMult, eval_chainMult]
  have h1 : ((2 : ℕ) : ℚ) - 1 = 1 := by norm_num
  simp only [h1, one_pow, one_mul]
  have hV : chainVolExp ms leaf = 3 * ms.sum + chainVolExp [] leaf := by
    simp [chainVolExp]
  rw [hV]
  have h2 : ((2 : ℕ) : ℚ) ^ (3 * ms.sum + chainVolExp [] leaf)
      = 8 ^ ms.sum * ((2 : ℕ) : ℚ) ^ chainVolExp [] leaf := by
    rw [pow_add, pow_mul]
    norm_num
  rw [h2, mul_inv]
  have h8 : ((1 : ℚ) / 8) ^ ms.sum = ((8 : ℚ) ^ ms.sum)⁻¹ := by
    rw [one_div, inv_pow]
  rw [h8]
  ring

/-- Depth-0 ramified leaf value at the real prime: `chainC [] (ram (2j−1)) 2 = (1/8)^j`
(`j ≥ 1`; the `H = 2j−1` rung, absolute mass `(q−1)q^{−3j}` at `q = 2`). -/
theorem chainC_ram_leaf (j : ℕ) (hj : 1 ≤ j) :
    chainC [] (ChainLeaf.ram (2 * j - 1)) M9.realP = (1 / 8 : ℚ) ^ j := by
  show chainC [] (ChainLeaf.ram (2 * j - 1)) 2 = _
  rw [chainC, eval_chainMult]
  have he : chainVolExp [] (ChainLeaf.ram (2 * j - 1)) = 3 * j := by
    simp only [chainVolExp, eLeaf, List.sum_nil]
    omega
  rw [he]
  simp only [List.length_nil, pow_zero, one_mul, leafPoolQ]
  have h2 : ((2 : ℕ) : ℚ) ^ (3 * j) = 8 ^ j := by
    rw [pow_mul]
    norm_num
  rw [h2]
  rw [show ((2 : ℕ) : ℚ) - 1 = 1 by norm_num, one_mul, one_div, inv_pow]

/-- Depth-0 inert leaf value at the real prime: `chainC [] (inert m) 2 = (1/4)·(1/8)^m`
(even-height root-free residual; pool `(q²−q)/2 = 1` at `q = 2`). -/
theorem chainC_inert_leaf (m : ℕ) :
    chainC [] (ChainLeaf.inert m) M9.realP = (1 / 4 : ℚ) * (1 / 8 : ℚ) ^ m := by
  show chainC [] (ChainLeaf.inert m) 2 = _
  rw [chainC, eval_chainMult]
  have he : chainVolExp [] (ChainLeaf.inert m) = 3 * m + 2 := by
    simp [chainVolExp, eLeaf]
  rw [he]
  simp only [List.length_nil, pow_zero, one_mul, leafPoolQ]
  have h2 : ((2 : ℕ) : ℚ) ^ (3 * m + 2) = 8 ^ m * 4 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [h2]
  push_cast
  rw [show ((2 : ℚ) ^ 2 - 2) / 2 = 1 by norm_num, one_mul, mul_inv,
    show ((1 : ℚ) / 8) = (8 : ℚ)⁻¹ by norm_num, inv_pow]
  ring

/-- Depth-0 two-sided split leaf value at the real prime: `chainC [] (split k) 2 = (1/4)·(1/8)^k`. -/
theorem chainC_split_leaf (k : ℕ) :
    chainC [] (ChainLeaf.split k) M9.realP = (1 / 4 : ℚ) * (1 / 8 : ℚ) ^ k := by
  show chainC [] (ChainLeaf.split k) 2 = _
  rw [chainC, eval_chainMult]
  have he : chainVolExp [] (ChainLeaf.split k) = 3 * k + 2 := by
    simp [chainVolExp, eLeaf]
  rw [he]
  simp only [List.length_nil, pow_zero, one_mul, leafPoolQ]
  have h2 : ((2 : ℕ) : ℚ) ^ (3 * k + 2) = 8 ^ k * 4 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [h2]
  rw [show ((2 : ℕ) : ℚ) - 1 = 1 by norm_num, one_mul, one_div, one_div, inv_pow]
  rw [mul_inv]
  ring

/-- The three degree-2 types are pairwise distinct. -/
theorem ram_ne_inert : ramType2 ≠ inertType2 := by
  intro h
  have := congrArg (fun σ => σ.data) h
  exact absurd this (by decide)

theorem ram_ne_split : ramType2 ≠ splitType2 := by
  intro h
  have := congrArg (fun σ => σ.data) h
  exact absurd this (by decide)

theorem inert_ne_split : inertType2 ≠ splitType2 := by
  intro h
  have := congrArg (fun σ => σ.data) h
  exact absurd this (by decide)

/-- The window-`K` ramified leaf sum: `Σ_{leaf ∈ chainLeaves K ram} chainC [] leaf 2 ≤ 1/7`
(the `q = 2` H-ladder total `(q−1)/(q³−1)·q³/(q³−… ) = R = 1/(q²+q+1)`; blueprint §2-W6's
per-type leaf pool). -/
theorem sum_leaf_ram_le (K : ℕ) :
    ∑ leaf ∈ chainLeaves K ramType2, chainC [] leaf M9.realP ≤ 1 / 7 := by
  rw [chainLeaves, if_pos rfl]
  rw [Finset.sum_image (by
    intro j hj j' hj' h
    rw [Finset.mem_coe, Finset.mem_Icc] at hj hj'
    have := ChainLeaf.ram.inj h
    omega)]
  calc ∑ j ∈ Finset.Icc 1 K, chainC [] (ChainLeaf.ram (2 * j - 1)) M9.realP
      = ∑ j ∈ Finset.Icc 1 K, ((1 : ℚ) / 8) ^ j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        exact chainC_ram_leaf j hj.1
    _ ≤ 1 / 7 := sum_Icc_eighth_le K

/-- The window-`K` inert leaf sum `≤ 1/28`. -/
theorem sum_leaf_inert_le (K : ℕ) :
    ∑ leaf ∈ chainLeaves K inertType2, chainC [] leaf M9.realP ≤ 1 / 28 := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_inert), if_pos rfl]
  rw [Finset.sum_image (by
    intro j _ j' _ h
    exact ChainLeaf.inert.inj h)]
  calc ∑ m ∈ Finset.Icc 1 K, chainC [] (ChainLeaf.inert m) M9.realP
      = ∑ m ∈ Finset.Icc 1 K, (1 / 4 : ℚ) * ((1 : ℚ) / 8) ^ m := by
        exact Finset.sum_congr rfl fun m _ => chainC_inert_leaf m
    _ = (1 / 4 : ℚ) * ∑ m ∈ Finset.Icc 1 K, ((1 : ℚ) / 8) ^ m := by
        rw [Finset.mul_sum]
    _ ≤ (1 / 4 : ℚ) * (1 / 7) := by
        have := sum_Icc_eighth_le K
        linarith [sum_Icc_eighth_nonneg K]
    _ = 1 / 28 := by norm_num

/-- The window-`K` split leaf sum `≤ 1/28`. -/
theorem sum_leaf_split_le (K : ℕ) :
    ∑ leaf ∈ chainLeaves K splitType2, chainC [] leaf M9.realP ≤ 1 / 28 := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), if_pos rfl]
  rw [Finset.sum_image (by
    intro j _ j' _ h
    exact ChainLeaf.split.inj h)]
  calc ∑ k ∈ Finset.Icc 1 K, chainC [] (ChainLeaf.split k) M9.realP
      = ∑ k ∈ Finset.Icc 1 K, (1 / 4 : ℚ) * ((1 : ℚ) / 8) ^ k := by
        exact Finset.sum_congr rfl fun k _ => chainC_split_leaf k
    _ = (1 / 4 : ℚ) * ∑ k ∈ Finset.Icc 1 K, ((1 : ℚ) / 8) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ (1 / 4 : ℚ) * (1 / 7) := by
        have := sum_Icc_eighth_le K
        linarith [sum_Icc_eighth_nonneg K]
    _ = 1 / 28 := by norm_num

theorem sum_leaf_nonneg (K : ℕ) (σ : FactorizationType) :
    0 ≤ ∑ leaf ∈ chainLeaves K σ, chainC [] leaf M9.realP :=
  Finset.sum_nonneg fun leaf _ => chainC_nonneg [] leaf M9.realP

/-- The rectangular chain-coefficient sum factorizes: `Σ_{(ms,leaf)} chainC = msW · leafSum`. -/
theorem sum_rect_chainC (D K K' : ℕ) (σ : FactorizationType) :
    ∑ x ∈ msMenu D K ×ˢ chainLeaves K' σ, chainC x.1 x.2 M9.realP
      = msW D K (1 / 8 : ℚ) * ∑ leaf ∈ chainLeaves K' σ, chainC [] leaf M9.realP := by
  rw [Finset.sum_product]
  unfold msW
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ms _ => Finset.sum_congr rfl fun leaf _ => ?_
  exact chainC_realP_factor ms leaf

section StallSection

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## §C. The stall strata (note 3.4′(a) step (i), Lean form)

`StallPair ms L₀ L₁ a`: the pair follows the certified descend chain `ms` (each step an
(S1)∧(S2) `StratumPair` with an existential recentering digit, exactly as `ChainPair`), and at
the bottom frame the constant slot is unreadable to the last digit — `v(b₀) ≥ B − 1` where
`B = L₀ − 2Σm` is the remaining budget (the note's stall containment: in every OTHER
configuration the frame's read completes, `cluster_covering` below). -/

/-- The stall stratum: chain prefix then `v(b₀) ≥ B − 1` in the bottom frame. -/
def StallPair : List ℕ → (L₀ L₁ : ℕ) → ZMod (p ^ L₀) × ZMod (p ^ L₁) → Prop
  | [], L₀, _, a => ClusterPair p L₀ _ a ∧ p ^ (L₀ - 1) ∣ a.1.val
  | m :: ms, L₀, L₁, a =>
      ∃ c : (ZMod p)ˣ, StratumPair p L₀ L₁ m c a ∧
        StallPair ms (L₀ - 2 * m) (L₁ - m) (descendPair p m ((c : ZMod p)).val a)

/-- Stall strata subsume the cluster condition (the `card_step` transport hypothesis). -/
theorem clusterPair_of_stallPair (ms : List ℕ) (hms : ∀ m ∈ ms, 1 ≤ m) {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (h : StallPair p ms L₀ L₁ a) :
    ClusterPair p L₀ L₁ a := by
  cases ms with
  | nil => exact h.1
  | cons m ms =>
      obtain ⟨c, hstep, -⟩ := h
      exact clusterPair_of_stratumPair p L₀ L₁ m (hms m List.mem_cons_self) c a hstep

/-- Cards of implied subtypes are monotone (finite ambient type). -/
theorem nat_card_subtype_mono {α : Type*} [Finite α] {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : Nat.card {a : α // P a} ≤ Nat.card {a : α // Q a} := by
  have hinj : Function.Injective
      (fun x : {a : α // P a} => (⟨x.1, h x.1 x.2⟩ : {a : α // Q a})) := by
    intro x y hxy
    have hval := congrArg (fun z : {a : α // Q a} => z.1) hxy
    exact Subtype.ext hval
  exact Nat.card_le_card_of_injective _ hinj

/-- **The stall count bound** (note (3f) + budget recovery): a stall stratum with certified
budget (`2Σm + 2 ≤ L₀` for nonempty chains) has at most `(p−1)^k · p^{L₁ − Σm}` points —
each step trades the `p^{−(3m−1)}`-sized stratum for a fresh frame (`card_step`), the bottom
stall slot leaves one `a₀`-digit and the free `a₁`-slot. -/
theorem card_stallPair_le (ms : List ℕ) :
    (∀ m ∈ ms, 1 ≤ m) → ∀ L₀ L₁ : ℕ, (ms ≠ [] → 2 * ms.sum + 2 ≤ L₀) → L₀ ≤ L₁ → 1 ≤ L₁ →
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StallPair p ms L₀ L₁ a}
      ≤ (p - 1) ^ ms.length * p ^ (L₁ - ms.sum) := by
  induction ms with
  | nil =>
      intro _ L₀ L₁ _ h01 hL₁
      haveI : NeZero (p ^ L₀) := QuotientBox.instNeZeroPow p L₀
      haveI : NeZero (p ^ L₁) := QuotientBox.instNeZeroPow p L₁
      simp only [List.length_nil, List.sum_nil, pow_zero, one_mul, Nat.sub_zero]
      have hmono : Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StallPair p [] L₀ L₁ a}
          ≤ Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
              p ^ (L₀ - 1) ∣ a.1.val ∧ p ^ 1 ∣ a.2.val} := by
        refine nat_card_subtype_mono ?_
        rintro a ⟨hcl, hdvd⟩
        exact ⟨hdvd, by rw [pow_one]; exact hcl.2⟩
      refine le_trans hmono ?_
      have hprod : Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
            p ^ (L₀ - 1) ∣ a.1.val ∧ p ^ 1 ∣ a.2.val}
          = p ^ (L₀ - (L₀ - 1)) * p ^ (L₁ - 1) := by
        rw [Nat.card_congr (Equiv.subtypeProdEquivProd
          (p := fun x : ZMod (p ^ L₀) => p ^ (L₀ - 1) ∣ x.val)
          (q := fun y : ZMod (p ^ L₁) => p ^ 1 ∣ y.val))]
        rw [Nat.card_prod, card_dvd_subtype p (by omega : L₀ - 1 ≤ L₀),
          card_dvd_subtype p (by omega : 1 ≤ L₁)]
      rw [hprod]
      have h1 : p ^ (L₀ - (L₀ - 1)) ≤ p ^ 1 :=
        Nat.pow_le_pow_right hp.out.pos (by omega)
      calc p ^ (L₀ - (L₀ - 1)) * p ^ (L₁ - 1) ≤ p ^ 1 * p ^ (L₁ - 1) :=
            Nat.mul_le_mul_right _ h1
        _ = p ^ L₁ := by rw [← pow_add]; congr 1; omega
  | cons m ms ih =>
      intro hms L₀ L₁ hbud h01 hL₁
      have hm1 : 1 ≤ m := hms m List.mem_cons_self
      have hbud' : 2 * (m + ms.sum) + 2 ≤ L₀ := by
        have := hbud (List.cons_ne_nil m ms)
        rwa [List.sum_cons] at this
      have hms' : ∀ x ∈ ms, 1 ≤ x := fun x hx => hms x (List.mem_cons_of_mem m hx)
      have hstep : Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
            StallPair p (m :: ms) L₀ L₁ a}
          = (p - 1) * Nat.card {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
              StallPair p ms (L₀ - 2 * m) (L₁ - m) b} := by
        have hmain := card_exists_eq_mul
          (Q := fun (c : (ZMod p)ˣ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) =>
            StratumPair p L₀ L₁ m c a ∧
              StallPair p ms (L₀ - 2 * m) (L₁ - m) (descendPair p m ((c : ZMod p)).val a))
          (fun c c' a h h' => stratumPair_unit_unique p h.1 h'.1)
          (Nat.card {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
              StallPair p ms (L₀ - 2 * m) (L₁ - m) b})
          (fun c => card_step p L₀ L₁ m c (by omega) h01
            (StallPair p ms (L₀ - 2 * m) (L₁ - m))
            (fun b hb => clusterPair_of_stallPair p ms hms' hb))
        rw [ZMod.card_units p] at hmain
        exact hmain
      rw [hstep]
      have hchild := ih hms' (L₀ - 2 * m) (L₁ - m)
        (fun _ => by omega) (by omega) (by omega)
      calc (p - 1) * Nat.card {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
            StallPair p ms (L₀ - 2 * m) (L₁ - m) b}
          ≤ (p - 1) * ((p - 1) ^ ms.length * p ^ (L₁ - m - ms.sum)) :=
            Nat.mul_le_mul_left _ hchild
        _ = (p - 1) ^ (m :: ms).length * p ^ (L₁ - (m :: ms).sum) := by
            rw [List.length_cons, List.sum_cons, pow_succ]
            rw [show L₁ - m - ms.sum = L₁ - (m + ms.sum) from by omega]
            ring

end StallSection

/-! ## §D. The covering (note 3.4′(a) steps (i)+(iii), the decision tree at the real prime)

Every cluster pair either realizes a terminating chain stratum whose threshold fits the
budget, or lies in a stall stratum. This is the Lean transcription of the note's stall
containment: with `v(a₀) ≤ B − 2` every configuration reads out — odd height one-sided → ram
leaf; two-sided (`2v(a₁) < v(a₀)`) → split leaf; even height one-sided with separable residual
→ inert leaf (at `p = 2` the residual `y² + d₁y + d₀` with `d₀ = 1` is `y²+y+1`, root-free) or
descend (`d₁ = 0`: `y² + 1 = (y+1)²`, the recentering digit `c̃ = 1`). -/

/-- ZMod-2 exhaustion: a nonzero residue is `1`. -/
theorem zmod_realP_ne_zero_eq_one : ∀ d : ZMod M9.realP, d ≠ 0 → d = 1 := by decide

theorem unit_one_sq : ((1 : (ZMod M9.realP)ˣ) : ZMod M9.realP) ^ 2 = 1 := by decide

theorem neg_two_unit_one : -(2 * ((1 : (ZMod M9.realP)ˣ) : ZMod M9.realP)) = 0 := by decide

/-- `(1,1) ∈ noRootPairs 2`: the residual `y² + y + 1` is root-free over `F₂`. -/
theorem one_one_mem_noRootPairs :
    ((1 : ZMod M9.realP), (1 : ZMod M9.realP)) ∈ noRootPairs M9.realP := by
  rw [mem_noRootPairs]
  decide

/-- **The cluster covering** (note 3.4′(a), the deterministic reader's trichotomy made
existential): a cluster pair either lies in a chain-stratum fiber whose threshold fits the
level budget, or in a stall stratum with certified steps. Strong induction on the budget. -/
theorem cluster_covering :
    ∀ L₀ L₁ : ℕ, L₀ ≤ L₁ →
    ∀ a : ZMod (M9.realP ^ L₀) × ZMod (M9.realP ^ L₁),
      ClusterPair M9.realP L₀ L₁ a →
      (∃ ms leaf, (∀ m ∈ ms, 1 ≤ m) ∧ leafOK leaf ∧
        2 * ms.sum + leafNeed leaf ≤ L₀ ∧ ChainPair M9.realP ms leaf L₀ L₁ a)
      ∨ (∃ ms, (∀ m ∈ ms, 1 ≤ m) ∧ (ms ≠ [] → 2 * ms.sum + 2 ≤ L₀) ∧
          StallPair M9.realP ms L₀ L₁ a) := by
  intro L₀
  induction L₀ using Nat.strong_induction_on with
  | _ L₀ ih =>
  intro L₁ h01 a hCl
  by_cases hstall : M9.realP ^ (L₀ - 1) ∣ a.1.val
  · exact Or.inr ⟨[], fun m hm => absurd hm List.not_mem_nil,
      fun h => absurd rfl h, hCl, hstall⟩
  · have hL₀2 : 2 ≤ L₀ := by
      by_contra hc
      exact hstall (by
        rw [show L₀ - 1 = 0 by omega, pow_zero]
        exact one_dvd _)
    set v₀ := PadicLift.zmodValuation M9.realP L₀ a.1 with hv₀def
    have hv₀le : v₀ ≤ L₀ - 2 := by
      by_contra hc
      exact hstall ((pow_dvd_val_iff M9.realP (by omega : L₀ - 1 ≤ L₀) a.1).mpr (by omega))
    have hdvd₀ : M9.realP ^ v₀ ∣ a.1.val :=
      (pow_dvd_val_iff M9.realP (by omega : v₀ ≤ L₀) a.1).mpr le_rfl
    have hdig₀ : digit M9.realP L₀ v₀ a.1 ≠ 0 :=
      (valuation_eq_iff_digit_ne M9.realP (by omega : v₀ < L₀) hdvd₀).mp hv₀def.symm
    have hv₀1 : 1 ≤ v₀ := by
      have h1 := (pow_dvd_val_iff M9.realP (by omega : 1 ≤ L₀) a.1).mp (by
        rw [pow_one]
        exact hCl.1)
      omega
    rcases Nat.even_or_odd v₀ with heven | hodd
    · -- even height `v₀ = 2m`: one-sided integer-slope read
      obtain ⟨m, hm⟩ := heven
      have hm2 : v₀ = 2 * m := by omega
      have hm1 : 1 ≤ m := by omega
      by_cases hb : M9.realP ^ m ∣ a.2.val
      · by_cases hd1 : digit M9.realP L₁ m a.2 = 0
        · -- DESCEND at slope `m`, recentering digit `c̃ = 1`
          have hstr : StratumPair M9.realP L₀ L₁ m 1 a := by
            refine ⟨⟨?_, ?_⟩, hb, ?_⟩
            · rw [← hm2]; exact hdvd₀
            · rw [unit_one_sq, ← hm2]
              exact zmod_realP_ne_zero_eq_one _ hdig₀
            · rw [neg_two_unit_one]
              exact hd1
          have h₀ : 2 * m + 1 ≤ L₀ := by omega
          have hchildCl : ClusterPair M9.realP (L₀ - 2 * m) (L₁ - m)
              (descendPair M9.realP m (((1 : (ZMod M9.realP)ˣ) : ZMod M9.realP)).val a) := by
            rw [descendPair_eq_stratumPairEquiv M9.realP L₀ L₁ m 1 h₀ h01 ⟨a, hstr⟩]
            exact ((stratumPairEquiv M9.realP L₀ L₁ m 1 h₀ h01) ⟨a, hstr⟩).2
          rcases ih (L₀ - 2 * m) (by omega) (L₁ - m) (by omega) _ hchildCl with
            ⟨ms', leaf, hms', hOK, hth, hcp⟩ | ⟨ms', hms', hbud, hsp⟩
          · refine Or.inl ⟨m :: ms', leaf, ?_, hOK, ?_, ⟨1, hstr, hcp⟩⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · omega
              · exact hms' x hx'
            · rw [List.sum_cons]
              omega
          · refine Or.inr ⟨m :: ms', ?_, ?_, ⟨1, hstr, hsp⟩⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · omega
              · exact hms' x hx'
            · intro _
              rw [List.sum_cons]
              by_cases hnil : ms' = []
              · subst hnil
                simp only [List.sum_nil]
                omega
              · have := hbud hnil
                omega
        · -- INERT leaf at height `2m` (residual `y² + y + 1`, root-free)
          have hd1' : digit M9.realP L₁ m a.2 = 1 := zmod_realP_ne_zero_eq_one _ hd1
          have hd0' : digit M9.realP L₀ (2 * m) a.1 = 1 := by
            rw [← hm2]
            exact zmod_realP_ne_zero_eq_one _ hdig₀
          refine Or.inl ⟨[], ChainLeaf.inert m, fun x hx => absurd hx List.not_mem_nil,
            hm1, ?_, ?_⟩
          · show 2 * List.sum [] + leafNeed (ChainLeaf.inert m) ≤ L₀
            simp only [List.sum_nil, leafNeed]
            omega
          · show LeafPair M9.realP (ChainLeaf.inert m) L₀ L₁ a
            refine ⟨by rw [← hm2]; exact hdvd₀, hb, ?_⟩
            rw [hd0', hd1']
            exact one_one_mem_noRootPairs
      · -- `v(a₁) < m`: two-sided polygon, SPLIT leaf at `k = v(a₁)`
        set v₁ := PadicLift.zmodValuation M9.realP L₁ a.2 with hv₁def
        have hv₁lt : v₁ < m := by
          by_contra hc
          exact hb ((pow_dvd_val_iff M9.realP (by omega : m ≤ L₁) a.2).mpr (by omega))
        have hdvd₁ : M9.realP ^ v₁ ∣ a.2.val :=
          (pow_dvd_val_iff M9.realP (by omega : v₁ ≤ L₁) a.2).mpr le_rfl
        have hdig₁ : digit M9.realP L₁ v₁ a.2 ≠ 0 :=
          (valuation_eq_iff_digit_ne M9.realP (by omega : v₁ < L₁) hdvd₁).mp hv₁def.symm
        have hv₁1 : 1 ≤ v₁ := by
          have h1 := (pow_dvd_val_iff M9.realP (by omega : 1 ≤ L₁) a.2).mp (by
            rw [pow_one]
            exact hCl.2)
          omega
        refine Or.inl ⟨[], ChainLeaf.split v₁, fun x hx => absurd hx List.not_mem_nil,
          hv₁1, ?_, ?_⟩
        · show 2 * List.sum [] + leafNeed (ChainLeaf.split v₁) ≤ L₀
          simp only [List.sum_nil, leafNeed]
          omega
        · show LeafPair M9.realP (ChainLeaf.split v₁) L₀ L₁ a
          exact ⟨by omega,
            dvd_trans (pow_dvd_pow M9.realP (by omega : 2 * v₁ + 1 ≤ v₀)) hdvd₀,
            hdvd₁, hdig₁⟩
    · -- odd height `v₀ = 2t + 1`
      obtain ⟨t, ht⟩ := hodd
      by_cases hb : M9.realP ^ ((v₀ + 1) / 2) ∣ a.2.val
      · -- RAM leaf at `H = v₀`
        refine Or.inl ⟨[], ChainLeaf.ram v₀, fun x hx => absurd hx List.not_mem_nil,
          ⟨⟨t, by omega⟩, hv₀1⟩, ?_, ⟨⟨hdvd₀, hdig₀⟩, hb⟩⟩
        show 2 * List.sum [] + leafNeed (ChainLeaf.ram v₀) ≤ L₀
        simp only [List.sum_nil, leafNeed]
        omega
      · -- `2·v(a₁) < v₀ + 1`: two-sided, SPLIT leaf at `k = v(a₁)`
        set v₁ := PadicLift.zmodValuation M9.realP L₁ a.2 with hv₁def
        have hv₁lt : v₁ < (v₀ + 1) / 2 := by
          by_contra hc
          exact hb ((pow_dvd_val_iff M9.realP (by omega : (v₀ + 1) / 2 ≤ L₁) a.2).mpr
            (by omega))
        have hdvd₁ : M9.realP ^ v₁ ∣ a.2.val :=
          (pow_dvd_val_iff M9.realP (by omega : v₁ ≤ L₁) a.2).mpr le_rfl
        have hdig₁ : digit M9.realP L₁ v₁ a.2 ≠ 0 :=
          (valuation_eq_iff_digit_ne M9.realP (by omega : v₁ < L₁) hdvd₁).mp hv₁def.symm
        have hv₁1 : 1 ≤ v₁ := by
          have h1 := (pow_dvd_val_iff M9.realP (by omega : 1 ≤ L₁) a.2).mp (by
            rw [pow_one]
            exact hCl.2)
          omega
        refine Or.inl ⟨[], ChainLeaf.split v₁, fun x hx => absurd hx List.not_mem_nil,
          hv₁1, ?_, ?_⟩
        · show 2 * List.sum [] + leafNeed (ChainLeaf.split v₁) ≤ L₀
          simp only [List.sum_nil, leafNeed]
          omega
        · show LeafPair M9.realP (ChainLeaf.split v₁) L₀ L₁ a
          exact ⟨by omega,
            dvd_trans (pow_dvd_pow M9.realP (by omega : 2 * v₁ + 1 ≤ v₀)) hdvd₀,
            hdvd₁, hdig₁⟩

/-! ## §E. Residue-point translates (the `f(x) ↦ f(x + ĉ)` recentering as `affineEquiv`) -/

instance instNeZeroRealPow (N : ℕ) : NeZero (M9.realP ^ N) :=
  QuotientBox.instNeZeroPow M9.realP N

/-- The coefficient-pair box at level `N` (via `coeffEquiv`, = the monic quadratic box). -/
abbrev pairBox (N : ℕ) : Type := ZMod (M9.realP ^ N) × ZMod (M9.realP ^ N)

/-- The residue-point translate on the coefficient pair: `f(x) ↦ f(x + ĉ)` reads
`(a₀, a₁) ↦ (a₀ + ĉa₁ + ĉ², a₁ + 2ĉ)` — exactly `RecenterBox.affineEquiv` at levels `(N, N)`
(the recentering triangular bijection with no rescale). -/
noncomputable def transMap (c N : ℕ) : pairBox N ≃ pairBox N :=
  affineEquiv M9.realP N N le_rfl c

theorem transMap_zero (N : ℕ) (a : pairBox N) : transMap 0 N a = a := by
  unfold transMap affineEquiv
  refine Prod.ext ?_ ?_
  · dsimp only [Equiv.coe_fn_mk]
    push_cast
    ring
  · dsimp only [Equiv.coe_fn_mk]
    push_cast
    ring

theorem castHom_pow_self_apply {N : ℕ} (x : ZMod (M9.realP ^ N)) :
    ZMod.castHom (pow_dvd_pow M9.realP (le_refl N)) (ZMod (M9.realP ^ N)) x = x :=
  RingHom.congr_fun (ZMod.castHom_self (n := M9.realP ^ N)) x

theorem transMap_one_fst {N : ℕ} (a : pairBox N) :
    (transMap 1 N a).1 = a.1 + a.2 + 1 := by
  show a.1 + ((1 : ℕ) : ZMod (M9.realP ^ N))
      * (ZMod.castHom (pow_dvd_pow M9.realP (le_refl N)) (ZMod (M9.realP ^ N)) a.2)
      + ((1 : ℕ) : ZMod (M9.realP ^ N)) ^ 2 = a.1 + a.2 + 1
  rw [castHom_pow_self_apply, Nat.cast_one, one_mul, one_pow]

theorem transMap_one_snd {N : ℕ} (a : pairBox N) :
    (transMap 1 N a).2 = a.2 + 2 := by
  show a.2 + 2 * ((1 : ℕ) : ZMod (M9.realP ^ N)) = a.2 + 2
  rw [Nat.cast_one, mul_one]

theorem transMap_snd (c N : ℕ) (a : pairBox N) :
    (transMap c N a).2 = a.2 + 2 * ((c : ℕ) : ZMod (M9.realP ^ N)) := rfl

/-- Parity through `ZMod` addition: `p ∣ (x + y).val ↔ p ∣ (x.val + y.val)`. -/
theorem dvd_val_add_iff {N : ℕ} (hN : 0 < N) (x y : ZMod (M9.realP ^ N)) :
    M9.realP ∣ (x + y).val ↔ M9.realP ∣ (x.val + y.val) := by
  rw [ZMod.val_add]
  exact Nat.dvd_mod_iff (dvd_pow_self M9.realP (by omega : N ≠ 0))

theorem dvd_val_one_false {N : ℕ} (hN : 0 < N)
    (h : M9.realP ∣ (1 : ZMod (M9.realP ^ N)).val) : False := by
  haveI : Fact (1 < M9.realP ^ N) :=
    ⟨Nat.one_lt_pow (by omega) (Fact.out (p := Nat.Prime M9.realP)).one_lt⟩
  rw [ZMod.val_one] at h
  have h2 := (Fact.out (p := Nat.Prime M9.realP)).two_le
  have := Nat.le_of_dvd one_pos h
  omega

theorem dvd_val_natCast_mul {N c : ℕ} (hN : 0 < N) :
    M9.realP ∣ ((2 * ((c : ℕ) : ZMod (M9.realP ^ N))).val) := by
  have h2 : (2 * ((c : ℕ) : ZMod (M9.realP ^ N)))
      = ((2 * c : ℕ) : ZMod (M9.realP ^ N)) := by
    push_cast
    ring
  rw [h2, ZMod.val_natCast,
    Nat.dvd_mod_iff (dvd_pow_self M9.realP (by omega : N ≠ 0))]
  refine Dvd.dvd.mul_right ?_ c
  rfl

/-- The translated chain/stall fibers on the pair box, and their counts. -/
def TransChain (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) (a : pairBox N) : Prop :=
  ChainPair M9.realP ms leaf N N (transMap c N a)

def TransStall (c : ℕ) (ms : List ℕ) (N : ℕ) (a : pairBox N) : Prop :=
  StallPair M9.realP ms N N (transMap c N a)

/-- Counts compose through an equivalence. -/
theorem card_comp_equiv {α β : Type*} (e : α ≃ β) (Q : β → Prop) :
    Nat.card {a : α // Q (e a)} = Nat.card {b : β // Q b} :=
  Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

noncomputable def transChainCount (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) : ℕ :=
  Nat.card {a : pairBox N // TransChain c ms leaf N a}

noncomputable def transStallCount (c : ℕ) (ms : List ℕ) (N : ℕ) : ℕ :=
  Nat.card {a : pairBox N // TransStall c ms N a}

theorem transChainCount_eq_pair (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) :
    transChainCount c ms leaf N
      = Nat.card {a : pairBox N // ChainPair M9.realP ms leaf N N a} :=
  card_comp_equiv (transMap c N) _

theorem transStallCount_eq_pair (c : ℕ) (ms : List ℕ) (N : ℕ) :
    transStallCount c ms N
      = Nat.card {a : pairBox N // StallPair M9.realP ms N N a} :=
  card_comp_equiv (transMap c N) _

/-- **The translate count tie**: every translated chain fiber has the Wave-5 stratum count
(`stratumCount5` on the corresponding chain literal) — translation is measure-exact. -/
theorem transChainCount_cast (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) :
    ((transChainCount c ms leaf N : ℕ) : ℚ) = stratumCount5 2 (chainLit ms leaf) N := by
  rw [transChainCount_eq_pair, stratumCount5_chainLit]
  congr 1
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : Nat.card {a : pairBox 0 // ChainPair M9.realP ms leaf 0 0 a} = 0 := by
      haveI : IsEmpty {a : pairBox 0 // ChainPair M9.realP ms leaf 0 0 a} :=
        ⟨fun x => chainPair_empty M9.realP ms leaf 0 0
          (by have := one_le_leafNeed leaf; omega) _ x.2⟩
      exact Nat.card_of_isEmpty
    rw [h1, card_chainCell_smallN M9.realP ms leaf
      (by have := one_le_leafNeed leaf; omega)]
  · exact (Nat.card_congr (Equiv.subtypeEquiv (coeffEquiv M9.realP N hN)
      (fun f => Iff.rfl))).symm

/-- Chain fibers (any translate) force `a₁` even — the cluster-locus parity pin. -/
theorem a1_even_of_transChain {c : ℕ} {ms : List ℕ} {leaf : ChainLeaf} {N : ℕ}
    {a : pairBox N} (hN : 0 < N) (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf)
    (h : TransChain c ms leaf N a) : M9.realP ∣ a.2.val := by
  have hcl := (clusterPair_of_chainPair M9.realP ms leaf hms hOK h).2
  rw [transMap_snd, dvd_val_add_iff hN] at hcl
  exact (Nat.dvd_add_right (dvd_val_natCast_mul hN)).mp
    (by rwa [Nat.add_comm] at hcl)

/-- Stall fibers (any translate) force `a₁` even. -/
theorem a1_even_of_transStall {c : ℕ} {ms : List ℕ} {N : ℕ}
    {a : pairBox N} (hN : 0 < N) (hms : ∀ m ∈ ms, 1 ≤ m)
    (h : TransStall c ms N a) : M9.realP ∣ a.2.val := by
  have hcl := (clusterPair_of_stallPair M9.realP ms hms h).2
  rw [transMap_snd, dvd_val_add_iff hN] at hcl
  exact (Nat.dvd_add_right (dvd_val_natCast_mul hN)).mp
    (by rwa [Nat.add_comm] at hcl)

/-- The `c = 0` and `c = 1` cluster fibers conflict on the `a₀` parity: the `c = 0` cluster
pins `a₀` even, the `c = 1` cluster pins `a₀ + a₁ + 1` even with `a₁` even. -/
theorem cross_cluster_conflict {N : ℕ} (hN : 0 < N) {a : pairBox N}
    (h0 : ClusterPair M9.realP N N (transMap 0 N a))
    (h1 : ClusterPair M9.realP N N (transMap 1 N a)) : False := by
  rw [transMap_zero] at h0
  have ha0 : M9.realP ∣ a.1.val := h0.1
  have ha1 : M9.realP ∣ a.2.val := h0.2
  have hb0 := h1.1
  rw [show (transMap 1 N a).1 = a.1 + a.2 + 1 from transMap_one_fst a] at hb0
  rw [dvd_val_add_iff hN (a.1 + a.2) 1] at hb0
  have hsum : M9.realP ∣ (a.1 + a.2).val := by
    rw [dvd_val_add_iff hN]
    exact Nat.dvd_add ha0 ha1
  exact dvd_val_one_false hN ((Nat.dvd_add_right hsum).mp hb0)

/-! ## §F. The order-0 separable strata (level-1-decided root reads at `p = 2`) -/

/-- `f̄ = x² + ā₁x + ā₀` separable-split over `F₂` ⟺ `ā₁ = 1, ā₀ = 0` (then `f̄ = x(x+1)`). -/
def SepSplitCell (N : ℕ) (a : pairBox N) : Prop :=
  M9.realP ∣ a.1.val ∧ ¬ M9.realP ∣ a.2.val

/-- `f̄` separable-irreducible over `F₂` ⟺ `ā₁ = 1, ā₀ = 1` (then `f̄ = x² + x + 1`). -/
def SepInertCell (N : ℕ) (a : pairBox N) : Prop :=
  ¬ M9.realP ∣ a.1.val ∧ ¬ M9.realP ∣ a.2.val

theorem card_dvd_one {L : ℕ} (hL : 0 < L) :
    Nat.card {x : ZMod (M9.realP ^ L) // M9.realP ∣ x.val} = M9.realP ^ (L - 1) := by
  have e : {x : ZMod (M9.realP ^ L) // M9.realP ∣ x.val}
      ≃ {x : ZMod (M9.realP ^ L) // M9.realP ^ 1 ∣ x.val} :=
    Equiv.subtypeEquivRight (fun x => by rw [pow_one])
  rw [Nat.card_congr e, card_dvd_subtype M9.realP (by omega : 1 ≤ L)]

theorem card_not_dvd {L : ℕ} (hL : 0 < L) :
    Nat.card {x : ZMod (M9.realP ^ L) // ¬ M9.realP ∣ x.val}
      = (M9.realP - 1) * M9.realP ^ (L - 1) := by
  have e : {x : ZMod (M9.realP ^ L) // ¬ M9.realP ∣ x.val}
      ≃ {x : ZMod (M9.realP ^ L) // M9.realP ^ 0 ∣ x.val ∧ digit M9.realP L 0 x ≠ 0} :=
    Equiv.subtypeEquivRight (fun x => by
      constructor
      · intro hx
        refine ⟨by rw [pow_zero]; exact one_dvd _, fun h0 => hx ?_⟩
        have h1 : ((x.val / M9.realP ^ 0 : ℕ) : ZMod M9.realP) = 0 := h0
        rw [pow_zero, Nat.div_one] at h1
        exact (CharP.cast_eq_zero_iff (ZMod M9.realP) M9.realP x.val).mp h1
      · rintro ⟨-, hd⟩ hx
        refine hd ?_
        show ((x.val / M9.realP ^ 0 : ℕ) : ZMod M9.realP) = 0
        rw [pow_zero, Nat.div_one]
        exact (CharP.cast_eq_zero_iff (ZMod M9.realP) M9.realP x.val).mpr hx)
  rw [Nat.card_congr e, card_dvd_digit_ne M9.realP (by omega : 0 < L), Nat.sub_zero]

theorem card_sepSplit {N : ℕ} (hN : 0 < N) :
    Nat.card {a : pairBox N // SepSplitCell N a}
      = M9.realP ^ (N - 1) * ((M9.realP - 1) * M9.realP ^ (N - 1)) := by
  unfold SepSplitCell
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
    (p := fun x : ZMod (M9.realP ^ N) => M9.realP ∣ x.val)
    (q := fun y : ZMod (M9.realP ^ N) => ¬ M9.realP ∣ y.val))]
  rw [Nat.card_prod, card_dvd_one hN, card_not_dvd hN]

theorem card_sepInert {N : ℕ} (hN : 0 < N) :
    Nat.card {a : pairBox N // SepInertCell N a}
      = (M9.realP - 1) * M9.realP ^ (N - 1) * ((M9.realP - 1) * M9.realP ^ (N - 1)) := by
  unfold SepInertCell
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
    (p := fun x : ZMod (M9.realP ^ N) => ¬ M9.realP ∣ x.val)
    (q := fun y : ZMod (M9.realP ^ N) => ¬ M9.realP ∣ y.val))]
  rw [Nat.card_prod, card_not_dvd hN]

/-- At `N = 0` the box is trivial (`ZMod 1`) and both separable cells are empty. -/
theorem sepSplit_zero_empty (a : pairBox 0) : ¬ SepSplitCell 0 a := by
  rintro ⟨-, h2⟩
  refine h2 ?_
  have hlt := ZMod.val_lt a.2
  have h1 : M9.realP ^ 0 = 1 := pow_zero _
  have h0 : a.2.val = 0 := by omega
  rw [h0]
  exact dvd_zero _

theorem sepInert_zero_empty (a : pairBox 0) : ¬ SepInertCell 0 a := by
  rintro ⟨-, h2⟩
  refine h2 ?_
  have hlt := ZMod.val_lt a.2
  have h1 : M9.realP ^ 0 = 1 := pow_zero _
  have h0 : a.2.val = 0 := by omega
  rw [h0]
  exact dvd_zero _

/-! ## §G. The full-model decided counts (blueprint §3's model resolution: level-indexed
finite stratum families, no infinite menu) -/

/-- The order-0 contribution, keyed by type. -/
noncomputable def sepCount6 (σ : FactorizationType) (N : ℕ) : ℚ :=
  if σ = splitType2 then (Nat.card {a : pairBox N // SepSplitCell N a} : ℚ)
  else if σ = inertType2 then (Nat.card {a : pairBox N // SepInertCell N a} : ℚ)
  else 0

/-- The chain contribution: both residue points, ALL chains and leaves in the level-`N`
rectangle (below-threshold strata have empty fibers, so the rectangle over-indexes harmlessly:
the count is the honest full-tree level-`N` decided count). -/
noncomputable def chainCount6 (σ : FactorizationType) (N : ℕ) : ℚ :=
  ∑ c ∈ ({0, 1} : Finset ℕ), ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ,
    ((transChainCount c x.1 x.2 N : ℕ) : ℚ)

/-- **The full-model per-type decided count.** -/
noncomputable def decidedCount6 (σ : FactorizationType) (N : ℕ) : ℚ :=
  sepCount6 σ N + chainCount6 σ N

/-- The degree-2 type menu. -/
noncomputable def typeMenu6 : Finset FactorizationType := {ramType2, inertType2, splitType2}

/-- **The full-model undecided count** (the box residual). -/
noncomputable def undecidedCount6 (N : ℕ) : ℚ :=
  (M9.realP : ℚ) ^ (2 * N) - ∑ σ ∈ typeMenu6, decidedCount6 σ N

theorem sepCount6_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ sepCount6 σ N := by
  unfold sepCount6
  split
  · exact Nat.cast_nonneg _
  · split
    · exact Nat.cast_nonneg _
    · exact le_refl 0

theorem chainCount6_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ chainCount6 σ N :=
  Finset.sum_nonneg fun _c _ => Finset.sum_nonneg fun _x _ => Nat.cast_nonneg _

theorem decidedCount6_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ decidedCount6 σ N :=
  add_nonneg (sepCount6_nonneg σ N) (chainCount6_nonneg σ N)

theorem sum_typeMenu6 (f : FactorizationType → ℚ) :
    ∑ σ ∈ typeMenu6, f σ = f ramType2 + f inertType2 + f splitType2 := by
  unfold typeMenu6
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact ram_ne_inert h
    · exact ram_ne_split h)]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    exact inert_ne_split)]
  rw [Finset.sum_singleton]
  ring

theorem chainLeaves_off {K : ℕ} {σ : FactorizationType} (h1 : σ ≠ ramType2)
    (h2 : σ ≠ inertType2) (h3 : σ ≠ splitType2) : chainLeaves K σ = ∅ := by
  rw [chainLeaves, if_neg h1, if_neg h2, if_neg h3]

theorem decidedCount6_off {σ : FactorizationType} (h : σ ∉ typeMenu6) (N : ℕ) :
    decidedCount6 σ N = 0 := by
  have hmem : σ ≠ ramType2 ∧ σ ≠ inertType2 ∧ σ ≠ splitType2 := by
    unfold typeMenu6 at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rw [not_or, not_or] at h
    exact h
  unfold decidedCount6 sepCount6 chainCount6
  rw [if_neg hmem.2.2, if_neg hmem.2.1, chainLeaves_off hmem.1 hmem.2.1 hmem.2.2]
  simp

/-- Everything vanishes at level `0` (trivial box: thresholds unreachable). -/
theorem decidedCount6_zero (σ : FactorizationType) : decidedCount6 σ 0 = 0 := by
  unfold decidedCount6
  have hsep : sepCount6 σ 0 = 0 := by
    unfold sepCount6
    have h1 : Nat.card {a : pairBox 0 // SepSplitCell 0 a} = 0 := by
      haveI : IsEmpty {a : pairBox 0 // SepSplitCell 0 a} :=
        ⟨fun x => sepSplit_zero_empty x.1 x.2⟩
      exact Nat.card_of_isEmpty
    have h2 : Nat.card {a : pairBox 0 // SepInertCell 0 a} = 0 := by
      haveI : IsEmpty {a : pairBox 0 // SepInertCell 0 a} :=
        ⟨fun x => sepInert_zero_empty x.1 x.2⟩
      exact Nat.card_of_isEmpty
    rw [h1, h2]
    simp
  have hchain : chainCount6 σ 0 = 0 := by
    unfold chainCount6
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun x _ => ?_
    rw [transChainCount_cast, stratumCount5_chainLit,
      card_chainCell_smallN M9.realP x.1 x.2 (by have := one_le_leafNeed x.2; omega)]
    simp
  rw [hsep, hchain]
  ring

/-! ## §H. The per-type upper bound (U): `decidedCount6 σ N ≤ (1/3)·box` — the geometric
fixpoint closes EXACTLY at the full values (note §7: `1/3` per type at `q = 2`) -/

/-- Per-stratum bound: the (translated) chain count never exceeds its coefficient × box. -/
theorem transChainCount_le_coeff (c : ℕ) {ms : List ℕ} {leaf : ChainLeaf}
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) (N : ℕ) :
    ((transChainCount c ms leaf N : ℕ) : ℚ)
      ≤ chainC ms leaf M9.realP * (M9.realP : ℚ) ^ (2 * N) := by
  rw [transChainCount_cast]
  rcases Nat.lt_or_ge N (2 * ms.sum + leafNeed leaf) with hlt | hge
  · rw [stratumCount5_chainLit, card_chainCell_smallN M9.realP ms leaf hlt, Nat.cast_zero]
    exact mul_nonneg (chainC_nonneg ms leaf M9.realP)
      (le_of_lt (RealInstanceV2.realP_pow_pos _))
  · have hnorm := normStratumCount5_chain_levelConst ms leaf hms hOK hge
    have hbox : (M9.realP : ℚ) ^ (2 * N) ≠ 0 := ne_of_gt (RealInstanceV2.realP_pow_pos _)
    rw [(div_eq_iff hbox).mp hnorm]

theorem sepCount6_le (σ : FactorizationType) (N : ℕ) :
    sepCount6 σ N ≤ (1 / 4 : ℚ) * (M9.realP : ℚ) ^ (2 * N) := by
  have hbox : (0 : ℚ) ≤ (M9.realP : ℚ) ^ (2 * N) := le_of_lt (RealInstanceV2.realP_pow_pos _)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show sepCount6 σ 0 = 0 from by
      unfold sepCount6
      have h1 : Nat.card {a : pairBox 0 // SepSplitCell 0 a} = 0 := by
        haveI : IsEmpty {a : pairBox 0 // SepSplitCell 0 a} :=
          ⟨fun x => sepSplit_zero_empty x.1 x.2⟩
        exact Nat.card_of_isEmpty
      have h2 : Nat.card {a : pairBox 0 // SepInertCell 0 a} = 0 := by
        haveI : IsEmpty {a : pairBox 0 // SepInertCell 0 a} :=
          ⟨fun x => sepInert_zero_empty x.1 x.2⟩
        exact Nat.card_of_isEmpty
      rw [h1, h2]
      simp]
    positivity
  · have hval : (2 : ℚ) ^ (N - 1) * (2 : ℚ) ^ (N - 1) ≤ (1 / 4 : ℚ) * (2 : ℚ) ^ (2 * N) := by
      have h1 : (2 : ℚ) ^ (2 * N) = (2 : ℚ) ^ (N - 1) * (2 : ℚ) ^ (N - 1) * 4 := by
        rw [show 2 * N = (N - 1) + ((N - 1) + 2) by omega, pow_add, pow_add]
        ring
      rw [h1]
      have h2 : (1 / 4 : ℚ) * ((2 : ℚ) ^ (N - 1) * (2 : ℚ) ^ (N - 1) * 4)
          = (2 : ℚ) ^ (N - 1) * (2 : ℚ) ^ (N - 1) := by ring
      rw [h2]
    unfold sepCount6
    split
    · rw [card_sepSplit hN, show M9.realP - 1 = 1 from rfl, one_mul]
      push_cast
      rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
      exact hval
    · split
      · rw [card_sepInert hN, show M9.realP - 1 = 1 from rfl, one_mul]
        push_cast
        rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
        exact hval
      · positivity

theorem chainCount6_le (σ : FactorizationType) (N : ℕ) :
    chainCount6 σ N
      ≤ 2 * (msW N N (1 / 8 : ℚ) * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf M9.realP)
        * (M9.realP : ℚ) ^ (2 * N) := by
  unfold chainCount6
  have hper : ∀ c : ℕ,
      ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, ((transChainCount c x.1 x.2 N : ℕ) : ℚ)
        ≤ (msW N N (1 / 8 : ℚ) * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf M9.realP)
            * (M9.realP : ℚ) ^ (2 * N) := by
    intro c
    calc ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, ((transChainCount c x.1 x.2 N : ℕ) : ℚ)
        ≤ ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ,
            chainC x.1 x.2 M9.realP * (M9.realP : ℚ) ^ (2 * N) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Finset.mem_product] at hx
          exact transChainCount_le_coeff c
            (fun m hm => (((mem_msMenu N N x.1).mp hx.1).2 m hm).1)
            (of_mem_chainLeaves hx.2).1 N
      _ = (∑ x ∈ msMenu N N ×ˢ chainLeaves N σ, chainC x.1 x.2 M9.realP)
            * (M9.realP : ℚ) ^ (2 * N) := by rw [Finset.sum_mul]
      _ = (msW N N (1 / 8 : ℚ) * ∑ leaf ∈ chainLeaves N σ, chainC [] leaf M9.realP)
            * (M9.realP : ℚ) ^ (2 * N) := by rw [sum_rect_chainC]
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  have h0 := hper 0
  have h1 := hper 1
  linarith

/-- **(U) The per-type third-bound**: every level's decided count is at most `(1/3)·box` —
sep ≤ 1/4 plus chains ≤ 2·(7/6)·leafcap, closing exactly at `1/3` per type. -/
theorem decided6_le_third (σ : FactorizationType) (N : ℕ) :
    decidedCount6 σ N ≤ (1 / 3 : ℚ) * (M9.realP : ℚ) ^ (2 * N) := by
  have hbox : (0 : ℚ) < (M9.realP : ℚ) ^ (2 * N) := RealInstanceV2.realP_pow_pos _
  have hW := msW_eighth_le N N
  have hW0 : 0 ≤ msW N N (1 / 8 : ℚ) := msW_nonneg N N (by norm_num)
  by_cases h1 : σ = ramType2
  · subst h1
    have hsep : sepCount6 ramType2 N = 0 := by
      unfold sepCount6
      rw [if_neg ram_ne_split, if_neg ram_ne_inert]
    have hS := sum_leaf_ram_le N
    have hS0 := sum_leaf_nonneg N ramType2
    have hchain := chainCount6_le ramType2 N
    unfold decidedCount6
    rw [hsep, zero_add]
    have hprod : msW N N (1 / 8 : ℚ) * ∑ leaf ∈ chainLeaves N ramType2, chainC [] leaf M9.realP
        ≤ 7 / 6 * (1 / 7) := by nlinarith
    nlinarith
  · by_cases h2 : σ = inertType2
    · subst h2
      have hS := sum_leaf_inert_le N
      have hS0 := sum_leaf_nonneg N inertType2
      have hchain := chainCount6_le inertType2 N
      have hsep := sepCount6_le inertType2 N
      unfold decidedCount6
      have hprod : msW N N (1 / 8 : ℚ)
          * ∑ leaf ∈ chainLeaves N inertType2, chainC [] leaf M9.realP
          ≤ 7 / 6 * (1 / 28) := by nlinarith
      nlinarith
    · by_cases h3 : σ = splitType2
      · subst h3
        have hS := sum_leaf_split_le N
        have hS0 := sum_leaf_nonneg N splitType2
        have hchain := chainCount6_le splitType2 N
        have hsep := sepCount6_le splitType2 N
        unfold decidedCount6
        have hprod : msW N N (1 / 8 : ℚ)
            * ∑ leaf ∈ chainLeaves N splitType2, chainC [] leaf M9.realP
            ≤ 7 / 6 * (1 / 28) := by nlinarith
        nlinarith
      · rw [decidedCount6_off (by
          unfold typeMenu6
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rw [not_or, not_or]
          exact ⟨h1, h2, h3⟩) N]
        positivity

/-! ## §I. Disjointness and the box bound (`undecidedCount6 ≥ 0`) -/

/-- The combined leaf menu across the three types. -/
noncomputable def allLeaves (K : ℕ) : Finset ChainLeaf :=
  chainLeaves K ramType2 ∪ chainLeaves K inertType2 ∪ chainLeaves K splitType2

theorem chainLeaves_shape_ram {K : ℕ} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K ramType2) : ∃ H, leaf = ChainLeaf.ram H := by
  rw [chainLeaves, if_pos rfl, Finset.mem_image] at h
  obtain ⟨j, -, rfl⟩ := h
  exact ⟨2 * j - 1, rfl⟩

theorem chainLeaves_shape_inert {K : ℕ} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K inertType2) : ∃ m, leaf = ChainLeaf.inert m := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_inert), if_pos rfl, Finset.mem_image] at h
  obtain ⟨m, -, rfl⟩ := h
  exact ⟨m, rfl⟩

theorem chainLeaves_shape_split {K : ℕ} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K splitType2) : ∃ k, leaf = ChainLeaf.split k := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split),
    if_pos rfl, Finset.mem_image] at h
  obtain ⟨k, -, rfl⟩ := h
  exact ⟨k, rfl⟩

theorem disj_ram_inert (K : ℕ) :
    Disjoint (chainLeaves K ramType2) (chainLeaves K inertType2) :=
  Finset.disjoint_left.mpr fun leaf h1 h2 => by
    obtain ⟨H, rfl⟩ := chainLeaves_shape_ram h1
    obtain ⟨m, hm⟩ := chainLeaves_shape_inert h2
    exact ChainLeaf.noConfusion hm

theorem disj_ramInert_split (K : ℕ) :
    Disjoint (chainLeaves K ramType2 ∪ chainLeaves K inertType2)
      (chainLeaves K splitType2) :=
  Finset.disjoint_left.mpr fun leaf h1 h2 => by
    obtain ⟨k, hk⟩ := chainLeaves_shape_split h2
    rcases Finset.mem_union.mp h1 with h | h
    · obtain ⟨H, rfl⟩ := chainLeaves_shape_ram h
      exact ChainLeaf.noConfusion hk
    · obtain ⟨m, rfl⟩ := chainLeaves_shape_inert h
      exact ChainLeaf.noConfusion hk

theorem leafOK_of_mem_allLeaves {K : ℕ} {leaf : ChainLeaf} (h : leaf ∈ allLeaves K) :
    leafOK leaf := by
  rcases Finset.mem_union.mp h with h' | h3
  · rcases Finset.mem_union.mp h' with h1 | h2
    · exact (of_mem_chainLeaves h1).1
    · exact (of_mem_chainLeaves h2).1
  · exact (of_mem_chainLeaves h3).1

/-- The σ-sum of chain counts re-indexes over the combined leaf menu. -/
theorem chainTotal_eq (N : ℕ) :
    ∑ σ ∈ typeMenu6, chainCount6 σ N
      = ∑ c ∈ ({0, 1} : Finset ℕ), ∑ x ∈ msMenu N N ×ˢ allLeaves N,
          ((transChainCount c x.1 x.2 N : ℕ) : ℚ) := by
  rw [sum_typeMenu6]
  unfold chainCount6
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product, Finset.sum_product]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ms _ => ?_
  unfold allLeaves
  rw [Finset.sum_union (disj_ramInert_split N), Finset.sum_union (disj_ram_inert N)]

/-- **The master pairwise disjointness** of the translated chain fibers: same residue point →
the banked digit-ledger conflict (`chainPair_disjoint`); distinct residue points → the `a₀`
parity conflict. -/
theorem transChain_pairwise_disjoint {N : ℕ} (hN : 0 < N)
    {i j : ℕ × List ℕ × ChainLeaf}
    (hi : i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)))
    (hj : j ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)))
    (hij : i ≠ j) (a : pairBox N)
    (h1 : TransChain i.1 i.2.1 i.2.2 N a) (h2 : TransChain j.1 j.2.1 j.2.2 N a) :
    False := by
  obtain ⟨ci, msi, leafi⟩ := i
  obtain ⟨cj, msj, leafj⟩ := j
  rw [Finset.mem_product] at hi hj
  obtain ⟨hci, hxi⟩ := hi
  obtain ⟨hcj, hxj⟩ := hj
  rw [Finset.mem_product] at hxi hxj
  have hmsi : ∀ m ∈ msi, 1 ≤ m := fun m hm => (((mem_msMenu N N msi).mp hxi.1).2 m hm).1
  have hmsj : ∀ m ∈ msj, 1 ≤ m := fun m hm => (((mem_msMenu N N msj).mp hxj.1).2 m hm).1
  have hOKi : leafOK leafi := leafOK_of_mem_allLeaves hxi.2
  have hOKj : leafOK leafj := leafOK_of_mem_allLeaves hxj.2
  by_cases hcc : ci = cj
  · subst hcc
    have hne : ¬(msi = msj ∧ leafi = leafj) := by
      rintro ⟨rfl, rfl⟩
      exact hij rfl
    exact chainPair_disjoint M9.realP msi leafi hmsi hOKi msj leafj hmsj hOKj hne
      N N _ h1 h2
  · have hcli := clusterPair_of_chainPair M9.realP msi leafi hmsi hOKi h1
    have hclj := clusterPair_of_chainPair M9.realP msj leafj hmsj hOKj h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hci hcj
    rcases hci with rfl | rfl <;> rcases hcj with rfl | rfl
    · exact hcc rfl
    · exact cross_cluster_conflict hN hcli hclj
    · exact cross_cluster_conflict hN hclj hcli
    · exact hcc rfl

/-- Predicate-only-on-the-second-coordinate product splitting. -/
def sndSubtypeEquiv {α β : Type*} (Q : β → Prop) :
    {a : α × β // Q a.2} ≃ α × {b : β // Q b} where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun y := ⟨(y.1, y.2.1), y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_a1_even (N : ℕ) (hN : 0 < N) :
    Nat.card {a : pairBox N // M9.realP ∣ a.2.val}
      = M9.realP ^ N * M9.realP ^ (N - 1) := by
  rw [Nat.card_congr (sndSubtypeEquiv (fun y : ZMod (M9.realP ^ N) => M9.realP ∣ y.val))]
  rw [Nat.card_prod, Nat.card_zmod, card_dvd_one hN]

/-- **The chain half-box bound**: all translated chain fibers live in the even-`a₁` half of
the box and are pairwise disjoint, so their total is `≤ box/2`. -/
theorem chainTotal_le_half (N : ℕ) (hN : 0 < N) :
    ∑ σ ∈ typeMenu6, chainCount6 σ N ≤ (M9.realP : ℚ) ^ (2 * N) / 2 := by
  rw [chainTotal_eq]
  have hkey : (∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
      transChainCount i.1 i.2.1 i.2.2 N) ≤ M9.realP ^ N * M9.realP ^ (N - 1) := by
    have hsub := MultiSlopeMenu.sum_card_disjoint_le
      (α := {a : pairBox N // M9.realP ∣ a.2.val})
      (s := ({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N))
      (F := fun i e => TransChain i.1 i.2.1 i.2.2 N e.1)
      (fun i hi j hj hij e he1 he2 =>
        transChain_pairwise_disjoint hN hi hj hij e.1 he1 he2)
    rw [card_a1_even N hN] at hsub
    refine le_trans (le_of_eq ?_) hsub
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_product] at hi
    obtain ⟨hci, hxi⟩ := hi
    rw [Finset.mem_product] at hxi
    have hms : ∀ m ∈ i.2.1, 1 ≤ m :=
      fun m hm => (((mem_msMenu N N i.2.1).mp hxi.1).2 m hm).1
    have hOK : leafOK i.2.2 := leafOK_of_mem_allLeaves hxi.2
    unfold transChainCount
    exact (Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : pairBox N => M9.realP ∣ a.2.val)
        (fun a => TransChain i.1 i.2.1 i.2.2 N a)).trans
      (Equiv.subtypeEquivRight (fun a =>
        ⟨fun h => h.2, fun h => ⟨a1_even_of_transChain hN hms hOK h, h⟩⟩)))).symm
  have hcast : ∑ c ∈ ({0, 1} : Finset ℕ), ∑ x ∈ msMenu N N ×ˢ allLeaves N,
      ((transChainCount c x.1 x.2 N : ℕ) : ℚ)
      = ((∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
          transChainCount i.1 i.2.1 i.2.2 N : ℕ) : ℚ) := by
    rw [Nat.cast_sum, Finset.sum_product]
  rw [hcast]
  have hbound : ((M9.realP ^ N * M9.realP ^ (N - 1) : ℕ) : ℚ)
      = (M9.realP : ℚ) ^ (2 * N) / 2 := by
    push_cast
    rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
    have h1 : (2 : ℚ) ^ (2 * N) = (2 : ℚ) ^ N * (2 : ℚ) ^ (N - 1) * 2 := by
      rw [show 2 * N = N + ((N - 1) + 1) by omega, pow_add, pow_add, pow_one]
      ring
    rw [h1]
    ring
  rw [← hbound]
  exact_mod_cast hkey

/-- The order-0 total is exactly the odd-`a₁` half of the box. -/
theorem sepCount6_ram (N : ℕ) : sepCount6 ramType2 N = 0 := by
  unfold sepCount6
  rw [if_neg ram_ne_split, if_neg ram_ne_inert]

theorem sepCount6_inert (N : ℕ) :
    sepCount6 inertType2 N = (Nat.card {a : pairBox N // SepInertCell N a} : ℚ) := by
  unfold sepCount6
  rw [if_neg inert_ne_split, if_pos rfl]

theorem sepCount6_split (N : ℕ) :
    sepCount6 splitType2 N = (Nat.card {a : pairBox N // SepSplitCell N a} : ℚ) := by
  unfold sepCount6
  rw [if_pos rfl]

theorem sepTotal_eq (N : ℕ) (hN : 0 < N) :
    ∑ σ ∈ typeMenu6, sepCount6 σ N = (M9.realP : ℚ) ^ (2 * N) / 2 := by
  rw [sum_typeMenu6, sepCount6_ram, sepCount6_inert, sepCount6_split,
    card_sepInert hN, card_sepSplit hN, show M9.realP - 1 = 1 from rfl]
  push_cast
  rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
  have h1 : (2 : ℚ) ^ (2 * N) = (2 : ℚ) ^ (N - 1) * (2 : ℚ) ^ (N - 1) * 4 := by
    rw [show 2 * N = (N - 1) + ((N - 1) + 2) by omega, pow_add, pow_add]
    ring
  rw [h1]
  ring

/-- **The box bound**: the full-model decided total never exceeds the box (all fibers are
pairwise disjoint box subsets) — `undecidedCount6 ≥ 0`. -/
theorem sum_decided6_le_box (N : ℕ) :
    ∑ σ ∈ typeMenu6, decidedCount6 σ N ≤ (M9.realP : ℚ) ^ (2 * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_eq_zero fun σ _ => decidedCount6_zero σ]
    exact le_of_lt (RealInstanceV2.realP_pow_pos _)
  · have h1 := sepTotal_eq N hN
    have h2 := chainTotal_le_half N hN
    have h3 : ∑ σ ∈ typeMenu6, decidedCount6 σ N
        = (∑ σ ∈ typeMenu6, sepCount6 σ N) + ∑ σ ∈ typeMenu6, chainCount6 σ N := by
      unfold decidedCount6
      rw [Finset.sum_add_distrib]
    rw [h3, h1]
    linarith

theorem undecided6_nonneg (N : ℕ) : 0 ≤ undecidedCount6 N := by
  unfold undecidedCount6
  linarith [sum_decided6_le_box N]

/-! ## §J. The top covering, the stall total, and THE ENVELOPE (note Lemma 3.4′(a)) -/

/-- The stall index at level `N`: chains of depth `≤ ⌊N/2⌋`, slopes `≤ N`, within budget. -/
noncomputable def stallIdx (N : ℕ) : Finset (List ℕ) :=
  (msMenu (N / 2) N).filter (fun ms => ms = [] ∨ 2 * ms.sum + 2 ≤ N)

noncomputable def stallTotal (N : ℕ) : ℚ :=
  ∑ c ∈ ({0, 1} : Finset ℕ), ∑ ms ∈ stallIdx N, ((transStallCount c ms N : ℕ) : ℚ)

theorem transStallCount_le {ms : List ℕ} {N : ℕ} (hN : 0 < N) (c : ℕ)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hbud : ms ≠ [] → 2 * ms.sum + 2 ≤ N) (hsum : ms.sum ≤ N) :
    ((transStallCount c ms N : ℕ) : ℚ) ≤ (2 : ℚ) ^ N * ((1 : ℚ) / 2) ^ ms.sum := by
  rw [transStallCount_eq_pair]
  have hcard := card_stallPair_le M9.realP ms hms N N hbud le_rfl (by omega)
  rw [show M9.realP - 1 = 1 from rfl, one_pow, one_mul] at hcard
  calc ((Nat.card {a : pairBox N // StallPair M9.realP ms N N a} : ℕ) : ℚ)
      ≤ ((M9.realP ^ (N - ms.sum) : ℕ) : ℚ) := by exact_mod_cast hcard
    _ = (2 : ℚ) ^ N * ((1 : ℚ) / 2) ^ ms.sum := by
        push_cast
        rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
        rw [show ((1 : ℚ) / 2) = (2 : ℚ)⁻¹ by norm_num, inv_pow]
        rw [eq_mul_inv_iff_mul_eq₀ (by positivity : ((2 : ℚ) ^ ms.sum) ≠ 0)]
        rw [← pow_add]
        congr 1
        omega

/-- **The stall total bound** (note (3h)): `stallTotal ≤ 2·(⌊N/2⌋+1)·2^N` — the ≤-relaxed
chain sum at the critical ratio. -/
theorem stallTotal_le (N : ℕ) (hN : 0 < N) :
    stallTotal N ≤ 2 * (((N / 2 : ℕ) : ℚ) + 1) * (2 : ℚ) ^ N := by
  unfold stallTotal
  have hper : ∀ c : ℕ, ∑ ms ∈ stallIdx N, ((transStallCount c ms N : ℕ) : ℚ)
      ≤ (((N / 2 : ℕ) : ℚ) + 1) * (2 : ℚ) ^ N := by
    intro c
    calc ∑ ms ∈ stallIdx N, ((transStallCount c ms N : ℕ) : ℚ)
        ≤ ∑ ms ∈ stallIdx N, (2 : ℚ) ^ N * ((1 : ℚ) / 2) ^ ms.sum := by
          refine Finset.sum_le_sum fun ms hms => ?_
          rw [stallIdx, Finset.mem_filter, mem_msMenu] at hms
          refine transStallCount_le hN c (fun m hm => (hms.1.2 m hm).1)
            (fun hnil => ?_) ?_
          · rcases hms.2 with h | h
            · exact absurd h hnil
            · exact h
          · rcases hms.2 with h | h
            · subst h
              simp
            · omega
      _ = (2 : ℚ) ^ N * ∑ ms ∈ stallIdx N, ((1 : ℚ) / 2) ^ ms.sum := by
          rw [Finset.mul_sum]
      _ ≤ (2 : ℚ) ^ N * msW (N / 2) N (1 / 2 : ℚ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          unfold msW stallIdx
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro ms _ _
          positivity
      _ ≤ (2 : ℚ) ^ N * (((N / 2 : ℕ) : ℚ) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact msW_half_le (N / 2) N
      _ = (((N / 2 : ℕ) : ℚ) + 1) * (2 : ℚ) ^ N := by ring
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  have h0 := hper 0
  have h1 := hper 1
  linarith

/-- List helpers: positive entries bound length and members by the sum. -/
theorem length_le_sum {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) : ms.length ≤ ms.sum := by
  induction ms with
  | nil => simp
  | cons m tl ih =>
      rw [List.length_cons, List.sum_cons]
      have h1 := hms m List.mem_cons_self
      have h2 := ih (fun x hx => hms x (List.mem_cons_of_mem m hx))
      omega

theorem mem_le_sum {ms : List ℕ} {m : ℕ} (hm : m ∈ ms) : m ≤ ms.sum := by
  induction ms with
  | nil => exact absurd hm List.not_mem_nil
  | cons x tl ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp hm with rfl | h
      · omega
      · have := ih h
        omega

/-- A well-formed leaf within the window is on the combined menu. -/
theorem mem_allLeaves_self {leaf : ChainLeaf} (hOK : leafOK leaf) {K : ℕ}
    (hK : leafNeed leaf ≤ K + 1) : leaf ∈ allLeaves K := by
  cases leaf with
  | ram H =>
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [chainLeaves, if_pos rfl, Finset.mem_image]
      obtain ⟨⟨t, ht⟩, hH1⟩ := hOK
      simp only [leafNeed] at hK
      refine ⟨(H + 1) / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      congr 1
      omega
  | inert m =>
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [chainLeaves, if_neg (Ne.symm ram_ne_inert), if_pos rfl, Finset.mem_image]
      simp only [leafNeed] at hK
      exact ⟨m, Finset.mem_Icc.mpr ⟨hOK, by omega⟩, rfl⟩
  | split k =>
      refine Finset.mem_union_right _ ?_
      rw [chainLeaves, if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split),
        if_pos rfl, Finset.mem_image]
      simp only [leafNeed] at hK
      exact ⟨k, Finset.mem_Icc.mpr ⟨hOK, by omega⟩, rfl⟩

/-- **The top covering**: every pair in the box is order-0 decided, chain-decided at one of
the two residue points, or stalled — the box-level partition feeding the envelope. -/
theorem top_covering (N : ℕ) (hN : 0 < N) (a : pairBox N) :
    (SepSplitCell N a ∨ SepInertCell N a ∨
      ∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
        TransChain i.1 i.2.1 i.2.2 N a)
    ∨ (∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ stallIdx N), TransStall i.1 i.2 N a) := by
  have hkey : ∀ c ∈ ({0, 1} : Finset ℕ), ClusterPair M9.realP N N (transMap c N a) →
      (∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
        TransChain i.1 i.2.1 i.2.2 N a)
      ∨ (∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ stallIdx N), TransStall i.1 i.2 N a) := by
    intro c hc hCl
    rcases cluster_covering N N le_rfl (transMap c N a) hCl with
      ⟨ms, leaf, hms, hOK, hth, hcp⟩ | ⟨ms, hms, hbud, hsp⟩
    · left
      have hmem1 : ms ∈ msMenu N N := by
        rw [mem_msMenu]
        have hlen := length_le_sum hms
        have hneed := one_le_leafNeed leaf
        refine ⟨by omega, fun m hm => ⟨hms m hm, ?_⟩⟩
        have := mem_le_sum hm
        omega
      have hmem2 : leaf ∈ allLeaves N :=
        mem_allLeaves_self hOK (by have := one_le_leafNeed leaf; omega)
      exact ⟨(c, ms, leaf),
        Finset.mem_product.mpr ⟨hc, Finset.mem_product.mpr ⟨hmem1, hmem2⟩⟩, hcp⟩
    · right
      have hmem1 : ms ∈ stallIdx N := by
        rw [stallIdx, Finset.mem_filter, mem_msMenu]
        by_cases hnil : ms = []
        · subst hnil
          exact ⟨⟨by simp, by simp⟩, Or.inl rfl⟩
        · have hb := hbud hnil
          have hlen := length_le_sum hms
          refine ⟨⟨by omega, fun m hm => ⟨hms m hm, ?_⟩⟩, Or.inr hb⟩
          have := mem_le_sum hm
          omega
      exact ⟨(c, ms), Finset.mem_product.mpr ⟨hc, hmem1⟩, hsp⟩
  by_cases h1 : M9.realP ∣ a.2.val
  · by_cases h0 : M9.realP ∣ a.1.val
    · have hCl : ClusterPair M9.realP N N (transMap 0 N a) := by
        rw [transMap_zero]
        exact ⟨h0, h1⟩
      rcases hkey 0 (by norm_num) hCl with h | h
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr h
    · have h0' : ¬ (2 : ℕ) ∣ a.1.val := h0
      have h1' : (2 : ℕ) ∣ a.2.val := h1
      have hCl : ClusterPair M9.realP N N (transMap 1 N a) := by
        constructor
        · rw [transMap_one_fst, dvd_val_add_iff hN (a.1 + a.2) 1]
          have hone : (1 : ZMod (M9.realP ^ N)).val = 1 := by
            haveI : Fact (1 < M9.realP ^ N) :=
              ⟨Nat.one_lt_pow (by omega) (Fact.out (p := Nat.Prime M9.realP)).one_lt⟩
            exact ZMod.val_one _
          rw [hone]
          have h3 : ¬ (2 : ℕ) ∣ (a.1 + a.2).val := by
            rw [show ((2 : ℕ) ∣ (a.1 + a.2).val) = (M9.realP ∣ (a.1 + a.2).val) from rfl,
              dvd_val_add_iff hN]
            show ¬ (2 : ℕ) ∣ (a.1.val + a.2.val)
            omega
          show (2 : ℕ) ∣ ((a.1 + a.2).val + 1)
          omega
        · rw [transMap_one_snd, dvd_val_add_iff hN a.2 2]
          have h2v : (2 : ℕ) ∣ ((2 : ZMod (M9.realP ^ N))).val := by
            have h2 : ((2 : ZMod (M9.realP ^ N)))
                = ((2 : ℕ) : ZMod (M9.realP ^ N)) := by push_cast; rfl
            rw [h2, ZMod.val_natCast]
            exact (Nat.dvd_mod_iff (show (2 : ℕ) ∣ M9.realP ^ N from
              dvd_pow_self M9.realP (by omega : N ≠ 0))).mpr dvd_rfl
          show (2 : ℕ) ∣ (a.2.val + ((2 : ZMod (M9.realP ^ N))).val)
          omega
      rcases hkey 1 (by norm_num) hCl with h | h
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr h
  · by_cases h0 : M9.realP ∣ a.1.val
    · exact Or.inl (Or.inl ⟨h0, h1⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨h0, h1⟩))

theorem filter_card_eq_nat_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = Nat.card {a : α // P a} := by
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype P).symm

theorem card_pairBox (N : ℕ) :
    (Fintype.card (pairBox N) : ℚ) = (M9.realP : ℚ) ^ (2 * N) := by
  rw [Fintype.card_prod, ZMod.card]
  push_cast
  rw [← pow_add]
  congr 1
  omega

/-- **The covering count bound**: box ≤ decided + stalls. -/
theorem box_le_decided_add_stall (N : ℕ) (hN : 0 < N) :
    (M9.realP : ℚ) ^ (2 * N) ≤ (∑ σ ∈ typeMenu6, decidedCount6 σ N) + stallTotal N := by
  classical
  have hcardsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (pairBox N)))
    (p := fun a : pairBox N => SepSplitCell N a ∨ SepInertCell N a ∨
      ∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
        TransChain i.1 i.2.1 i.2.2 N a)
  have hDecBound : (Finset.univ.filter (fun a : pairBox N =>
      SepSplitCell N a ∨ SepInertCell N a ∨
      ∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
        TransChain i.1 i.2.1 i.2.2 N a)).card
      ≤ Nat.card {a : pairBox N // SepSplitCell N a}
        + Nat.card {a : pairBox N // SepInertCell N a}
        + ∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
            transChainCount i.1 i.2.1 i.2.2 N := by
    have hsub : Finset.univ.filter (fun a : pairBox N =>
        SepSplitCell N a ∨ SepInertCell N a ∨
        ∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
          TransChain i.1 i.2.1 i.2.2 N a)
        ⊆ (Finset.univ.filter (fun a : pairBox N => SepSplitCell N a))
          ∪ (Finset.univ.filter (fun a : pairBox N => SepInertCell N a))
          ∪ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)).biUnion (fun i =>
              Finset.univ.filter (fun a : pairBox N => TransChain i.1 i.2.1 i.2.2 N a)) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases ha.2 with h | h | ⟨i, hi, h⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩⟩)
    calc (Finset.univ.filter _).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ ((Finset.univ.filter (fun a : pairBox N => SepSplitCell N a))
            ∪ (Finset.univ.filter (fun a : pairBox N => SepInertCell N a))).card
          + ((({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)).biUnion (fun i =>
              Finset.univ.filter (fun a : pairBox N =>
                TransChain i.1 i.2.1 i.2.2 N a))).card :=
          Finset.card_union_le _ _
      _ ≤ ((Finset.univ.filter (fun a : pairBox N => SepSplitCell N a)).card
            + (Finset.univ.filter (fun a : pairBox N => SepInertCell N a)).card)
          + ∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
              (Finset.univ.filter (fun a : pairBox N =>
                TransChain i.1 i.2.1 i.2.2 N a)).card :=
          Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
      _ = _ := by
          rw [filter_card_eq_nat_card, filter_card_eq_nat_card]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [filter_card_eq_nat_card]
          rfl
  have hStBound : (Finset.univ.filter (fun a : pairBox N => ¬(SepSplitCell N a
      ∨ SepInertCell N a ∨
      ∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
        TransChain i.1 i.2.1 i.2.2 N a))).card
      ≤ ∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ stallIdx N), transStallCount i.1 i.2 N := by
    have hsub : Finset.univ.filter (fun a : pairBox N => ¬(SepSplitCell N a
        ∨ SepInertCell N a ∨
        ∃ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
          TransChain i.1 i.2.1 i.2.2 N a))
        ⊆ (({0, 1} : Finset ℕ) ×ˢ stallIdx N).biUnion (fun i =>
            Finset.univ.filter (fun a : pairBox N => TransStall i.1 i.2 N a)) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases top_covering N hN a with h | ⟨i, hi, hst⟩
      · exact absurd h ha.2
      · exact Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hst⟩⟩
    calc (Finset.univ.filter _).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ stallIdx N),
            (Finset.univ.filter (fun a : pairBox N => TransStall i.1 i.2 N a)).card :=
          Finset.card_biUnion_le
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [filter_card_eq_nat_card]
          rfl
  -- assemble in ℕ, then cast
  have hNbound : Fintype.card (pairBox N)
      ≤ (Nat.card {a : pairBox N // SepSplitCell N a}
          + Nat.card {a : pairBox N // SepInertCell N a}
          + ∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
              transChainCount i.1 i.2.1 i.2.2 N)
        + ∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ stallIdx N), transStallCount i.1 i.2 N := by
    have hcu : (Finset.univ : Finset (pairBox N)).card = Fintype.card (pairBox N) :=
      Finset.card_univ
    omega
  have hQ : (M9.realP : ℚ) ^ (2 * N)
      ≤ ((Nat.card {a : pairBox N // SepSplitCell N a} : ℕ) : ℚ)
        + ((Nat.card {a : pairBox N // SepInertCell N a} : ℕ) : ℚ)
        + (∑ c ∈ ({0, 1} : Finset ℕ), ∑ x ∈ msMenu N N ×ˢ allLeaves N,
            ((transChainCount c x.1 x.2 N : ℕ) : ℚ))
        + (∑ c ∈ ({0, 1} : Finset ℕ), ∑ ms ∈ stallIdx N,
            ((transStallCount c ms N : ℕ) : ℚ)) := by
    rw [← card_pairBox N]
    have hc1 : (∑ c ∈ ({0, 1} : Finset ℕ), ∑ x ∈ msMenu N N ×ˢ allLeaves N,
        ((transChainCount c x.1 x.2 N : ℕ) : ℚ))
        = ((∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ (msMenu N N ×ˢ allLeaves N)),
            transChainCount i.1 i.2.1 i.2.2 N : ℕ) : ℚ) := by
      rw [Nat.cast_sum, Finset.sum_product]
    have hc2 : (∑ c ∈ ({0, 1} : Finset ℕ), ∑ ms ∈ stallIdx N,
        ((transStallCount c ms N : ℕ) : ℚ))
        = ((∑ i ∈ (({0, 1} : Finset ℕ) ×ˢ stallIdx N),
            transStallCount i.1 i.2 N : ℕ) : ℚ) := by
      rw [Nat.cast_sum, Finset.sum_product]
    rw [hc1, hc2]
    exact_mod_cast hNbound
  have hfinal : (∑ σ ∈ typeMenu6, decidedCount6 σ N) + stallTotal N
      = ((Nat.card {a : pairBox N // SepSplitCell N a} : ℕ) : ℚ)
        + ((Nat.card {a : pairBox N // SepInertCell N a} : ℕ) : ℚ)
        + (∑ c ∈ ({0, 1} : Finset ℕ), ∑ x ∈ msMenu N N ×ˢ allLeaves N,
            ((transChainCount c x.1 x.2 N : ℕ) : ℚ))
        + (∑ c ∈ ({0, 1} : Finset ℕ), ∑ ms ∈ stallIdx N,
            ((transStallCount c ms N : ℕ) : ℚ)) := by
    have hd : ∑ σ ∈ typeMenu6, decidedCount6 σ N
        = (∑ σ ∈ typeMenu6, sepCount6 σ N) + ∑ σ ∈ typeMenu6, chainCount6 σ N := by
      unfold decidedCount6
      rw [Finset.sum_add_distrib]
    rw [hd, chainTotal_eq, sum_typeMenu6, sepCount6_ram, sepCount6_inert, sepCount6_split]
    unfold stallTotal
    ring
  rw [hfinal]
  exact hQ

/-- **THE UNDECIDED ENVELOPE (note Lemma 3.4′(a), Lean form; all `N ≥ 1` — the note proved
`N ≥ 4`)**: `undecidedCount6 N / p^{2N} ≤ (⌊N/2⌋ + 1) · p^{−(N−1)}`. -/
theorem undecided_envelope (N : ℕ) (hN : 1 ≤ N) :
    undecidedCount6 N / (M9.realP : ℚ) ^ (2 * N)
      ≤ (((N / 2 : ℕ) : ℚ) + 1) * ((M9.realP : ℚ) ^ (N - 1))⁻¹ := by
  rw [div_le_iff₀ (RealInstanceV2.realP_pow_pos _)]
  have h1 : undecidedCount6 N ≤ stallTotal N := by
    unfold undecidedCount6
    linarith [box_le_decided_add_stall N (by omega)]
  have h2 := stallTotal_le N (by omega)
  have harr : (((N / 2 : ℕ) : ℚ) + 1) * ((M9.realP : ℚ) ^ (N - 1))⁻¹
      * (M9.realP : ℚ) ^ (2 * N)
      = 2 * (((N / 2 : ℕ) : ℚ) + 1) * (2 : ℚ) ^ N := by
    rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
    have hsplit : (2 : ℚ) ^ (2 * N) = 2 ^ (N - 1) * (2 : ℚ) ^ (N + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hne : (2 : ℚ) ^ (N - 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [harr]
  linarith

/-! ## §K. `hExhaust` and the squeeze value ties -/

/-- The envelope as a named bound. -/
noncomputable def envBound (N : ℕ) : ℚ :=
  (((N / 2 : ℕ) : ℚ) + 1) * ((M9.realP : ℚ) ^ (N - 1))⁻¹

theorem envBound_nonneg (N : ℕ) : 0 ≤ envBound N := by
  unfold envBound
  positivity

theorem envBound_mul_box (N : ℕ) (hN : 1 ≤ N) :
    envBound N * (M9.realP : ℚ) ^ (2 * N)
      = 2 * (((N / 2 : ℕ) : ℚ) + 1) * (2 : ℚ) ^ N := by
  unfold envBound
  rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
  have hsplit : (2 : ℚ) ^ (2 * N) = 2 ^ (N - 1) * (2 : ℚ) ^ (N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  have hne : (2 : ℚ) ^ (N - 1) ≠ 0 := by positivity
  field_simp
  ring

theorem nat_sq_le_two_pow {N : ℕ} (hN : 4 ≤ N) : N ^ 2 ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 4 with h4 | h4
      · have hn3 : n = 3 := by omega
        subst hn3
        norm_num
      · have h1 := ih h4
        have h2 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := h2
          _ ≤ 2 * 2 ^ n := by omega
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

theorem envBound_le {N : ℕ} (hN : 4 ≤ N) : envBound N ≤ 2 / (N : ℚ) := by
  unfold envBound
  rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
  have h1 : (((N / 2 : ℕ) : ℚ) + 1) ≤ (N : ℚ) := by
    have h0 : (N / 2 : ℕ) + 1 ≤ N := by omega
    exact_mod_cast h0
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  have hcast : ((N : ℚ)) * N ≤ (2 : ℚ) * (2 : ℚ) ^ (N - 1) := by
    have hn := nat_sq_le_two_pow hN
    have h5 : ((N : ℚ)) ^ 2 ≤ (2 : ℚ) ^ N := by exact_mod_cast hn
    have hp : (2 : ℚ) ^ N = 2 * (2 : ℚ) ^ (N - 1) := by
      conv_lhs => rw [show N = N - 1 + 1 by omega]
      rw [pow_succ]
      ring
    nlinarith
  calc (((N / 2 : ℕ) : ℚ) + 1) * ((2 : ℚ) ^ (N - 1))⁻¹
      ≤ (N : ℚ) * ((2 : ℚ) ^ (N - 1))⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 2 / N := by
        rw [mul_inv_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ (N - 1)),
          div_mul_eq_mul_div, le_div_iff₀ hNQ]
        linarith

theorem tendsto_envBound_zero : Tendsto envBound atTop (nhds 0) := by
  have h2 : Tendsto (fun N : ℕ => 2 / (N : ℚ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards with N using envBound_nonneg N
  · filter_upwards [eventually_ge_atTop 4] with N hN using envBound_le hN

/-- **`hExhaust`, DISCHARGED (blueprint §2-W6 item 3)**: the full model's undecided density
tends to 0 — the first unconditional exhaustion, pure counting. -/
theorem hExhaust_n2 :
    Tendsto (fun N => undecidedCount6 N / (M9.realP : ℚ) ^ (2 * N)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_envBound_zero ?_ ?_
  · filter_upwards with N
    exact div_nonneg (undecided6_nonneg N) (le_of_lt (RealInstanceV2.realP_pow_pos _))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact undecided_envelope N hN

theorem decided6_upper (σ : FactorizationType) (N : ℕ) :
    decidedCount6 σ N / (M9.realP : ℚ) ^ (2 * N) ≤ 1 / 3 := by
  rw [div_le_iff₀ (RealInstanceV2.realP_pow_pos _)]
  have := decided6_le_third σ N
  linarith

/-- The squeeze's lower half: box partition + (U) for the other two types + the envelope. -/
theorem decided6_lower (σ : FactorizationType) (hσ : σ ∈ typeMenu6) (N : ℕ) (hN : 1 ≤ N) :
    1 / 3 - envBound N ≤ decidedCount6 σ N / (M9.realP : ℚ) ^ (2 * N) := by
  have hbox : (0 : ℚ) < (M9.realP : ℚ) ^ (2 * N) := RealInstanceV2.realP_pow_pos _
  rw [le_div_iff₀ hbox]
  have hb := box_le_decided_add_stall N (by omega)
  have hstall_env : stallTotal N ≤ envBound N * (M9.realP : ℚ) ^ (2 * N) := by
    rw [envBound_mul_box N hN]
    exact stallTotal_le N (by omega)
  have hsum := sum_typeMenu6 (fun σ' => decidedCount6 σ' N)
  have hle1 := decided6_le_third ramType2 N
  have hle2 := decided6_le_third inertType2 N
  have hle3 := decided6_le_third splitType2 N
  unfold typeMenu6 at hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

/-- **The window-limit value tie (blueprint §2-W6 item 1)**: the full model's per-type
normalized decided count — monotone in the level window (`decided6_mono` below) — tends to
the closed-form value `1/3` at the real prime, by the two-sided squeeze. -/
theorem fullDecided_tendsto (σ : FactorizationType) (hσ : σ ∈ typeMenu6) :
    Tendsto (fun N => decidedCount6 σ N / (M9.realP : ℚ) ^ (2 * N)) atTop (nhds (1 / 3)) := by
  have hlow : Tendsto (fun N : ℕ => 1 / 3 - envBound N) atTop (nhds (1 / 3)) := by
    simpa using (tendsto_const_nhds (x := (1 / 3 : ℚ))).sub tendsto_envBound_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN using decided6_lower σ hσ N hN
  · filter_upwards with N using decided6_upper σ N

/-! ## §L. Monotonicity in the level window -/

theorem chainLeaves_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) (σ : FactorizationType) :
    chainLeaves K₁ σ ⊆ chainLeaves K₂ σ := by
  unfold chainLeaves
  by_cases h1 : σ = ramType2
  · rw [if_pos h1, if_pos h1]
    exact Finset.image_subset_image (Finset.Icc_subset_Icc le_rfl h)
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : σ = inertType2
    · rw [if_pos h2, if_pos h2]
      exact Finset.image_subset_image (Finset.Icc_subset_Icc le_rfl h)
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : σ = splitType2
      · rw [if_pos h3, if_pos h3]
        exact Finset.image_subset_image (Finset.Icc_subset_Icc le_rfl h)
      · rw [if_neg h3, if_neg h3]

theorem rect_mono {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) (σ : FactorizationType) :
    msMenu N₁ N₁ ×ˢ chainLeaves N₁ σ ⊆ msMenu N₂ N₂ ×ˢ chainLeaves N₂ σ := by
  intro x hx
  rw [Finset.mem_product] at hx ⊢
  constructor
  · obtain ⟨hlen, hall⟩ := (mem_msMenu N₁ N₁ x.1).mp hx.1
    refine (mem_msMenu N₂ N₂ x.1).mpr ⟨by omega, fun m hm => ⟨(hall m hm).1, ?_⟩⟩
    have := (hall m hm).2
    omega
  · exact chainLeaves_mono h σ hx.2

theorem sepCount6_zero (σ : FactorizationType) : sepCount6 σ 0 = 0 := by
  unfold sepCount6
  have h1 : Nat.card {a : pairBox 0 // SepSplitCell 0 a} = 0 := by
    haveI : IsEmpty {a : pairBox 0 // SepSplitCell 0 a} :=
      ⟨fun x => sepSplit_zero_empty x.1 x.2⟩
    exact Nat.card_of_isEmpty
  have h2 : Nat.card {a : pairBox 0 // SepInertCell 0 a} = 0 := by
    haveI : IsEmpty {a : pairBox 0 // SepInertCell 0 a} :=
      ⟨fun x => sepInert_zero_empty x.1 x.2⟩
    exact Nat.card_of_isEmpty
  rw [h1, h2]
  simp

/-- The normalized order-0 count is `0, 1/4, 1/4, …` per keyed type (constant from `N = 1`). -/
theorem sepCount6_div_le (σ : FactorizationType) {N₁ N₂ : ℕ} (h12 : N₁ ≤ N₂) :
    sepCount6 σ N₁ / (M9.realP : ℚ) ^ (2 * N₁)
      ≤ sepCount6 σ N₂ / (M9.realP : ℚ) ^ (2 * N₂) := by
  rcases Nat.eq_zero_or_pos N₁ with rfl | hN₁
  · rw [sepCount6_zero, zero_div]
    exact div_nonneg (sepCount6_nonneg σ N₂) (le_of_lt (RealInstanceV2.realP_pow_pos _))
  · have hN₂ : 0 < N₂ := by omega
    have hval : ∀ N : ℕ, 0 < N →
        sepCount6 σ N / (M9.realP : ℚ) ^ (2 * N)
          = sepCount6 σ 1 / (M9.realP : ℚ) ^ (2 * 1) := by
      intro N hN
      have hcard : ∀ M : ℕ, 0 < M → sepCount6 σ M
          = (if σ = splitType2 then (1 : ℚ) else if σ = inertType2 then 1 else 0)
            * (M9.realP : ℚ) ^ (2 * M) / 4 := by
        intro M hM
        unfold sepCount6
        have harith : ((M9.realP ^ (M - 1) * ((M9.realP - 1) * M9.realP ^ (M - 1)) : ℕ) : ℚ)
            = (M9.realP : ℚ) ^ (2 * M) / 4 := by
          rw [show M9.realP - 1 = 1 from rfl, one_mul]
          push_cast
          rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
          rw [show (2 : ℚ) ^ (2 * M) = (2 : ℚ) ^ (M - 1) * (2 : ℚ) ^ (M - 1) * 4 from by
            rw [show 2 * M = (M - 1) + ((M - 1) + 2) by omega, pow_add, pow_add]
            ring]
          ring
        have harith' : (((M9.realP - 1) * M9.realP ^ (M - 1)
              * ((M9.realP - 1) * M9.realP ^ (M - 1)) : ℕ) : ℚ)
            = (M9.realP : ℚ) ^ (2 * M) / 4 := by
          rw [show M9.realP - 1 = 1 from rfl, one_mul]
          push_cast
          rw [show ((M9.realP : ℚ)) = 2 from by norm_num [M9.realP]]
          rw [show (2 : ℚ) ^ (2 * M) = (2 : ℚ) ^ (M - 1) * (2 : ℚ) ^ (M - 1) * 4 from by
            rw [show 2 * M = (M - 1) + ((M - 1) + 2) by omega, pow_add, pow_add]
            ring]
          ring
        split
        · rw [card_sepSplit hM, harith, one_mul]
        · split
          · rw [card_sepInert hM, harith', one_mul]
          · rw [zero_mul, zero_div]
      rw [hcard N hN, hcard 1 (by norm_num)]
      have hb1 : (M9.realP : ℚ) ^ (2 * N) ≠ 0 := ne_of_gt (RealInstanceV2.realP_pow_pos _)
      have hb2 : (M9.realP : ℚ) ^ (2 * 1) ≠ 0 := ne_of_gt (RealInstanceV2.realP_pow_pos _)
      field_simp
    rw [hval N₁ hN₁, hval N₂ hN₂]

/-- **Full monotonicity in the level window** (`decided_mono`): the sep legs are constant
staircases, the chain legs are the banked staircases, and the index rectangle only grows. -/
theorem decided6_mono (σ : FactorizationType) :
    Monotone (fun N => decidedCount6 σ N / (M9.realP : ℚ) ^ (2 * N)) := by
  intro N₁ N₂ h12
  dsimp only
  unfold decidedCount6
  rw [add_div, add_div]
  refine add_le_add (sepCount6_div_le σ h12) ?_
  unfold chainCount6
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  calc ∑ x ∈ msMenu N₁ N₁ ×ˢ chainLeaves N₁ σ,
        ((transChainCount c x.1 x.2 N₁ : ℕ) : ℚ) / (M9.realP : ℚ) ^ (2 * N₁)
      ≤ ∑ x ∈ msMenu N₁ N₁ ×ˢ chainLeaves N₁ σ,
        ((transChainCount c x.1 x.2 N₂ : ℕ) : ℚ) / (M9.realP : ℚ) ^ (2 * N₂) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_product] at hx
        have hms : ∀ m ∈ x.1, 1 ≤ m :=
          fun m hm => (((mem_msMenu N₁ N₁ x.1).mp hx.1).2 m hm).1
        have hOK : leafOK x.2 := (of_mem_chainLeaves hx.2).1
        rw [transChainCount_cast, transChainCount_cast]
        exact normChainCount_mono x.1 x.2 hms hOK h12
    _ ≤ ∑ x ∈ msMenu N₂ N₂ ×ˢ chainLeaves N₂ σ,
        ((transChainCount c x.1 x.2 N₂ : ℕ) : ℚ) / (M9.realP : ℚ) ^ (2 * N₂) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (rect_mono h12 σ) ?_
        intro x _ _
        exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (RealInstanceV2.realP_pow_pos _))

/-! ## §M. The closed-form value family, the full model, and THE CAPSTONE -/

/-- **The full per-type density closed forms** (`q`-uniform family; module docstring for the
derivation and the note-§7 ledger match — `q = 2` values are `1/3, 1/3, 1/3`). -/
noncomputable def fullValueFn (σ : FactorizationType) (q' : ℕ) : ℚ :=
  if σ = ramType2 then 1 / ((q' : ℚ) + 1)
  else if σ = inertType2 then (q' : ℚ) / (2 * ((q' : ℚ) + 1))
  else if σ = splitType2 then
    ((q' : ℚ) ^ 3 - (q' : ℚ) + 2) / (2 * (q' : ℚ) ^ 2 * ((q' : ℚ) + 1))
  else 0

theorem fullValueFn_realP (σ : FactorizationType) (hσ : σ ∈ typeMenu6) :
    fullValueFn σ M9.realP = 1 / 3 := by
  unfold typeMenu6 at hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  unfold fullValueFn
  rcases hσ with rfl | rfl | rfl
  · rw [if_pos rfl]
    norm_num [M9.realP]
  · rw [if_neg (Ne.symm ram_ne_inert), if_pos rfl]
    norm_num [M9.realP]
  · rw [if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), if_pos rfl]
    norm_num [M9.realP]

theorem fullValueFn_off {σ : FactorizationType} (hσ : σ ∉ typeMenu6) (q' : ℕ) :
    fullValueFn σ q' = 0 := by
  unfold typeMenu6 at hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rw [not_or, not_or] at hσ
  unfold fullValueFn
  rw [if_neg hσ.1, if_neg hσ.2.1, if_neg hσ.2.2]

theorem fullValueFn_nonneg (σ : FactorizationType) (q' : ℕ) : 0 ≤ fullValueFn σ q' := by
  unfold fullValueFn
  by_cases h1 : σ = ramType2
  · rw [if_pos h1]
    positivity
  · rw [if_neg h1]
    by_cases h2 : σ = inertType2
    · rw [if_pos h2]
      positivity
    · rw [if_neg h2]
      by_cases h3 : σ = splitType2
      · rw [if_pos h3]
        refine div_nonneg ?_ (by positivity)
        have h4 : (q' : ℚ) ≤ (q' : ℚ) ^ 3 := by
          rcases Nat.eq_zero_or_pos q' with rfl | hq
          · norm_num
          · have h5 : (1 : ℚ) ≤ (q' : ℚ) := by exact_mod_cast hq
            have h6 : (1 : ℚ) ≤ (q' : ℚ) ^ 2 := by nlinarith
            calc (q' : ℚ) = (q' : ℚ) * 1 := by ring
              _ ≤ (q' : ℚ) * (q' : ℚ) ^ 2 :=
                  mul_le_mul_of_nonneg_left h6 (by linarith)
              _ = (q' : ℚ) ^ 3 := by ring
        linarith
      · rw [if_neg h3]

/-- Uniform rationality of the closed forms (one `num/den` per type, pole-free on `q > 1`). -/
theorem fullValueFn_isRational (σ : FactorizationType) : IsRationalFn (fullValueFn σ) := by
  by_cases h1 : σ = ramType2
  · have hfn : fullValueFn σ = fun q' : ℕ => 1 / ((q' : ℚ) + 1) := by
      funext q'
      unfold fullValueFn
      rw [if_pos h1]
    rw [hfn]
    refine ⟨1, X + C 1, Polynomial.X_add_C_ne_zero 1, fun q hq => ?_⟩
    have hq0 : (0 : ℚ) < (q : ℚ) + 1 := by positivity
    constructor
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      linarith
    · simp only [Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
  · by_cases h2 : σ = inertType2
    · have hfn : fullValueFn σ = fun q' : ℕ => (q' : ℚ) / (2 * ((q' : ℚ) + 1)) := by
        funext q'
        unfold fullValueFn
        rw [if_neg h1, if_pos h2]
      rw [hfn]
      refine ⟨X, C 2 * (X + C 1),
        mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero) (Polynomial.X_add_C_ne_zero 1),
        fun q hq => ?_⟩
      have hq0 : (0 : ℚ) < (q : ℚ) + 1 := by positivity
      constructor
      · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C]
        positivity
      · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C]
    · by_cases h3 : σ = splitType2
      · have hfn : fullValueFn σ = fun q' : ℕ =>
            ((q' : ℚ) ^ 3 - (q' : ℚ) + 2) / (2 * (q' : ℚ) ^ 2 * ((q' : ℚ) + 1)) := by
          funext q'
          unfold fullValueFn
          rw [if_neg h1, if_neg h2, if_pos h3]
        rw [hfn]
        refine ⟨X ^ 3 - X + C 2, C 2 * X ^ 2 * (X + C 1),
          mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
            (pow_ne_zero 2 Polynomial.X_ne_zero)) (Polynomial.X_add_C_ne_zero 1),
          fun q hq => ?_⟩
        have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
        constructor
        · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          positivity
        · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      · have hfn : fullValueFn σ = fun _ : ℕ => (0 : ℚ) := by
          funext q'
          unfold fullValueFn
          rw [if_neg h1, if_neg h2, if_neg h3]
        rw [hfn]
        exact isRationalFn_const 0

/-- **`realMW6` — the FULL `n = 2` counting model** (blueprint §3's resolution: a genuine
`CountingModel` whose decided counts are the complete stratum tree's level-`N` counts). -/
noncomputable def realMW6 : CountingModel M9.realP 2 where
  hq := by norm_num [M9.realP]
  decidedCount := decidedCount6
  undecidedCount := undecidedCount6
  decidedCount_nonneg := decidedCount6_nonneg
  undecidedCount_nonneg := undecided6_nonneg
  typeMenu := typeMenu6
  typeMenu_degree := by
    intro σ hσ
    unfold typeMenu6 at hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
  decidedCount_off_menu := fun σ N hσ => decidedCount6_off hσ N
  box_partition := by
    intro N
    unfold undecidedCount6
    ring
  decided_mono := decided6_mono
  densityVal := fun σ => fullValueFn σ M9.realP
  decided_tendsto := by
    intro σ
    by_cases hσ : σ ∈ typeMenu6
    · rw [fullValueFn_realP σ hσ]
      exact fullDecided_tendsto σ hσ
    · rw [fullValueFn_off hσ]
      refine Tendsto.congr (fun N => ?_) tendsto_const_nhds
      rw [decidedCount6_off hσ N, zero_div]
  upper_tail := by
    intro σ N K' hNK
    have hBK := RealInstanceV2.realP_pow_pos (2 * K')
    have hBN := RealInstanceV2.realP_pow_pos (2 * N)
    by_cases hσ : σ ∈ typeMenu6
    · have hstep : ∀ σ' ∈ typeMenu6,
          (0 : ℚ) ≤ decidedCount6 σ' K' / (M9.realP : ℚ) ^ (2 * K')
            - decidedCount6 σ' N / (M9.realP : ℚ) ^ (2 * N) := fun σ' _ =>
        sub_nonneg.mpr (decided6_mono σ' hNK)
      have hsingle := Finset.single_le_sum (f := fun σ' =>
          decidedCount6 σ' K' / (M9.realP : ℚ) ^ (2 * K')
          - decidedCount6 σ' N / (M9.realP : ℚ) ^ (2 * N)) hstep hσ
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsingle
      have htotK : (∑ σ' ∈ typeMenu6, decidedCount6 σ' K') / (M9.realP : ℚ) ^ (2 * K') ≤ 1 :=
        (div_le_one hBK).mpr (sum_decided6_le_box K')
      have hundec : undecidedCount6 N / (M9.realP : ℚ) ^ (2 * N)
          = 1 - (∑ σ' ∈ typeMenu6, decidedCount6 σ' N) / (M9.realP : ℚ) ^ (2 * N) := by
        unfold undecidedCount6
        rw [sub_div, div_self (ne_of_gt hBN)]
      linarith
    · rw [decidedCount6_off hσ N, decidedCount6_off hσ K', zero_div, zero_div, zero_add]
      exact div_nonneg (undecided6_nonneg N) (le_of_lt hBN)

/-- One marker shape per type (bookkeeping for the deliberately-weak `MontesDataV2` spine —
the semantics are pinned by the count definitions and the squeeze theorems, per the interface
docstring's statement-fence note). -/
noncomputable def marker (σ : FactorizationType) : ClusterShape :=
  if σ = ramType2 then chainLit [] (ChainLeaf.ram 1)
  else if σ = inertType2 then chainLit [] (ChainLeaf.inert 1)
  else chainLit [] (ChainLeaf.split 1)

noncomputable def shapesOf6 (σ : FactorizationType) : Finset ClusterShape :=
  if σ ∈ typeMenu6 then {marker σ} else ∅

noncomputable def stratumCount6 (T : ClusterShape) (N : ℕ) : ℚ :=
  decidedCount6 (leafType (decodeLeaf T)) N

noncomputable def C6 (T : ClusterShape) (q' : ℕ) : ℚ :=
  fullValueFn (leafType (decodeLeaf T)) q'

theorem marker_type {σ : FactorizationType} (hσ : σ ∈ typeMenu6) :
    leafType (decodeLeaf (marker σ)) = σ := by
  unfold typeMenu6 at hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  unfold marker
  rcases hσ with rfl | rfl | rfl
  · rw [if_pos rfl, decodeLeaf_chainLit]
    rfl
  · rw [if_neg (Ne.symm ram_ne_inert), if_pos rfl, decodeLeaf_chainLit]
    rfl
  · rw [if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split), decodeLeaf_chainLit]
    rfl

/-- **`realDW6` — the abstract-coefficient spine over the full model.** -/
noncomputable def realDW6 : LeanUrat.MontesV2.MontesDataV2 M9.realP 2 realMW6 where
  shapesOf := shapesOf6
  stratumCount := stratumCount6
  partition := by
    intro σ N
    show decidedCount6 σ N = ∑ T ∈ shapesOf6 σ, stratumCount6 T N
    unfold shapesOf6
    by_cases hσ : σ ∈ typeMenu6
    · rw [if_pos hσ, Finset.sum_singleton]
      unfold stratumCount6
      rw [marker_type hσ]
    · rw [if_neg hσ, Finset.sum_empty]
      exact decidedCount6_off hσ N
  C := C6
  C_isRational := fun T => fullValueFn_isRational (leafType (decodeLeaf T))
  stratum_tendsto_C := by
    intro σ T hT
    unfold shapesOf6 at hT
    by_cases hσ : σ ∈ typeMenu6
    · rw [if_pos hσ, Finset.mem_singleton] at hT
      subst hT
      show Tendsto (fun N => stratumCount6 (marker σ) N / (M9.realP : ℚ) ^ (2 * N))
        atTop (nhds (C6 (marker σ) M9.realP))
      unfold stratumCount6 C6
      rw [marker_type hσ, fullValueFn_realP σ hσ]
      exact fullDecided_tendsto σ hσ
    · rw [if_neg hσ] at hT
      exact absurd hT (Finset.notMem_empty T)

/-- **`realFW6` — the full density foundation** (density at degree 2 = the closed-form family
via the marker sum; the `htameFE` hypothesis of the capstone is about THIS foundation). -/
noncomputable def realFW6 : DensityFoundation where
  density := fun m σ q' => if m = 2 then ∑ T ∈ shapesOf6 σ, C6 T q' else 0
  clusterVolume := fun T q' => C6 T q'
  shapes := fun m σ => if m = 2 then shapesOf6 σ else ∅
  multiplicity := fun _ => Polynomial.C 1
  decomposition := by
    intro m σ _ q' _
    by_cases hm : m = 2
    · subst hm
      simp only [if_pos rfl]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Polynomial.eval_C, one_mul]
    · simp only [if_neg hm, Finset.sum_empty]
  density_nonneg := by
    intro m σ q'
    by_cases hm : m = 2
    · subst hm
      simp only [if_pos rfl]
      exact Finset.sum_nonneg fun T _ => fullValueFn_nonneg _ q'
    · simp only [if_neg hm]
      exact le_refl 0

/-- **`montes_unconditional_n2_full` — THE WAVE-6 CAPSTONE (blueprint §0, the prize).**

For every degree-2 type σ, over the FULL `n = 2` counting model `realMW6` (both residue
points, all depths, all leaf kinds — the complete stratum tree):

* (R) UNCONDITIONAL uniform rationality of the closed-form density family
  `g_σ(q') = ∑_{T ∈ shapesOf6 σ} C6 T q' = fullValueFn σ q'` — one `num/den`, denominator
  nonvanishing at every `q' > 1`;
* (V) the FULL-DENSITY TIE, UNCONDITIONAL: `realMW6.countingDensity σ` — the genuine
  `N → ∞` decided limit of the complete tree's normalized counts — equals
  `num(realP)/den(realP)` (`= 1/3` for each of the three types, `gate_w6_*` below);
* (P) palindromy `IsPalindromic num den` — CONDITIONAL on the explicit hypothesis `htameFE`
  (about `realFW6`; never an axiom);
* (B) **BRACKET UNIQUENESS, UNCONDITIONAL — `hExhaust` PROVED, not hypothesized** (the
  first full-density clause fired outright): any `d` bracketed by the decided counts and
  the undecided remainder at every level IS the counting density.

**Honest scope**: counting-side digit fibers (σ-keying of the translate and depth-0
inert/split fibers is definitional here — outside Wave 5c's declared axiom scope; a future
scope extension is required before calling the keying Montes-faithful); the `q`-family is
the `p = 2`-complete tree (the even-height split-residual family, empty at `q = 2`, is not
carried); palindromy is exactly the content of `htameFE`. NO axiom on any path: the
footprint must be Lean core only (`AxCheck` below). -/
theorem montes_unconditional_n2_full (σ : FactorizationType) (hσ : σ.degree = 2)
    (htameFE : TameFunctionalEquation realFW6 2 σ) :
    (∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ shapesOf6 σ, C6 T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (realMW6.countingDensity σ = num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)) ∧
      IsPalindromic num den) ∧
    ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
        realMW6.decidedCount σ N / (M9.realP : ℚ) ^ (2 * N) ≤ d ∧
        d ≤ realMW6.decidedCount σ N / (M9.realP : ℚ) ^ (2 * N)
              + realMW6.undecidedCount N / (M9.realP : ℚ) ^ (2 * N)) →
      d = realMW6.countingDensity σ := by
  constructor
  · obtain ⟨num, den, hden, hall, hval, hpalin⟩ :=
      LeanUrat.MontesV2.goal_theorem_montes realMW6 realDW6 σ realFW6 hσ
        (fun q' _ => by
          show (if 2 = 2 then ∑ T ∈ shapesOf6 σ, C6 T q' else 0) = _
          rw [if_pos rfl]
          rfl) htameFE
    exact ⟨num, den, hden, hall, hval (by norm_num [M9.realP]), hpalin⟩
  · intro d hd
    have hlim : Tendsto
        (fun N => realMW6.decidedCount σ N / (M9.realP : ℚ) ^ (2 * N))
        atTop (nhds (realMW6.countingDensity σ)) := realMW6.decided_tendsto σ
    have h1 : realMW6.countingDensity σ ≤ d := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hd N hN).1
    have h2 : d ≤ realMW6.countingDensity σ := by
      have hEx : Tendsto
          (fun N => realMW6.undecidedCount N / (M9.realP : ℚ) ^ (2 * N))
          atTop (nhds 0) := hExhaust_n2
      have hlim2 : Tendsto
          (fun N => realMW6.decidedCount σ N / (M9.realP : ℚ) ^ (2 * N)
            + realMW6.undecidedCount N / (M9.realP : ℚ) ^ (2 * N))
          atTop (nhds (realMW6.countingDensity σ)) := by
        have hadd := hlim.add hEx
        simpa using hadd
      refine ge_of_tendsto hlim2 ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hd N hN).2
    exact le_antisymm h2 h1

/-! ## §N. Gates -/

/-- G-value: the full ramified density at the real prime is `1/3` (note §7:
`q·q^{−2}·β_ram = 1/(q+1)` at `q = 2`). -/
theorem gate_w6_ram_full : realMW6.countingDensity ramType2 = 1 / 3 :=
  fullValueFn_realP ramType2 (Finset.mem_insert_self _ _)

theorem gate_w6_inert_full : realMW6.countingDensity inertType2 = 1 / 3 :=
  fullValueFn_realP inertType2
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

theorem gate_w6_split_full : realMW6.countingDensity splitType2 = 1 / 3 :=
  fullValueFn_realP splitType2
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- G-checksum: the three full densities + the (vanishing) undecided limit exhaust the box. -/
theorem gate_w6_checksum :
    realMW6.countingDensity ramType2 + realMW6.countingDensity inertType2
      + realMW6.countingDensity splitType2 = 1 := by
  rw [gate_w6_ram_full, gate_w6_inert_full, gate_w6_split_full]
  norm_num

/-- G-compare: the full value strictly dominates the Wave-5 `D = 0` window value (`1/8`). -/
theorem gate_w6_gt_w5_D0 :
    (RealInstanceW5.realMW5 2 0 1 (by norm_num)).countingDensity ramType2
      < realMW6.countingDensity ramType2 := by
  calc (RealInstanceW5.realMW5 2 0 1 (by norm_num)).countingDensity ramType2
      = 1 / 8 := RealInstanceW5Gates.gate_w5_D0
    _ < 1 / 3 := by norm_num
    _ = realMW6.countingDensity ramType2 := gate_w6_ram_full.symm

/-- G-compare: the full value strictly dominates the Wave-5 `D = 1` window value (`9/64`). -/
theorem gate_w6_gt_w5_D1 :
    (RealInstanceW5.realMW5 2 1 1 (by norm_num)).countingDensity ramType2
      < realMW6.countingDensity ramType2 := by
  calc (RealInstanceW5.realMW5 2 1 1 (by norm_num)).countingDensity ramType2
      = 9 / 64 := RealInstanceW5Gates.gate_w5_D1
    _ < 1 / 3 := by norm_num
    _ = realMW6.countingDensity ramType2 := gate_w6_ram_full.symm

/-- The Wave-5 windowed family is MONOTONE in the depth window `D` (blueprint §2-W6 item 1's
window-family clause): deeper windows certify more decided mass. -/
theorem omMenu5_mono_D {n K D₁ D₂ : ℕ} (h : D₁ ≤ D₂) (σ : FactorizationType) :
    omMenu5 n D₁ K σ ⊆ omMenu5 n D₂ K σ := by
  intro T hT
  rcases mem_omMenu5_cases hT with h4 | ⟨hn2, ms, leaf, hms, hne, hleaf, rfl⟩
  · exact Finset.mem_union_left _ h4
  · subst hn2
    refine Finset.mem_union_right _ (mem_chainShapes.mpr ⟨rfl, ms, leaf, ?_, hne, hleaf, rfl⟩)
    obtain ⟨hlen, hall⟩ := (mem_msMenu D₁ K ms).mp hms
    exact (mem_msMenu D₂ K ms).mpr ⟨by omega, hall⟩

theorem w5_window_mono (K : ℕ) (σ : FactorizationType) (hn : 0 < 2) :
    Monotone (fun D => (RealInstanceW5.realMW5 2 D K hn).countingDensity σ) := by
  intro D₁ D₂ h12
  dsimp only
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
      (RealInstanceW5.realDW5 2 D₁ K hn),
    LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
      (RealInstanceW5.realDW5 2 D₂ K hn)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (omMenu5_mono_D h12 σ) ?_
  intro T hT _
  exact RealInstanceW5.C5_nonneg_of_mem hT M9.realP

end LeanUrat.OM.SeriesAssembly

/-! ## G4 — mutation evidence (blueprint §2-W6 gate)

A scratch copy of `realDW6` with the per-shape coefficient mutated to the constant `0`
(`C := fun _ _ => 0`, all other fields verbatim, `stratum_tendsto_C` discharged by the same
squeeze theorem) FAILS to compile: the squeeze proves convergence to the closed-form value
(`1/3` at the real prime), not to `0`. Verbatim compiler output (`lake env lean` on the
scratch `OM/ScratchG4W6.lean`, 2026-07-22; scratch deleted after capture):

```
LeanUrat/OM/ScratchG4W6.lean:24:6: error: Type mismatch
  fullDecided_tendsto σ hσ
has type
  Filter.Tendsto (fun N => decidedCount6 σ N / ↑M9.realP ^ (2 * N)) Filter.atTop (nhds (1 / 3))
but is expected to have type
  Filter.Tendsto (fun N => decidedCount6 σ N / ↑M9.realP ^ (2 * N)) Filter.atTop (nhds 0)
```

The mutation gate certifies the full model's value tie is load-bearing, not decorative. -/

section AxCheck

-- Wave-6 gate (blueprint §2-W6): every capstone and every load-bearing theorem must be Lean
-- core ONLY (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a
-- stop-the-line event). The envelope, `hExhaust`, and the value ties are PURE COUNTING —
-- no Montes axiom, no cited axiom, nothing beyond core anywhere on the path.
#print axioms LeanUrat.OM.SeriesAssembly.cluster_covering
#print axioms LeanUrat.OM.SeriesAssembly.card_stallPair_le
#print axioms LeanUrat.OM.SeriesAssembly.box_le_decided_add_stall
#print axioms LeanUrat.OM.SeriesAssembly.undecided_envelope
#print axioms LeanUrat.OM.SeriesAssembly.hExhaust_n2
#print axioms LeanUrat.OM.SeriesAssembly.decided6_le_third
#print axioms LeanUrat.OM.SeriesAssembly.fullDecided_tendsto
#print axioms LeanUrat.OM.SeriesAssembly.montes_unconditional_n2_full
#print axioms LeanUrat.OM.SeriesAssembly.gate_w6_ram_full
#print axioms LeanUrat.OM.SeriesAssembly.gate_w6_inert_full
#print axioms LeanUrat.OM.SeriesAssembly.gate_w6_split_full
#print axioms LeanUrat.OM.SeriesAssembly.gate_w6_checksum
#print axioms LeanUrat.OM.SeriesAssembly.gate_w6_gt_w5_D0
#print axioms LeanUrat.OM.SeriesAssembly.gate_w6_gt_w5_D1
#print axioms LeanUrat.OM.SeriesAssembly.w5_window_mono
-- Re-census of the Wave-5 capstones from the Wave-6 module (unchanged trusted base):
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5_exhaustive

end AxCheck
