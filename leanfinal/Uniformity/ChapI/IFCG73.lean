/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG70
import Uniformity.ChapI.IFCG71

/-!
# Uniformity.ChapI.IFCG73 — [GCV 2026-08-31] THE DEEP-BOX DRAINS CLOSE AT EVERY MASS
SPLIT: the `primo` value stack sums to the box (`Σ_v zed(K,n,v)·q^{−v} = q^{2n}`),
so `DeepStratumDrain n₁ n₂` holds OUTRIGHT for all `n₁, n₂ ≥ 1` and the census
master loses its drain premise

Stage GCV of the cone census (design record `runs/wave-c/verdict_GCV.md`; consumes
GNA = `IFCG70`, VA23 = `IFCG71`, and through them IGV = `IFCG61`, VCL = `IFCG60`).
VA23 re-based the convolution row `VisCensusLaw g m σ` onto exactly {per-entry
geometric CLUSTER values, the `min ≥ 2` deep-box drains, the two collision limits}
and identified the drain with GNA's value-stack identity
`Σ_v zed(K,n,v)·q^{−v} = q^{2n}` — "the natural next unit".  THIS file proves that
identity and fires the drain:

* **§1 THE `primo` VALUE STACK** (pure arithmetic on IFCG65's recursion, Lean-core):
  the partial sums `Σ_{v<V} primo(q,δ,e,v)·q^{−v}` are bounded by `q^{δe}`
  (`sum_primo_mul_le`), hence summable, and the total is EXACTLY the primary box
  ★ `tsum_primo_mul : Σ'_v primo(q,δ,e,v)·q^{−v} = q^{δe}` — the recursion's
  self-loop contributes `q^{−δe}·S`, the peel terms telescope to `q^{δe} − 1`, and
  the fixed-point equation `S(1 − q^{−δe}) = q^{δe} − 1` has the box as its unique
  solution.
* **§2 THE PATTERN STACK** (★ `tsum_patRate_mul`): the Cauchy product over the
  pattern's blocks — `Σ'_v coeff_v(patRate q λ)·q^{−v} = q^{patternWeight λ}`
  (mathlib's antidiagonal instruments; nonnegative coefficients make norm-summability
  free).
* **§3 THE CENSUS STACK** (★★ `tsum_zed_mul`): summing over the `q^n` monic
  residuals, `Σ'_v zed(K,n,v)·q^{−v} = q^{2n}` — **VA23's named identity, the
  full-box strata masses sum to `1`.**
* **§4 ★★★ THE DRAIN FIRES EVERYWHERE** (`deepStratumDrain_all`): through IGV's
  min-reduction (`card_depthPairSet_reduce` + the swap) and GNA's exact diagonal
  census (`card_redDepthPairSet_general`), the normalized depth-`v` stratum mass at
  ANY mass split `(n₁, n₂ ≥ 1)` is the level-free `zed(K,min,v)·q^{−v−2·min}`
  (`card_depthPairSet_general`); the §3 stack then drains the deep box:
  **`DeepStratumDrain n₁ n₂` holds OUTRIGHT at every positive mass split** —
  subsuming VA23's `min = 1` fires and closing the `min ≥ 2` remainder.
* **§5 ★★★ THE ROW AND THE MASTERS RE-BASED WITHOUT THE DRAIN**:
  `visCensusLaw_of_clusterGeom_collisions` (the row on exactly {cluster values,
  collision limits}), `decidedSliceAt_all_of_clusterGeom`,
  `capstoneHypotheses_of_clusterGeom` — VA23's masters with the `hDR` premise GONE;
  every other premise byte-identical.

## THE HONEST FENCE

The charge's items (a)/(c) and the outright fire (item 4) do NOT close, and are not
claimed:
* **(a) the genre-restricted cluster values** (`VisEntryClusterGeom`): the genre is
  sector membership of the PRODUCT cell (`splitSectorVis`/`powerSectorProperVis`) —
  decided-type data at the deep level.  GNA's assembly is graded by the RESIDUAL
  (mod-`π`) pattern only; the charged "type-restricted sub-sum of GNA's assembly"
  conflates the residual pattern with the decided type, and the sector-membership ×
  depth joint census remains the named remainder exactly as VA23 fenced.
* **(c) the two collision limits**: the charged formula
  `collisions = Σ_v (q^v−1)·(clusters at depth v)` is exact ONLY if every visible
  cell is hit by exactly one cluster across the whole convolution table — false in
  general (a fully split type at `m = 4` admits `(1,3)/(2,2)/(3,1)` groupings of the
  same cell); the discrepancy is precisely the per-cell cluster-multiplicity
  (block-grouping) census, VCL's fence axis (iii), untouched here.
After this file the convolution row rests on exactly {per-entry geometric CLUSTER
values, the two collision limits} — the drain axis is CLOSED.  Nothing weakened;
every consumed statement byte-untouched.

## Axiom fence (machine-exact at landing)

§§1–4 (the stacks and the drain) expect PURE Lean core
`{propext, Classical.choice, Quot.sound}` — GNA's census, IGV's transport, VCL's
box partition, and VA23's GE partition are all Lean-core.  §5's row inherits exactly
the owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization`
(through VA23's assembly — never re-consumed); the census master adds nothing; the
capstone master additionally inherits `Uniformity.Density.Tower.agnprw_termination`
(ID12's, previously declared).  C.33 and `AX_cellRecursion` must NOT occur.  Zero
sorries, zero new axioms, zero new definitions — the drain Prop and the value
currencies are all VA23's.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG73

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ConeRemainderLaw)
open Uniformity.Density.IFCG41 (CollisionLaw)
open Uniformity.Density.IFCG44 (PowerFullSpanLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG56 (depthPairSet depthPairSetGE)
open Uniformity.Density.IFCG57 (LeafSubfaceLaw)
open Uniformity.Density.IFCG58 (VisGenre VisCensusLaw PowerVisWeightLaw
  powerCollisionTotal)
open Uniformity.Density.IFCG60 (sum_card_depthPairSet_eq)
open Uniformity.Density.IFCG61 (redDepthPairSet card_depthPairSet_reduce
  card_depthPairSet_swap)
open Uniformity.Density.IFCG65 (primo)
open Uniformity.Density.IFCG17 (patternOf monicFinset mem_monicFinset_iff)
open Uniformity.Density.IFCG70 (patRate patternWeight zed
  card_redDepthPairSet_general patternWeight_patternOf one_le_of_mem_patternOf)
open Uniformity.Density.IFCG71 (DeepStratumDrain VisEntryClusterGeom
  card_depthPairSetGE_eq_sum card_depthPairSetGE_swap)

/-! ## §1 — THE `primo` VALUE STACK: the per-primary depth values sum to the primary
box, `Σ'_v primo(q,δ,e,v)·q^{−v} = q^{δe}` (pure arithmetic on IFCG65's recursion) -/

section PrimoStack

/-- The ℕ-telescope of the peel coefficients: partial sums of `q^{E−δj} − q^{E−δj−δ}`
complement the last power exactly (stated additively — no truncated subtraction on
the outside). -/
private theorem sum_peel_telescope {q : ℕ} (hq : 1 ≤ q) {δ E : ℕ} (W : ℕ)
    (hW : δ * W ≤ E) :
    ∑ j ∈ Finset.range W, (q ^ (E - δ * j) - q ^ (E - δ * j - δ)) + q ^ (E - δ * W)
      = q ^ E := by
  induction W with
  | zero => simp
  | succ W ih =>
      have hW' : δ * W ≤ E := le_trans (Nat.mul_le_mul_left δ (by omega)) hW
      have hδW : δ * W + δ ≤ E := by
        have := hW
        rw [Nat.mul_succ] at this
        omega
      have hpowle : q ^ (E - δ * W - δ) ≤ q ^ (E - δ * W) :=
        Nat.pow_le_pow_right hq (by omega)
      have hsub : E - δ * (W + 1) = E - δ * W - δ := by
        rw [Nat.mul_succ]
        omega
      rw [Finset.sum_range_succ, hsub, add_assoc,
        Nat.sub_add_cancel hpowle]
      exact ih hW'

/-- Shifting instrument: a range sum of an `E`-shifted, `E`-gated sequence against
`x^v` is `x^E` times the unshifted range sum. -/
private theorem sum_ite_shift {x : ℝ} (a : ℕ → ℕ) (E V : ℕ) :
    ∑ v ∈ Finset.range V, (if E ≤ v then (a (v - E) : ℝ) else 0) * x ^ v
      = x ^ E * ∑ w ∈ Finset.range (V - E), (a w : ℝ) * x ^ w := by
  rcases Nat.lt_or_ge V E with hVE | hEV
  · rw [Nat.sub_eq_zero_of_le hVE.le, Finset.range_zero, Finset.sum_empty, mul_zero]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [if_neg (by have := Finset.mem_range.mp hv; omega), zero_mul]
  · rw [← Finset.sum_range_add_sum_Ico
      (fun v => (if E ≤ v then (a (v - E) : ℝ) else 0) * x ^ v) hEV,
      Finset.sum_eq_zero (fun v hv => by
        rw [if_neg (by have := Finset.mem_range.mp hv; omega), zero_mul]),
      zero_add, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (by omega), show E + i - E = i from by omega, pow_add]
    ring

/-- The `(e+1)`-case of IFCG65's `primo` recursion, with the attach-sum flattened and
the vacuous positivity guard removed. -/
private theorem primo_succ (q δ e v : ℕ) (hδ : 1 ≤ δ) :
    primo q δ (e + 1) v
      = (if δ * (e + 1) ≤ v then primo q δ (e + 1) (v - δ * (e + 1)) else 0)
        + ∑ j ∈ Finset.range (e + 1),
            (q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ))
              * (if δ * j ≤ v then primo q δ j (v - δ * j) else 0) := by
  have hE1 : 1 ≤ δ * (e + 1) := Nat.mul_pos (by omega) (by omega)
  rw [primo]
  rw [Finset.sum_attach (Finset.range (e + 1)) (fun j =>
    (q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ))
      * (if δ * j ≤ v then primo q δ j (v - δ * j) else 0))]
  congr 1
  by_cases hEv : δ * (e + 1) ≤ v
  · rw [dif_pos ⟨hE1, hEv⟩, if_pos hEv]
  · rw [dif_neg (fun hc => hEv hc.2), if_neg hEv]

/-- ★ **The partial sums of the `primo` stack are bounded by the primary box**:
`Σ_{v<V} primo(q,δ,e,v)·q^{−v} ≤ q^{δe}`, uniformly in the window — the recursion's
self-loop is absorbed by the fixed-point inequality `P ≤ q^{−δe}·P + (q^{δe} − 1)`. -/
theorem sum_primo_mul_le {q δ : ℕ} (hq : 2 ≤ q) (hδ : 1 ≤ δ) (e : ℕ) (V : ℕ) :
    ∑ v ∈ Finset.range V, (primo q δ e v : ℝ) * ((q : ℝ)⁻¹) ^ v
      ≤ (q : ℝ) ^ (δ * e) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hx0 : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hx1 : (q : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast (by omega : 1 < q)
  induction e using Nat.strong_induction_on generalizing V with
  | _ e IH =>
    rcases e with _ | e
    · -- exponent 0: the unit mass
      have hp0 : ∀ w, primo q δ 0 w = if w = 0 then 1 else 0 := fun w => by rw [primo]
      have hterm : ∀ v, (primo q δ 0 v : ℝ) * ((q : ℝ)⁻¹) ^ v
          = if v = 0 then ((q : ℝ)⁻¹) ^ v else 0 := by
        intro v
        rw [hp0 v]
        by_cases hv : v = 0
        · rw [if_pos hv, if_pos hv, Nat.cast_one, one_mul]
        · rw [if_neg hv, if_neg hv, Nat.cast_zero, zero_mul]
      rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_ite_eq' (Finset.range V) 0,
        Nat.mul_zero, pow_zero]
      by_cases h0 : 0 ∈ Finset.range V
      · rw [if_pos h0, pow_zero]
      · rw [if_neg h0]
        norm_num
    · -- exponent e+1: the fixed-point inequality
      set E := δ * (e + 1) with hE
      have hE1 : 1 ≤ E := Nat.mul_pos (by omega) (by omega)
      have hxE1 : ((q : ℝ)⁻¹) ^ E < 1 := pow_lt_one₀ hx0 hx1 (by omega)
      have hxE0 : (0 : ℝ) < 1 - ((q : ℝ)⁻¹) ^ E := by linarith
      have hqxE : (q : ℝ) ^ E * ((q : ℝ)⁻¹) ^ E = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hq0), one_pow]
      -- the pointwise recursion, cast to ℝ
      have hrec : ∀ v, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
          = (if E ≤ v then (primo q δ (e + 1) (v - E) : ℝ) else 0) * ((q : ℝ)⁻¹) ^ v
            + ∑ j ∈ Finset.range (e + 1),
                ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
                  * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                      * ((q : ℝ)⁻¹) ^ v) := by
        intro v
        rw [primo_succ q δ e v hδ]
        push_cast
        rw [add_mul, Finset.sum_mul]
        refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => by ring)
      -- the self-loop part
      have hself : ∑ v ∈ Finset.range V,
            (if E ≤ v then (primo q δ (e + 1) (v - E) : ℝ) else 0) * ((q : ℝ)⁻¹) ^ v
          = ((q : ℝ)⁻¹) ^ E
              * ∑ w ∈ Finset.range (V - E), (primo q δ (e + 1) w : ℝ) * ((q : ℝ)⁻¹) ^ w :=
        sum_ite_shift (fun w => primo q δ (e + 1) w) E V
      -- the peel part: swap, shift, bound by the inner induction, telescope
      have hpeel : ∑ v ∈ Finset.range V, ∑ j ∈ Finset.range (e + 1),
            ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
              * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                  * ((q : ℝ)⁻¹) ^ v)
          ≤ (q : ℝ) ^ E - 1 := by
        rw [Finset.sum_comm]
        have hjterm : ∀ j ∈ Finset.range (e + 1),
            ∑ v ∈ Finset.range V,
              ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
                * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                    * ((q : ℝ)⁻¹) ^ v)
              ≤ ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ) := by
          intro j hj
          rw [← Finset.mul_sum, sum_ite_shift (fun w => primo q δ j w) (δ * j) V]
          have hIH := IH j (Finset.mem_range.mp hj) (V - δ * j)
          calc ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
                * (((q : ℝ)⁻¹) ^ (δ * j)
                    * ∑ w ∈ Finset.range (V - δ * j), (primo q δ j w : ℝ) * ((q : ℝ)⁻¹) ^ w)
              ≤ ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
                  * (((q : ℝ)⁻¹) ^ (δ * j) * (q : ℝ) ^ (δ * j)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_left hIH (by positivity)
            _ = ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ) := by
                rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hq0), one_pow, mul_one]
        calc ∑ j ∈ Finset.range (e + 1), ∑ v ∈ Finset.range V,
              ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
                * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                    * ((q : ℝ)⁻¹) ^ v)
            ≤ ∑ j ∈ Finset.range (e + 1),
                ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ) :=
              Finset.sum_le_sum hjterm
          _ = (q : ℝ) ^ E - 1 := by
              rw [← Nat.cast_sum]
              have htel := sum_peel_telescope (by omega : 1 ≤ q) (E := E) (e + 1) le_rfl
              rw [Nat.sub_self, pow_zero] at htel
              have hsum : ∑ j ∈ Finset.range (e + 1),
                  (q ^ (E - δ * j) - q ^ (E - δ * j - δ)) = q ^ E - 1 := by omega
              rw [hsum, Nat.cast_sub (Nat.one_le_pow E q (by omega)), Nat.cast_pow,
                Nat.cast_one]
      -- assemble the fixed-point inequality
      have hmono : ∑ w ∈ Finset.range (V - E), (primo q δ (e + 1) w : ℝ) * ((q : ℝ)⁻¹) ^ w
          ≤ ∑ v ∈ Finset.range V, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) fun v _ _ => by positivity
      have hkey : ∑ v ∈ Finset.range V, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
          ≤ ((q : ℝ)⁻¹) ^ E
              * ∑ v ∈ Finset.range V, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
            + ((q : ℝ) ^ E - 1) := by
        calc ∑ v ∈ Finset.range V, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
            = ∑ v ∈ Finset.range V,
                  (if E ≤ v then (primo q δ (e + 1) (v - E) : ℝ) else 0) * ((q : ℝ)⁻¹) ^ v
                + ∑ v ∈ Finset.range V, ∑ j ∈ Finset.range (e + 1),
                    ((q ^ (E - δ * j) - q ^ (E - δ * j - δ) : ℕ) : ℝ)
                      * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                          * ((q : ℝ)⁻¹) ^ v) := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun v _ => hrec v
          _ ≤ ((q : ℝ)⁻¹) ^ E
                  * ∑ v ∈ Finset.range V, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
                + ((q : ℝ) ^ E - 1) := by
              refine add_le_add ?_ hpeel
              rw [hself]
              exact mul_le_mul_of_nonneg_left hmono (by positivity)
      -- solve: P·(1 − x^E) ≤ q^E − 1 = q^E·(1 − x^E)
      have h1 : (∑ v ∈ Finset.range V, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v)
          * (1 - ((q : ℝ)⁻¹) ^ E) ≤ (q : ℝ) ^ E - 1 := by nlinarith [hkey]
      have h2 : (q : ℝ) ^ E - 1 = (q : ℝ) ^ E * (1 - ((q : ℝ)⁻¹) ^ E) := by
        rw [mul_sub, mul_one, hqxE]
      exact le_of_mul_le_mul_right (h2 ▸ h1) hxE0

/-- The `primo` stack is summable. -/
theorem summable_primo_mul {q δ : ℕ} (hq : 2 ≤ q) (hδ : 1 ≤ δ) (e : ℕ) :
    Summable (fun v => (primo q δ e v : ℝ) * ((q : ℝ)⁻¹) ^ v) :=
  summable_of_sum_range_le (fun v => by positivity)
    (fun V => sum_primo_mul_le hq hδ e V)

/-- The tsum form of the shifting instrument: an `k`-shifted, `k`-gated stack sums to
`x^k` times the unshifted stack (summability included). -/
private theorem tsum_ite_shift {x : ℝ} {a : ℕ → ℕ} (k : ℕ)
    (hsum : Summable (fun w => (a w : ℝ) * x ^ w)) :
    Summable (fun v => (if k ≤ v then (a (v - k) : ℝ) else 0) * x ^ v)
      ∧ ∑' v, (if k ≤ v then (a (v - k) : ℝ) else 0) * x ^ v
          = x ^ k * ∑' w, (a w : ℝ) * x ^ w := by
  have hg : ∀ n : ℕ, (if k ≤ n + k then (a (n + k - k) : ℝ) else 0) * x ^ (n + k)
      = x ^ k * ((a n : ℝ) * x ^ n) := by
    intro n
    rw [if_pos (by omega : k ≤ n + k), show n + k - k = n from by omega, pow_add]
    ring
  have hS : Summable (fun v => (if k ≤ v then (a (v - k) : ℝ) else 0) * x ^ v) := by
    refine (summable_nat_add_iff k).mp ?_
    exact Summable.congr (hsum.mul_left (x ^ k)) fun n => (hg n).symm
  refine ⟨hS, ?_⟩
  rw [← hS.sum_add_tsum_nat_add k,
    Finset.sum_eq_zero (fun v hv => by
      rw [if_neg (by have := Finset.mem_range.mp hv; omega), zero_mul]),
    zero_add, tsum_congr hg, tsum_mul_left]

/-- The peel coefficients sum to `q^{δ(e+1)} − 1`, cast to `ℝ`. -/
private theorem sum_peel_cast {q δ : ℕ} (hq : 2 ≤ q) (e : ℕ) :
    ∑ j ∈ Finset.range (e + 1),
        ((q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ) : ℕ) : ℝ)
      = (q : ℝ) ^ (δ * (e + 1)) - 1 := by
  rw [← Nat.cast_sum]
  have htel := sum_peel_telescope (by omega : 1 ≤ q) (E := δ * (e + 1)) (e + 1) le_rfl
  rw [show δ * (e + 1) - δ * (e + 1) = 0 from by omega, pow_zero] at htel
  have hsum : ∑ j ∈ Finset.range (e + 1),
      (q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ))
        = q ^ (δ * (e + 1)) - 1 := by omega
  rw [hsum, Nat.cast_sub (Nat.one_le_pow _ q (by omega)), Nat.cast_pow, Nat.cast_one]

/-- ★ **THE PRIMARY VALUE STACK**: the normalized primary census values sum over all
depths EXACTLY to the primary box — `Σ'_v primo(q,δ,e,v)·q^{−v} = q^{δe}`.  The
recursion's self-loop contributes `q^{−δ(e+1)}·S`, the peel terms telescope to
`q^{δ(e+1)} − 1`, and the fixed-point equation `S·(1 − q^{−δ(e+1)}) = q^{δ(e+1)} − 1`
has the box as its unique solution. -/
theorem tsum_primo_mul {q δ : ℕ} (hq : 2 ≤ q) (hδ : 1 ≤ δ) (e : ℕ) :
    ∑' v, (primo q δ e v : ℝ) * ((q : ℝ)⁻¹) ^ v = (q : ℝ) ^ (δ * e) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hx0 : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hx1 : (q : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast (by omega : 1 < q)
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    rcases e with _ | e
    · -- exponent 0: the unit mass
      have hp0 : ∀ w, primo q δ 0 w = if w = 0 then 1 else 0 := fun w => by rw [primo]
      have hterm : ∀ v : ℕ, v ≠ 0 → (primo q δ 0 v : ℝ) * ((q : ℝ)⁻¹) ^ v = 0 := by
        intro v hv
        rw [hp0 v, if_neg hv, Nat.cast_zero, zero_mul]
      rw [tsum_eq_single 0 hterm, hp0 0, if_pos rfl, Nat.mul_zero, pow_zero, pow_zero,
        Nat.cast_one, one_mul]
    · -- exponent e+1: the fixed-point equation
      have hE1 : 1 ≤ δ * (e + 1) := Nat.mul_pos (by omega) (by omega)
      have hxE1 : ((q : ℝ)⁻¹) ^ (δ * (e + 1)) < 1 := pow_lt_one₀ hx0 hx1 (by omega)
      have hxE0 : (0 : ℝ) < 1 - ((q : ℝ)⁻¹) ^ (δ * (e + 1)) := by linarith
      have hqxE : (q : ℝ) ^ (δ * (e + 1)) * ((q : ℝ)⁻¹) ^ (δ * (e + 1)) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hq0), one_pow]
      have hsumF : Summable (fun v => (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v) :=
        summable_primo_mul hq hδ (e + 1)
      -- the pointwise recursion, cast to ℝ
      have hrec : ∀ v, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
          = (if δ * (e + 1) ≤ v then (primo q δ (e + 1) (v - δ * (e + 1)) : ℝ) else 0)
                * ((q : ℝ)⁻¹) ^ v
            + ∑ j ∈ Finset.range (e + 1),
                ((q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ) : ℕ) : ℝ)
                  * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                      * ((q : ℝ)⁻¹) ^ v) := by
        intro v
        rw [primo_succ q δ e v hδ]
        push_cast
        rw [add_mul, Finset.sum_mul]
        refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => by ring)
      -- summability of the pieces
      have hsumJ : ∀ j ∈ Finset.range (e + 1), Summable (fun v =>
          ((q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ) : ℕ) : ℝ)
            * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                * ((q : ℝ)⁻¹) ^ v)) :=
        fun j _ =>
          ((tsum_ite_shift (δ * j) (summable_primo_mul hq hδ j)).1).mul_left _
      have hsumB : Summable (fun v => ∑ j ∈ Finset.range (e + 1),
          ((q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ) : ℕ) : ℝ)
            * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                * ((q : ℝ)⁻¹) ^ v)) := summable_sum hsumJ
      -- the fixed-point equation
      have hmain : ∑' v, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
          = ((q : ℝ)⁻¹) ^ (δ * (e + 1))
              * ∑' v, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v
            + ((q : ℝ) ^ (δ * (e + 1)) - 1) := by
        conv_lhs => rw [tsum_congr hrec]
        rw [Summable.tsum_add (tsum_ite_shift (δ * (e + 1)) hsumF).1 hsumB,
          (tsum_ite_shift (δ * (e + 1)) hsumF).2, Summable.tsum_finsetSum hsumJ]
        congr 1
        -- the peel terms telescope
        have hjval : ∀ j ∈ Finset.range (e + 1),
            ∑' v, ((q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ) : ℕ) : ℝ)
                * ((if δ * j ≤ v then (primo q δ j (v - δ * j) : ℝ) else 0)
                    * ((q : ℝ)⁻¹) ^ v)
              = ((q ^ (δ * (e + 1) - δ * j) - q ^ (δ * (e + 1) - δ * j - δ) : ℕ) : ℝ) := by
          intro j hj
          rw [tsum_mul_left, (tsum_ite_shift (δ * j) (summable_primo_mul hq hδ j)).2,
            IH j (Finset.mem_range.mp hj), ← mul_pow,
            inv_mul_cancel₀ (ne_of_gt hq0), one_pow, mul_one]
        rw [Finset.sum_congr rfl hjval, sum_peel_cast hq e]
      -- solve the fixed point: S·(1 − x^E) = q^E − 1 = q^E·(1 − x^E)
      have h1 : (∑' v, (primo q δ (e + 1) v : ℝ) * ((q : ℝ)⁻¹) ^ v)
          * (1 - ((q : ℝ)⁻¹) ^ (δ * (e + 1)))
          = (q : ℝ) ^ (δ * (e + 1)) * (1 - ((q : ℝ)⁻¹) ^ (δ * (e + 1))) := by
        nlinarith [hmain, hqxE]
      exact mul_right_cancel₀ (ne_of_gt hxE0) h1

end PrimoStack

/-! ## §2 — THE PATTERN STACK: the Cauchy product over the pattern's blocks,
`Σ'_v coeff_v(patRate q λ)·q^{−v} = q^{patternWeight λ}` -/

section PatternStack

/-- The pattern weight of a cons. -/
private theorem patternWeight_cons (de : ℕ × ℕ) (lam : Multiset (ℕ × ℕ)) :
    patternWeight (de ::ₘ lam) = de.1 * de.2 + patternWeight lam := by
  unfold Uniformity.Density.IFCG70.patternWeight
  rw [Multiset.map_cons, Multiset.sum_cons]

/-- ★ **THE PATTERN VALUE STACK** (the Cauchy product over the blocks): for a pattern
with positive block degrees, the depth-summed pattern-convolution values total the
shape box — `Σ'_v coeff_v(patRate q λ)·q^{−v} = q^{patternWeight λ}`, with
summability. -/
theorem summable_tsum_patRate_mul {q : ℕ} (hq : 2 ≤ q) (lam : Multiset (ℕ × ℕ))
    (hlam : ∀ de ∈ lam, 1 ≤ de.1) :
    Summable (fun v => ((PowerSeries.coeff v (patRate q lam) : ℕ) : ℝ)
        * ((q : ℝ)⁻¹) ^ v)
      ∧ ∑' v, ((PowerSeries.coeff v (patRate q lam) : ℕ) : ℝ) * ((q : ℝ)⁻¹) ^ v
          = (q : ℝ) ^ patternWeight lam := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  induction lam using Multiset.induction_on with
  | empty =>
      have hone : patRate q 0 = 1 := by
        unfold Uniformity.Density.IFCG70.patRate
        rw [Multiset.map_zero, Multiset.prod_zero]
      have hterm : ∀ v : ℕ,
          ((PowerSeries.coeff v (patRate q 0) : ℕ) : ℝ) * ((q : ℝ)⁻¹) ^ v
            = if v = 0 then 1 else 0 := by
        intro v
        rw [hone, PowerSeries.coeff_one]
        by_cases hv : v = 0
        · rw [if_pos hv, if_pos hv, hv, Nat.cast_one, pow_zero, one_mul]
        · rw [if_neg hv, if_neg hv, Nat.cast_zero, zero_mul]
      constructor
      · refine summable_of_ne_finset_zero (s := {0}) fun v hv => ?_
        rw [hterm v, if_neg (by simpa using hv)]
      · rw [tsum_congr hterm, tsum_eq_single 0 (fun v hv => if_neg hv), if_pos rfl]
        have hw : patternWeight (0 : Multiset (ℕ × ℕ)) = 0 := by
          unfold Uniformity.Density.IFCG70.patternWeight
          rw [Multiset.map_zero, Multiset.sum_zero]
        rw [hw, pow_zero]
  | cons de lam IH =>
      have hde : 1 ≤ de.1 := hlam de (Multiset.mem_cons_self de lam)
      obtain ⟨hgs, hgt⟩ := IH (fun d hd => hlam d (Multiset.mem_cons_of_mem hd))
      have hprod : patRate q (de ::ₘ lam)
          = PowerSeries.mk (fun w => primo q de.1 de.2 w) * patRate q lam := by
        unfold Uniformity.Density.IFCG70.patRate
        rw [Multiset.map_cons, Multiset.prod_cons]
      have hfs : Summable (fun i => (primo q de.1 de.2 i : ℝ) * ((q : ℝ)⁻¹) ^ i) :=
        summable_primo_mul hq hde de.2
      have hfn : Summable (fun i => ‖(primo q de.1 de.2 i : ℝ) * ((q : ℝ)⁻¹) ^ i‖) :=
        hfs.congr fun i => (Real.norm_of_nonneg (by positivity)).symm
      have hgn : Summable (fun j =>
          ‖((PowerSeries.coeff j (patRate q lam) : ℕ) : ℝ) * ((q : ℝ)⁻¹) ^ j‖) :=
        hgs.congr fun j => (Real.norm_of_nonneg (by positivity)).symm
      -- the pointwise identification of the Cauchy product with the cons coefficients
      have hpoint : ∀ v, ∑ kl ∈ Finset.antidiagonal v,
            ((primo q de.1 de.2 kl.1 : ℝ) * ((q : ℝ)⁻¹) ^ kl.1)
              * (((PowerSeries.coeff kl.2 (patRate q lam) : ℕ) : ℝ)
                  * ((q : ℝ)⁻¹) ^ kl.2)
          = ((PowerSeries.coeff v (patRate q (de ::ₘ lam)) : ℕ) : ℝ)
              * ((q : ℝ)⁻¹) ^ v := by
        intro v
        rw [hprod, PowerSeries.coeff_mul]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        have hv : kl.1 + kl.2 = v := Finset.mem_antidiagonal.mp hkl
        simp only [PowerSeries.coeff_mk]
        rw [← hv, pow_add]
        ring
      have hcauchy : Summable (fun v => ∑ kl ∈ Finset.antidiagonal v,
          ((primo q de.1 de.2 kl.1 : ℝ) * ((q : ℝ)⁻¹) ^ kl.1)
            * (((PowerSeries.coeff kl.2 (patRate q lam) : ℕ) : ℝ)
                * ((q : ℝ)⁻¹) ^ kl.2)) :=
        (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
      constructor
      · exact hcauchy.congr hpoint
      · rw [← tsum_congr hpoint,
          ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
          tsum_primo_mul hq hde de.2, hgt, ← pow_add, patternWeight_cons]

end PatternStack

/-! ## §3 — THE CENSUS STACK: `Σ'_v zed(K,n,v)·q^{−v} = q^{2n}` — the full-box strata
masses sum to `1` (VA23's named identity, GNA's value stack summed) -/

section ZedStack

/-- The monic carrier count: `q^n` monic degree-`n` polynomials. -/
private theorem card_monicFinset (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    (monicFinset K n).card = Fintype.card K ^ n := by
  classical
  unfold Uniformity.Density.IFCG17.monicFinset
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
    Uniformity.Density.IFCG4.card_monicOfDeg]

/-- `zed`'s stack term expands to the per-monic pattern stacks. -/
private theorem zed_expand (K : Type*) [Field K] [Fintype K] (n v : ℕ) :
    (zed K n v : ℝ) * ((Fintype.card K : ℝ)⁻¹) ^ v
      = ∑ g ∈ monicFinset K n,
          ((PowerSeries.coeff v (patRate (Fintype.card K) (patternOf g)) : ℕ) : ℝ)
            * ((Fintype.card K : ℝ)⁻¹) ^ v := by
  unfold Uniformity.Density.IFCG70.zed
  push_cast
  rw [Finset.sum_mul]

/-- The census stack is summable at every mass. -/
theorem summable_zed_mul (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    Summable (fun v => (zed K n v : ℝ) * ((Fintype.card K : ℝ)⁻¹) ^ v) := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  refine Summable.congr (summable_sum fun g hg => ?_) fun v => (zed_expand K n v).symm
  exact (summable_tsum_patRate_mul hq (patternOf g)
    (fun de hde => (one_le_of_mem_patternOf de hde).1)).1

/-- ★★ **THE CENSUS VALUE STACK — VA23's named identity, GNA's stack summed**:
`Σ'_v zed(K,n,v)·q^{−v} = q^{2n}` — each of the `q^n` monic residuals contributes its
shape box `q^n` through the pattern stack; equivalently the full-box depth-stratum
masses sum to `1`. -/
theorem tsum_zed_mul (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    ∑' v, (zed K n v : ℝ) * ((Fintype.card K : ℝ)⁻¹) ^ v
      = (Fintype.card K : ℝ) ^ (2 * n) := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [tsum_congr (zed_expand K n),
    Summable.tsum_finsetSum (fun g hg =>
      (summable_tsum_patRate_mul hq (patternOf g)
        (fun de hde => (one_le_of_mem_patternOf de hde).1)).1)]
  have hgval : ∀ g ∈ monicFinset K n,
      ∑' v, ((PowerSeries.coeff v (patRate (Fintype.card K) (patternOf g)) : ℕ) : ℝ)
          * ((Fintype.card K : ℝ)⁻¹) ^ v
        = (Fintype.card K : ℝ) ^ n := by
    intro g hg
    obtain ⟨hm, hd⟩ := mem_monicFinset_iff.mp hg
    rw [(summable_tsum_patRate_mul hq (patternOf g)
        (fun de hde => (one_le_of_mem_patternOf de hde).1)).2,
      patternWeight_patternOf hm, hd]
  rw [Finset.sum_congr rfl hgval, Finset.sum_const, card_monicFinset, nsmul_eq_mul]
  push_cast
  rw [← pow_add, two_mul]

end ZedStack

/-! ## §4 — ★★★ THE DRAIN FIRES AT EVERY POSITIVE MASS SPLIT: IGV's min-reduction and
GNA's exact diagonal census make the normalized stratum mass the level-free
`zed(K,min,v)·q^{−v−2·min}`, and the §3 stack drains the deep box -/

section DrainAll

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The general box census** (IGV's min-reduction composed with GNA's diagonal
census): at any mass split `0 < n₁ ≤ n₂` and level `L > v`,
`#depthPairSet(n₁,n₂,L,v)·q^{v+2n₁} = zed(K,n₁,v)·q^{(n₁+n₂)L}` — the normalized
stratum mass is the LEVEL-FREE `zed(K,n₁,v)·q^{−v−2n₁}`. -/
private theorem card_depthPairSet_general [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] {π : O} (hπ : Irreducible π) {n₁ n₂ L v : ℕ}
    (h1 : 0 < n₁) (hn : n₁ ≤ n₂) (hv : v < L) :
    Nat.card (depthPairSet O π n₁ n₂ L v) * residueCard O ^ (v + 2 * n₁)
      = zed (ResidueField O) n₁ v * residueCard O ^ ((n₁ + n₂) * L) := by
  have hexp : n₁ * (2 * L - 1) + ((n₂ - n₁) * L + n₁) = (n₁ + n₂) * L := by
    have h2L : 1 ≤ 2 * L := by omega
    zify [hn, h2L]
    ring
  calc Nat.card (depthPairSet O π n₁ n₂ L v) * residueCard O ^ (v + 2 * n₁)
      = Nat.card (redDepthPairSet O π n₁ L v) * residueCard O ^ ((n₂ - n₁) * L)
          * residueCard O ^ (v + 2 * n₁) := by
        rw [card_depthPairSet_reduce h1 hn hv]
    _ = Nat.card (redDepthPairSet O π n₁ L v) * residueCard O ^ (v + n₁)
          * residueCard O ^ ((n₂ - n₁) * L + n₁) := by
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
        congr 2
        omega
    _ = zed (ResidueField O) n₁ v * residueCard O ^ (n₁ * (2 * L - 1))
          * residueCard O ^ ((n₂ - n₁) * L + n₁) := by
        rw [card_redDepthPairSet_general hπ hv]
    _ = zed (ResidueField O) n₁ v * residueCard O ^ ((n₁ + n₂) * L) := by
        rw [mul_assoc, ← pow_add, hexp]

/-- The drain at an ordered split, from the §3 stack. -/
private theorem deepStratumDrain_of_le {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) :
    DeepStratumDrain n₁ n₂ := by
  intro O _ _ _ _ _ π hπ
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  have hqF : Fintype.card (ResidueField O) = residueCard O := Nat.card_eq_fintype_card.symm
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < residueCard O)
  -- ★ the complementary identity: the deep-box mass is 1 minus the head masses
  have hkey : ∀ V : ℕ,
      (Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1)) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2))
        = 1 - ∑ v ∈ Finset.range (V + 1),
            (zed (ResidueField O) n₁ v : ℝ) * (((residueCard O : ℕ) : ℝ)⁻¹) ^ v
              * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (2 * n₁) := by
    intro V
    -- the ℕ partition at level V+2
    have hpart : ∑ v ∈ Finset.range (V + 1), Nat.card (depthPairSet O π n₁ n₂ (V + 2) v)
        + Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1))
        = residueCard O ^ ((n₁ + n₂) * (V + 2)) := by
      rw [card_depthPairSetGE_eq_sum π,
        Finset.sum_range_add_sum_Ico _ (by omega : V + 1 ≤ V + 2 + 1)]
      exact sum_card_depthPairSet_eq π n₁ n₂ (V + 2)
    have hcastpart : (Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1)) : ℝ)
        + ∑ v ∈ Finset.range (V + 1),
            (Nat.card (depthPairSet O π n₁ n₂ (V + 2) v) : ℝ)
        = ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2)) := by
      rw [add_comm]
      exact_mod_cast hpart
    -- the per-stratum mass, level-free
    have hmass : ∀ v ∈ Finset.range (V + 1),
        (Nat.card (depthPairSet O π n₁ n₂ (V + 2) v) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2))
          = (zed (ResidueField O) n₁ v : ℝ) * (((residueCard O : ℕ) : ℝ)⁻¹) ^ v
              * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (2 * n₁) := by
      intro v hv
      have hvL : v < V + 2 := by have := Finset.mem_range.mp hv; omega
      have hcast : (Nat.card (depthPairSet O π n₁ n₂ (V + 2) v) : ℝ)
            * ((residueCard O : ℕ) : ℝ) ^ (v + 2 * n₁)
          = (zed (ResidueField O) n₁ v : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2)) := by
        exact_mod_cast card_depthPairSet_general hπ h₁ hn hvL
      have hcancel : ((residueCard O : ℕ) : ℝ) ^ (v + 2 * n₁)
          * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (v + 2 * n₁) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hq0), one_pow]
      rw [div_eq_iff (by positivity)]
      calc (Nat.card (depthPairSet O π n₁ n₂ (V + 2) v) : ℝ)
          = (Nat.card (depthPairSet O π n₁ n₂ (V + 2) v) : ℝ)
              * (((residueCard O : ℕ) : ℝ) ^ (v + 2 * n₁)
                  * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (v + 2 * n₁)) := by
            rw [hcancel, mul_one]
        _ = ((Nat.card (depthPairSet O π n₁ n₂ (V + 2) v) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ (v + 2 * n₁))
                * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (v + 2 * n₁) := by ring
        _ = (zed (ResidueField O) n₁ v : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2))
                * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (v + 2 * n₁) := by rw [hcast]
        _ = (zed (ResidueField O) n₁ v : ℝ) * (((residueCard O : ℕ) : ℝ)⁻¹) ^ v
              * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (2 * n₁)
                * ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2)) := by
            rw [pow_add]
            ring
    rw [eq_sub_iff_add_eq, ← Finset.sum_congr rfl hmass, ← Finset.sum_div, ← add_div,
      hcastpart, div_self (ne_of_gt (by positivity))]
  -- ★ the head masses tend to 1 (the §3 stack)
  have hsz := summable_zed_mul (ResidueField O) n₁
  have hts := tsum_zed_mul (ResidueField O) n₁
  simp only [hqF] at hsz hts
  have hhead : Filter.Tendsto (fun V : ℕ => ∑ v ∈ Finset.range (V + 1),
      (zed (ResidueField O) n₁ v : ℝ) * (((residueCard O : ℕ) : ℝ)⁻¹) ^ v
        * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (2 * n₁)) Filter.atTop (nhds 1) := by
    have hh : HasSum (fun v =>
        (zed (ResidueField O) n₁ v : ℝ) * (((residueCard O : ℕ) : ℝ)⁻¹) ^ v
          * (((residueCard O : ℕ) : ℝ)⁻¹) ^ (2 * n₁)) 1 := by
      have hmul := hsz.hasSum.mul_right ((((residueCard O : ℕ) : ℝ)⁻¹) ^ (2 * n₁))
      rw [hts, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hq0), one_pow] at hmul
      exact hmul
    exact hh.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  -- assemble
  have hlim := tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ)) |>.sub hhead
  rw [sub_self] at hlim
  exact hlim.congr fun V => (hkey V).symm

/-- ★★★ **THE DEEP-BOX DRAIN AT EVERY POSITIVE MASS SPLIT** — the `min ≥ 2` remainder
of VA23 closes (and the `min = 1` fires are subsumed): `DeepStratumDrain n₁ n₂` holds
OUTRIGHT for all `n₁, n₂ ≥ 1`. -/
theorem deepStratumDrain_all {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    DeepStratumDrain n₁ n₂ := by
  rcases Nat.lt_or_ge n₂ n₁ with hlt | hge
  · have h := deepStratumDrain_of_le h₂ (le_of_lt hlt)
    intro O _ _ _ _ _ π hπ
    refine (h O π hπ).congr fun V => ?_
    rw [card_depthPairSetGE_swap, Nat.add_comm n₂ n₁]
  · exact deepStratumDrain_of_le h₁ hge

end DrainAll

/-! ## §5 — ★★★ THE ROW AND THE MASTERS RE-BASED WITHOUT THE DRAIN: VA23's premises
with `hDR` DISCHARGED; every other premise byte-identical -/

section Masters

/-- The exact premise currency of VA23's masters, now a theorem. -/
theorem deepStratumDrain_min_two : ∀ n₁ n₂ : ℕ, 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂ :=
  fun _ _ h₁ h₂ => deepStratumDrain_all (by omega) (by omega)

/-- ★★★ **THE CONVOLUTION ROW'S BASE, DRAIN-FREE**: `VisCensusLaw g m σ` at EVERY
mass and type, both genres, now rests on exactly

  {per-entry geometric CLUSTER census values (`VisEntryClusterGeom`),
   the two collision limits (`CollisionLaw` + the power collision `ZcURLim`)}.

VA23's `min ≥ 2` deep-box drain premise is GONE (§4). -/
theorem visCensusLaw_of_clusterGeom_collisions {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType)
    (hentry : ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
      0 < n₁ → 0 < n₂ → n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
        VisEntryClusterGeom g n₁ n₂ σ part)
    (hC : CollisionLaw m σ)
    (hPC : ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
    ∀ g, VisCensusLaw g m σ :=
  Uniformity.Density.IFCG71.visCensusLaw_of_clusterGeom_collisions hm σ hentry
    (fun n₁ n₂ _ h₁ h₂ => deepStratumDrain_all (by omega) (by omega)) hC hPC

/-- ★★★ **THE CENSUS MASTER, DRAIN-FREE**: VA23's `decidedSliceAt_all_of_clusterGeom`
with the σ-free drain premise `hDR` DISCHARGED — the all-degree decided slice now
rests on {cluster values + collision limits (row-guarded), `PowerFullSpanLaw`,
`LeafSubfaceLaw` at non-singleton σ, the `e = 4` remainder laws}. -/
theorem decidedSliceAt_all_of_clusterGeom
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
            VisEntryClusterGeom g n₁ n₂ σ part)
    (hCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → CollisionLaw e σ)
    (hPCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ZcURLim (fun O _ _ _ _ _ π M =>
          (powerCollisionTotal O π e σ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (e * (M + e))))
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG71.decidedSliceAt_all_of_clusterGeom hCG
    deepStratumDrain_min_two hCL hPCL hPF hLeafSub hR4

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, DRAIN-FREE**: VA23's `capstoneHypotheses_of_clusterGeom`
with the drain premise DISCHARGED. -/
theorem capstoneHypotheses_of_clusterGeom (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
            VisEntryClusterGeom g n₁ n₂ σ part)
    (hCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → CollisionLaw e σ)
    (hPCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ZcURLim (fun O _ _ _ _ _ π M =>
          (powerCollisionTotal O π e σ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (e * (M + e))))
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG71.capstoneHypotheses_of_clusterGeom n hladder hdeepTwist hFC
    hEis hCG deepStratumDrain_min_two hCL hPCL hLeafSub

end Masters

end Uniformity.Density.IFCG73

end

/-! ## AXCHECK FOOTER — §§1–4 (the primo/pattern/census value stacks and the drain)
expect PURE Lean core `{propext, Classical.choice, Quot.sound}` — GNA's census, IGV's
transport, VCL's box partition, and VA23's GE partition are all Lean-core.  §5's row
inherits exactly the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (through VA23's assembly — never
re-consumed); the two masters additionally inherit
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).  C.33
and `AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG73.sum_primo_mul_le
#print axioms Uniformity.Density.IFCG73.summable_primo_mul
#print axioms Uniformity.Density.IFCG73.tsum_primo_mul
#print axioms Uniformity.Density.IFCG73.summable_tsum_patRate_mul
#print axioms Uniformity.Density.IFCG73.summable_zed_mul
#print axioms Uniformity.Density.IFCG73.tsum_zed_mul
#print axioms Uniformity.Density.IFCG73.deepStratumDrain_all
#print axioms Uniformity.Density.IFCG73.deepStratumDrain_min_two
#print axioms Uniformity.Density.IFCG73.visCensusLaw_of_clusterGeom_collisions
#print axioms Uniformity.Density.IFCG73.decidedSliceAt_all_of_clusterGeom
#print axioms Uniformity.Density.IFCG73.capstoneHypotheses_of_clusterGeom
