/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.LinearFiber
import LeanUrat.OM.HenselCount
import LeanUrat.OM.SparseResultant
import LeanUrat.OM.BlockProduct

/-!
# GradedHensel — W4d2′: the polygon-graded Hensel margin

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md`, the W4d2-1 STATUS block's named
obligation: `BlockProduct`'s flat margins (`2c < N`, floors in `[c+1, N-c]`) are EMPTY at all
three real d2-0 gate cells; the fix is to redo the HenselCount torsor/saturation bootstrap in
the polygon-GRADED filtration.  Numeric ground truth: `/workspace-vast/asving/tmp/phaseb_w4d2p/`
(this wave's gate — margins verified where the flat ones were false) on top of
`/workspace-vast/asving/tmp/phaseb_w4d2_0/` (cases A/B/C).

**THE PINNED GRADED MARGIN** (gate-verified, `h = 1`).  Per block `i` (ramification `e_i`,
degree `m_i = e_i·μ_i`, cross-resultant share `S_i = Σ_{j≠i} m_j·w_ij ∈ ℕ`), x-slot `t < m_i`:

* `sideFloor e m t = ⌈(m + 1 - t)/e⌉` — the x-adic shadow of the `FreshClusterPattern`
  θ-floors (the pattern coset IS the coefficient box at these floors);
* `sideDepth e S N t = (N - S) - ⌊t/e⌋` — the graded kernel depth (θ-form `e(N-S) - t`,
  ceiled; F5's measured torsor-stability fit `K ≥ e_i(N-S_i) - e_i·j`);
* **(M1) saturation margin**: `sideFloor e_i m_i t ≤ sideDepth e_i S_i N t` — replaces the
  flat `flo ≤ N - c`;
* **(M2) quadratic margin**: `sideDepth_i s + sideDepth_j t ≥ N` — replaces the flat
  `N ≤ 2(m - c)`;
* **(M0) graded kernel bound**: kernel vectors of the Sylvester map at every point of the
  graded cells are per-slot `p^dep`-divisible — replaces the flat uniform `p^(N-c)`.

`gate_margin_graded_{A,B,C}` prove M1 ∧ M2 hold at the three real cells (the direct
counterpart of the flat `gate_margin_*` failures in `BlockProduct`).

**Deliverables.**
1. `sideFloor`/`sideDepth` + **`graded_mulVec_upgrade`/`graded_ker_bound`** — the graded
   kernel/upgrade engine: a scaled diagonal-dominance certificate (pivot rows `r`, diagonal
   valuations `v`, scaled target depths `D` at scale `w`, off-diagonal certified valuations
   `off` with `w·v j + D j + 1 ≤ w·off j j' + D j'`) upgrades solutions of `M *ᵥ x = y` with
   graded-deep `y` to per-slot depths `⌈D j / w⌉`.  This is the graded replacement of
   `HenselCount.dvd_of_mulVec_dvd` (which only reaches the flat `min (k-c) (N-c)`).
2. `SaturatedAt` + `patternCell_saturatedAt` — graded saturation of pattern cosets under M1 —
   and `ker_shift_graded` (kernel translation stays in the cosets, product preserved under M2).
3. `pair_card_graded` — the graded pair law `card(image)·p^c = card S_A · card S_B` under the
   pointwise margin hypothesis `GradedUpgradeAt` (per-slot kernel depth at every cell point,
   stated in polynomial form) + per-point kernel count `p^c`; via `fiberEquivPolyKer`, the
   graded torsor bijection.
4. `gate_margin_graded_{A,B,C}` + the full case-B instantiation: `caseB_upgrade` (the
   pointwise bootstrap at every cell point, via unit-diagonal elimination — no `decide`),
   `caseB_ker_card`, `caseB_law_graded` (the gate law `81·3² = 27·27` derived THROUGH
   `pair_card_graded`), cross-checked against `BlockProduct.gateB_image_card`.
5. `GradedChain`/`blocks_card_graded` — the k-block fold of the graded pair law (the graded
   `BlockProduct.blocks_card`).

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints; no existing module
touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanUrat.OM.GradedHensel

open Polynomial Matrix
open LeanUrat.OM
open LeanUrat.OM.HenselCount
open LeanUrat.OM.BlockProduct

/-! ## 0. Ceiling-division helpers (the scaled-grading arithmetic) -/

/-- `⌈q / w⌉` as `(q + (w - 1)) / w`. -/
def cdiv (q w : ℕ) : ℕ := (q + (w - 1)) / w

theorem cdiv_le_iff {w : ℕ} (hw : 0 < w) (q A : ℕ) : cdiv q w ≤ A ↔ q ≤ w * A := by
  unfold cdiv
  rw [Nat.div_le_iff_le_mul_add_pred hw, Nat.add_le_add_iff_right]

theorem le_w_mul_cdiv {w : ℕ} (hw : 0 < w) (q : ℕ) : q ≤ w * cdiv q w :=
  (cdiv_le_iff hw q _).mp le_rfl

theorem cdiv_zero_left {w : ℕ} (hw : 0 < w) : cdiv 0 w = 0 := by
  unfold cdiv
  rw [Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

theorem cdiv_mono {w q q' : ℕ} (h : q ≤ q') : cdiv q w ≤ cdiv q' w :=
  Nat.div_le_div_right (by omega)

/-- The transport helper for the engine's per-round arithmetic:
`q' + w·u ≤ q + w·k  ⟹  ⌈q'/w⌉ + u ≤ ⌈q/w⌉ + k`. -/
theorem cdiv_add_le_cdiv_add {w : ℕ} (hw : 0 < w) {q q' u k : ℕ}
    (h : q' + w * u ≤ q + w * k) : cdiv q' w + u ≤ cdiv q w + k := by
  have h1 : cdiv q' w + u = (q' + w * u + (w - 1)) / w := by
    unfold cdiv
    rw [show q' + w * u + (w - 1) = (q' + (w - 1)) + u * w by ring,
      Nat.add_mul_div_right _ _ hw]
  have h2 : cdiv q w + k = (q + w * k + (w - 1)) / w := by
    unfold cdiv
    rw [show q + w * k + (w - 1) = (q + (w - 1)) + k * w by ring,
      Nat.add_mul_div_right _ _ hw]
  rw [h1, h2]
  exact Nat.div_le_div_right (Nat.add_le_add_right h _)

/-! ## 1. The graded weights: per-slot floors and depths (h = 1) -/

/-- x-slot pattern floor of a block of degree `m = e·μ`, slope `1/e` (`h = 1`):
`⌈(m + 1 - t)/e⌉` — the x-adic shadow of the `FreshClusterPattern` floors
`β_j ∈ (θ)^(e(μ-j)+1)` (every increment has θ-valuation `≥ m + 1`; slot `x^t` carries
θ-weight `t`, `p` carries θ-weight `e`). -/
def sideFloor (e m t : ℕ) : ℕ := cdiv (m + 1 - t) e

/-- x-slot graded kernel depth of a block with cross-resultant share `S`:
`(N - S) - ⌊t/e⌋` (the ceiling of the θ-form `(e(N - S) - t)/e`). -/
def sideDepth (e S N t : ℕ) : ℕ := N - S - t / e

/-! ## 2. Per-slot saturation (deliverable 2) -/

variable {p : ℕ} [hp : Fact p.Prime] {N : ℕ}

/-- **Per-slot (graded) saturation**: `S` is stable under coefficientwise perturbation at the
per-slot depths `dep` — the graded refinement of `BlockProduct.Saturated` (which is the
constant-depth instance). -/
def SaturatedAt (S : Set ((ZMod (p ^ N))[X])) (d : ℕ) (dep : ℕ → ℕ) : Prop :=
  ∀ P ∈ S, ∀ Q : (ZMod (p ^ N))[X], Q.Monic → Q.natDegree = d →
    (∀ i, (p : ZMod (p ^ N)) ^ dep i ∣ (Q - P).coeff i) → Q ∈ S

/-- **Graded saturation of pattern cosets under the pinned per-slot margin M1**
(`flo i ≤ dep i` per slot): kernel translation at per-slot depths `dep` preserves the coset.
This replaces the flat `patternCell_saturated` (uniform `flo i ≤ m`), which is gate-empty. -/
theorem patternCell_saturatedAt {P₀ : (ZMod (p ^ N))[X]} {d : ℕ} {flo dep : ℕ → ℕ}
    (h : ∀ i, flo i ≤ dep i) : SaturatedAt (patternCell P₀ d flo) d dep := by
  intro P hP Q hQmon hQdeg hdvd
  refine ⟨hQmon, hQdeg, fun i => ?_⟩
  have hsplit : Q - P₀ = (P - P₀) + (Q - P) := by ring
  rw [hsplit, Polynomial.coeff_add]
  exact dvd_add (hP.2.2 i) (dvd_trans (pow_dvd_pow _ (h i)) (hdvd i))

/-- Differences of pattern-coset members satisfy the per-slot floors. -/
theorem patternCell_sub_dvd {P₀ : (ZMod (p ^ N))[X]} {d : ℕ} {flo : ℕ → ℕ}
    {P Q : (ZMod (p ^ N))[X]} (hP : P ∈ patternCell P₀ d flo)
    (hQ : Q ∈ patternCell P₀ d flo) (i : ℕ) :
    (p : ZMod (p ^ N)) ^ flo i ∣ (P - Q).coeff i := by
  have hPQ : P - Q = P - P₀ - (Q - P₀) := by ring
  rw [hPQ, Polynomial.coeff_sub]
  exact dvd_sub (hP.2.2 i) (hQ.2.2 i)

theorem patternCell_finite (P₀ : (ZMod (p ^ N))[X]) (d : ℕ) (flo : ℕ → ℕ) :
    (patternCell P₀ d flo).Finite :=
  (HenselCount.cell_finite P₀ d 0).subset (patternCell_subset_cell fun _ => Nat.zero_le _)

/-! ## 3. Slot-graded multiplication: conv floors and quadratic death -/

/-- Products of per-slot-divisible polynomials are per-row divisible below the convolution
floor: if `qb (s + t) ≤ fA s + fB t` on the supported range, then `p^(qb r) ∣ (P·Q).coeff r`. -/
theorem dvd_coeff_mul_slot {a b : ℕ} {fA fB qb : ℕ → ℕ}
    (hqb : ∀ s t, s < a → t < b → qb (s + t) ≤ fA s + fB t)
    {P Q : (ZMod (p ^ N))[X]}
    (hP : ∀ i, (p : ZMod (p ^ N)) ^ fA i ∣ P.coeff i) (hPtop : ∀ i, a ≤ i → P.coeff i = 0)
    (hQ : ∀ i, (p : ZMod (p ^ N)) ^ fB i ∣ Q.coeff i) (hQtop : ∀ i, b ≤ i → Q.coeff i = 0)
    (r : ℕ) : (p : ZMod (p ^ N)) ^ qb r ∣ (P * Q).coeff r := by
  rw [Polynomial.coeff_mul]
  refine Finset.dvd_sum fun ij hij => ?_
  have hsum : ij.1 + ij.2 = r := Finset.mem_antidiagonal.mp hij
  by_cases hs : ij.1 < a
  · by_cases ht : ij.2 < b
    · have h1 := mul_dvd_mul (hP ij.1) (hQ ij.2)
      rw [← pow_add] at h1
      exact dvd_trans (pow_dvd_pow _ (hsum ▸ hqb ij.1 ij.2 hs ht)) h1
    · rw [hQtop ij.2 (by omega), mul_zero]
      exact dvd_zero _
  · rw [hPtop ij.1 (by omega), zero_mul]
    exact dvd_zero _

/-- **Graded quadratic death**: under the pinned quadratic margin M2
(`dep_A s + dep_B t ≥ N` per slot pair), the product of two per-slot-`dep`-divisible
increments vanishes outright — the graded replacement of the flat
`mul_eq_zero_of_coeff_dvd` (margin `2c ≤ N`). -/
theorem mul_eq_zero_of_slot_dvd {a b : ℕ} {depA depB : ℕ → ℕ}
    (hM2 : ∀ s t, s < a → t < b → N ≤ depA s + depB t)
    {P Q : (ZMod (p ^ N))[X]}
    (hP : ∀ i, (p : ZMod (p ^ N)) ^ depA i ∣ P.coeff i) (hPtop : ∀ i, a ≤ i → P.coeff i = 0)
    (hQ : ∀ i, (p : ZMod (p ^ N)) ^ depB i ∣ Q.coeff i) (hQtop : ∀ i, b ≤ i → Q.coeff i = 0) :
    P * Q = 0 := by
  have hN0 : (p : ZMod (p ^ N)) ^ N = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  ext r
  rw [Polynomial.coeff_zero]
  have h := dvd_coeff_mul_slot (qb := fun _ => N) (fA := depA) (fB := depB)
    (fun s t hs ht => hM2 s t hs ht) hP hPtop hQ hQtop r
  rw [hN0] at h
  exact zero_dvd_iff.mp h

/-! ## 4. Deliverable 1 — the graded kernel/upgrade engine

The graded replacement of `HenselCount.dvd_of_mulVec_dvd`.  Certificate data: a pivot row
`r j` per column `j`, diagonal valuations `v` (`M (r j) j = p^(v j)·unit`), scaled target
depths `D` at scale `w` (θ-units: `w = e`, `D = e·(N - S) - t`), and certified off-diagonal
valuations `off` dominating in the scaled sense `w·v j + D j + 1 ≤ w·off j j' + D j'`.
Conclusion: solutions of `M *ᵥ x = y` with `y` graded-deep at the pivot rows are per-slot
`p^⌈D j / w⌉`-divisible.  The flat lemma is the instance `w = 1`, `r = τ⁻¹`-transversal,
constant `D`; the scale `w` is what lets half-integer θ-depths (the polygon grading of
`SparseResultant.sparseTwist`) ride through integer `p`-divisibilities. -/

theorem graded_mulVec_upgrade {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod (p ^ N)))
    {w : ℕ} (hw : 0 < w) (r : Fin n → Fin n) (v D : Fin n → ℕ) (off : Fin n → Fin n → ℕ)
    (hvN : ∀ j, v j ≤ N)
    (hdiag : ∀ j, ∃ u : (ZMod (p ^ N))ˣ, M (r j) j = (p : ZMod (p ^ N)) ^ v j * u)
    (hDvN : ∀ j, D j ≤ w * (N - v j))
    (hoffdvd : ∀ j j', j' ≠ j → (p : ZMod (p ^ N)) ^ off j j' ∣ M (r j) j')
    (hoffbound : ∀ j j', j' ≠ j → w * v j + D j + 1 ≤ w * off j j' + D j')
    {x y : Fin n → ZMod (p ^ N)} (hxy : M.mulVec x = y)
    (hy : ∀ j, (p : ZMod (p ^ N)) ^ (v j + cdiv (D j) w) ∣ y (r j)) :
    ∀ j, (p : ZMod (p ^ N)) ^ cdiv (D j) w ∣ x j := by
  classical
  set T : ℕ := Finset.univ.sup D with hT
  have hDT : ∀ j, D j ≤ T := fun j => Finset.le_sup (Finset.mem_univ j)
  have main : ∀ s : ℕ, ∀ j, (p : ZMod (p ^ N)) ^ cdiv (D j - (T - s)) w ∣ x j := by
    intro s
    induction s with
    | zero =>
      intro j
      have h0 : D j - (T - 0) = 0 := by have := hDT j; omega
      rw [h0, cdiv_zero_left hw, pow_zero]
      exact one_dvd _
    | succ s ih =>
      intro j
      by_cases hb0 : cdiv (D j - (T - (s + 1))) w = 0
      · rw [hb0, pow_zero]
        exact one_dvd _
      have hq1 : 1 ≤ D j - (T - (s + 1)) := by
        by_contra hq
        exact hb0 (by rw [show D j - (T - (s + 1)) = 0 by omega, cdiv_zero_left hw])
      obtain ⟨u, hu⟩ := hdiag j
      have hrow : ∑ j' : Fin n, M (r j) j' * x j' = y (r j) := by
        have h := congrFun hxy (r j)
        simpa [Matrix.mulVec, dotProduct] using h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hrow
      have hsplit : M (r j) j * x j
          = y (r j) - ∑ j' ∈ Finset.univ.erase j, M (r j) j' * x j' := by
        linear_combination hrow
      set b' : ℕ := cdiv (D j - (T - (s + 1))) w with hb'
      have hble : b' ≤ cdiv (D j) w := cdiv_mono (by omega)
      have hterm : ∀ j' ∈ Finset.univ.erase j,
          (p : ZMod (p ^ N)) ^ (v j + b') ∣ M (r j) j' * x j' := by
        intro j' hj'
        have hne : j' ≠ j := (Finset.mem_erase.mp hj').1
        have h3 := mul_dvd_mul (hoffdvd j j' hne) (ih j')
        rw [← pow_add] at h3
        refine dvd_trans (pow_dvd_pow _ ?_) h3
        have hb := hoffbound j j' hne
        have hDT' := hDT j'
        have harith : (D j - (T - (s + 1))) + w * v j
            ≤ (D j' - (T - s)) + w * off j j' := by
          generalize w * v j = W1 at hb ⊢
          generalize w * off j j' = W2 at hb ⊢
          omega
        have hkey := cdiv_add_le_cdiv_add hw harith
        rw [hb']
        omega
      have hRHS : (p : ZMod (p ^ N)) ^ (v j + b') ∣
          y (r j) - ∑ j' ∈ Finset.univ.erase j, M (r j) j' * x j' :=
        dvd_sub
          (dvd_trans (pow_dvd_pow _ (by omega : v j + b' ≤ v j + cdiv (D j) w)) (hy j))
          (Finset.dvd_sum hterm)
      obtain ⟨z, hz⟩ := hRHS
      have hMx : (p : ZMod (p ^ N)) ^ v j * (u : ZMod (p ^ N)) * x j
          = (p : ZMod (p ^ N)) ^ (v j + b') * z := by
        rw [← hu, hsplit, hz]
      have hkill : (p : ZMod (p ^ N)) ^ v j
          * ((u : ZMod (p ^ N)) * x j - (p : ZMod (p ^ N)) ^ b' * z) = 0 := by
        rw [pow_add] at hMx
        linear_combination hMx
      obtain ⟨z', hz'⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (hvN j) hkill
      have hxj : x j = (u⁻¹ : (ZMod (p ^ N))ˣ)
          * ((p : ZMod (p ^ N)) ^ b' * z + (p : ZMod (p ^ N)) ^ (N - v j) * z') := by
        have hux : (u : ZMod (p ^ N)) * x j
            = (p : ZMod (p ^ N)) ^ b' * z + (p : ZMod (p ^ N)) ^ (N - v j) * z' := by
          linear_combination hz'
        calc x j = (u⁻¹ : (ZMod (p ^ N))ˣ) * ((u : ZMod (p ^ N)) * x j) := by
              rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = _ := by rw [hux]
      rw [hxj]
      refine Dvd.dvd.mul_left (dvd_add (dvd_mul_right _ z) ?_) _
      refine Dvd.dvd.mul_right (pow_dvd_pow _ ?_) z'
      rw [hb']
      refine (cdiv_le_iff hw _ _).mpr ?_
      exact le_trans (Nat.sub_le _ _) (hDvN j)
  intro j
  have h := main T j
  rwa [Nat.sub_self, Nat.sub_zero] at h

/-- **The graded kernel bound** (deliverable 1, kernel form): kernel vectors of a certified
matrix are per-slot `p^⌈D j / w⌉`-divisible — the graded replacement of the flat uniform
`p^(N-c)`-divisibility (`HenselCount.dvd_of_mulVec_eq_zero`). -/
theorem graded_ker_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod (p ^ N)))
    {w : ℕ} (hw : 0 < w) (r : Fin n → Fin n) (v D : Fin n → ℕ) (off : Fin n → Fin n → ℕ)
    (hvN : ∀ j, v j ≤ N)
    (hdiag : ∀ j, ∃ u : (ZMod (p ^ N))ˣ, M (r j) j = (p : ZMod (p ^ N)) ^ v j * u)
    (hDvN : ∀ j, D j ≤ w * (N - v j))
    (hoffdvd : ∀ j j', j' ≠ j → (p : ZMod (p ^ N)) ^ off j j' ∣ M (r j) j')
    (hoffbound : ∀ j j', j' ≠ j → w * v j + D j + 1 ≤ w * off j j' + D j')
    {x : Fin n → ZMod (p ^ N)} (hx : M.mulVec x = 0) :
    ∀ j, (p : ZMod (p ^ N)) ^ cdiv (D j) w ∣ x j :=
  graded_mulVec_upgrade M hw r v D off hvN hdiag hDvN hoffdvd hoffbound hx
    (fun j => by rw [Pi.zero_apply]; exact dvd_zero _)

/-! ## 5. Deliverable 3 — the graded pair law

The pointwise margin hypothesis is `GradedUpgradeAt` (polynomial form): at the factorization
point `(A, B)`, any solution of the linearized system `B·α + A·β = Y` with conv-floor-deep
`Y` is per-slot `dep`-deep.  With `Y = 0` this is exactly the graded kernel bound M0 at the
point; consumers discharge it via `graded_mulVec_upgrade` on a certificate-reduced Sylvester
matrix, or directly (case B below). -/

variable {p : ℕ} [hp : Fact p.Prime] {N : ℕ}

/-- **The pointwise graded-margin hypothesis** at `(A, B)`. -/
def GradedUpgradeAt (A B : (ZMod (p ^ N))[X]) (a b : ℕ) (depA depB qb : ℕ → ℕ) : Prop :=
  ∀ α β Y : (ZMod (p ^ N))[X],
    (∀ i, a ≤ i → α.coeff i = 0) → (∀ i, b ≤ i → β.coeff i = 0) →
    B * α + A * β = Y → (∀ i, (p : ZMod (p ^ N)) ^ qb i ∣ Y.coeff i) →
    (∀ i, (p : ZMod (p ^ N)) ^ depA i ∣ α.coeff i)
      ∧ ∀ i, (p : ZMod (p ^ N)) ^ depB i ∣ β.coeff i

/-- The polynomial kernel at `(A, B)`: increment pairs annihilated by the linearization. -/
def polyKer (A B : (ZMod (p ^ N))[X]) (a b : ℕ) :
    Set ((ZMod (p ^ N))[X] × (ZMod (p ^ N))[X]) :=
  {q | (∀ i, a ≤ i → q.1.coeff i = 0) ∧ (∀ i, b ≤ i → q.2.coeff i = 0)
    ∧ B * q.1 + A * q.2 = 0}

/-- **Graded increment bootstrap** (the graded `fiber_sub_dvd`): increments of two
factorizations with equal product in the pattern cells are per-slot `dep`-divisible, given
the pointwise margin at the base point (the quadratic right side is conv-floor-deep). -/
theorem fiber_sub_dvd_graded {a b : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    {floA floB depA depB qb : ℕ → ℕ}
    (hqb : ∀ s t, s < a → t < b → qb (s + t) ≤ floA s + floB t)
    {A B A' B' : (ZMod (p ^ N))[X]}
    (hA : A ∈ patternCell A₀ a floA) (hB : B ∈ patternCell B₀ b floB)
    (hA' : A' ∈ patternCell A₀ a floA) (hB' : B' ∈ patternCell B₀ b floB)
    (hup : GradedUpgradeAt A B a b depA depB qb)
    (hprod : A' * B' = A * B) :
    (∀ i, (p : ZMod (p ^ N)) ^ depA i ∣ (A' - A).coeff i)
      ∧ ∀ i, (p : ZMod (p ^ N)) ^ depB i ∣ (B' - B).coeff i := by
  have hαtop : ∀ i, a ≤ i → (A' - A).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hA'.1 hA.1 hA'.2.1 hA.2.1 hi
  have hβtop : ∀ i, b ≤ i → (B' - B).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hB'.1 hB.1 hB'.2.1 hB.2.1 hi
  have hkey : B * (A' - A) + A * (B' - B) = -((A' - A) * (B' - B)) := by
    linear_combination hprod
  have hY : ∀ i, (p : ZMod (p ^ N)) ^ qb i ∣ (-((A' - A) * (B' - B))).coeff i := by
    intro i
    rw [Polynomial.coeff_neg]
    exact dvd_neg.mpr (dvd_coeff_mul_slot hqb
      (fun i => patternCell_sub_dvd hA' hA i) hαtop
      (fun i => patternCell_sub_dvd hB' hB i) hβtop i)
  exact hup (A' - A) (B' - B) _ hαtop hβtop hkey hY

/-- **Graded kernel shift** (deliverable 2, torsor direction 2): translating a factorization
by a polynomial-kernel element stays in the (saturated) sub-cells and preserves the product —
per-slot depths from the pointwise margin, quadratic death from M2. -/
theorem ker_shift_graded {a b : ℕ} (hN : 0 < N) {A₀ B₀ : (ZMod (p ^ N))[X]}
    {floA floB depA depB qb : ℕ → ℕ} {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ patternCell A₀ a floA) (hSAsat : SaturatedAt SA a depA)
    (hSB : SB ⊆ patternCell B₀ b floB) (hSBsat : SaturatedAt SB b depB)
    (hM2 : ∀ s t, s < a → t < b → N ≤ depA s + depB t)
    {A B : (ZMod (p ^ N))[X]} (hA : A ∈ SA) (hB : B ∈ SB)
    (hup : GradedUpgradeAt A B a b depA depB qb)
    {αβ : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X]} (hk : αβ ∈ polyKer A B a b) :
    A + αβ.1 ∈ SA ∧ B + αβ.2 ∈ SB ∧ (A + αβ.1) * (B + αβ.2) = A * B := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow (by omega : N ≠ 0) hp.out.one_lt⟩
  obtain ⟨hαtop, hβtop, hcombo⟩ := hk
  obtain ⟨hdA, hdB⟩ := hup αβ.1 αβ.2 0 hαtop hβtop hcombo
    (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
  have hquad : αβ.1 * αβ.2 = 0 := mul_eq_zero_of_slot_dvd hM2 hdA hαtop hdB hβtop
  have hAmem := hSA hA
  have hBmem := hSB hB
  obtain ⟨hA'mon, hA'deg⟩ := monic_add_of_coeff hAmem.1 hAmem.2.1 hαtop
  obtain ⟨hB'mon, hB'deg⟩ := monic_add_of_coeff hBmem.1 hBmem.2.1 hβtop
  refine ⟨?_, ?_, ?_⟩
  · refine hSAsat A hA _ hA'mon hA'deg fun i => ?_
    have he : A + αβ.1 - A = αβ.1 := by ring
    rw [he]
    exact hdA i
  · refine hSBsat B hB _ hB'mon hB'deg fun i => ?_
    have he : B + αβ.2 - B = αβ.2 := by ring
    rw [he]
    exact hdB i
  · have hexp : (A + αβ.1) * (B + αβ.2)
        = A * B + (B * αβ.1 + A * αβ.2) + αβ.1 * αβ.2 := by ring
    rw [hexp, hcombo, hquad, add_zero, add_zero]

/-- **The graded torsor bijection**: the fiber of `(A, B) ↦ A·B` through a cell point is in
bijection with the polynomial kernel at that point — the graded `fiberEquivKer`. -/
noncomputable def fiberEquivPolyKer {a b : ℕ} (hN : 0 < N) {A₀ B₀ : (ZMod (p ^ N))[X]}
    {floA floB depA depB qb : ℕ → ℕ} {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ patternCell A₀ a floA) (hSAsat : SaturatedAt SA a depA)
    (hSB : SB ⊆ patternCell B₀ b floB) (hSBsat : SaturatedAt SB b depB)
    (hM2 : ∀ s t, s < a → t < b → N ≤ depA s + depB t)
    (hqb : ∀ s t, s < a → t < b → qb (s + t) ≤ floA s + floB t)
    {A B : (ZMod (p ^ N))[X]} (hA : A ∈ SA) (hB : B ∈ SB)
    (hup : GradedUpgradeAt A B a b depA depB qb) :
    {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
        AB.1 ∈ SA ∧ AB.2 ∈ SB ∧ AB.1 * AB.2 = A * B}
      ≃ {q : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] // q ∈ polyKer A B a b} where
  toFun AB' := ⟨(AB'.1.1 - A, AB'.1.2 - B), by
    obtain ⟨⟨A', B'⟩, hA', hB', hprod⟩ := AB'
    have hαtop : ∀ i, a ≤ i → (A' - A).coeff i = 0 := fun i hi =>
      sub_coeff_eq_zero_of_ge (hSA hA').1 (hSA hA).1 (hSA hA').2.1 (hSA hA).2.1 hi
    have hβtop : ∀ i, b ≤ i → (B' - B).coeff i = 0 := fun i hi =>
      sub_coeff_eq_zero_of_ge (hSB hB').1 (hSB hB).1 (hSB hB').2.1 (hSB hB).2.1 hi
    obtain ⟨hdA, hdB⟩ := fiber_sub_dvd_graded hqb (hSA hA) (hSB hB) (hSA hA') (hSB hB')
      hup hprod
    have hquad : (A' - A) * (B' - B) = 0 :=
      mul_eq_zero_of_slot_dvd hM2 hdA hαtop hdB hβtop
    have hkey : B * (A' - A) + A * (B' - B) = -((A' - A) * (B' - B)) := by
      linear_combination hprod
    exact ⟨hαtop, hβtop, by rw [hkey, hquad, neg_zero]⟩⟩
  invFun q := ⟨(A + q.1.1, B + q.1.2), by
    have h := ker_shift_graded hN hSA hSAsat hSB hSBsat hM2 hA hB hup q.2
    exact ⟨h.1, h.2.1, h.2.2⟩⟩
  left_inv := by
    rintro ⟨⟨A', B'⟩, hmem⟩
    apply Subtype.ext
    dsimp only
    have h1 : A + (A' - A) = A' := by ring
    have h2 : B + (B' - B) = B' := by ring
    rw [h1, h2]
  right_inv := by
    rintro ⟨⟨α, β⟩, hmem⟩
    apply Subtype.ext
    dsimp only
    have h1 : A + α - A = α := by ring
    have h2 : B + β - B = β := by ring
    rw [h1, h2]

/-- **Graded fiber count**: under the pointwise margin and the per-point kernel count
`p^c`, every fiber over the image has exactly `p^c` points. -/
theorem pair_fiber_card_graded {a b c : ℕ} (hN : 0 < N) {A₀ B₀ : (ZMod (p ^ N))[X]}
    {floA floB depA depB qb : ℕ → ℕ} {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ patternCell A₀ a floA) (hSAsat : SaturatedAt SA a depA)
    (hSB : SB ⊆ patternCell B₀ b floB) (hSBsat : SaturatedAt SB b depB)
    (hM2 : ∀ s t, s < a → t < b → N ≤ depA s + depB t)
    (hqb : ∀ s t, s < a → t < b → qb (s + t) ≤ floA s + floB t)
    (hup : ∀ A ∈ SA, ∀ B ∈ SB, GradedUpgradeAt A B a b depA depB qb)
    (hkc : ∀ A ∈ SA, ∀ B ∈ SB,
      Nat.card {q : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] // q ∈ polyKer A B a b} = p ^ c)
    {g : (ZMod (p ^ N))[X]}
    (hg : g ∈ (fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
      (SA ×ˢ SB)) :
    Nat.card {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
        AB.1 ∈ SA ∧ AB.2 ∈ SB ∧ AB.1 * AB.2 = g} = p ^ c := by
  obtain ⟨⟨A, B⟩, hABmem, hgeq⟩ := hg
  rw [Set.mem_prod] at hABmem
  obtain ⟨hA, hB⟩ := hABmem
  have hgAB : A * B = g := hgeq
  subst hgAB
  rw [Nat.card_congr (fiberEquivPolyKer hN hSA hSAsat hSB hSBsat hM2 hqb hA hB
    (hup A hA B hB))]
  exact hkc A hA B hB

/-- **Deliverable 3 — the graded pair law**: `card (image) · p^c = card S_A · card S_B` on
pattern sub-cells, under the pinned graded margins (M1 via `SaturatedAt`, M2, the conv floor)
and the pointwise kernel data.  This is `BlockProduct.pair_card` with the flat margins
(`2c < N`, `c+1 ≤ flo ≤ N-c` — gate-EMPTY) replaced by the graded ones (gate-verified). -/
theorem pair_card_graded {a b c : ℕ} (hN : 0 < N) {A₀ B₀ : (ZMod (p ^ N))[X]}
    {floA floB depA depB qb : ℕ → ℕ} {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ patternCell A₀ a floA) (hSAsat : SaturatedAt SA a depA)
    (hSB : SB ⊆ patternCell B₀ b floB) (hSBsat : SaturatedAt SB b depB)
    (hM2 : ∀ s t, s < a → t < b → N ≤ depA s + depB t)
    (hqb : ∀ s t, s < a → t < b → qb (s + t) ≤ floA s + floB t)
    (hup : ∀ A ∈ SA, ∀ B ∈ SB, GradedUpgradeAt A B a b depA depB qb)
    (hkc : ∀ A ∈ SA, ∀ B ∈ SB,
      Nat.card {q : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] // q ∈ polyKer A B a b} = p ^ c) :
    Nat.card ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
        (SA ×ˢ SB)) * p ^ c
      = Nat.card SA * Nat.card SB := by
  classical
  set D : Set ((ZMod (p ^ N))[X] × (ZMod (p ^ N))[X]) := SA ×ˢ SB with hD
  set f : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] → (ZMod (p ^ N))[X] :=
    fun AB => AB.1 * AB.2 with hf
  have hSAfin : SA.Finite := (patternCell_finite A₀ a floA).subset hSA
  have hSBfin : SB.Finite := (patternCell_finite B₀ b floB).subset hSB
  have hDfin : D.Finite := hSAfin.prod hSBfin
  have hIfin : (f '' D).Finite := hDfin.image f
  haveI : Fintype ↥(f '' D) := hIfin.fintype
  haveI : Finite ↥D := hDfin.to_subtype
  let F : ↥D → ↥(f '' D) := fun x => ⟨f x.1, Set.mem_image_of_mem f x.2⟩
  have hcard : ∀ gg : ↥(f '' D), Nat.card {x : ↥D // F x = gg} = p ^ c := by
    intro gg
    have e : {x : ↥D // F x = gg}
        ≃ {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
            AB.1 ∈ SA ∧ AB.2 ∈ SB ∧ AB.1 * AB.2 = gg.1} :=
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1⟩, Subtype.ext y.2.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => rfl }
    rw [Nat.card_congr e]
    exact pair_fiber_card_graded hN hSA hSAsat hSB hSBsat hM2 hqb hup hkc gg.2
  have h1 : Nat.card ↥D = Nat.card ↥(f '' D) * p ^ c := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
      Finset.sum_congr rfl fun gg _ => hcard gg, Finset.sum_const, smul_eq_mul,
      Finset.card_univ, Nat.card_eq_fintype_card]
  have h2 : Nat.card ↥D = Nat.card SA * Nat.card SB := by
    rw [hD, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  rw [← h1]
  exact h2

/-! ## 6. Deliverable 4a — the graded margins HOLD at the three real gate cells

The direct counterpart of `BlockProduct.gate_margin_{A,B,C}` (which pin the flat failures):
M1 ∧ M2 at the d2-0 parameters, with the pinned `sideFloor`/`sideDepth`.  Numeric gate:
`/workspace-vast/asving/tmp/phaseb_w4d2p/gate_stdout.txt`. -/

/-- Case A (p=2, N=5, blocks (e,μ) = (1,2), (2,2), shares S = (2,1)): the graded margins
hold — flat `gate_margin_A` was false. -/
theorem gate_margin_graded_A :
    (∀ t < 2, sideFloor 1 2 t ≤ sideDepth 1 2 5 t)
      ∧ (∀ t < 4, sideFloor 2 4 t ≤ sideDepth 2 1 5 t)
      ∧ (∀ s < 2, ∀ t < 4, 5 ≤ sideDepth 1 2 5 s + sideDepth 2 1 5 t) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Case B (p=3, N=3, blocks (2,1)×2, shares S = (1,1)): the graded margins hold — flat
`gate_margin_B` was false. -/
theorem gate_margin_graded_B :
    (∀ t < 2, sideFloor 2 2 t ≤ sideDepth 2 1 3 t)
      ∧ (∀ s < 2, ∀ t < 2, 3 ≤ sideDepth 2 1 3 s + sideDepth 2 1 3 t) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Case C (p=3, N=4, blocks (2,2), (2,1), shares S = (1,2)): the graded margins hold — flat
`gate_margin_C` was false. -/
theorem gate_margin_graded_C :
    (∀ t < 4, sideFloor 2 4 t ≤ sideDepth 2 1 4 t)
      ∧ (∀ t < 2, sideFloor 2 2 t ≤ sideDepth 2 2 4 t)
      ∧ (∀ s < 4, ∀ t < 2, 4 ≤ sideDepth 2 1 4 s + sideDepth 2 2 4 t) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 7. Deliverable 4b — case B end-to-end THROUGH the graded lemmas

The d2-0 case-B cell (p = 3, N = 3, two decided blocks `(e, μ, c̃) = (2, 1, 1)` and
`(2, 1, 2)`, same side, `S = (1, 1)`, `c = X = 2`): the pattern cosets are the x-slot boxes
at floors `bFlo = (2, 1)` around `φ₁ = X² − 3`, `φ₂ = X² − 6`; the pinned depths are
`bDep = (2, 2)`.  `caseB_upgrade` discharges the pointwise graded margin at EVERY cell point
by unit-diagonal elimination + two annihilator rounds (`b₀ − a₀ = 3·unit` is the graded
diagonal — exactly the `sparseTwist` polygon weight); `caseB_ker_card` counts the polynomial
kernel (`3² = p^c`, the gate's torsor); `caseB_law_graded` then derives the gate law
`81·3² = 27·27` THROUGH `pair_card_graded` — not by `decide` — and `caseB_matches_gateB`
cross-checks the image count against `BlockProduct.gateB_image_card`. -/

section GateB

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

private instance : Fact (1 < 3 ^ 3) := ⟨by norm_num⟩

/-! ### Scalar helpers over `ZMod 27` -/

private theorem h27 : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private theorem eq_zero_of_pow3_dvd {x : ZMod (3 ^ 3)}
    (h : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 3 ∣ x) : x = 0 := by
  obtain ⟨z, hz⟩ := h
  rw [hz, h27, zero_mul]

private theorem eq_zero_of_pow4_dvd {x : ZMod (3 ^ 3)}
    (h : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 4 ∣ x) : x = 0 := by
  obtain ⟨z, hz⟩ := h
  rw [hz, show ((3 : ℕ) : ZMod (3 ^ 3)) ^ 4
      = ((3 : ℕ) : ZMod (3 ^ 3)) ^ 3 * ((3 : ℕ) : ZMod (3 ^ 3)) from by ring,
    h27, zero_mul, zero_mul]

/-- `x·y = 0` in `ZMod 27` when `3 ∣ x` and `9 ∣ y`. -/
private theorem mul3_kill {x y : ZMod (3 ^ 3)}
    (hx : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ x) (hy : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ y) :
    x * y = 0 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  rw [hu, hv]
  calc ((3 : ℕ) : ZMod (3 ^ 3)) * u * (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 * v)
      = ((3 : ℕ) : ZMod (3 ^ 3)) ^ 3 * (u * v) := by ring
    _ = 0 := by rw [h27, zero_mul]

/-- `−1 + 3k` is a unit of `ZMod 27`. -/
private theorem isUnit_neg_one_add (k : ZMod (3 ^ 3)) :
    IsUnit (-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * k) := by
  have hnil : IsNilpotent (((3 : ℕ) : ZMod (3 ^ 3)) * k) :=
    ⟨3, by rw [mul_pow, h27, zero_mul]⟩
  exact hnil.isUnit_add_left_of_commute isUnit_one.neg (Commute.all _ _)

/-- Divisibility transfers across multiplication by a unit. -/
private theorem dvd_of_isUnit_mul {w x d : ZMod (3 ^ 3)} (hw : IsUnit w)
    (h : d ∣ w * x) : d ∣ x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(hw.unit⁻¹ : (ZMod (3 ^ 3))ˣ) * c, ?_⟩
  calc x = (hw.unit⁻¹ : (ZMod (3 ^ 3))ˣ) * ((hw.unit : ZMod (3 ^ 3)) * x) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (hw.unit⁻¹ : (ZMod (3 ^ 3))ˣ) * (w * x) := by rw [IsUnit.unit_spec]
    _ = d * ((hw.unit⁻¹ : (ZMod (3 ^ 3))ˣ) * c) := by rw [hc]; ring

/-! ### Small-degree coefficient helpers -/

private theorem coeff_lin₀ (u v : ZMod (3 ^ 3)) : (C u + C v * X).coeff 0 = u := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private theorem coeff_lin₁ (u v : ZMod (3 ^ 3)) : (C u + C v * X).coeff 1 = v := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private theorem coeff_lin_top (u v : ZMod (3 ^ 3)) {i : ℕ} (hi : 2 ≤ i) :
    (C u + C v * X).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_C_mul,
    Polynomial.coeff_X, if_neg (by omega), mul_zero, add_zero]

private theorem coeff_quad₀ (u v : ZMod (3 ^ 3)) : (X ^ 2 + (C u + C v * X)).coeff 0 = u := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_lin₀, zero_add]

private theorem coeff_quad₁ (u v : ZMod (3 ^ 3)) : (X ^ 2 + (C u + C v * X)).coeff 1 = v := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_lin₁, zero_add]

private theorem coeff_quad₂ (u v : ZMod (3 ^ 3)) : (X ^ 2 + (C u + C v * X)).coeff 2 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl, coeff_lin_top _ _ le_rfl, add_zero]

private theorem coeff_quad_top (u v : ZMod (3 ^ 3)) {i : ℕ} (hi : 3 ≤ i) :
    (X ^ 2 + (C u + C v * X)).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
    coeff_lin_top _ _ (by omega), add_zero]

/-- Linear reconstruction from vanishing top coefficients. -/
private theorem eq_lin {α : (ZMod (3 ^ 3))[X]} (htop : ∀ i, 2 ≤ i → α.coeff i = 0) :
    α = C (α.coeff 0) + C (α.coeff 1) * X := by
  ext i
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · rw [coeff_lin₀]
    · rw [coeff_lin₁]
  · rw [htop i hi, coeff_lin_top _ _ hi]

/-- Monic-quadratic reconstruction. -/
private theorem eq_quad {A : (ZMod (3 ^ 3))[X]} (h2 : A.coeff 2 = 1)
    (h3 : ∀ i, 3 ≤ i → A.coeff i = 0) :
    A = X ^ 2 + (C (A.coeff 0) + C (A.coeff 1) * X) := by
  ext i
  rcases Nat.lt_or_ge i 3 with hi | hi
  · interval_cases i
    · rw [coeff_quad₀]
    · rw [coeff_quad₁]
    · rw [coeff_quad₂, h2]
  · rw [h3 i hi, coeff_quad_top _ _ hi]

/-- **The quadratic-pair combination identity**: for monic quadratics `A, B` and linear
increments `α, β`, the linearization `B·α + A·β` in cubic normal form. -/
private theorem combo_eq {A B α β : (ZMod (3 ^ 3))[X]}
    (hA2 : A.coeff 2 = 1) (hA3 : ∀ i, 3 ≤ i → A.coeff i = 0)
    (hB2 : B.coeff 2 = 1) (hB3 : ∀ i, 3 ≤ i → B.coeff i = 0)
    (hαtop : ∀ i, 2 ≤ i → α.coeff i = 0) (hβtop : ∀ i, 2 ≤ i → β.coeff i = 0) :
    B * α + A * β
      = C (B.coeff 0 * α.coeff 0 + A.coeff 0 * β.coeff 0)
        + C (B.coeff 1 * α.coeff 0 + B.coeff 0 * α.coeff 1
            + A.coeff 1 * β.coeff 0 + A.coeff 0 * β.coeff 1) * X
        + C (α.coeff 0 + B.coeff 1 * α.coeff 1 + β.coeff 0 + A.coeff 1 * β.coeff 1) * X ^ 2
        + C (α.coeff 1 + β.coeff 1) * X ^ 3 := by
  conv_lhs => rw [eq_quad hA2 hA3, eq_quad hB2 hB3, eq_lin hαtop, eq_lin hβtop]
  simp only [map_add, map_mul]
  ring

private theorem coeff_cub₀ (c0 c1 c2 c3 : ZMod (3 ^ 3)) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 0 = c0 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₁ (c0 c1 c2 c3 : ZMod (3 ^ 3)) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 1 = c1 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₂ (c0 c1 c2 c3 : ZMod (3 ^ 3)) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 2 = c2 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₃ (c0 c1 c2 c3 : ZMod (3 ^ 3)) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 3 = c3 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub_top (c0 c1 c2 c3 : ZMod (3 ^ 3)) {i : ℕ} (hi : 4 ≤ i) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  ring

/-! ### The case-B cell data -/

/-- Case-B first center `φ₁ = X² − 3` over `ZMod 27` (quadratic normal form). -/
noncomputable def bA₀ : (ZMod (3 ^ 3))[X] := X ^ 2 + (C (-3) + C 0 * X)

/-- Case-B second center `φ₂ = X² − 6` over `ZMod 27` (quadratic normal form). -/
noncomputable def bB₀ : (ZMod (3 ^ 3))[X] := X ^ 2 + (C (-6) + C 0 * X)

/-- The pinned case-B x-slot floors `(2, 1)`. -/
def bFlo : ℕ → ℕ := sideFloor 2 2

/-- The pinned case-B graded kernel depths `(2, 2)` (`S = 1`). -/
def bDep : ℕ → ℕ := sideDepth 2 1 3

/-- The pinned case-B conv floor `(4, 3, 2)` (padded by `N = 3` beyond the support). -/
def bQb : ℕ → ℕ := fun r => if r ≤ 2 then 4 - r else 3

/-- The case-B pattern coset of the first decided block, as an x-slot box. -/
noncomputable def bSA : Set ((ZMod (3 ^ 3))[X]) := patternCell (p := 3) (N := 3) bA₀ 2 bFlo

/-- The case-B pattern coset of the second decided block. -/
noncomputable def bSB : Set ((ZMod (3 ^ 3))[X]) := patternCell (p := 3) (N := 3) bB₀ 2 bFlo

private theorem hM1B : ∀ i, bFlo i ≤ bDep i := by
  intro i
  simp only [bFlo, bDep, sideFloor, sideDepth, cdiv]
  omega

private theorem hM2B : ∀ s t : ℕ, s < 2 → t < 2 → 3 ≤ bDep s + bDep t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

private theorem hqbB : ∀ s t : ℕ, s < 2 → t < 2 → bQb (s + t) ≤ bFlo s + bFlo t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

/-- Membership facts for a case-B coset around center `X² + C w`: top coefficients and the
floor divisibilities (shared engine for both `bSA_facts` and `bSB_facts`). -/
private theorem bS_facts {w : ZMod (3 ^ 3)} {A : (ZMod (3 ^ 3))[X]}
    (hA : A ∈ patternCell (p := 3) (N := 3) (X ^ 2 + (C w + C 0 * X)) 2 bFlo) :
    A.coeff 2 = 1 ∧ (∀ i, 3 ≤ i → A.coeff i = 0)
      ∧ (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ A.coeff 0 - w)
      ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ A.coeff 1 := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hA
  have h2 : A.coeff 2 = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
  have h3 : ∀ i, 3 ≤ i → A.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  refine ⟨h2, h3, ?_, ?_⟩
  · have h := hdvd 0
    rwa [Polynomial.coeff_sub, coeff_quad₀] at h
  · have h : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1 ∣ A.coeff 1 := by
      have h := hdvd 1
      rwa [Polynomial.coeff_sub, coeff_quad₁, sub_zero] at h
    rwa [pow_one] at h

/-- Membership facts for the first coset: top coefficients and the floor divisibilities. -/
private theorem bSA_facts {A : (ZMod (3 ^ 3))[X]} (hA : A ∈ bSA) :
    A.coeff 2 = 1 ∧ (∀ i, 3 ≤ i → A.coeff i = 0)
      ∧ (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ A.coeff 0 + 3)
      ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ A.coeff 1 := by
  obtain ⟨h2, h3, h0, h1⟩ := bS_facts (w := -3) hA
  exact ⟨h2, h3, by rwa [sub_neg_eq_add] at h0, h1⟩

/-- Membership facts for the second coset. -/
private theorem bSB_facts {B : (ZMod (3 ^ 3))[X]} (hB : B ∈ bSB) :
    B.coeff 2 = 1 ∧ (∀ i, 3 ≤ i → B.coeff i = 0)
      ∧ (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ B.coeff 0 + 6)
      ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ B.coeff 1 := by
  obtain ⟨h2, h3, h0, h1⟩ := bS_facts (w := -6) hB
  exact ⟨h2, h3, by rwa [sub_neg_eq_add] at h0, h1⟩

/-! ### The pointwise graded margin at every case-B cell point -/

/-- **Case-B pointwise graded upgrade** (the certificate bootstrap, at EVERY point of the
two pattern cosets): the graded diagonal `b₀ − a₀ = 3·unit` (the polygon weight of the
`sparseTwist` pair, stable across the cosets) plus two annihilator rounds give the per-slot
kernel depths `bDep = (2, 2)` — where the flat bound `N − c = 1` is empty.  No `decide`. -/
theorem caseB_upgrade : ∀ A ∈ bSA, ∀ B ∈ bSB,
    GradedUpgradeAt (p := 3) (N := 3) A B 2 2 bDep bDep bQb := by
  intro A hA B hB α β Y hαtop hβtop hcombo hY
  obtain ⟨hA2, hA3, hA0, hA1⟩ := bSA_facts hA
  obtain ⟨hB2, hB3, hB0, hB1⟩ := bSB_facts hB
  -- the four coefficient equations
  rw [combo_eq hA2 hA3 hB2 hB3 hαtop hβtop] at hcombo
  have e0 : B.coeff 0 * α.coeff 0 + A.coeff 0 * β.coeff 0 = Y.coeff 0 := by
    have h := congrArg (fun P : (ZMod (3 ^ 3))[X] => P.coeff 0) hcombo
    rwa [coeff_cub₀] at h
  have e1 : B.coeff 1 * α.coeff 0 + B.coeff 0 * α.coeff 1
      + A.coeff 1 * β.coeff 0 + A.coeff 0 * β.coeff 1 = Y.coeff 1 := by
    have h := congrArg (fun P : (ZMod (3 ^ 3))[X] => P.coeff 1) hcombo
    rwa [coeff_cub₁] at h
  have e2 : α.coeff 0 + B.coeff 1 * α.coeff 1 + β.coeff 0 + A.coeff 1 * β.coeff 1
      = Y.coeff 2 := by
    have h := congrArg (fun P : (ZMod (3 ^ 3))[X] => P.coeff 2) hcombo
    rwa [coeff_cub₂] at h
  have e3 : α.coeff 1 + β.coeff 1 = Y.coeff 3 := by
    have h := congrArg (fun P : (ZMod (3 ^ 3))[X] => P.coeff 3) hcombo
    rwa [coeff_cub₃] at h
  -- the conv-floor RHS facts
  have hy0 : Y.coeff 0 = 0 := eq_zero_of_pow4_dvd (by
    have h := hY 0
    rwa [show bQb 0 = 4 from rfl] at h)
  have hy1 : Y.coeff 1 = 0 := eq_zero_of_pow3_dvd (by
    have h := hY 1
    rwa [show bQb 1 = 3 from rfl] at h)
  have hy3 : Y.coeff 3 = 0 := eq_zero_of_pow3_dvd (by
    have h := hY 3
    rwa [show bQb 3 = 3 from rfl] at h)
  have hy2 : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ Y.coeff 2 := by
    have h := hY 2
    rwa [show bQb 2 = 2 from rfl] at h
  rw [hy0] at e0
  rw [hy1] at e1
  rw [hy3] at e3
  -- decompositions
  obtain ⟨s, hs⟩ := hA0
  obtain ⟨t, ht⟩ := hB0
  obtain ⟨a', ha'⟩ := hA1
  obtain ⟨b', hb'⟩ := hB1
  obtain ⟨v, hv⟩ := hy2
  -- units
  have hwu : IsUnit (-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * (t - s)) := isUnit_neg_one_add _
  have hw2u : IsUnit (-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * ((t - s) + a' * (a' - b'))) :=
    isUnit_neg_one_add _
  have hv2u : IsUnit ((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * (s - t)) := by
    have h := (isUnit_neg_one_add (t - s)).neg
    rwa [show -(-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * (t - s))
        = (1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * (s - t) from by ring] at h
  have hv3u : IsUnit ((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * ((s - t) + b' * (b' - a'))) := by
    have h := (isUnit_neg_one_add ((t - s) - b' * (b' - a'))).neg
    rwa [show -(-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * ((t - s) - b' * (b' - a')))
        = (1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * ((s - t) + b' * (b' - a')) from by ring] at h
  -- Y-kills
  have hka : A.coeff 0 * Y.coeff 2 = 0 := by
    linear_combination A.coeff 0 * hv + (9 : ZMod (3 ^ 3)) * v * hs
      + ((3 : ZMod (3 ^ 3)) * s - 1) * v * h27
  have hka1 : A.coeff 1 * Y.coeff 2 = 0 := by
    linear_combination A.coeff 1 * hv + (9 : ZMod (3 ^ 3)) * v * ha' + a' * v * h27
  have hkb : B.coeff 0 * Y.coeff 2 = 0 := by
    linear_combination B.coeff 0 * hv + (9 : ZMod (3 ^ 3)) * v * ht
      + ((3 : ZMod (3 ^ 3)) * t - 2) * v * h27
  have hkb1 : B.coeff 1 * Y.coeff 2 = 0 := by
    linear_combination B.coeff 1 * hv + (9 : ZMod (3 ^ 3)) * v * hb' + b' * v * h27
  -- the reduced (unit-diagonal) equations
  have hE0 : ((3 : ℕ) : ZMod (3 ^ 3))
      * ((-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * (t - s)) * α.coeff 0
        + ((3 : ℕ) : ZMod (3 ^ 3))
          * ((((3 : ℕ) : ZMod (3 ^ 3)) * s - 1) * (a' - b') * α.coeff 1)) = 0 := by
    linear_combination e0 - A.coeff 0 * e2 + (A.coeff 0 * A.coeff 1) * e3 - hka
      + (α.coeff 0 - 3 * (a' - b') * α.coeff 1) * hs - α.coeff 0 * ht
      - (A.coeff 0 * α.coeff 1) * ha' + (A.coeff 0 * α.coeff 1) * hb'
  have hE1 : ((3 : ℕ) : ZMod (3 ^ 3))
      * ((b' - a') * α.coeff 0
        + (-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * ((t - s) + a' * (a' - b'))) * α.coeff 1) = 0 := by
    have E1p : (B.coeff 1 - A.coeff 1) * α.coeff 0
        + ((B.coeff 0 - A.coeff 0) + A.coeff 1 * A.coeff 1 - A.coeff 1 * B.coeff 1)
          * α.coeff 1 = 0 := by
      linear_combination e1 - A.coeff 1 * e2 - (A.coeff 0 - A.coeff 1 * A.coeff 1) * e3 - hka1
    linear_combination E1p + (α.coeff 0 - α.coeff 1 * (3 * a' + A.coeff 1 - B.coeff 1)) * ha'
      + (-α.coeff 0 + 3 * a' * α.coeff 1) * hb' + α.coeff 1 * hs - α.coeff 1 * ht
  have hE2 : ((3 : ℕ) : ZMod (3 ^ 3))
      * (((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * (s - t)) * β.coeff 0
        + ((3 : ℕ) : ZMod (3 ^ 3))
          * ((((3 : ℕ) : ZMod (3 ^ 3)) * t - 2) * (b' - a') * β.coeff 1)) = 0 := by
    have E2p : (A.coeff 0 - B.coeff 0) * β.coeff 0
        + B.coeff 0 * (B.coeff 1 - A.coeff 1) * β.coeff 1 = 0 := by
      linear_combination e0 - B.coeff 0 * e2 + (B.coeff 0 * B.coeff 1) * e3 - hkb
    linear_combination E2p + B.coeff 0 * β.coeff 1 * ha' - B.coeff 0 * β.coeff 1 * hb'
      - β.coeff 0 * hs + (β.coeff 0 - 3 * (b' - a') * β.coeff 1) * ht
  have hE3 : ((3 : ℕ) : ZMod (3 ^ 3))
      * ((a' - b') * β.coeff 0
        + ((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * ((s - t) + b' * (b' - a')))
          * β.coeff 1) = 0 := by
    have E3p : (A.coeff 1 - B.coeff 1) * β.coeff 0
        + ((A.coeff 0 - B.coeff 0) + B.coeff 1 * B.coeff 1 - A.coeff 1 * B.coeff 1)
          * β.coeff 1 = 0 := by
      linear_combination e1 - B.coeff 1 * e2 - (B.coeff 0 - B.coeff 1 * B.coeff 1) * e3 - hkb1
    linear_combination E3p + (-β.coeff 0 + 3 * b' * β.coeff 1) * ha'
      + (β.coeff 0 - (3 * b' + B.coeff 1 - A.coeff 1) * β.coeff 1) * hb'
      - β.coeff 1 * hs + β.coeff 1 * ht
  -- round 1: depth 1 on all four slots
  have hE0' : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * ((-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * (t - s)) * α.coeff 0
        + ((3 : ℕ) : ZMod (3 ^ 3))
          * ((((3 : ℕ) : ZMod (3 ^ 3)) * s - 1) * (a' - b') * α.coeff 1)) = 0 := by
    rw [pow_one]; exact hE0
  obtain ⟨z01, hz01⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) hE0'
  have hα0d1 : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ α.coeff 0 := by
    refine dvd_of_isUnit_mul hwu ⟨((3 : ℕ) : ZMod (3 ^ 3)) * z01
      - (((3 : ℕ) : ZMod (3 ^ 3)) * s - 1) * (a' - b') * α.coeff 1, ?_⟩
    linear_combination hz01
  have hE1' : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * ((b' - a') * α.coeff 0
        + (-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * ((t - s) + a' * (a' - b'))) * α.coeff 1) = 0 := by
    rw [pow_one]; exact hE1
  obtain ⟨z02, hz02⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) hE1'
  obtain ⟨c01, hc01⟩ := hα0d1
  have hα1d1 : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ α.coeff 1 := by
    refine dvd_of_isUnit_mul hw2u ⟨((3 : ℕ) : ZMod (3 ^ 3)) * z02 - (b' - a') * c01, ?_⟩
    linear_combination hz02 - (b' - a') * hc01
  have hE2' : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * (((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * (s - t)) * β.coeff 0
        + ((3 : ℕ) : ZMod (3 ^ 3))
          * ((((3 : ℕ) : ZMod (3 ^ 3)) * t - 2) * (b' - a') * β.coeff 1)) = 0 := by
    rw [pow_one]; exact hE2
  obtain ⟨z03, hz03⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) hE2'
  have hβ0d1 : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ β.coeff 0 := by
    refine dvd_of_isUnit_mul hv2u ⟨((3 : ℕ) : ZMod (3 ^ 3)) * z03
      - (((3 : ℕ) : ZMod (3 ^ 3)) * t - 2) * (b' - a') * β.coeff 1, ?_⟩
    linear_combination hz03
  have hE3' : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * ((a' - b') * β.coeff 0
        + ((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * ((s - t) + b' * (b' - a')))
          * β.coeff 1) = 0 := by
    rw [pow_one]; exact hE3
  obtain ⟨z04, hz04⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) hE3'
  obtain ⟨c03, hc03⟩ := hβ0d1
  have hβ1d1 : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ β.coeff 1 := by
    refine dvd_of_isUnit_mul hv3u ⟨((3 : ℕ) : ZMod (3 ^ 3)) * z04 - (a' - b') * c03, ?_⟩
    linear_combination hz04 - (a' - b') * hc03
  -- round 2: depth 2 on all four slots
  obtain ⟨c11, hc11⟩ := hα1d1
  have h2a : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * ((-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * (t - s)) * α.coeff 0) = 0 := by
    rw [pow_one]
    linear_combination hE0
      - ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 * ((((3 : ℕ) : ZMod (3 ^ 3)) * s - 1) * (a' - b')) * hc11
      - ((((3 : ℕ) : ZMod (3 ^ 3)) * s - 1) * (a' - b')) * c11 * h27
  obtain ⟨z11, hz11⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) h2a
  have hα0 : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ α.coeff 0 :=
    dvd_of_isUnit_mul hwu ⟨z11, by linear_combination hz11⟩
  obtain ⟨c12, hc12⟩ := id hα0
  have h2b : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * ((-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * ((t - s) + a' * (a' - b'))) * α.coeff 1) = 0 := by
    rw [pow_one]
    linear_combination hE1 - ((3 : ℕ) : ZMod (3 ^ 3)) * (b' - a') * hc12
      - (b' - a') * c12 * h27
  obtain ⟨z12, hz12⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) h2b
  have hα1 : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ α.coeff 1 :=
    dvd_of_isUnit_mul hw2u ⟨z12, by linear_combination hz12⟩
  obtain ⟨c13, hc13⟩ := hβ1d1
  have h2c : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * (((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * (s - t)) * β.coeff 0) = 0 := by
    rw [pow_one]
    linear_combination hE2
      - ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 * ((((3 : ℕ) : ZMod (3 ^ 3)) * t - 2) * (b' - a')) * hc13
      - ((((3 : ℕ) : ZMod (3 ^ 3)) * t - 2) * (b' - a')) * c13 * h27
  obtain ⟨z13, hz13⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) h2c
  have hβ0 : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ β.coeff 0 :=
    dvd_of_isUnit_mul hv2u ⟨z13, by linear_combination hz13⟩
  obtain ⟨c14, hc14⟩ := id hβ0
  have h2d : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1
      * (((1 : ZMod (3 ^ 3)) + ((3 : ℕ) : ZMod (3 ^ 3)) * ((s - t) + b' * (b' - a')))
        * β.coeff 1) = 0 := by
    rw [pow_one]
    linear_combination hE3 - ((3 : ℕ) : ZMod (3 ^ 3)) * (a' - b') * hc14
      - (a' - b') * c14 * h27
  obtain ⟨z14, hz14⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 3) (N := 3)
    (by norm_num) h2d
  have hβ1 : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ β.coeff 1 :=
    dvd_of_isUnit_mul hv3u ⟨z14, by linear_combination hz14⟩
  -- conclusion, per slot
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · exact hα0
      · exact hα1
    · rw [hαtop i hi]
      exact dvd_zero _
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · exact hβ0
      · exact hβ1
    · rw [hβtop i hi]
      exact dvd_zero _

/-! ### Kernel count and coset cards -/

private theorem dvd9_iff_val (x : ZMod (3 ^ 3)) :
    ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ x ↔ x.val % 9 = 0 := by
  rw [RestartEquiv.pow_dvd_iff_dvd_val 3 3 (by norm_num) x]
  norm_num [Nat.dvd_iff_mod_eq_zero]

private theorem dvd3_iff_val (x : ZMod (3 ^ 3)) :
    ((3 : ℕ) : ZMod (3 ^ 3)) ∣ x ↔ x.val % 3 = 0 := by
  have h : (((3 : ℕ) : ZMod (3 ^ 3)) ∣ x) ↔ (((3 : ℕ) : ZMod (3 ^ 3)) ^ 1 ∣ x) := by
    rw [pow_one]
  rw [h, RestartEquiv.pow_dvd_iff_dvd_val 3 3 (by norm_num) x]
  norm_num [Nat.dvd_iff_mod_eq_zero]

set_option maxRecDepth 10000 in
private theorem caseB_box_card :
    Nat.card {z : ZMod (3 ^ 3) × ZMod (3 ^ 3) //
      ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.2} = 9 := by
  have he : ∀ z : ZMod (3 ^ 3) × ZMod (3 ^ 3),
      (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.2)
        ↔ (z.1.val % 9 = 0 ∧ z.2.val % 9 = 0) := by
    intro z
    rw [dvd9_iff_val, dvd9_iff_val]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- **Case-B kernel count** (the gate's torsor): at EVERY point of the two cosets the
polynomial kernel has exactly `3² = p^c` elements — it is the graph of an explicit linear
section over the depth-`(2, 2)` box. -/
theorem caseB_ker_card : ∀ A ∈ bSA, ∀ B ∈ bSB,
    Nat.card {q : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] //
      q ∈ polyKer (p := 3) (N := 3) A B 2 2} = 3 ^ 2 := by
  intro A hA B hB
  obtain ⟨hA2, hA3, hA0, hA1⟩ := bSA_facts hA
  obtain ⟨hB2, hB3, hB0, hB1⟩ := bSB_facts hB
  obtain ⟨s, hs⟩ := hA0
  obtain ⟨t, ht⟩ := hB0
  obtain ⟨a', ha'⟩ := hA1
  obtain ⟨b', hb'⟩ := hB1
  have hba : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ B.coeff 0 - A.coeff 0 :=
    ⟨-1 + ((3 : ℕ) : ZMod (3 ^ 3)) * (t - s), by linear_combination ht - hs⟩
  have ha0d : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ A.coeff 0 :=
    ⟨((3 : ℕ) : ZMod (3 ^ 3)) * s - 1, by linear_combination hs⟩
  have hb1a1 : ((3 : ℕ) : ZMod (3 ^ 3)) ∣ B.coeff 1 - A.coeff 1 :=
    ⟨b' - a', by linear_combination hb' - ha'⟩
  have e : {q : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] //
        q ∈ polyKer (p := 3) (N := 3) A B 2 2}
      ≃ {z : ZMod (3 ^ 3) × ZMod (3 ^ 3) //
          ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.2} :=
    { toFun := fun q => ⟨(q.1.1.coeff 0, q.1.1.coeff 1), by
        obtain ⟨hq1, hq2, hq3⟩ := q.2
        have h := caseB_upgrade A hA B hB q.1.1 q.1.2 0 hq1 hq2 hq3
          (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
        exact ⟨h.1 0, h.1 1⟩⟩
      invFun := fun z => ⟨(C z.1.1 + C z.1.2 * X,
        C (-z.1.1 + (A.coeff 1 - B.coeff 1) * z.1.2) + C (-z.1.2) * X), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨fun i hi => coeff_lin_top _ _ hi, fun i hi => coeff_lin_top _ _ hi, ?_⟩
        rw [combo_eq hA2 hA3 hB2 hB3 (fun i hi => coeff_lin_top _ _ hi)
          (fun i hi => coeff_lin_top _ _ hi)]
        have t4 : (B.coeff 0 - A.coeff 0) * z.1.1 = 0 := mul3_kill hba hz1
        have t5 : (A.coeff 0 * (A.coeff 1 - B.coeff 1)) * z.1.2 = 0 :=
          mul3_kill (Dvd.dvd.mul_right ha0d _) hz2
        have t1 : (B.coeff 1 - A.coeff 1) * z.1.1 = 0 := mul3_kill hb1a1 hz1
        have t2 : (B.coeff 0 - A.coeff 0) * z.1.2 = 0 := mul3_kill hba hz2
        have t3 : (A.coeff 1 * (A.coeff 1 - B.coeff 1)) * z.1.2 = 0 :=
          mul3_kill (Dvd.dvd.mul_right ⟨a', ha'⟩ _) hz2
        ext k
        rcases Nat.lt_or_ge k 4 with hk | hk
        · interval_cases k
          · rw [coeff_cub₀, Polynomial.coeff_zero]
            simp only [coeff_lin₀]
            linear_combination t4 + t5
          · rw [coeff_cub₁, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁]
            linear_combination t1 + t2 + t3
          · rw [coeff_cub₂, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁]
            ring
          · rw [coeff_cub₃, Polynomial.coeff_zero]
            simp only [coeff_lin₁]
            ring
        · rw [coeff_cub_top _ _ _ _ hk, Polynomial.coeff_zero]⟩
      left_inv := fun q => by
        obtain ⟨⟨α, β⟩, hq1, hq2, hq3⟩ := q
        apply Subtype.ext
        dsimp only
        rw [combo_eq hA2 hA3 hB2 hB3 hq1 hq2] at hq3
        have e3z : α.coeff 1 + β.coeff 1 = 0 := by
          have h := congrArg (fun P : (ZMod (3 ^ 3))[X] => P.coeff 3) hq3
          rwa [coeff_cub₃, Polynomial.coeff_zero] at h
        have e2z : α.coeff 0 + B.coeff 1 * α.coeff 1 + β.coeff 0
            + A.coeff 1 * β.coeff 1 = 0 := by
          have h := congrArg (fun P : (ZMod (3 ^ 3))[X] => P.coeff 2) hq3
          rwa [coeff_cub₂, Polynomial.coeff_zero] at h
        have h1 : C (α.coeff 0) + C (α.coeff 1) * X = α := (eq_lin hq1).symm
        have hb0r : -α.coeff 0 + (A.coeff 1 - B.coeff 1) * α.coeff 1 = β.coeff 0 := by
          linear_combination -e2z + A.coeff 1 * e3z
        have hb1r : -α.coeff 1 = β.coeff 1 := by linear_combination -e3z
        have h2 : C (-α.coeff 0 + (A.coeff 1 - B.coeff 1) * α.coeff 1)
            + C (-α.coeff 1) * X = β := by
          rw [hb0r, hb1r]
          exact (eq_lin hq2).symm
        rw [h1, h2]
      right_inv := fun z => by
        apply Subtype.ext
        dsimp only
        rw [coeff_lin₀, coeff_lin₁] }
  rw [Nat.card_congr e]
  exact caseB_box_card

/-- The x-slot box bijection for a case-B pattern coset around a quadratic center. -/
private noncomputable def cosetEquiv (w : ZMod (3 ^ 3)) :
    ↥(patternCell (p := 3) (N := 3) (X ^ 2 + (C w + C 0 * X)) 2 bFlo)
      ≃ {z : ZMod (3 ^ 3) × ZMod (3 ^ 3) //
          ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 - w ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ z.2} where
  toFun P := ⟨(P.1.coeff 0, P.1.coeff 1), (bS_facts P.2).2.2⟩
  invFun z := ⟨X ^ 2 + (C z.1.1 + C z.1.2 * X), by
    have hmd := monic_add_of_coeff (Polynomial.monic_X_pow 2) (Polynomial.natDegree_X_pow 2)
      (fun i hi => coeff_lin_top z.1.1 z.1.2 hi)
    refine ⟨hmd.1, hmd.2, fun i => ?_⟩
    rcases Nat.lt_or_ge i 3 with hi | hi
    · interval_cases i
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - (X ^ 2 + (C w + C 0 * X))).coeff 0
            = z.1.1 - w := by
          rw [Polynomial.coeff_sub, coeff_quad₀, coeff_quad₀]
        rw [he]
        exact z.2.1
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - (X ^ 2 + (C w + C 0 * X))).coeff 1
            = z.1.2 := by
          rw [Polynomial.coeff_sub, coeff_quad₁, coeff_quad₁, sub_zero]
        rw [he]
        have h' : ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1 ∣ z.1.2 := by
          rw [pow_one]
          exact z.2.2
        exact h'
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - (X ^ 2 + (C w + C 0 * X))).coeff 2
            = 0 := by
          rw [Polynomial.coeff_sub, coeff_quad₂, coeff_quad₂, sub_self]
        rw [he]
        exact dvd_zero _
    · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - (X ^ 2 + (C w + C 0 * X))).coeff i
          = 0 := by
        rw [Polynomial.coeff_sub, coeff_quad_top _ _ hi, coeff_quad_top _ _ hi, sub_self]
      rw [he]
      exact dvd_zero _⟩
  left_inv P := by
    apply Subtype.ext
    dsimp only
    obtain ⟨h2, h3, _, _⟩ := bS_facts P.2
    exact (eq_quad h2 h3).symm
  right_inv z := by
    apply Subtype.ext
    dsimp only
    rw [coeff_quad₀, coeff_quad₁]

set_option maxRecDepth 10000 in
private theorem caseB_SA_box_card :
    Nat.card {z : ZMod (3 ^ 3) × ZMod (3 ^ 3) //
      ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 - (-3) ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ z.2} = 27 := by
  have he : ∀ z : ZMod (3 ^ 3) × ZMod (3 ^ 3),
      (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 - (-3) ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ z.2)
        ↔ ((z.1 + 3).val % 9 = 0 ∧ z.2.val % 3 = 0) := by
    intro z
    rw [show z.1 - (-3 : ZMod (3 ^ 3)) = z.1 + 3 from by ring, dvd9_iff_val, dvd3_iff_val]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

set_option maxRecDepth 10000 in
private theorem caseB_SB_box_card :
    Nat.card {z : ZMod (3 ^ 3) × ZMod (3 ^ 3) //
      ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 - (-6) ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ z.2} = 27 := by
  have he : ∀ z : ZMod (3 ^ 3) × ZMod (3 ^ 3),
      (((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ z.1 - (-6) ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ∣ z.2)
        ↔ ((z.1 + 6).val % 9 = 0 ∧ z.2.val % 3 = 0) := by
    intro z
    rw [show z.1 - (-6 : ZMod (3 ^ 3)) = z.1 + 6 from by ring, dvd9_iff_val, dvd3_iff_val]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- Coset card `|P₁| = 27` — agrees with `card_freshPattern` at `(3,3,2,1)`. -/
theorem caseB_card_SA : Nat.card bSA = 27 :=
  (Nat.card_congr (cosetEquiv (-3))).trans caseB_SA_box_card

/-- Coset card `|P₂| = 27`. -/
theorem caseB_card_SB : Nat.card bSB = 27 :=
  (Nat.card_congr (cosetEquiv (-6))).trans caseB_SB_box_card

/-! ### The end-to-end law -/

/-- **Case B, THE LAW, derived THROUGH the graded pair law** (deliverable 4): at the real
gate cell — where the flat margins are provably empty (`gate_margin_B`) — the graded margins
hold and give `card(image) · 3² = |P₁| · |P₂|`.  Not by `decide`: this instantiates
`pair_card_graded` with `caseB_upgrade` + `caseB_ker_card`. -/
theorem caseB_law_graded :
    Nat.card ((fun AB : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] => AB.1 * AB.2) ''
        (bSA ×ˢ bSB)) * 3 ^ 2
      = Nat.card bSA * Nat.card bSB :=
  pair_card_graded (p := 3) (N := 3) (c := 2) (floA := bFlo) (floB := bFlo)
    (by norm_num) subset_rfl (patternCell_saturatedAt hM1B) subset_rfl
    (patternCell_saturatedAt hM1B) hM2B hqbB caseB_upgrade caseB_ker_card

/-- The image count forced by the law and the coset cards: `81` fibers. -/
theorem caseB_image_card :
    Nat.card ((fun AB : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] => AB.1 * AB.2) ''
      (bSA ×ˢ bSB)) = 81 := by
  have h := caseB_law_graded
  rw [caseB_card_SA, caseB_card_SB] at h
  omega

/-- **Cross-check against `BlockProduct.gateB_image_card`** (the direct tuple-level
enumeration of W4d2-1): the graded-lemma-derived image count equals the enumerated one. -/
theorem caseB_matches_gateB :
    Nat.card ((fun AB : (ZMod (3 ^ 3))[X] × (ZMod (3 ^ 3))[X] => AB.1 * AB.2) ''
      (bSA ×ˢ bSB)) = ((gateB_P₁ ×ˢ gateB_P₂).image gateB_mul).card := by
  rw [caseB_image_card, BlockProduct.gateB_image_card]

end GateB

/-! ## 8. Deliverable 5 — the k-block graded fold

The graded replacement of `BlockProduct.GoodChain`/`blocks_card`: the per-step data are the
graded margins (per-slot floors/depths, M2, the conv floor, the pointwise upgrade and the
kernel count) instead of the flat `2c < N` / `c+1 ≤ flo ≤ N-c` package (gate-empty).
Reuses `BlockProduct.Block`, `imageSet`, `prodCenter`, `sumDeg`. -/

section Fold

variable {p : ℕ} [hp : Fact p.Prime] {N : ℕ}

/-- **The graded chain invariant**: at each step the next block's coset and the accumulated
image are pattern sub-cells, per-slot saturated at their depths, with the pinned graded
margins M2/conv and the pointwise kernel data at the accumulated pair.  Saturation and
containment of the image are constructor fields (dischargeable case-by-case; the flat
uniform-margin suppliers are gate-empty, which is exactly why they are data here). -/
inductive GradedChain : List (Block p N) → ℕ → Prop
  | nil : GradedChain [] 0
  | cons {l : List (Block p N)} {X : ℕ} (b : Block p N) (c : ℕ)
      (floA floB depA depB qb : ℕ → ℕ) (A₀ B₀ : (ZMod (p ^ N))[X]) (hN : 0 < N)
      (hbsub : b.coset ⊆ patternCell A₀ b.deg floA)
      (hbsat : SaturatedAt b.coset b.deg depA)
      (hlsub : imageSet l ⊆ patternCell B₀ (sumDeg l) floB)
      (hlsat : SaturatedAt (imageSet l) (sumDeg l) depB)
      (hM2 : ∀ s t, s < b.deg → t < sumDeg l → N ≤ depA s + depB t)
      (hqb : ∀ s t, s < b.deg → t < sumDeg l → qb (s + t) ≤ floA s + floB t)
      (hup : ∀ A ∈ b.coset, ∀ B ∈ imageSet l,
        GradedUpgradeAt A B b.deg (sumDeg l) depA depB qb)
      (hkc : ∀ A ∈ b.coset, ∀ B ∈ imageSet l,
        Nat.card {q : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
          q ∈ polyKer A B b.deg (sumDeg l)} = p ^ c)
      (hchain : GradedChain l X) : GradedChain (b :: l) (c + X)

/-- **The k-block graded product law**: `card (imageSet l) · p^X = Π_i card (coset i)`,
`X = Σ (chain kernel valuations)` — `pair_card_graded` folded along the chain (the graded
`BlockProduct.blocks_card`). -/
theorem blocks_card_graded {l : List (Block p N)} {X : ℕ} (h : GradedChain l X) :
    Nat.card (imageSet l) * p ^ X = (l.map fun b => Nat.card b.coset).prod := by
  induction h with
  | nil =>
    show Nat.card ({1} : Set ((ZMod (p ^ N))[X])) * p ^ 0 = _
    rw [Nat.card_unique, pow_zero, one_mul, List.map_nil, List.prod_nil]
  | @cons l' X' b c floA floB depA depB qb A₀ B₀ hN hbsub hbsat hlsub hlsat hM2 hqb hup hkc hchain ih =>
    have hpair := pair_card_graded hN hbsub hbsat hlsub hlsat hM2 hqb hup hkc
    calc Nat.card (imageSet (b :: l')) * p ^ (c + X')
        = (Nat.card ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
            (b.coset ×ˢ imageSet l')) * p ^ c) * p ^ X' := by
          rw [imageSet_cons, pow_add, mul_assoc]
      _ = (Nat.card b.coset * Nat.card (imageSet l')) * p ^ X' := by rw [hpair]
      _ = Nat.card b.coset * (Nat.card (imageSet l') * p ^ X') := by ring
      _ = Nat.card b.coset * (l'.map fun b => Nat.card b.coset).prod := by rw [ih]
      _ = ((b :: l').map fun b => Nat.card b.coset).prod := by
          rw [List.map_cons, List.prod_cons]

end Fold

end LeanUrat.OM.GradedHensel
