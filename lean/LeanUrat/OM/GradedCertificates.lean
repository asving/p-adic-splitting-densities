/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.GradedHensel
import LeanUrat.OM.HNode1

/-!
# GradedCertificates — W4d2′ pointwise certificates at gate cells A and C

**Provenance.** The two named W4d2′ TODOs of `GradedHensel`/`HNode1` (`HNode1.h_node1_general`
docstring ledger): the pointwise `GradedUpgradeAt` certificates + kernel-count certificates at
the d2-0 gate cells A and C (case B's are DONE in `GradedHensel`, sections 7).  Numeric ground
truth: `/workspace-vast/asving/tmp/phaseb_w4d2_0/` (case pins) and
`/workspace-vast/asving/tmp/phaseb_w4d2p/` (graded margins); every identity below was verified
in exact arithmetic first (`/workspace-vast/asving/tmp/phaseb_certs/` — 70 symbolic/numeric
checks, kernels enumerated at 84 (A) resp. 74 (C) cell points, 25600 + 77760 deep-`Y` upgrade
solutions).

**Case A** (`p = 2, N = 5`, blocks `(e,μ,c̃) = (1,2,1)` × `(2,2,1)`, `c = X = 4`): the A-side
coset is the quadratic box around `(X−2)²` at floors `(3,2)`, the B-side the quartic box around
`(X²−2)²` at floors `(3,2,2,1)`; depths `(3,2)` / `(4,4,3,3)`.  `caseA_upgrade` discharges the
pointwise graded margin at EVERY pair of cell points by a **Schur-style reduction**: the e=1
block's rows (the two top coefficient equations, unit diagonal from monicity) eliminate `α`
first — as explicit row operations, i.e. the `linear_combination` cofactors
`e_i − b_i·e₄ + (b_i b₃ − b_{i−1})·e₅` — leaving a reduced 4×4 `β`-system that is fed to the
engine `GradedHensel.graded_mulVec_upgrade` at **scale `w = 2`** (the e=2 block's half-integer
θ-depths `D = (8,7,6,5)`, `⌈D/2⌉ = (4,4,3,3)`), pivot rows `r = (2,3,0,1)`, diagonal
valuations `v = (0,0,2,2)` (units `1`, `1`, `−b₀/4`, `(b₁(b₃−a₁)−b₀)/4`); `α` inherits by
back-substitution.  `caseA_ker_card` counts the polynomial kernel as the graph of an explicit
linear section over the depth box `{(z₂, z₃) : 2³ ∣ z}` — `2⁴ = p^c` points.

**Case C** (`p = 3, N = 4`, blocks `(2,2,1)` child × `(2,1,2)` decided, `c = X = 4`): quartic
box around `(X²−3)²` at floors `(3,2,2,1)` (depths `(3,3,2,2)`) × quadratic box around `X²−6`
at floors `(2,1)` (depths `(2,2)`).  Same shape at scale `w = 2`: the child block's four rows
eliminate `α` (cofactors `e₀ − b₀e₂ + b₀b₁e₃ + (b₀²−b₀b₁²)e₄ + (b₀b₁³−2b₀²b₁)e₅` etc.),
leaving a reduced 2×2 `β`-system, `D = (4,3)`, `v = (2,2)` (both pivots `9·(1+3·E)` with
explicit unit cofactors `E`), `off = (3,2)`.  Kernel = section graph over `{(z₀,z₁) : 3² ∣ z}`,
`3⁴ = p^c` points.

**Deliverables.**
1. `caseA_upgrade` / `caseC_upgrade` — the pointwise `GradedUpgradeAt` certificates;
2. `caseA_ker_card` / `caseC_ker_card` — `|ker| = p^c` (`2⁴` resp. `3⁴`) via explicit sections;
3. `caseA_law_graded` / `caseC_law_graded` — the end-to-end laws THROUGH
   `GradedHensel.pair_card_graded`, with the coset cards (`32·4096`, `6561·243`) and the fiber
   cards `8192` resp. `19683` forced through the graded ladder
   (`caseA_image_card`/`caseC_image_card`), cross-checked against the banked closed forms
   `BlockProduct.gateA_coset_product` / `gateC_coset_product`
   (`caseA_matches_gateA`/`caseC_matches_gateC`);
4. `caseA_chain` / `caseC_chain` + `h_node1_at_A` / `h_node1_at_C` — `GradedHensel.GradedChain`
   certificates for the two-block lists and the discharge of `HNode1.h_node1_general` at both
   cells (`#(node fiber) · p⁴ = 2¹⁷` resp. `3¹³`, via `blocks_card_graded`).

Discipline: no `sorry`/`axiom`/`native_decide`; `decide` only for small box cards and ℕ-table
facts, never for the laws; core-only footprints; no existing module touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.GradedCertificates

open Polynomial Matrix
open LeanUrat.OM
open LeanUrat.OM.HenselCount
open LeanUrat.OM.BlockProduct
open LeanUrat.OM.GradedHensel

/-! ## 0. Small-degree coefficient helpers (generic) -/

section PolyHelpers

variable {R : Type*} [CommRing R]

private theorem coeff_lin₀ (u v : R) : (C u + C v * X).coeff 0 = u := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_pos rfl, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, if_neg (by omega), mul_zero, add_zero]

private theorem coeff_lin₁ (u v : R) : (C u + C v * X).coeff 1 = v := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_C_mul,
    Polynomial.coeff_X, if_pos rfl, mul_one, zero_add]

private theorem coeff_lin_top (u v : R) {i : ℕ} (hi : 2 ≤ i) :
    (C u + C v * X).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_C_mul,
    Polynomial.coeff_X, if_neg (by omega), mul_zero, add_zero]

private theorem coeff_cub₀ (w0 w1 w2 w3 : R) :
    (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3).coeff 0 = w0 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₁ (w0 w1 w2 w3 : R) :
    (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3).coeff 1 = w1 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₂ (w0 w1 w2 w3 : R) :
    (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3).coeff 2 = w2 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₃ (w0 w1 w2 w3 : R) :
    (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3).coeff 3 = w3 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub_top (w0 w1 w2 w3 : R) {i : ℕ} (hi : 4 ≤ i) :
    (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  ring

private theorem coeff_quad₀ (u v : R) : (X ^ 2 + (C u + C v * X)).coeff 0 = u := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_lin₀, zero_add]

private theorem coeff_quad₁ (u v : R) : (X ^ 2 + (C u + C v * X)).coeff 1 = v := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_lin₁, zero_add]

private theorem coeff_quad₂ (u v : R) : (X ^ 2 + (C u + C v * X)).coeff 2 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
    coeff_lin_top _ _ (le_refl 2), add_zero]

private theorem coeff_quad_top (u v : R) {i : ℕ} (hi : 3 ≤ i) :
    (X ^ 2 + (C u + C v * X)).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
    coeff_lin_top _ _ (by omega), add_zero]

private theorem coeff_quart₀ (w0 w1 w2 w3 : R) :
    (X ^ 4 + (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3)).coeff 0 = w0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₀, zero_add]

private theorem coeff_quart₁ (w0 w1 w2 w3 : R) :
    (X ^ 4 + (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3)).coeff 1 = w1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₁, zero_add]

private theorem coeff_quart₂ (w0 w1 w2 w3 : R) :
    (X ^ 4 + (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3)).coeff 2 = w2 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₂, zero_add]

private theorem coeff_quart₃ (w0 w1 w2 w3 : R) :
    (X ^ 4 + (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3)).coeff 3 = w3 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₃, zero_add]

private theorem coeff_quart₄ (w0 w1 w2 w3 : R) :
    (X ^ 4 + (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3)).coeff 4 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
    coeff_cub_top _ _ _ _ (le_refl 4), add_zero]

private theorem coeff_quart_top (w0 w1 w2 w3 : R) {i : ℕ} (hi : 5 ≤ i) :
    (X ^ 4 + (C w0 + C w1 * X + C w2 * X ^ 2 + C w3 * X ^ 3)).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
    coeff_cub_top _ _ _ _ (by omega), add_zero]

private theorem coeff_quint₀ (d0 d1 d2 d3 d4 d5 : R) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff 0
      = d0 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₁ (d0 d1 d2 d3 d4 d5 : R) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff 1
      = d1 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₂ (d0 d1 d2 d3 d4 d5 : R) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff 2
      = d2 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₃ (d0 d1 d2 d3 d4 d5 : R) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff 3
      = d3 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₄ (d0 d1 d2 d3 d4 d5 : R) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff 4
      = d4 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₅ (d0 d1 d2 d3 d4 d5 : R) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff 5
      = d5 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint_top (d0 d1 d2 d3 d4 d5 : R) {i : ℕ} (hi : 6 ≤ i) :
    (C d0 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5).coeff i
      = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add]
  rw [Polynomial.coeff_C, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  ring

/-- Linear reconstruction from vanishing top coefficients. -/
private theorem eq_lin {α : R[X]} (htop : ∀ i, 2 ≤ i → α.coeff i = 0) :
    α = C (α.coeff 0) + C (α.coeff 1) * X := by
  ext i
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · rw [coeff_lin₀]
    · rw [coeff_lin₁]
  · rw [htop i hi, coeff_lin_top _ _ hi]

/-- Cubic reconstruction from vanishing top coefficients. -/
private theorem eq_cub {α : R[X]} (htop : ∀ i, 4 ≤ i → α.coeff i = 0) :
    α = C (α.coeff 0) + C (α.coeff 1) * X + C (α.coeff 2) * X ^ 2 + C (α.coeff 3) * X ^ 3 := by
  ext i
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · rw [coeff_cub₀]
    · rw [coeff_cub₁]
    · rw [coeff_cub₂]
    · rw [coeff_cub₃]
  · rw [htop i hi, coeff_cub_top _ _ _ _ hi]

/-- Monic-quadratic reconstruction. -/
private theorem eq_quad {A : R[X]} (h2 : A.coeff 2 = 1) (h3 : ∀ i, 3 ≤ i → A.coeff i = 0) :
    A = X ^ 2 + (C (A.coeff 0) + C (A.coeff 1) * X) := by
  ext i
  rcases Nat.lt_or_ge i 3 with hi | hi
  · interval_cases i
    · rw [coeff_quad₀]
    · rw [coeff_quad₁]
    · rw [coeff_quad₂, h2]
  · rw [h3 i hi, coeff_quad_top _ _ hi]

/-- Monic-quartic reconstruction. -/
private theorem eq_quart {A : R[X]} (h4 : A.coeff 4 = 1) (h5 : ∀ i, 5 ≤ i → A.coeff i = 0) :
    A = X ^ 4 + (C (A.coeff 0) + C (A.coeff 1) * X + C (A.coeff 2) * X ^ 2
        + C (A.coeff 3) * X ^ 3) := by
  ext i
  rcases Nat.lt_or_ge i 5 with hi | hi
  · interval_cases i
    · rw [coeff_quart₀]
    · rw [coeff_quart₁]
    · rw [coeff_quart₂]
    · rw [coeff_quart₃]
    · rw [coeff_quart₄, h4]
  · rw [h5 i hi, coeff_quart_top _ _ _ _ hi]

/-- **The quartic×linear + quadratic×cubic combination identity** in quintic normal form —
the case-A/C linearization `B·α + A·β` (`Q` the monic quartic, `P` the monic quadratic,
`u` the linear increment, `w` the cubic increment). -/
private theorem combo_quart_quad {Q P u w : R[X]}
    (hQ4 : Q.coeff 4 = 1) (hQtop : ∀ i, 5 ≤ i → Q.coeff i = 0)
    (hP2 : P.coeff 2 = 1) (hPtop : ∀ i, 3 ≤ i → P.coeff i = 0)
    (hu : ∀ i, 2 ≤ i → u.coeff i = 0) (hw : ∀ i, 4 ≤ i → w.coeff i = 0) :
    Q * u + P * w
      = C (Q.coeff 0 * u.coeff 0 + P.coeff 0 * w.coeff 0)
        + C (Q.coeff 1 * u.coeff 0 + Q.coeff 0 * u.coeff 1
            + P.coeff 1 * w.coeff 0 + P.coeff 0 * w.coeff 1) * X
        + C (Q.coeff 2 * u.coeff 0 + Q.coeff 1 * u.coeff 1
            + w.coeff 0 + P.coeff 1 * w.coeff 1 + P.coeff 0 * w.coeff 2) * X ^ 2
        + C (Q.coeff 3 * u.coeff 0 + Q.coeff 2 * u.coeff 1
            + w.coeff 1 + P.coeff 1 * w.coeff 2 + P.coeff 0 * w.coeff 3) * X ^ 3
        + C (u.coeff 0 + Q.coeff 3 * u.coeff 1 + w.coeff 2 + P.coeff 1 * w.coeff 3) * X ^ 4
        + C (u.coeff 1 + w.coeff 3) * X ^ 5 := by
  conv_lhs => rw [eq_quart hQ4 hQtop, eq_quad hP2 hPtop, eq_lin hu, eq_cub hw]
  simp only [map_add, map_mul]
  ring

/-- The summand-swapped form (case C reads `B·α + A·β` with `B` the quadratic). -/
private theorem combo_quad_quart {Q P u w : R[X]}
    (hQ4 : Q.coeff 4 = 1) (hQtop : ∀ i, 5 ≤ i → Q.coeff i = 0)
    (hP2 : P.coeff 2 = 1) (hPtop : ∀ i, 3 ≤ i → P.coeff i = 0)
    (hu : ∀ i, 2 ≤ i → u.coeff i = 0) (hw : ∀ i, 4 ≤ i → w.coeff i = 0) :
    P * w + Q * u
      = C (Q.coeff 0 * u.coeff 0 + P.coeff 0 * w.coeff 0)
        + C (Q.coeff 1 * u.coeff 0 + Q.coeff 0 * u.coeff 1
            + P.coeff 1 * w.coeff 0 + P.coeff 0 * w.coeff 1) * X
        + C (Q.coeff 2 * u.coeff 0 + Q.coeff 1 * u.coeff 1
            + w.coeff 0 + P.coeff 1 * w.coeff 1 + P.coeff 0 * w.coeff 2) * X ^ 2
        + C (Q.coeff 3 * u.coeff 0 + Q.coeff 2 * u.coeff 1
            + w.coeff 1 + P.coeff 1 * w.coeff 2 + P.coeff 0 * w.coeff 3) * X ^ 3
        + C (u.coeff 0 + Q.coeff 3 * u.coeff 1 + w.coeff 2 + P.coeff 1 * w.coeff 3) * X ^ 4
        + C (u.coeff 1 + w.coeff 3) * X ^ 5 := by
  rw [add_comm]
  exact combo_quart_quad hQ4 hQtop hP2 hPtop hu hw

end PolyHelpers

/-! ## 1. Scalar helpers over `ZMod (p^N)` (generic) -/

section ScalarHelpers

private theorem pow_cast_eq_zero {p N k : ℕ} (hk : N ≤ k) :
    ((p : ℕ) : ZMod (p ^ N)) ^ k = 0 := by
  have hN : ((p : ℕ) : ZMod (p ^ N)) ^ N = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  calc ((p : ℕ) : ZMod (p ^ N)) ^ k
      = ((p : ℕ) : ZMod (p ^ N)) ^ N * ((p : ℕ) : ZMod (p ^ N)) ^ (k - N) := by
        rw [← pow_add]; congr 1; omega
    _ = 0 := by rw [hN, zero_mul]

private theorem eq_zero_of_deep_dvd {p N k : ℕ} (hk : N ≤ k) {x : ZMod (p ^ N)}
    (h : ((p : ℕ) : ZMod (p ^ N)) ^ k ∣ x) : x = 0 := by
  obtain ⟨z, hz⟩ := h
  rw [hz, pow_cast_eq_zero hk, zero_mul]

/-- `x·y = 0` in `ZMod (p^N)` when the certified valuations reach `N`. -/
private theorem mul_kill {p N i j : ℕ} (hij : N ≤ i + j) {x y : ZMod (p ^ N)}
    (hx : ((p : ℕ) : ZMod (p ^ N)) ^ i ∣ x) (hy : ((p : ℕ) : ZMod (p ^ N)) ^ j ∣ y) :
    x * y = 0 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  rw [hu, hv]
  calc ((p : ℕ) : ZMod (p ^ N)) ^ i * u * (((p : ℕ) : ZMod (p ^ N)) ^ j * v)
      = ((p : ℕ) : ZMod (p ^ N)) ^ (i + j) * (u * v) := by rw [pow_add]; ring
    _ = 0 := by rw [pow_cast_eq_zero hij, zero_mul]

/-- Valuations add across products. -/
private theorem pow_mul_dvd {p N i j : ℕ} {x y : ZMod (p ^ N)}
    (hx : ((p : ℕ) : ZMod (p ^ N)) ^ i ∣ x) (hy : ((p : ℕ) : ZMod (p ^ N)) ^ j ∣ y) :
    ((p : ℕ) : ZMod (p ^ N)) ^ (i + j) ∣ x * y := by
  rw [pow_add]
  exact mul_dvd_mul hx hy

/-- `1 + p·k` is a unit of `ZMod (p^N)`. -/
private theorem isUnit_one_add_pmul {p N : ℕ} (k : ZMod (p ^ N)) :
    IsUnit (1 + ((p : ℕ) : ZMod (p ^ N)) * k) := by
  have hnil : IsNilpotent (((p : ℕ) : ZMod (p ^ N)) * k) :=
    ⟨N, by rw [mul_pow, pow_cast_eq_zero le_rfl, zero_mul]⟩
  exact hnil.isUnit_add_left_of_commute isUnit_one (Commute.all _ _)

/-- `−1 + p·k` is a unit of `ZMod (p^N)`. -/
private theorem isUnit_neg_one_add_pmul {p N : ℕ} (k : ZMod (p ^ N)) :
    IsUnit (-1 + ((p : ℕ) : ZMod (p ^ N)) * k) := by
  have hnil : IsNilpotent (((p : ℕ) : ZMod (p ^ N)) * k) :=
    ⟨N, by rw [mul_pow, pow_cast_eq_zero le_rfl, zero_mul]⟩
  exact hnil.isUnit_add_left_of_commute isUnit_one.neg (Commute.all _ _)

end ScalarHelpers

/-! ## 2. Singleton-block helpers (the `GradedChain` base step, generic) -/

section SingletonBlock

variable {p : ℕ} [hp : Fact p.Prime] {N : ℕ}

theorem imageSet_nil_subset_patternCell (flo : ℕ → ℕ) :
    imageSet ([] : List (Block p N)) ⊆ patternCell 1 0 flo := by
  intro P hP
  rw [imageSet_nil, Set.mem_singleton_iff] at hP
  subst hP
  exact ⟨monic_one, natDegree_one, fun i => by
    rw [sub_self, Polynomial.coeff_zero]; exact dvd_zero _⟩

theorem imageSet_nil_saturatedAt (dep : ℕ → ℕ) :
    SaturatedAt (imageSet ([] : List (Block p N))) 0 dep := by
  intro P hP Q hQmon hQdeg _
  rw [imageSet_nil, Set.mem_singleton_iff]
  exact hQmon.natDegree_eq_zero.mp hQdeg

/-- The one-block image is the block's own coset. -/
theorem imageSet_singleton (b : Block p N) : imageSet [b] = b.coset := by
  rw [imageSet_cons, imageSet_nil]
  ext P
  constructor
  · rintro ⟨⟨A, B⟩, hmem, rfl⟩
    rw [Set.mem_prod] at hmem
    obtain ⟨hA, hB⟩ := hmem
    rw [Set.mem_singleton_iff] at hB
    have hB1 : B = 1 := hB
    have hA1 : A ∈ b.coset := hA
    show A * B ∈ b.coset
    rw [hB1, mul_one]
    exact hA1
  · intro hP
    exact ⟨(P, 1), Set.mem_prod.mpr ⟨hP, Set.mem_singleton_iff.mpr rfl⟩, mul_one P⟩

/-- The pointwise graded margin against the trivial block `B = 1` (base step of the chain):
`α = Y` outright, so any depths at conv floor `qb = depA` upgrade. -/
theorem gradedUpgradeAt_one (A : (ZMod (p ^ N))[X]) (a : ℕ) (dep depB : ℕ → ℕ) :
    GradedUpgradeAt A 1 a 0 dep depB dep := by
  intro α β Y hαtop hβtop hcombo hY
  have hβ0 : β = 0 := Polynomial.ext fun i => by
    rw [hβtop i (Nat.zero_le i), Polynomial.coeff_zero]
  have hα : α = Y := by
    rw [hβ0, mul_zero, add_zero, one_mul] at hcombo
    exact hcombo
  constructor
  · intro i
    rw [hα]
    exact hY i
  · intro i
    rw [hβ0, Polynomial.coeff_zero]
    exact dvd_zero _

theorem polyKer_one (A : (ZMod (p ^ N))[X]) (a : ℕ) :
    polyKer A 1 a 0 = {((0 : (ZMod (p ^ N))[X]), (0 : (ZMod (p ^ N))[X]))} := by
  ext q
  simp only [polyKer, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hq2 : q.2 = 0 := Polynomial.ext fun i => by
      rw [h2 i (Nat.zero_le i), Polynomial.coeff_zero]
    have hq1 : q.1 = 0 := by
      rw [hq2, mul_zero, add_zero, one_mul] at h3
      exact h3
    exact Prod.ext hq1 hq2
  · rintro rfl
    exact ⟨fun i _ => Polynomial.coeff_zero i, fun i _ => Polynomial.coeff_zero i,
      by rw [mul_zero, mul_zero, add_zero]⟩

theorem polyKer_one_card (A : (ZMod (p ^ N))[X]) (a : ℕ) :
    Nat.card {q : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] // q ∈ polyKer A 1 a 0} = p ^ 0 := by
  rw [pow_zero, polyKer_one]
  exact Nat.card_unique

end SingletonBlock

/-! ## 3. Case A — `p = 2, N = 5`, blocks `(1,2,1)` × `(2,2,1)`, `c = X = 4`

The pointwise certificates at the gate-A cell.  A-side: the e=1 child, quadratic box around
`aA₀ = (X−2)²` at floors `aFloA = (3,2)`, depths `aDepA = (3,2)`.  B-side: the e=2 child,
quartic box around `aB₀ = (X²−2)²` at floors `aFloB = (3,2,2,1)`, depths `aDepB = (4,4,3,3)`.
Schur reduction: rows 4–5 (unit diagonal on `α`) eliminate first; the reduced 4×4 `β`-system
feeds `graded_mulVec_upgrade` at scale `w = 2`, `D = (8,7,6,5)`, pivots `r = (2,3,0,1)`,
`v = (0,0,2,2)`, off-diagonal table `((0,2,2,2),(5,0,1,2),(2,5,0,3),(2,2,2,0))`. -/

section GateA

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private instance : Fact (1 < 2 ^ 5) := ⟨by norm_num⟩

/-- Case-A first center `(X−2)² = X² − 4X + 4` over `ZMod 32` (quadratic normal form). -/
noncomputable def aA₀ : (ZMod (2 ^ 5))[X] := X ^ 2 + (C 4 + C (-4) * X)

/-- Case-A second center `(X²−2)² = X⁴ − 4X² + 4` over `ZMod 32` (quartic normal form). -/
noncomputable def aB₀ : (ZMod (2 ^ 5))[X] :=
  X ^ 4 + (C 4 + C 0 * X + C (-4) * X ^ 2 + C 0 * X ^ 3)

/-- The pinned case-A x-slot floors of the e=1 block: `(3, 2)`. -/
def aFloA : ℕ → ℕ := sideFloor 1 2

/-- The pinned case-A x-slot floors of the e=2 block: `(3, 2, 2, 1)`. -/
def aFloB : ℕ → ℕ := sideFloor 2 4

/-- The pinned case-A graded depths of the e=1 block: `(3, 2)` (`S = 2`). -/
def aDepA : ℕ → ℕ := sideDepth 1 2 5

/-- The pinned case-A graded depths of the e=2 block: `(4, 4, 3, 3)` (`S = 1`). -/
def aDepB : ℕ → ℕ := sideDepth 2 1 5

/-- The pinned case-A conv floor `(6, 5, 4, 4, 3)` (padded by `N = 5` beyond the support). -/
def aQb : ℕ → ℕ := fun r =>
  if r = 0 then 6 else if r = 1 then 5 else if r ≤ 3 then 4 else if r = 4 then 3 else 5

/-- The case-A pattern coset of the e=1 child block, as an x-slot box. -/
noncomputable def aSA : Set ((ZMod (2 ^ 5))[X]) := patternCell (p := 2) (N := 5) aA₀ 2 aFloA

/-- The case-A pattern coset of the e=2 child block. -/
noncomputable def aSB : Set ((ZMod (2 ^ 5))[X]) := patternCell (p := 2) (N := 5) aB₀ 4 aFloB

private theorem hM1A₁ : ∀ i, aFloA i ≤ aDepA i := by
  intro i
  simp only [aFloA, aDepA, sideFloor, sideDepth, cdiv]
  omega

private theorem hM1A₂ : ∀ i, aFloB i ≤ aDepB i := by
  intro i
  simp only [aFloB, aDepB, sideFloor, sideDepth, cdiv]
  omega

private theorem hM2A : ∀ s t : ℕ, s < 2 → t < 4 → 5 ≤ aDepA s + aDepB t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

private theorem hqbA : ∀ s t : ℕ, s < 2 → t < 4 → aQb (s + t) ≤ aFloA s + aFloB t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

/-- Membership facts for the quadratic coset: top coefficients + floor divisibilities. -/
private theorem aSA_facts {A : (ZMod (2 ^ 5))[X]} (hA : A ∈ aSA) :
    A.coeff 2 = 1 ∧ (∀ i, 3 ≤ i → A.coeff i = 0)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ A.coeff 0 - 4)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 1 + 4) := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hA
  have h2 : A.coeff 2 = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hdeg] at h
  have h3 : ∀ i, 3 ≤ i → A.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  refine ⟨h2, h3, ?_, ?_⟩
  · have h := hdvd 0
    have he : (A - aA₀).coeff 0 = A.coeff 0 - 4 := by
      have hc : aA₀.coeff 0 = 4 := coeff_quad₀ _ _
      rw [Polynomial.coeff_sub, hc]
    rwa [he] at h
  · have h := hdvd 1
    have he : (A - aA₀).coeff 1 = A.coeff 1 + 4 := by
      have hc : aA₀.coeff 1 = -4 := coeff_quad₁ _ _
      rw [Polynomial.coeff_sub, hc]
      ring
    rwa [he] at h

/-- Membership facts for the quartic coset. -/
private theorem aSB_facts {B : (ZMod (2 ^ 5))[X]} (hB : B ∈ aSB) :
    B.coeff 4 = 1 ∧ (∀ i, 5 ≤ i → B.coeff i = 0)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ B.coeff 0 - 4)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 1)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 2 + 4)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3) := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hB
  have h4 : B.coeff 4 = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hdeg] at h
  have h5 : ∀ i, 5 ≤ i → B.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  refine ⟨h4, h5, ?_, ?_, ?_, ?_⟩
  · have h := hdvd 0
    have he : (B - aB₀).coeff 0 = B.coeff 0 - 4 := by
      have hc : aB₀.coeff 0 = 4 := coeff_quart₀ _ _ _ _
      rw [Polynomial.coeff_sub, hc]
    rwa [he] at h
  · have h := hdvd 1
    have he : (B - aB₀).coeff 1 = B.coeff 1 := by
      have hc : aB₀.coeff 1 = 0 := coeff_quart₁ _ _ _ _
      rw [Polynomial.coeff_sub, hc, sub_zero]
    rwa [he] at h
  · have h := hdvd 2
    have he : (B - aB₀).coeff 2 = B.coeff 2 + 4 := by
      have hc : aB₀.coeff 2 = -4 := coeff_quart₂ _ _ _ _
      rw [Polynomial.coeff_sub, hc]
      ring
    rwa [he] at h
  · have h := hdvd 3
    have he : (B - aB₀).coeff 3 = B.coeff 3 := by
      have hc : aB₀.coeff 3 = 0 := coeff_quart₃ _ _ _ _
      rw [Polynomial.coeff_sub, hc, sub_zero]
    rwa [he] at h

/-- **Case-A pointwise graded upgrade** (W4d2′ TODO 1 at cell A): at EVERY pair of cell
points the Schur-reduced 4×4 `β`-system carries a scale-2 diagonal-dominance certificate for
`graded_mulVec_upgrade` (`D = (8,7,6,5)`, `v = (0,0,2,2)`, pivots `(2,3,0,1)`), and `α`
inherits by back-substitution through the unit rows — per-slot depths
`aDepA = (3,2)`, `aDepB = (4,4,3,3)`.  No `decide` beyond ℕ-table facts. -/
theorem caseA_upgrade : ∀ A ∈ aSA, ∀ B ∈ aSB,
    GradedUpgradeAt (p := 2) (N := 5) A B 2 4 aDepA aDepB aQb := by
  intro A hA B hB α β Y hαtop hβtop hcombo hY
  obtain ⟨hA2, hA3, hA0f, hA1f⟩ := aSA_facts hA
  obtain ⟨hB4, hB5, hB0f, hB1f, hB2f, hB3f⟩ := aSB_facts hB
  -- solved decompositions
  obtain ⟨s, hs⟩ := hA0f
  obtain ⟨av, hav⟩ := hA1f
  obtain ⟨t, ht⟩ := hB0f
  obtain ⟨u1, hu1⟩ := hB1f
  obtain ⟨u2, hu2⟩ := hB2f
  obtain ⟨u3, hu3⟩ := hB3f
  have hA0' : A.coeff 0 = 4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 * s := by linear_combination hs
  have hA1' : A.coeff 1 = -4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * av := by linear_combination hav
  have hB0' : B.coeff 0 = 4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 * t := by linear_combination ht
  have hB1' : B.coeff 1 = ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * u1 := hu1
  have hB2' : B.coeff 2 = -4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * u2 := by linear_combination hu2
  have hB3' : B.coeff 3 = ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 * u3 := hu3
  -- atom divisibilities
  have ha0d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 0 := ⟨1 + 2 * s, by rw [hA0']; ring⟩
  have ha1d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 1 := ⟨av - 1, by rw [hA1']; ring⟩
  have hb0d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 0 := ⟨1 + 2 * t, by rw [hB0']; ring⟩
  have hb1d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 1 := ⟨u1, hB1'⟩
  have hb2d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 2 := ⟨u2 - 1, by rw [hB2']; ring⟩
  have hb3p : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3 := ⟨u3, hB3'⟩
  have h2a1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ A.coeff 1 :=
    (pow_dvd_pow _ (by norm_num : 1 ≤ 2)).trans ha1d
  have hb3ma1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3 - A.coeff 1 := dvd_sub hb3p h2a1
  -- conv-floor facts on Y
  have hy0 : Y.coeff 0 = 0 := eq_zero_of_deep_dvd (show (5 : ℕ) ≤ 6 by norm_num) (hY 0)
  have hy1 : Y.coeff 1 = 0 := eq_zero_of_deep_dvd (show (5 : ℕ) ≤ 5 by norm_num) (hY 1)
  have hy5 : Y.coeff 5 = 0 := eq_zero_of_deep_dvd (show (5 : ℕ) ≤ 5 by norm_num) (hY 5)
  have hy2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ Y.coeff 2 := hY 2
  have hy3 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ Y.coeff 3 := hY 3
  have hy4 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ Y.coeff 4 := hY 4
  obtain ⟨y2w, hy2w⟩ := id hy2
  obtain ⟨y3w, hy3w⟩ := id hy3
  obtain ⟨y4w, hy4w⟩ := id hy4
  -- coefficient equations of the linearization
  rw [combo_quart_quad hB4 hB5 hA2 hA3 hαtop hβtop] at hcombo
  have e0 : B.coeff 0 * α.coeff 0 + A.coeff 0 * β.coeff 0 = Y.coeff 0 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 0) hcombo
    rwa [coeff_quint₀] at h
  have e1 : B.coeff 1 * α.coeff 0 + B.coeff 0 * α.coeff 1
      + A.coeff 1 * β.coeff 0 + A.coeff 0 * β.coeff 1 = Y.coeff 1 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 1) hcombo
    rwa [coeff_quint₁] at h
  have e2 : B.coeff 2 * α.coeff 0 + B.coeff 1 * α.coeff 1
      + β.coeff 0 + A.coeff 1 * β.coeff 1 + A.coeff 0 * β.coeff 2 = Y.coeff 2 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 2) hcombo
    rwa [coeff_quint₂] at h
  have e3 : B.coeff 3 * α.coeff 0 + B.coeff 2 * α.coeff 1
      + β.coeff 1 + A.coeff 1 * β.coeff 2 + A.coeff 0 * β.coeff 3 = Y.coeff 3 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 3) hcombo
    rwa [coeff_quint₃] at h
  have e4 : α.coeff 0 + B.coeff 3 * α.coeff 1 + β.coeff 2 + A.coeff 1 * β.coeff 3
      = Y.coeff 4 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 4) hcombo
    rwa [coeff_quint₄] at h
  have e5 : α.coeff 1 + β.coeff 3 = Y.coeff 5 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 5) hcombo
    rwa [coeff_quint₅] at h
  -- the engine on the Schur-reduced 4×4 β-system, scale w = 2
  have hβall : ∀ j : Fin 4, ((2 : ℕ) : ZMod (2 ^ 5)) ^ cdiv ((![8, 7, 6, 5] : Fin 4 → ℕ) j) 2
      ∣ (![β.coeff 0, β.coeff 1, β.coeff 2, β.coeff 3] : Fin 4 → ZMod (2 ^ 5)) j := by
    refine graded_mulVec_upgrade (p := 2) (N := 5)
      (Matrix.of ![![A.coeff 0, 0, -B.coeff 0, B.coeff 0 * (B.coeff 3 - A.coeff 1)],
        ![A.coeff 1, A.coeff 0, -B.coeff 1, B.coeff 1 * (B.coeff 3 - A.coeff 1) - B.coeff 0],
        ![1, A.coeff 1, A.coeff 0 - B.coeff 2, B.coeff 2 * (B.coeff 3 - A.coeff 1) - B.coeff 1],
        ![0, 1, A.coeff 1 - B.coeff 3,
          A.coeff 0 - B.coeff 2 + B.coeff 3 * (B.coeff 3 - A.coeff 1)]])
      (w := 2) (by norm_num) ![2, 3, 0, 1] ![0, 0, 2, 2] ![8, 7, 6, 5]
      ![![0, 2, 2, 2], ![5, 0, 1, 2], ![2, 5, 0, 3], ![2, 2, 2, 0]]
      (by decide) ?_ (by decide) ?_ (by decide)
      (x := ![β.coeff 0, β.coeff 1, β.coeff 2, β.coeff 3])
      (y := ![-(B.coeff 0 * Y.coeff 4), -(B.coeff 1 * Y.coeff 4),
        Y.coeff 2 - B.coeff 2 * Y.coeff 4, Y.coeff 3 - B.coeff 3 * Y.coeff 4]) ?_ ?_
    · -- hdiag: unit pivots (1, 1, −b₀/4·unit, (b₁(b₃−a₁)−b₀)/4·unit)
      intro j
      fin_cases j
      · refine ⟨1, ?_⟩
        show (1 : ZMod (2 ^ 5))
          = ((2 : ℕ) : ZMod (2 ^ 5)) ^ (0 : ℕ) * ((1 : (ZMod (2 ^ 5))ˣ) : ZMod (2 ^ 5))
        rw [pow_zero, one_mul, Units.val_one]
      · refine ⟨1, ?_⟩
        show (1 : ZMod (2 ^ 5))
          = ((2 : ℕ) : ZMod (2 ^ 5)) ^ (0 : ℕ) * ((1 : (ZMod (2 ^ 5))ˣ) : ZMod (2 ^ 5))
        rw [pow_zero, one_mul, Units.val_one]
      · refine ⟨(isUnit_neg_one_add_pmul (p := 2) (N := 5) (-t)).unit, ?_⟩
        show -B.coeff 0 = ((2 : ℕ) : ZMod (2 ^ 5)) ^ (2 : ℕ)
          * ((isUnit_neg_one_add_pmul (p := 2) (N := 5) (-t)).unit : ZMod (2 ^ 5))
        rw [IsUnit.unit_spec, hB0']
        ring
      · refine ⟨(isUnit_neg_one_add_pmul (p := 2) (N := 5)
          (u1 * (u3 + 2 - 2 * av) - t)).unit, ?_⟩
        show B.coeff 1 * (B.coeff 3 - A.coeff 1) - B.coeff 0
          = ((2 : ℕ) : ZMod (2 ^ 5)) ^ (2 : ℕ)
            * ((isUnit_neg_one_add_pmul (p := 2) (N := 5)
                (u1 * (u3 + 2 - 2 * av) - t)).unit : ZMod (2 ^ 5))
        rw [IsUnit.unit_spec, hB1', hB3', hA1', hB0']
        ring
    · -- hoffdvd: certified off-diagonal valuations (row order r = (2,3,0,1))
      intro j j' hne
      fin_cases j <;> fin_cases j'
      · exact absurd rfl hne
      · exact ha1d
      · exact dvd_sub ha0d hb2d
      · exact dvd_sub (hb2d.mul_right _) hb1d
      · exact dvd_zero _
      · exact absurd rfl hne
      · exact dvd_sub h2a1 hb3p
      · exact dvd_add (dvd_sub ha0d hb2d) (pow_mul_dvd hb3p hb3ma1)
      · exact ha0d
      · exact dvd_zero _
      · exact absurd rfl hne
      · exact pow_mul_dvd hb0d hb3ma1
      · exact ha1d
      · exact ha0d
      · exact dvd_neg.mpr hb1d
      · exact absurd rfl hne
    · -- hxy: the Schur row operations, as explicit linear_combination cofactors
      funext j
      fin_cases j <;>
        simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const, Fin.isValue]
      · show A.coeff 0 * β.coeff 0 + 0 * β.coeff 1 + -B.coeff 0 * β.coeff 2
            + B.coeff 0 * (B.coeff 3 - A.coeff 1) * β.coeff 3 = -(B.coeff 0 * Y.coeff 4)
        linear_combination e0 - B.coeff 0 * e4 + B.coeff 0 * B.coeff 3 * e5
          + hy0 + B.coeff 0 * B.coeff 3 * hy5
      · show A.coeff 1 * β.coeff 0 + A.coeff 0 * β.coeff 1 + -B.coeff 1 * β.coeff 2
            + (B.coeff 1 * (B.coeff 3 - A.coeff 1) - B.coeff 0) * β.coeff 3
          = -(B.coeff 1 * Y.coeff 4)
        linear_combination e1 - B.coeff 1 * e4 + (B.coeff 1 * B.coeff 3 - B.coeff 0) * e5
          + hy1 + (B.coeff 1 * B.coeff 3 - B.coeff 0) * hy5
      · show 1 * β.coeff 0 + A.coeff 1 * β.coeff 1 + (A.coeff 0 - B.coeff 2) * β.coeff 2
            + (B.coeff 2 * (B.coeff 3 - A.coeff 1) - B.coeff 1) * β.coeff 3
          = Y.coeff 2 - B.coeff 2 * Y.coeff 4
        linear_combination e2 - B.coeff 2 * e4 + (B.coeff 2 * B.coeff 3 - B.coeff 1) * e5
          + (B.coeff 2 * B.coeff 3 - B.coeff 1) * hy5
      · show 0 * β.coeff 0 + 1 * β.coeff 1 + (A.coeff 1 - B.coeff 3) * β.coeff 2
            + (A.coeff 0 - B.coeff 2 + B.coeff 3 * (B.coeff 3 - A.coeff 1)) * β.coeff 3
          = Y.coeff 3 - B.coeff 3 * Y.coeff 4
        linear_combination e3 - B.coeff 3 * e4 + (B.coeff 3 * B.coeff 3 - B.coeff 2) * e5
          + (B.coeff 3 * B.coeff 3 - B.coeff 2) * hy5
    · -- hy: the reduced RHS is graded-deep at the pivot rows
      intro j
      fin_cases j
      · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (4 : ℕ) ∣ Y.coeff 2 - B.coeff 2 * Y.coeff 4
        exact ⟨y2w + 2 * y4w - 2 * u2 * y4w, by rw [hy2w, hB2', hy4w]; ring⟩
      · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (4 : ℕ) ∣ Y.coeff 3 - B.coeff 3 * Y.coeff 4
        exact ⟨y3w - u3 * y4w, by rw [hy3w, hB3', hy4w]; ring⟩
      · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (5 : ℕ) ∣ -(B.coeff 0 * Y.coeff 4)
        exact ⟨-((1 + 2 * t) * y4w), by rw [hB0', hy4w]; ring⟩
      · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (5 : ℕ) ∣ -(B.coeff 1 * Y.coeff 4)
        exact ⟨-(u1 * y4w), by rw [hB1', hy4w]; ring⟩
  -- extract the β-slot depths (defeq: `cdiv (8,7,6,5) 2 = (4,4,3,3)`)
  have hβ0d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ β.coeff 0 := hβall 0
  have hβ1d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ β.coeff 1 := hβall 1
  have hβ2d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ β.coeff 2 := hβall 2
  have hβ3d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ β.coeff 3 := hβall 3
  -- α inherits by back-substitution through the unit rows
  have hα1eq : α.coeff 1 = -β.coeff 3 := by linear_combination e5 + hy5
  have hα0eq : α.coeff 0 = Y.coeff 4 + (B.coeff 3 - A.coeff 1) * β.coeff 3 - β.coeff 2 := by
    linear_combination e4 - B.coeff 3 * hα1eq
  have hα1d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ α.coeff 1 := by
    rw [hα1eq]
    exact dvd_neg.mpr ((pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans hβ3d)
  have hα0d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ α.coeff 0 := by
    rw [hα0eq]
    exact dvd_sub (dvd_add hy4 (hβ3d.mul_left _)) hβ2d
  -- per-slot conclusions
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · exact hα0d
      · exact hα1d
    · rw [hαtop i hi]
      exact dvd_zero _
  · rcases Nat.lt_or_ge i 4 with hi | hi
    · interval_cases i
      · exact hβ0d
      · exact hβ1d
      · exact hβ2d
      · exact hβ3d
    · rw [hβtop i hi]
      exact dvd_zero _

/-! ### Case-A kernel count: the graph of an explicit linear section over the depth box -/

private theorem dvd_val_A {k : ℕ} (hk : k ≤ 5) (x : ZMod (2 ^ 5)) :
    ((2 : ℕ) : ZMod (2 ^ 5)) ^ k ∣ x ↔ 2 ^ k ∣ x.val :=
  RestartEquiv.pow_dvd_iff_dvd_val 2 5 hk x

set_option maxRecDepth 40000 in
private theorem boxA_card :
    Nat.card {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.2} = 16 := by
  have he : ∀ z : ZMod (2 ^ 5) × ZMod (2 ^ 5),
      (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.2)
        ↔ (z.1.val % 8 = 0 ∧ z.2.val % 8 = 0) := by
    intro z
    rw [dvd_val_A (by norm_num) z.1, dvd_val_A (by norm_num) z.2]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- **Case-A kernel count** (W4d2′ TODO 2 at cell A): at EVERY pair of cell points the
polynomial kernel has exactly `2⁴ = p^c` elements — it is the graph of the explicit linear
section `(z₂, z₃) ↦ (α, β) = ((−z₂ + (b₃−a₁)z₃, −z₃), (0, (b₃−a₁)z₂, z₂, z₃))` over the
depth box `{(z₂, z₃) : 2³ ∣ z₂, 2³ ∣ z₃}`. -/
theorem caseA_ker_card : ∀ A ∈ aSA, ∀ B ∈ aSB,
    Nat.card {q : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] //
      q ∈ polyKer (p := 2) (N := 5) A B 2 4} = 2 ^ 4 := by
  intro A hA B hB
  obtain ⟨hA2, hA3, hA0f, hA1f⟩ := aSA_facts hA
  obtain ⟨hB4, hB5, hB0f, hB1f, hB2f, hB3f⟩ := aSB_facts hB
  obtain ⟨s, hs⟩ := hA0f
  obtain ⟨av, hav⟩ := hA1f
  obtain ⟨t, ht⟩ := hB0f
  obtain ⟨u1, hu1⟩ := hB1f
  obtain ⟨u2, hu2⟩ := hB2f
  obtain ⟨u3, hu3⟩ := hB3f
  have hA0' : A.coeff 0 = 4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 * s := by linear_combination hs
  have hA1' : A.coeff 1 = -4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * av := by linear_combination hav
  have hB0' : B.coeff 0 = 4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 * t := by linear_combination ht
  have hB2' : B.coeff 2 = -4 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * u2 := by linear_combination hu2
  have ha0d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 0 := ⟨1 + 2 * s, by rw [hA0']; ring⟩
  have ha1d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 1 := ⟨av - 1, by rw [hA1']; ring⟩
  have hb0d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 0 := ⟨1 + 2 * t, by rw [hB0']; ring⟩
  have hb1d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 1 := ⟨u1, hu1⟩
  have hb2d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 2 := ⟨u2 - 1, by rw [hB2']; ring⟩
  have hb3p : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3 := ⟨u3, hu3⟩
  have h2a1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ A.coeff 1 :=
    (pow_dvd_pow _ (by norm_num : 1 ≤ 2)).trans ha1d
  have hb3ma1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3 - A.coeff 1 := dvd_sub hb3p h2a1
  have e : {q : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] //
        q ∈ polyKer (p := 2) (N := 5) A B 2 4}
      ≃ {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
          ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.2} :=
    { toFun := fun q => ⟨(q.1.2.coeff 2, q.1.2.coeff 3), by
        obtain ⟨hq1, hq2, hq3⟩ := q.2
        have h := caseA_upgrade A hA B hB q.1.1 q.1.2 0 hq1 hq2 hq3
          (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
        exact ⟨h.2 2, h.2 3⟩⟩
      invFun := fun z => ⟨(C (-z.1.1 + (B.coeff 3 - A.coeff 1) * z.1.2) + C (-z.1.2) * X,
          C 0 + C ((B.coeff 3 - A.coeff 1) * z.1.1) * X + C z.1.1 * X ^ 2 + C z.1.2 * X ^ 3), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨fun i hi => coeff_lin_top _ _ hi, fun i hi => coeff_cub_top _ _ _ _ hi, ?_⟩
        rw [combo_quart_quad hB4 hB5 hA2 hA3 (fun i hi => coeff_lin_top _ _ hi)
          (fun i hi => coeff_cub_top _ _ _ _ hi)]
        have K0a : B.coeff 0 * z.1.1 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3) hb0d hz1
        have K0b : B.coeff 0 * (B.coeff 3 - A.coeff 1) * z.1.2 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3) (hb0d.mul_right _) hz2
        have K1a : (-B.coeff 1 + A.coeff 0 * (B.coeff 3 - A.coeff 1)) * z.1.1 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3)
            (dvd_add (dvd_neg.mpr hb1d) (ha0d.mul_right _)) hz1
        have K1b : (B.coeff 1 * (B.coeff 3 - A.coeff 1) - B.coeff 0) * z.1.2 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3) (dvd_sub (hb1d.mul_right _) hb0d) hz2
        have K2a : (A.coeff 0 - B.coeff 2 + A.coeff 1 * (B.coeff 3 - A.coeff 1)) * z.1.1 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3)
            (dvd_add (dvd_sub ha0d hb2d) (ha1d.mul_right _)) hz1
        have K2b : (B.coeff 2 * (B.coeff 3 - A.coeff 1) - B.coeff 1) * z.1.2 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3) (dvd_sub (hb2d.mul_right _) hb1d) hz2
        have K3 : (A.coeff 0 - B.coeff 2 + B.coeff 3 * (B.coeff 3 - A.coeff 1)) * z.1.2 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3)
            (dvd_add (dvd_sub ha0d hb2d) (pow_mul_dvd hb3p hb3ma1)) hz2
        ext k
        rcases Nat.lt_or_ge k 6 with hk | hk
        · interval_cases k <;>
            simp only [coeff_quint₀, coeff_quint₁, coeff_quint₂, coeff_quint₃, coeff_quint₄,
              coeff_quint₅, Polynomial.coeff_zero, coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁,
              coeff_cub₂, coeff_cub₃]
          · linear_combination -K0a + K0b
          · linear_combination K1a + K1b
          · linear_combination K2a + K2b
          · linear_combination K3
          · ring
          · ring
        · rw [coeff_quint_top _ _ _ _ _ _ hk, Polynomial.coeff_zero]⟩
      left_inv := fun q => by
        obtain ⟨⟨α, β⟩, hq1, hq2, hq3⟩ := q
        apply Subtype.ext
        dsimp only
        have hup := caseA_upgrade A hA B hB α β 0 hq1 hq2 hq3
          (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
        have hβ2d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ β.coeff 2 := hup.2 2
        have hβ3d : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ β.coeff 3 := hup.2 3
        rw [combo_quart_quad hB4 hB5 hA2 hA3 hq1 hq2] at hq3
        have e2 : B.coeff 2 * α.coeff 0 + B.coeff 1 * α.coeff 1
            + β.coeff 0 + A.coeff 1 * β.coeff 1 + A.coeff 0 * β.coeff 2 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 2) hq3
          rwa [coeff_quint₂, Polynomial.coeff_zero] at h
        have e3 : B.coeff 3 * α.coeff 0 + B.coeff 2 * α.coeff 1
            + β.coeff 1 + A.coeff 1 * β.coeff 2 + A.coeff 0 * β.coeff 3 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 3) hq3
          rwa [coeff_quint₃, Polynomial.coeff_zero] at h
        have e4 : α.coeff 0 + B.coeff 3 * α.coeff 1 + β.coeff 2 + A.coeff 1 * β.coeff 3
            = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 4) hq3
          rwa [coeff_quint₄, Polynomial.coeff_zero] at h
        have e5 : α.coeff 1 + β.coeff 3 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 5) hq3
          rwa [coeff_quint₅, Polynomial.coeff_zero] at h
        have K7 : (A.coeff 0 - B.coeff 2 + B.coeff 3 * (B.coeff 3 - A.coeff 1)) * β.coeff 3
            = 0 := mul_kill (by norm_num : 5 ≤ 2 + 3)
          (dvd_add (dvd_sub ha0d hb2d) (pow_mul_dvd hb3p hb3ma1)) hβ3d
        have K5 : (A.coeff 0 - B.coeff 2 + A.coeff 1 * (B.coeff 3 - A.coeff 1)) * β.coeff 2
            = 0 := mul_kill (by norm_num : 5 ≤ 2 + 3)
          (dvd_add (dvd_sub ha0d hb2d) (ha1d.mul_right _)) hβ2d
        have K6 : (B.coeff 2 * (B.coeff 3 - A.coeff 1) - B.coeff 1) * β.coeff 3 = 0 :=
          mul_kill (by norm_num : 5 ≤ 2 + 3) (dvd_sub (hb2d.mul_right _) hb1d) hβ3d
        have hα1eq : α.coeff 1 = -β.coeff 3 := by linear_combination e5
        have hα0eq : α.coeff 0 = -β.coeff 2 + (B.coeff 3 - A.coeff 1) * β.coeff 3 := by
          linear_combination e4 - B.coeff 3 * hα1eq
        have hβ1eq : β.coeff 1 = (B.coeff 3 - A.coeff 1) * β.coeff 2 := by
          linear_combination e3 - B.coeff 3 * e4 + (B.coeff 3 ^ 2 - B.coeff 2) * e5 - K7
        have hβ0eq : β.coeff 0 = 0 := by
          linear_combination e2 - B.coeff 2 * e4 + (B.coeff 2 * B.coeff 3 - B.coeff 1) * e5
            - A.coeff 1 * hβ1eq - K5 - K6
        have h1 : C (-β.coeff 2 + (B.coeff 3 - A.coeff 1) * β.coeff 3) + C (-β.coeff 3) * X
            = α := by
          rw [← hα0eq, ← hα1eq]
          exact (eq_lin hq1).symm
        have h2 : C 0 + C ((B.coeff 3 - A.coeff 1) * β.coeff 2) * X + C (β.coeff 2) * X ^ 2
            + C (β.coeff 3) * X ^ 3 = β := by
          rw [← hβ1eq, ← hβ0eq]
          exact (eq_cub hq2).symm
        rw [h1, h2]
      right_inv := fun z => by
        apply Subtype.ext
        dsimp only
        rw [coeff_cub₂, coeff_cub₃] }
  rw [Nat.card_congr e]
  exact boxA_card

/-! ### Case-A coset cards -/

set_option maxRecDepth 40000 in
private theorem cosetA_SA_box_card :
    Nat.card {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 - 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.2 + 4}
      = 32 := by
  have he : ∀ z : ZMod (2 ^ 5) × ZMod (2 ^ 5),
      (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 - 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.2 + 4)
        ↔ ((z.1 - 4).val % 8 = 0 ∧ (z.2 + 4).val % 4 = 0) := by
    intro z
    rw [dvd_val_A (by norm_num) (z.1 - 4), dvd_val_A (by norm_num) (z.2 + 4)]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

set_option maxRecDepth 40000 in
private theorem cosetA_SB1_card :
    Nat.card {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 - 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.2} = 32 := by
  have he : ∀ z : ZMod (2 ^ 5) × ZMod (2 ^ 5),
      (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 - 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.2)
        ↔ ((z.1 - 4).val % 8 = 0 ∧ z.2.val % 4 = 0) := by
    intro z
    rw [dvd_val_A (by norm_num) (z.1 - 4), dvd_val_A (by norm_num) z.2]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

set_option maxRecDepth 40000 in
private theorem cosetA_SB2_card :
    Nat.card {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.1 + 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ z.2} = 128 := by
  have he : ∀ z : ZMod (2 ^ 5) × ZMod (2 ^ 5),
      (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.1 + 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ z.2)
        ↔ ((z.1 + 4).val % 4 = 0 ∧ z.2.val % 2 = 0) := by
    intro z
    rw [dvd_val_A (by norm_num) (z.1 + 4), dvd_val_A (by norm_num) z.2]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- The x-slot box bijection for the case-A quadratic coset. -/
private noncomputable def aSAEquiv :
    ↥aSA ≃ {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 - 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.2 + 4} where
  toFun P := ⟨(P.1.coeff 0, P.1.coeff 1), by
    obtain ⟨-, -, h0, h1⟩ := aSA_facts P.2
    exact ⟨h0, h1⟩⟩
  invFun z := ⟨X ^ 2 + (C z.1.1 + C z.1.2 * X), by
    have hmd := monic_add_of_coeff (Polynomial.monic_X_pow 2)
      (Polynomial.natDegree_X_pow 2) (fun i hi => coeff_lin_top z.1.1 z.1.2 hi)
    refine ⟨hmd.1, hmd.2, fun i => ?_⟩
    rcases Nat.lt_or_ge i 3 with hi | hi
    · interval_cases i
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - aA₀).coeff 0 = z.1.1 - 4 := by
          have hc : aA₀.coeff 0 = 4 := coeff_quad₀ _ _
          rw [Polynomial.coeff_sub, coeff_quad₀, hc]
        rw [he]
        exact z.2.1
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - aA₀).coeff 1 = z.1.2 + 4 := by
          have hc : aA₀.coeff 1 = -4 := coeff_quad₁ _ _
          rw [Polynomial.coeff_sub, coeff_quad₁, hc]
          ring
        rw [he]
        exact z.2.2
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - aA₀).coeff 2 = 0 := by
          have hc : aA₀.coeff 2 = 1 := coeff_quad₂ _ _
          rw [Polynomial.coeff_sub, coeff_quad₂, hc, sub_self]
        rw [he]
        exact dvd_zero _
    · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - aA₀).coeff i = 0 := by
        have hc : aA₀.coeff i = 0 := coeff_quad_top _ _ hi
        rw [Polynomial.coeff_sub, coeff_quad_top _ _ hi, hc, sub_self]
      rw [he]
      exact dvd_zero _⟩
  left_inv P := by
    apply Subtype.ext
    dsimp only
    obtain ⟨h2, h3, -, -⟩ := aSA_facts P.2
    exact (eq_quad h2 h3).symm
  right_inv z := by
    apply Subtype.ext
    dsimp only
    rw [coeff_quad₀, coeff_quad₁]

/-- The x-slot box bijection for the case-A quartic coset (split as a product of two
coefficient pairs). -/
private noncomputable def aSBEquiv :
    ↥aSB ≃ ({z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
        ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 - 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.2}
      × {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
        ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ z.1 + 4 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ z.2}) where
  toFun P :=
    (⟨(P.1.coeff 0, P.1.coeff 1),
      (aSB_facts P.2).2.2.1, (aSB_facts P.2).2.2.2.1⟩,
     ⟨(P.1.coeff 2, P.1.coeff 3),
      (aSB_facts P.2).2.2.2.2.1, (aSB_facts P.2).2.2.2.2.2⟩)
  invFun zw := ⟨X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
      + C zw.2.1.2 * X ^ 3), by
    have hmd := monic_add_of_coeff (Polynomial.monic_X_pow 4)
      (Polynomial.natDegree_X_pow 4)
      (fun i hi => coeff_cub_top zw.1.1.1 zw.1.1.2 zw.2.1.1 zw.2.1.2 hi)
    refine ⟨hmd.1, hmd.2, fun i => ?_⟩
    rcases Nat.lt_or_ge i 5 with hi | hi
    · interval_cases i
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - aB₀).coeff 0 = zw.1.1.1 - 4 := by
          have hc : aB₀.coeff 0 = 4 := coeff_quart₀ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₀, hc]
        rw [he]
        exact zw.1.2.1
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - aB₀).coeff 1 = zw.1.1.2 := by
          have hc : aB₀.coeff 1 = 0 := coeff_quart₁ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₁, hc, sub_zero]
        rw [he]
        exact zw.1.2.2
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - aB₀).coeff 2 = zw.2.1.1 + 4 := by
          have hc : aB₀.coeff 2 = -4 := coeff_quart₂ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₂, hc]
          ring
        rw [he]
        exact zw.2.2.1
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - aB₀).coeff 3 = zw.2.1.2 := by
          have hc : aB₀.coeff 3 = 0 := coeff_quart₃ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₃, hc, sub_zero]
        rw [he]
        exact zw.2.2.2
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - aB₀).coeff 4 = 0 := by
          have hc : aB₀.coeff 4 = 1 := coeff_quart₄ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₄, hc, sub_self]
        rw [he]
        exact dvd_zero _
    · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
            + C zw.2.1.2 * X ^ 3)) - aB₀).coeff i = 0 := by
        have hc : aB₀.coeff i = 0 := coeff_quart_top _ _ _ _ hi
        rw [Polynomial.coeff_sub, coeff_quart_top _ _ _ _ hi, hc, sub_self]
      rw [he]
      exact dvd_zero _⟩
  left_inv P := by
    apply Subtype.ext
    dsimp only
    obtain ⟨h4, h5, -, -, -, -⟩ := aSB_facts P.2
    exact (eq_quart h4 h5).symm
  right_inv zw := by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      dsimp only
      rw [coeff_quart₀, coeff_quart₁]
    · apply Subtype.ext
      dsimp only
      rw [coeff_quart₂, coeff_quart₃]

/-- Coset card `|P₁| = 32 = 2^5` — agrees with `card_freshPattern` at `(2,5,1,2)`. -/
theorem caseA_card_SA : Nat.card aSA = 32 :=
  (Nat.card_congr aSAEquiv).trans cosetA_SA_box_card

/-- Coset card `|P₂| = 4096 = 2^12` — agrees with `card_freshPattern` at `(2,5,2,2)`. -/
theorem caseA_card_SB : Nat.card aSB = 4096 := by
  rw [Nat.card_congr aSBEquiv, Nat.card_prod, cosetA_SB1_card, cosetA_SB2_card]

/-! ### The case-A end-to-end law THROUGH the graded ladder -/

/-- **Case A, THE LAW, derived THROUGH the graded pair law**: at the real gate cell — where
the flat margins are provably empty (`BlockProduct.gate_margin_A`) — the pointwise
certificates give `card(image) · 2⁴ = |P₁| · |P₂|`.  Not by `decide`: this instantiates
`pair_card_graded` with `caseA_upgrade` + `caseA_ker_card`. -/
theorem caseA_law_graded :
    Nat.card ((fun AB : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] => AB.1 * AB.2) ''
        (aSA ×ˢ aSB)) * 2 ^ 4
      = Nat.card aSA * Nat.card aSB :=
  pair_card_graded (p := 2) (N := 5) (c := 4) (floA := aFloA) (floB := aFloB)
    (by norm_num) subset_rfl (patternCell_saturatedAt hM1A₁) subset_rfl
    (patternCell_saturatedAt hM1A₂) hM2A hqbA caseA_upgrade caseA_ker_card

/-- The fiber card forced THROUGH the graded ladder: `8192` fibers. -/
theorem caseA_image_card :
    Nat.card ((fun AB : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] => AB.1 * AB.2) ''
      (aSA ×ˢ aSB)) = 8192 := by
  have h := caseA_law_graded
  rw [caseA_card_SA, caseA_card_SB, show (2 : ℕ) ^ 4 = 16 from rfl] at h
  omega

/-- **Cross-check against the banked closed form `BlockProduct.gateA_coset_product`**
(`131072 = 8192 · 2⁴`): the graded-ladder law meets the `card_freshPattern` product. -/
theorem caseA_matches_gateA :
    Nat.card ((fun AB : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] => AB.1 * AB.2) ''
        (aSA ×ˢ aSB)) * 2 ^ 4
      = Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 1 1 1 //
          RestartEquiv.FreshClusterPattern 2 5 1 2 1 β}
        * Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 2 1 1 //
            RestartEquiv.FreshClusterPattern 2 5 2 2 1 β} := by
  rw [caseA_image_card, BlockProduct.gateA_coset_product]

/-! ### The case-A `GradedChain` and the discharge of `h_node1_general` -/

/-- Case-A first block: the e=1 child. -/
noncomputable def blockA₁ : Block 2 5 := ⟨aA₀, 2, aSA⟩

/-- Case-A second block: the e=2 child. -/
noncomputable def blockA₂ : Block 2 5 := ⟨aB₀, 4, aSB⟩

/-- **The case-A graded chain certificate**: the two-block list carries the full W4d2′
data — M1/M2/conv margins, the pointwise upgrade and the kernel count at every point. -/
theorem caseA_chain : GradedChain [blockA₁, blockA₂] 4 := by
  have h2 : GradedChain [blockA₂] 0 := by
    have h := GradedChain.cons (p := 2) (N := 5) (l := []) (X := 0) blockA₂ 0
      aFloB (fun _ => 0) aDepB (fun _ => 0) aDepB aB₀ 1 (by norm_num)
      subset_rfl (patternCell_saturatedAt hM1A₂)
      (imageSet_nil_subset_patternCell (fun _ => 0)) (imageSet_nil_saturatedAt (fun _ => 0))
      (fun s t _ ht => absurd ht (Nat.not_lt_zero t))
      (fun s t _ ht => absurd ht (Nat.not_lt_zero t))
      (fun A hA B hB => by
        have hB1 : B = 1 := hB
        rw [hB1]
        exact gradedUpgradeAt_one A 4 aDepB (fun _ => 0))
      (fun A hA B hB => by
        have hB1 : B = 1 := hB
        rw [hB1]
        exact polyKer_one_card A 4)
      GradedChain.nil
    exact h
  have h1 := GradedChain.cons (p := 2) (N := 5) (l := [blockA₂]) (X := 0) blockA₁ 4
    aFloA aFloB aDepA aDepB aQb aA₀ aB₀ (by norm_num)
    subset_rfl (patternCell_saturatedAt hM1A₁)
    (by rw [imageSet_singleton]; exact subset_rfl)
    (by rw [imageSet_singleton]; exact patternCell_saturatedAt hM1A₂)
    hM2A hqbA
    (fun A hA B hB => by
      rw [imageSet_singleton] at hB
      exact caseA_upgrade A hA B hB)
    (fun A hA B hB => by
      rw [imageSet_singleton] at hB
      exact caseA_ker_card A hA B hB)
    h2
  exact h1

/-- **`h_node1_general` DISCHARGED at gate cell A** (W4d2′ TODO 4, case A): the block-product
IMAGE `imageSet [blockA₁, blockA₂]` obeys the em-square law `#(imageSet) · 2⁴ = 2^(5+12) = 2¹⁷`
— the HNode1 ledger's case-A hypothesis gate is closed by `caseA_chain` + the coset-card
certificates.  SCOPE (verifier finding 2026-07-05, no-gloss discipline): `imageSet` is the
image of the block-coset product under polynomial multiplication, NOT the classifier's
multi-block `InCell` fiber.  Their identification (theorem-of-the-product surjectivity
`imageSet = {f | multi-block InCell f c}`) is GATE-VERIFIED numerically (d2-0, box-by-box) but
NOT formalized, and no multi-block `InCell` is yet defined in `CellMenu` (W2 scope was
single-side).  Named remaining obligation: **W4d2-surj** (theorem of the product at level N).
The single-block restart IS fully identified — `RestartEquiv.restartEquiv` is a genuine
bijection to the classifier fiber. -/
theorem h_node1_at_A :
    Nat.card (imageSet [blockA₁, blockA₂]) * 2 ^ 4 = 2 ^ 17 := by
  have h := HNode1.h_node1_general 2 5 caseA_chain
    (fun b => if b.deg = 2 then 5 else 12)
    (by
      intro b hb
      rcases List.mem_cons.mp hb with h1 | h1
      · subst h1
        exact caseA_card_SA.trans (by decide)
      · rcases List.mem_cons.mp h1 with h2 | h2
        · subst h2
          exact caseA_card_SB.trans (by decide)
        · simp at h2)
  exact h

/-- The block-product IMAGE count at cell A, through the chain: `8192` — matches
`caseA_image_card`.  (Not the classifier multi-block fiber; see `h_node1_at_A` scope note and
the named obligation W4d2-surj.) -/
theorem caseA_node_census : Nat.card (imageSet [blockA₁, blockA₂]) = 8192 := by
  have h := h_node1_at_A
  rw [show (2 : ℕ) ^ 4 = 16 from rfl, show (2 : ℕ) ^ 17 = 131072 from rfl] at h
  omega

end GateA

/-! ## 4. Case C — `p = 3, N = 4`, blocks `(2,2,1)` child × `(2,1,2)` decided, `c = X = 4`

A-side: the `(y−1)²` child, quartic box around `cA₀ = (X²−3)²` at floors `(3,2,2,1)`, depths
`cDepA = (3,3,2,2)`.  B-side: the decided `(y−2)` block, quadratic box around `cB₀ = X²−6` at
floors `(2,1)`, depths `cDepB = (2,2)`.  The child block's four rows eliminate `α`; the
reduced 2×2 `β`-system feeds the engine at scale `w = 2`, `D = (4,3)`, `v = (2,2)` (both
pivots `9·(1+3E)`), `off = ((·,3),(2,·))`. -/

section GateC

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

private instance : Fact (1 < 3 ^ 4) := ⟨by norm_num⟩

/-- Case-C first center `(X²−3)² = X⁴ − 6X² + 9` over `ZMod 81` (quartic normal form). -/
noncomputable def cA₀ : (ZMod (3 ^ 4))[X] :=
  X ^ 4 + (C 9 + C 0 * X + C (-6) * X ^ 2 + C 0 * X ^ 3)

/-- Case-C second center `X² − 6` over `ZMod 81` (quadratic normal form). -/
noncomputable def cB₀ : (ZMod (3 ^ 4))[X] := X ^ 2 + (C (-6) + C 0 * X)

/-- The pinned case-C x-slot floors of the child block: `(3, 2, 2, 1)`. -/
def cFloA : ℕ → ℕ := sideFloor 2 4

/-- The pinned case-C x-slot floors of the decided block: `(2, 1)`. -/
def cFloB : ℕ → ℕ := sideFloor 2 2

/-- The pinned case-C graded depths of the child block: `(3, 3, 2, 2)` (`S = 1`). -/
def cDepA : ℕ → ℕ := sideDepth 2 1 4

/-- The pinned case-C graded depths of the decided block: `(2, 2)` (`S = 2`). -/
def cDepB : ℕ → ℕ := sideDepth 2 2 4

/-- The pinned case-C conv floor `(5, 4, 3, 3, 2)` (padded by `N = 4` beyond the support). -/
def cQb : ℕ → ℕ := fun r =>
  if r = 0 then 5 else if r = 1 then 4 else if r ≤ 3 then 3 else if r = 4 then 2 else 4

/-- The case-C pattern coset of the `(y−1)²` child block, as an x-slot box. -/
noncomputable def cSA : Set ((ZMod (3 ^ 4))[X]) := patternCell (p := 3) (N := 4) cA₀ 4 cFloA

/-- The case-C pattern coset of the decided `(y−2)` block. -/
noncomputable def cSB : Set ((ZMod (3 ^ 4))[X]) := patternCell (p := 3) (N := 4) cB₀ 2 cFloB

private theorem hM1C₁ : ∀ i, cFloA i ≤ cDepA i := by
  intro i
  simp only [cFloA, cDepA, sideFloor, sideDepth, cdiv]
  omega

private theorem hM1C₂ : ∀ i, cFloB i ≤ cDepB i := by
  intro i
  simp only [cFloB, cDepB, sideFloor, sideDepth, cdiv]
  omega

private theorem hM2C : ∀ s t : ℕ, s < 4 → t < 2 → 4 ≤ cDepA s + cDepB t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

private theorem hqbC : ∀ s t : ℕ, s < 4 → t < 2 → cQb (s + t) ≤ cFloA s + cFloB t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

/-- Membership facts for the quartic coset. -/
private theorem cSA_facts {A : (ZMod (3 ^ 4))[X]} (hA : A ∈ cSA) :
    A.coeff 4 = 1 ∧ (∀ i, 5 ≤ i → A.coeff i = 0)
      ∧ (((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ A.coeff 0 - 9)
      ∧ (((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ A.coeff 1)
      ∧ (((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ A.coeff 2 + 6)
      ∧ (((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ A.coeff 3) := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hA
  have h4 : A.coeff 4 = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hdeg] at h
  have h5 : ∀ i, 5 ≤ i → A.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  refine ⟨h4, h5, ?_, ?_, ?_, ?_⟩
  · have h := hdvd 0
    have he : (A - cA₀).coeff 0 = A.coeff 0 - 9 := by
      have hc : cA₀.coeff 0 = 9 := coeff_quart₀ _ _ _ _
      rw [Polynomial.coeff_sub, hc]
    rwa [he] at h
  · have h := hdvd 1
    have he : (A - cA₀).coeff 1 = A.coeff 1 := by
      have hc : cA₀.coeff 1 = 0 := coeff_quart₁ _ _ _ _
      rw [Polynomial.coeff_sub, hc, sub_zero]
    rwa [he] at h
  · have h := hdvd 2
    have he : (A - cA₀).coeff 2 = A.coeff 2 + 6 := by
      have hc : cA₀.coeff 2 = -6 := coeff_quart₂ _ _ _ _
      rw [Polynomial.coeff_sub, hc]
      ring
    rwa [he] at h
  · have h := hdvd 3
    have he : (A - cA₀).coeff 3 = A.coeff 3 := by
      have hc : cA₀.coeff 3 = 0 := coeff_quart₃ _ _ _ _
      rw [Polynomial.coeff_sub, hc, sub_zero]
    rwa [he] at h

/-- Membership facts for the quadratic coset. -/
private theorem cSB_facts {B : (ZMod (3 ^ 4))[X]} (hB : B ∈ cSB) :
    B.coeff 2 = 1 ∧ (∀ i, 3 ≤ i → B.coeff i = 0)
      ∧ (((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ B.coeff 0 + 6)
      ∧ (((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ B.coeff 1) := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hB
  have h2 : B.coeff 2 = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hdeg] at h
  have h3 : ∀ i, 3 ≤ i → B.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  refine ⟨h2, h3, ?_, ?_⟩
  · have h := hdvd 0
    have he : (B - cB₀).coeff 0 = B.coeff 0 + 6 := by
      have hc : cB₀.coeff 0 = -6 := coeff_quad₀ _ _
      rw [Polynomial.coeff_sub, hc]
      ring
    rwa [he] at h
  · have h := hdvd 1
    have he : (B - cB₀).coeff 1 = B.coeff 1 := by
      have hc : cB₀.coeff 1 = 0 := coeff_quad₁ _ _
      rw [Polynomial.coeff_sub, hc, sub_zero]
    rwa [he] at h

/-- **Case-C pointwise graded upgrade** (W4d2′ TODO 1 at cell C): the child block's four
unit rows eliminate `α`; the Schur-reduced 2×2 `β`-system carries a scale-2 certificate for
`graded_mulVec_upgrade` (`D = (4,3)`, `v = (2,2)`, both pivots `9·(1+3E)` with explicit unit
cofactors); `α` inherits by back-substitution — per-slot depths `cDepA = (3,3,2,2)`,
`cDepB = (2,2)`. -/
theorem caseC_upgrade : ∀ A ∈ cSA, ∀ B ∈ cSB,
    GradedUpgradeAt (p := 3) (N := 4) A B 4 2 cDepA cDepB cQb := by
  intro A hA B hB α β Y hαtop hβtop hcombo hY
  obtain ⟨hA4, hA5, hA0f, hA1f, hA2f, hA3f⟩ := cSA_facts hA
  obtain ⟨hB2, hB3, hB0f, hB1f⟩ := cSB_facts hB
  obtain ⟨s, hs⟩ := hA0f
  obtain ⟨a1, ha1⟩ := hA1f
  obtain ⟨a2, ha2⟩ := hA2f
  obtain ⟨a3, ha3⟩ := hA3f
  obtain ⟨t, ht⟩ := hB0f
  obtain ⟨u, hu⟩ := hB1f
  have hA0' : A.coeff 0 = 9 + ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 * s := by linear_combination hs
  have hA1' : A.coeff 1 = ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 * a1 := ha1
  have hA2' : A.coeff 2 = -6 + ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 * a2 := by linear_combination ha2
  have hA3' : A.coeff 3 = ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 * a3 := ha3
  have hB0' : B.coeff 0 = -6 + ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 * t := by linear_combination ht
  have hB1' : B.coeff 1 = ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 * u := hu
  have ha0d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ A.coeff 0 := ⟨1 + 3 * s, by rw [hA0']; ring⟩
  have ha1d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ A.coeff 1 := ⟨a1, hA1'⟩
  have ha2d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ A.coeff 2 := ⟨-2 + 3 * a2, by rw [hA2']; ring⟩
  have ha3d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ A.coeff 3 := ⟨a3, hA3'⟩
  have hb0d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ B.coeff 0 := ⟨-2 + 3 * t, by rw [hB0']; ring⟩
  have hb1d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ B.coeff 1 := ⟨u, hB1'⟩
  have hy0 : Y.coeff 0 = 0 := eq_zero_of_deep_dvd (show (4 : ℕ) ≤ 5 by norm_num) (hY 0)
  have hy1 : Y.coeff 1 = 0 := eq_zero_of_deep_dvd (show (4 : ℕ) ≤ 4 by norm_num) (hY 1)
  have hy5 : Y.coeff 5 = 0 := eq_zero_of_deep_dvd (show (4 : ℕ) ≤ 4 by norm_num) (hY 5)
  have hy2 : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ Y.coeff 2 := hY 2
  have hy3 : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ Y.coeff 3 := hY 3
  have hy4 : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ Y.coeff 4 := hY 4
  obtain ⟨z2w, hz2w⟩ := id hy2
  obtain ⟨z3w, hz3w⟩ := id hy3
  obtain ⟨z4w, hz4w⟩ := id hy4
  rw [combo_quad_quart hA4 hA5 hB2 hB3 hβtop hαtop] at hcombo
  have e0 : A.coeff 0 * β.coeff 0 + B.coeff 0 * α.coeff 0 = Y.coeff 0 := by
    have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 0) hcombo
    rwa [coeff_quint₀] at h
  have e1 : A.coeff 1 * β.coeff 0 + A.coeff 0 * β.coeff 1
      + B.coeff 1 * α.coeff 0 + B.coeff 0 * α.coeff 1 = Y.coeff 1 := by
    have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 1) hcombo
    rwa [coeff_quint₁] at h
  have e2 : A.coeff 2 * β.coeff 0 + A.coeff 1 * β.coeff 1
      + α.coeff 0 + B.coeff 1 * α.coeff 1 + B.coeff 0 * α.coeff 2 = Y.coeff 2 := by
    have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 2) hcombo
    rwa [coeff_quint₂] at h
  have e3 : A.coeff 3 * β.coeff 0 + A.coeff 2 * β.coeff 1
      + α.coeff 1 + B.coeff 1 * α.coeff 2 + B.coeff 0 * α.coeff 3 = Y.coeff 3 := by
    have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 3) hcombo
    rwa [coeff_quint₃] at h
  have e4 : β.coeff 0 + A.coeff 3 * β.coeff 1 + α.coeff 2 + B.coeff 1 * α.coeff 3
      = Y.coeff 4 := by
    have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 4) hcombo
    rwa [coeff_quint₄] at h
  have e5 : β.coeff 1 + α.coeff 3 = Y.coeff 5 := by
    have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 5) hcombo
    rwa [coeff_quint₅] at h
  -- the engine on the Schur-reduced 2×2 β-system, scale w = 2
  have hβall : ∀ j : Fin 2, ((3 : ℕ) : ZMod (3 ^ 4)) ^ cdiv ((![4, 3] : Fin 2 → ℕ) j) 2
      ∣ (![β.coeff 0, β.coeff 1] : Fin 2 → ZMod (3 ^ 4)) j := by
    refine graded_mulVec_upgrade (p := 3) (N := 4)
      (Matrix.of ![![A.coeff 0 - B.coeff 0 * A.coeff 2 + B.coeff 0 * B.coeff 1 * A.coeff 3
            + B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2,
          -(B.coeff 0 * A.coeff 1) + B.coeff 0 * B.coeff 1 * A.coeff 2
            + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * A.coeff 3
            - 2 * B.coeff 0 ^ 2 * B.coeff 1 + B.coeff 0 * B.coeff 1 ^ 3],
        ![A.coeff 1 - B.coeff 1 * A.coeff 2 + (B.coeff 1 ^ 2 - B.coeff 0) * A.coeff 3
            + 2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3,
          A.coeff 0 - B.coeff 1 * A.coeff 1 + (B.coeff 1 ^ 2 - B.coeff 0) * A.coeff 2
            + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * A.coeff 3
            + B.coeff 0 ^ 2 - 3 * B.coeff 0 * B.coeff 1 ^ 2 + B.coeff 1 ^ 4]])
      (w := 2) (by norm_num) ![0, 1] ![2, 2] ![4, 3] ![![0, 3], ![2, 0]]
      (by decide) ?_ (by decide) ?_ (by decide)
      (x := ![β.coeff 0, β.coeff 1])
      (y := ![-(B.coeff 0 * Y.coeff 2) + B.coeff 0 * B.coeff 1 * Y.coeff 3
          + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * Y.coeff 4,
        -(B.coeff 1 * Y.coeff 2) + (B.coeff 1 ^ 2 - B.coeff 0) * Y.coeff 3
          + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * Y.coeff 4]) ?_ ?_
    · -- hdiag: both pivots are 9·(1 + 3E), E the explicit unit cofactor
      intro j
      fin_cases j
      · refine ⟨(isUnit_one_add_pmul (p := 3) (N := 4)
          (-(3 * a2 * t) + 2 * a2 + 3 * a3 * t * u - 2 * a3 * u + s + 3 * t ^ 2
            - 3 * t * u ^ 2 - 2 * t + 2 * u ^ 2)).unit, ?_⟩
        show A.coeff 0 - B.coeff 0 * A.coeff 2 + B.coeff 0 * B.coeff 1 * A.coeff 3
            + B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2
          = ((3 : ℕ) : ZMod (3 ^ 4)) ^ (2 : ℕ)
            * ((isUnit_one_add_pmul (p := 3) (N := 4)
                (-(3 * a2 * t) + 2 * a2 + 3 * a3 * t * u - 2 * a3 * u + s + 3 * t ^ 2
                  - 3 * t * u ^ 2 - 2 * t + 2 * u ^ 2)).unit : ZMod (3 ^ 4))
        rw [IsUnit.unit_spec, hA0', hA2', hA3', hB0', hB1']
        ring
      · refine ⟨(isUnit_one_add_pmul (p := 3) (N := 4)
          (-(a1 * u) - 3 * a2 * t + 3 * a2 * u ^ 2 + 2 * a2 + 6 * a3 * t * u
            - 3 * a3 * u ^ 3 - 4 * a3 * u + s + 3 * t ^ 2 - 9 * t * u ^ 2 - 2 * t
            + 3 * u ^ 4 + 4 * u ^ 2)).unit, ?_⟩
        show A.coeff 0 - B.coeff 1 * A.coeff 1 + (B.coeff 1 ^ 2 - B.coeff 0) * A.coeff 2
            + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * A.coeff 3
            + B.coeff 0 ^ 2 - 3 * B.coeff 0 * B.coeff 1 ^ 2 + B.coeff 1 ^ 4
          = ((3 : ℕ) : ZMod (3 ^ 4)) ^ (2 : ℕ)
            * ((isUnit_one_add_pmul (p := 3) (N := 4)
                (-(a1 * u) - 3 * a2 * t + 3 * a2 * u ^ 2 + 2 * a2 + 6 * a3 * t * u
                  - 3 * a3 * u ^ 3 - 4 * a3 * u + s + 3 * t ^ 2 - 9 * t * u ^ 2 - 2 * t
                  + 3 * u ^ 4 + 4 * u ^ 2)).unit : ZMod (3 ^ 4))
        rw [IsUnit.unit_spec, hA0', hA1', hA2', hA3', hB0', hB1']
        ring
    · -- hoffdvd: M₀₁ = 27·W₀₁, M₁₀ = 9·W₁₀ (sympy-verified witnesses)
      intro j j' hne
      fin_cases j <;> fin_cases j'
      · exact absurd rfl hne
      · show ((3 : ℕ) : ZMod (3 ^ 4)) ^ (3 : ℕ)
          ∣ -(B.coeff 0 * A.coeff 1) + B.coeff 0 * B.coeff 1 * A.coeff 2
            + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * A.coeff 3
            - 2 * B.coeff 0 ^ 2 * B.coeff 1 + B.coeff 0 * B.coeff 1 ^ 3
        exact ⟨-(3 * a1 * t) + 2 * a1 + 9 * a2 * t * u - 6 * a2 * u + 9 * a3 * t ^ 2
            - 9 * a3 * t * u ^ 2 - 12 * a3 * t + 6 * a3 * u ^ 2 + 4 * a3 - 18 * t ^ 2 * u
            + 9 * t * u ^ 3 + 18 * t * u - 6 * u ^ 3 - 4 * u,
          by rw [hA1', hA2', hA3', hB0', hB1']; ring⟩
      · show ((3 : ℕ) : ZMod (3 ^ 4)) ^ (2 : ℕ)
          ∣ A.coeff 1 - B.coeff 1 * A.coeff 2 + (B.coeff 1 ^ 2 - B.coeff 0) * A.coeff 3
            + 2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3
        exact ⟨a1 - 3 * a2 * u - 3 * a3 * t + 3 * a3 * u ^ 2 + 2 * a3 + 6 * t * u
            - 3 * u ^ 3 - 2 * u,
          by rw [hA1', hA2', hA3', hB0', hB1']; ring⟩
      · exact absurd rfl hne
    · -- hxy: the Schur row operations, as explicit linear_combination cofactors
      funext j
      fin_cases j <;>
        simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
      · show (A.coeff 0 - B.coeff 0 * A.coeff 2 + B.coeff 0 * B.coeff 1 * A.coeff 3
              + B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * β.coeff 0
            + (-(B.coeff 0 * A.coeff 1) + B.coeff 0 * B.coeff 1 * A.coeff 2
              + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * A.coeff 3
              - 2 * B.coeff 0 ^ 2 * B.coeff 1 + B.coeff 0 * B.coeff 1 ^ 3) * β.coeff 1
          = -(B.coeff 0 * Y.coeff 2) + B.coeff 0 * B.coeff 1 * Y.coeff 3
            + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * Y.coeff 4
        linear_combination e0 - B.coeff 0 * e2 + B.coeff 0 * B.coeff 1 * e3
          + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * e4
          + (-(2 * B.coeff 0 ^ 2 * B.coeff 1) + B.coeff 0 * B.coeff 1 ^ 3) * e5
          + hy0 + (-(2 * B.coeff 0 ^ 2 * B.coeff 1) + B.coeff 0 * B.coeff 1 ^ 3) * hy5
      · show (A.coeff 1 - B.coeff 1 * A.coeff 2 + (B.coeff 1 ^ 2 - B.coeff 0) * A.coeff 3
              + 2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * β.coeff 0
            + (A.coeff 0 - B.coeff 1 * A.coeff 1 + (B.coeff 1 ^ 2 - B.coeff 0) * A.coeff 2
              + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * A.coeff 3
              + B.coeff 0 ^ 2 - 3 * B.coeff 0 * B.coeff 1 ^ 2 + B.coeff 1 ^ 4) * β.coeff 1
          = -(B.coeff 1 * Y.coeff 2) + (B.coeff 1 ^ 2 - B.coeff 0) * Y.coeff 3
            + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * Y.coeff 4
        linear_combination e1 - B.coeff 1 * e2 + (B.coeff 1 ^ 2 - B.coeff 0) * e3
          + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * e4
          + (B.coeff 0 ^ 2 - 3 * B.coeff 0 * B.coeff 1 ^ 2 + B.coeff 1 ^ 4) * e5
          + hy1 + (B.coeff 0 ^ 2 - 3 * B.coeff 0 * B.coeff 1 ^ 2 + B.coeff 1 ^ 4) * hy5
    · -- hy: the reduced RHS is graded-deep at the pivot rows
      intro j
      fin_cases j
      · show ((3 : ℕ) : ZMod (3 ^ 4)) ^ (4 : ℕ)
          ∣ -(B.coeff 0 * Y.coeff 2) + B.coeff 0 * B.coeff 1 * Y.coeff 3
            + (B.coeff 0 ^ 2 - B.coeff 0 * B.coeff 1 ^ 2) * Y.coeff 4
        exact ⟨(2 - 3 * t) * z2w + (-6 + 9 * t) * u * z3w
            + (4 - 12 * t + 6 * u ^ 2 + 9 * t ^ 2 - 9 * t * u ^ 2) * z4w,
          by rw [hB0', hB1', hz2w, hz3w, hz4w]; ring⟩
      · show ((3 : ℕ) : ZMod (3 ^ 4)) ^ (4 : ℕ)
          ∣ -(B.coeff 1 * Y.coeff 2) + (B.coeff 1 ^ 2 - B.coeff 0) * Y.coeff 3
            + (2 * B.coeff 0 * B.coeff 1 - B.coeff 1 ^ 3) * Y.coeff 4
        exact ⟨-(u * z2w) + (3 * u ^ 2 + 2 - 3 * t) * z3w
            + (-(4 * u) + 6 * t * u - 3 * u ^ 3) * z4w,
          by rw [hB0', hB1', hz2w, hz3w, hz4w]; ring⟩
  -- extract the β-slot depths (defeq: `cdiv (4,3) 2 = (2,2)`)
  have hβ0d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ β.coeff 0 := hβall 0
  have hβ1d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ β.coeff 1 := hβall 1
  -- α inherits by back-substitution through the unit rows
  have hα3eq : α.coeff 3 = -β.coeff 1 := by linear_combination e5 + hy5
  have hα2eq : α.coeff 2 = Y.coeff 4 + (B.coeff 1 - A.coeff 3) * β.coeff 1 - β.coeff 0 := by
    linear_combination e4 - B.coeff 1 * hα3eq
  have hα3d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ α.coeff 3 := by
    rw [hα3eq]
    exact dvd_neg.mpr hβ1d
  have hα2d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ α.coeff 2 := by
    rw [hα2eq]
    exact dvd_sub (dvd_add hy4 (hβ1d.mul_left _)) hβ0d
  have hα1eq : α.coeff 1 = Y.coeff 3 - B.coeff 1 * α.coeff 2 - B.coeff 0 * α.coeff 3
      - A.coeff 3 * β.coeff 0 - A.coeff 2 * β.coeff 1 := by
    linear_combination e3
  have hα1d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ α.coeff 1 := by
    rw [hα1eq]
    refine dvd_sub (dvd_sub (dvd_sub (dvd_sub hy3 ?_) ?_) ?_) ?_
    · exact pow_mul_dvd hb1d hα2d
    · exact pow_mul_dvd hb0d hα3d
    · exact pow_mul_dvd ha3d hβ0d
    · exact pow_mul_dvd ha2d hβ1d
  have hα0eq : α.coeff 0 = Y.coeff 2 - B.coeff 1 * α.coeff 1 - B.coeff 0 * α.coeff 2
      - A.coeff 2 * β.coeff 0 - A.coeff 1 * β.coeff 1 := by
    linear_combination e2
  have hα0d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ α.coeff 0 := by
    rw [hα0eq]
    refine dvd_sub (dvd_sub (dvd_sub (dvd_sub hy2 ?_) ?_) ?_) ?_
    · exact (pow_dvd_pow _ (by norm_num : 3 ≤ 4)).trans (pow_mul_dvd hb1d hα1d)
    · exact pow_mul_dvd hb0d hα2d
    · exact pow_mul_dvd ha2d hβ0d
    · exact (pow_dvd_pow _ (by norm_num : 3 ≤ 4)).trans (pow_mul_dvd ha1d hβ1d)
  -- per-slot conclusions
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge i 4 with hi | hi
    · interval_cases i
      · exact hα0d
      · exact hα1d
      · exact hα2d
      · exact hα3d
    · rw [hαtop i hi]
      exact dvd_zero _
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · exact hβ0d
      · exact hβ1d
    · rw [hβtop i hi]
      exact dvd_zero _

/-! ### Case-C kernel count: the graph of an explicit linear section over the depth box -/

private theorem dvd_val_C {k : ℕ} (hk : k ≤ 4) (x : ZMod (3 ^ 4)) :
    ((3 : ℕ) : ZMod (3 ^ 4)) ^ k ∣ x ↔ 3 ^ k ∣ x.val :=
  RestartEquiv.pow_dvd_iff_dvd_val 3 4 hk x

set_option maxRecDepth 100000 in
private theorem boxC_card :
    Nat.card {z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
      ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.2} = 81 := by
  have he : ∀ z : ZMod (3 ^ 4) × ZMod (3 ^ 4),
      (((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.2)
        ↔ (z.1.val % 9 = 0 ∧ z.2.val % 9 = 0) := by
    intro z
    rw [dvd_val_C (by norm_num) z.1, dvd_val_C (by norm_num) z.2]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- **Case-C kernel count** (W4d2′ TODO 2 at cell C): at EVERY pair of cell points the
polynomial kernel has exactly `3⁴ = p^c` elements — the graph of the explicit linear section
`(z₀, z₁) ↦ (α, β) = ((0, (b₁−a₃)z₀, −z₀ + (b₁−a₃)z₁, −z₁), (z₀, z₁))` over the depth box
`{(z₀, z₁) : 3² ∣ z₀, 3² ∣ z₁}`. -/
theorem caseC_ker_card : ∀ A ∈ cSA, ∀ B ∈ cSB,
    Nat.card {q : (ZMod (3 ^ 4))[X] × (ZMod (3 ^ 4))[X] //
      q ∈ polyKer (p := 3) (N := 4) A B 4 2} = 3 ^ 4 := by
  intro A hA B hB
  obtain ⟨hA4, hA5, hA0f, hA1f, hA2f, hA3f⟩ := cSA_facts hA
  obtain ⟨hB2, hB3, hB0f, hB1f⟩ := cSB_facts hB
  obtain ⟨s, hs⟩ := hA0f
  obtain ⟨a1, ha1⟩ := hA1f
  obtain ⟨a2, ha2⟩ := hA2f
  obtain ⟨a3, ha3⟩ := hA3f
  obtain ⟨t, ht⟩ := hB0f
  obtain ⟨u, hu⟩ := hB1f
  have hA0' : A.coeff 0 = 9 + ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 * s := by linear_combination hs
  have hA1' : A.coeff 1 = ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 * a1 := ha1
  have hA2' : A.coeff 2 = -6 + ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 * a2 := by linear_combination ha2
  have hA3' : A.coeff 3 = ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 * a3 := ha3
  have hB0' : B.coeff 0 = -6 + ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 * t := by linear_combination ht
  have hB1' : B.coeff 1 = ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 * u := hu
  have ha0d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ A.coeff 0 := ⟨1 + 3 * s, by rw [hA0']; ring⟩
  have hKCAd : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2
      ∣ B.coeff 1 * (B.coeff 1 - A.coeff 3) - B.coeff 0 + A.coeff 2 :=
    ⟨u * (u - a3) + a2 - t, by rw [hB1', hA3', hB0', hA2']; ring⟩
  have hKCBd : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2
      ∣ B.coeff 0 * (B.coeff 1 - A.coeff 3) + A.coeff 1 :=
    ⟨(-2 + 3 * t) * (u - a3) + a1, by rw [hB0', hB1', hA3', hA1']; ring⟩
  have e : {q : (ZMod (3 ^ 4))[X] × (ZMod (3 ^ 4))[X] //
        q ∈ polyKer (p := 3) (N := 4) A B 4 2}
      ≃ {z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
          ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.2} :=
    { toFun := fun q => ⟨(q.1.2.coeff 0, q.1.2.coeff 1), by
        obtain ⟨hq1, hq2, hq3⟩ := q.2
        have h := caseC_upgrade A hA B hB q.1.1 q.1.2 0 hq1 hq2 hq3
          (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
        exact ⟨h.2 0, h.2 1⟩⟩
      invFun := fun z => ⟨(C 0 + C ((B.coeff 1 - A.coeff 3) * z.1.1) * X
          + C (-z.1.1 + (B.coeff 1 - A.coeff 3) * z.1.2) * X ^ 2 + C (-z.1.2) * X ^ 3,
          C z.1.1 + C z.1.2 * X), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨fun i hi => coeff_cub_top _ _ _ _ hi, fun i hi => coeff_lin_top _ _ hi, ?_⟩
        rw [combo_quad_quart hA4 hA5 hB2 hB3 (fun i hi => coeff_lin_top _ _ hi)
          (fun i hi => coeff_cub_top _ _ _ _ hi)]
        have K0 : A.coeff 0 * z.1.1 = 0 :=
          mul_kill (by norm_num : 4 ≤ 2 + 2) ha0d hz1
        have K1a : (B.coeff 0 * (B.coeff 1 - A.coeff 3) + A.coeff 1) * z.1.1 = 0 :=
          mul_kill (by norm_num : 4 ≤ 2 + 2) hKCBd hz1
        have K1b : A.coeff 0 * z.1.2 = 0 :=
          mul_kill (by norm_num : 4 ≤ 2 + 2) ha0d hz2
        have K2a : (B.coeff 1 * (B.coeff 1 - A.coeff 3) - B.coeff 0 + A.coeff 2) * z.1.1
            = 0 := mul_kill (by norm_num : 4 ≤ 2 + 2) hKCAd hz1
        have K2b : (B.coeff 0 * (B.coeff 1 - A.coeff 3) + A.coeff 1) * z.1.2 = 0 :=
          mul_kill (by norm_num : 4 ≤ 2 + 2) hKCBd hz2
        have K3 : (B.coeff 1 * (B.coeff 1 - A.coeff 3) - B.coeff 0 + A.coeff 2) * z.1.2
            = 0 := mul_kill (by norm_num : 4 ≤ 2 + 2) hKCAd hz2
        ext k
        rcases Nat.lt_or_ge k 6 with hk | hk
        · interval_cases k <;>
            simp only [coeff_quint₀, coeff_quint₁, coeff_quint₂, coeff_quint₃, coeff_quint₄,
              coeff_quint₅, Polynomial.coeff_zero, coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁,
              coeff_cub₂, coeff_cub₃]
          · linear_combination K0
          · linear_combination K1a + K1b
          · linear_combination K2a + K2b
          · linear_combination K3
          · ring
          · ring
        · rw [coeff_quint_top _ _ _ _ _ _ hk, Polynomial.coeff_zero]⟩
      left_inv := fun q => by
        obtain ⟨⟨α, β⟩, hq1, hq2, hq3⟩ := q
        apply Subtype.ext
        dsimp only
        have hup := caseC_upgrade A hA B hB α β 0 hq1 hq2 hq3
          (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
        have hβ0d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ β.coeff 0 := hup.2 0
        have hβ1d : ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ β.coeff 1 := hup.2 1
        rw [combo_quad_quart hA4 hA5 hB2 hB3 hq2 hq1] at hq3
        have e2 : A.coeff 2 * β.coeff 0 + A.coeff 1 * β.coeff 1
            + α.coeff 0 + B.coeff 1 * α.coeff 1 + B.coeff 0 * α.coeff 2 = 0 := by
          have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 2) hq3
          rwa [coeff_quint₂, Polynomial.coeff_zero] at h
        have e3 : A.coeff 3 * β.coeff 0 + A.coeff 2 * β.coeff 1
            + α.coeff 1 + B.coeff 1 * α.coeff 2 + B.coeff 0 * α.coeff 3 = 0 := by
          have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 3) hq3
          rwa [coeff_quint₃, Polynomial.coeff_zero] at h
        have e4 : β.coeff 0 + A.coeff 3 * β.coeff 1 + α.coeff 2 + B.coeff 1 * α.coeff 3
            = 0 := by
          have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 4) hq3
          rwa [coeff_quint₄, Polynomial.coeff_zero] at h
        have e5 : β.coeff 1 + α.coeff 3 = 0 := by
          have h := congrArg (fun P : (ZMod (3 ^ 4))[X] => P.coeff 5) hq3
          rwa [coeff_quint₅, Polynomial.coeff_zero] at h
        have KC3 : (B.coeff 1 * (B.coeff 1 - A.coeff 3) - B.coeff 0 + A.coeff 2) * β.coeff 1
            = 0 := mul_kill (by norm_num : 4 ≤ 2 + 2) hKCAd hβ1d
        have KC2a : (B.coeff 1 * (B.coeff 1 - A.coeff 3) - B.coeff 0 + A.coeff 2) * β.coeff 0
            = 0 := mul_kill (by norm_num : 4 ≤ 2 + 2) hKCAd hβ0d
        have KC2b : (B.coeff 0 * (B.coeff 1 - A.coeff 3) + A.coeff 1) * β.coeff 1 = 0 :=
          mul_kill (by norm_num : 4 ≤ 2 + 2) hKCBd hβ1d
        have hα3eq : α.coeff 3 = -β.coeff 1 := by linear_combination e5
        have hα2eq : α.coeff 2 = -β.coeff 0 + (B.coeff 1 - A.coeff 3) * β.coeff 1 := by
          linear_combination e4 - B.coeff 1 * hα3eq
        have hα1eq : α.coeff 1 = (B.coeff 1 - A.coeff 3) * β.coeff 0 := by
          linear_combination e3 - B.coeff 1 * hα2eq - B.coeff 0 * hα3eq - KC3
        have hα0eq : α.coeff 0 = 0 := by
          linear_combination e2 - B.coeff 1 * hα1eq - B.coeff 0 * hα2eq - KC2a - KC2b
        have h1 : C 0 + C ((B.coeff 1 - A.coeff 3) * β.coeff 0) * X
            + C (-β.coeff 0 + (B.coeff 1 - A.coeff 3) * β.coeff 1) * X ^ 2
            + C (-β.coeff 1) * X ^ 3 = α := by
          rw [← hα1eq, ← hα2eq, ← hα3eq, ← hα0eq]
          exact (eq_cub hq1).symm
        have h2 : C (β.coeff 0) + C (β.coeff 1) * X = β := (eq_lin hq2).symm
        rw [h1, h2]
      right_inv := fun z => by
        apply Subtype.ext
        dsimp only
        rw [coeff_lin₀, coeff_lin₁] }
  rw [Nat.card_congr e]
  exact boxC_card

/-! ### Case-C coset cards -/

set_option maxRecDepth 100000 in
private theorem cosetC_SA1_card :
    Nat.card {z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
      ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ z.1 - 9 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.2} = 27 := by
  have he : ∀ z : ZMod (3 ^ 4) × ZMod (3 ^ 4),
      (((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ z.1 - 9 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.2)
        ↔ ((z.1 - 9).val % 27 = 0 ∧ z.2.val % 9 = 0) := by
    intro z
    rw [dvd_val_C (by norm_num) (z.1 - 9), dvd_val_C (by norm_num) z.2]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

set_option maxRecDepth 100000 in
private theorem cosetC_quad_card :
    Nat.card {z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
      ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 + 6 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ z.2}
      = 243 := by
  have he : ∀ z : ZMod (3 ^ 4) × ZMod (3 ^ 4),
      (((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 + 6 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ z.2)
        ↔ ((z.1 + 6).val % 9 = 0 ∧ z.2.val % 3 = 0) := by
    intro z
    rw [dvd_val_C (by norm_num) (z.1 + 6), dvd_val_C (by norm_num) z.2]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- The x-slot box bijection for the case-C quartic coset (split as a product of two
coefficient pairs — the `(2,3)`-pair condition is the same `(+6, ·)` box as the decided
block's). -/
private noncomputable def cSAEquiv :
    ↥cSA ≃ ({z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
        ((3 : ℕ) : ZMod (3 ^ 4)) ^ 3 ∣ z.1 - 9 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.2}
      × {z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
        ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 + 6 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ z.2}) where
  toFun P :=
    (⟨(P.1.coeff 0, P.1.coeff 1),
      (cSA_facts P.2).2.2.1, (cSA_facts P.2).2.2.2.1⟩,
     ⟨(P.1.coeff 2, P.1.coeff 3),
      (cSA_facts P.2).2.2.2.2.1, (cSA_facts P.2).2.2.2.2.2⟩)
  invFun zw := ⟨X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
      + C zw.2.1.2 * X ^ 3), by
    have hmd := monic_add_of_coeff (Polynomial.monic_X_pow 4)
      (Polynomial.natDegree_X_pow 4)
      (fun i hi => coeff_cub_top zw.1.1.1 zw.1.1.2 zw.2.1.1 zw.2.1.2 hi)
    refine ⟨hmd.1, hmd.2, fun i => ?_⟩
    rcases Nat.lt_or_ge i 5 with hi | hi
    · interval_cases i
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - cA₀).coeff 0 = zw.1.1.1 - 9 := by
          have hc : cA₀.coeff 0 = 9 := coeff_quart₀ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₀, hc]
        rw [he]
        exact zw.1.2.1
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - cA₀).coeff 1 = zw.1.1.2 := by
          have hc : cA₀.coeff 1 = 0 := coeff_quart₁ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₁, hc, sub_zero]
        rw [he]
        exact zw.1.2.2
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - cA₀).coeff 2 = zw.2.1.1 + 6 := by
          have hc : cA₀.coeff 2 = -6 := coeff_quart₂ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₂, hc]
          ring
        rw [he]
        exact zw.2.2.1
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - cA₀).coeff 3 = zw.2.1.2 := by
          have hc : cA₀.coeff 3 = 0 := coeff_quart₃ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₃, hc, sub_zero]
        rw [he]
        exact zw.2.2.2
      · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
              + C zw.2.1.2 * X ^ 3)) - cA₀).coeff 4 = 0 := by
          have hc : cA₀.coeff 4 = 1 := coeff_quart₄ _ _ _ _
          rw [Polynomial.coeff_sub, coeff_quart₄, hc, sub_self]
        rw [he]
        exact dvd_zero _
    · have he : ((X ^ 4 + (C zw.1.1.1 + C zw.1.1.2 * X + C zw.2.1.1 * X ^ 2
            + C zw.2.1.2 * X ^ 3)) - cA₀).coeff i = 0 := by
        have hc : cA₀.coeff i = 0 := coeff_quart_top _ _ _ _ hi
        rw [Polynomial.coeff_sub, coeff_quart_top _ _ _ _ hi, hc, sub_self]
      rw [he]
      exact dvd_zero _⟩
  left_inv P := by
    apply Subtype.ext
    dsimp only
    obtain ⟨h4, h5, -, -, -, -⟩ := cSA_facts P.2
    exact (eq_quart h4 h5).symm
  right_inv zw := by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      dsimp only
      rw [coeff_quart₀, coeff_quart₁]
    · apply Subtype.ext
      dsimp only
      rw [coeff_quart₂, coeff_quart₃]

/-- The x-slot box bijection for the case-C quadratic coset. -/
private noncomputable def cSBEquiv :
    ↥cSB ≃ {z : ZMod (3 ^ 4) × ZMod (3 ^ 4) //
      ((3 : ℕ) : ZMod (3 ^ 4)) ^ 2 ∣ z.1 + 6 ∧ ((3 : ℕ) : ZMod (3 ^ 4)) ^ 1 ∣ z.2} where
  toFun P := ⟨(P.1.coeff 0, P.1.coeff 1), by
    obtain ⟨-, -, h0, h1⟩ := cSB_facts P.2
    exact ⟨h0, h1⟩⟩
  invFun z := ⟨X ^ 2 + (C z.1.1 + C z.1.2 * X), by
    have hmd := monic_add_of_coeff (Polynomial.monic_X_pow 2)
      (Polynomial.natDegree_X_pow 2) (fun i hi => coeff_lin_top z.1.1 z.1.2 hi)
    refine ⟨hmd.1, hmd.2, fun i => ?_⟩
    rcases Nat.lt_or_ge i 3 with hi | hi
    · interval_cases i
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - cB₀).coeff 0 = z.1.1 + 6 := by
          have hc : cB₀.coeff 0 = -6 := coeff_quad₀ _ _
          rw [Polynomial.coeff_sub, coeff_quad₀, hc]
          ring
        rw [he]
        exact z.2.1
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - cB₀).coeff 1 = z.1.2 := by
          have hc : cB₀.coeff 1 = 0 := coeff_quad₁ _ _
          rw [Polynomial.coeff_sub, coeff_quad₁, hc, sub_zero]
        rw [he]
        exact z.2.2
      · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - cB₀).coeff 2 = 0 := by
          have hc : cB₀.coeff 2 = 1 := coeff_quad₂ _ _
          rw [Polynomial.coeff_sub, coeff_quad₂, hc, sub_self]
        rw [he]
        exact dvd_zero _
    · have he : ((X ^ 2 + (C z.1.1 + C z.1.2 * X)) - cB₀).coeff i = 0 := by
        have hc : cB₀.coeff i = 0 := coeff_quad_top _ _ hi
        rw [Polynomial.coeff_sub, coeff_quad_top _ _ hi, hc, sub_self]
      rw [he]
      exact dvd_zero _⟩
  left_inv P := by
    apply Subtype.ext
    dsimp only
    obtain ⟨h2, h3, -, -⟩ := cSB_facts P.2
    exact (eq_quad h2 h3).symm
  right_inv z := by
    apply Subtype.ext
    dsimp only
    rw [coeff_quad₀, coeff_quad₁]

/-- Coset card `|P₁| = 6561 = 3^8` — agrees with `card_freshPattern` at `(3,4,2,2)`. -/
theorem caseC_card_SA : Nat.card cSA = 6561 := by
  rw [Nat.card_congr cSAEquiv, Nat.card_prod, cosetC_SA1_card, cosetC_quad_card]

/-- Coset card `|P₂| = 243 = 3^5` — agrees with `card_freshPattern` at `(3,4,2,1)`. -/
theorem caseC_card_SB : Nat.card cSB = 243 :=
  (Nat.card_congr cSBEquiv).trans cosetC_quad_card

/-! ### The case-C end-to-end law THROUGH the graded ladder -/

/-- **Case C, THE LAW, derived THROUGH the graded pair law**: at the real gate cell — where
the flat margins are provably empty (`BlockProduct.gate_margin_C`) — the pointwise
certificates give `card(image) · 3⁴ = |P₁| · |P₂|`. -/
theorem caseC_law_graded :
    Nat.card ((fun AB : (ZMod (3 ^ 4))[X] × (ZMod (3 ^ 4))[X] => AB.1 * AB.2) ''
        (cSA ×ˢ cSB)) * 3 ^ 4
      = Nat.card cSA * Nat.card cSB :=
  pair_card_graded (p := 3) (N := 4) (c := 4) (floA := cFloA) (floB := cFloB)
    (by norm_num) subset_rfl (patternCell_saturatedAt hM1C₁) subset_rfl
    (patternCell_saturatedAt hM1C₂) hM2C hqbC caseC_upgrade caseC_ker_card

/-- The fiber card forced THROUGH the graded ladder: `19683` fibers. -/
theorem caseC_image_card :
    Nat.card ((fun AB : (ZMod (3 ^ 4))[X] × (ZMod (3 ^ 4))[X] => AB.1 * AB.2) ''
      (cSA ×ˢ cSB)) = 19683 := by
  have h := caseC_law_graded
  rw [caseC_card_SA, caseC_card_SB] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3 ^ 4)
    (h.trans (by norm_num : (6561 : ℕ) * 243 = 19683 * 3 ^ 4))

/-- **Cross-check against the banked closed form `BlockProduct.gateC_coset_product`**
(`3¹³ = 19683 · 3⁴`): the graded-ladder law meets the `card_freshPattern` product. -/
theorem caseC_matches_gateC :
    Nat.card ((fun AB : (ZMod (3 ^ 4))[X] × (ZMod (3 ^ 4))[X] => AB.1 * AB.2) ''
        (cSA ×ˢ cSB)) * 3 ^ 4
      = Nat.card {β : Fin 2 → RphiRing.Rphi 3 4 2 1 1 //
          RestartEquiv.FreshClusterPattern 3 4 2 2 1 β}
        * Nat.card {β : Fin 1 → RphiRing.Rphi 3 4 2 1 cC₂ //
            RestartEquiv.FreshClusterPattern 3 4 2 1 cC₂ β} := by
  rw [caseC_image_card, BlockProduct.gateC_coset_product]

/-! ### The case-C `GradedChain` and the discharge of `h_node1_general` -/

/-- Case-C first block: the `(y−1)²` child. -/
noncomputable def blockC₁ : Block 3 4 := ⟨cA₀, 4, cSA⟩

/-- Case-C second block: the decided `(y−2)` block. -/
noncomputable def blockC₂ : Block 3 4 := ⟨cB₀, 2, cSB⟩

/-- **The case-C graded chain certificate.** -/
theorem caseC_chain : GradedChain [blockC₁, blockC₂] 4 := by
  have h2 : GradedChain [blockC₂] 0 := by
    have h := GradedChain.cons (p := 3) (N := 4) (l := []) (X := 0) blockC₂ 0
      cFloB (fun _ => 0) cDepB (fun _ => 0) cDepB cB₀ 1 (by norm_num)
      subset_rfl (patternCell_saturatedAt hM1C₂)
      (imageSet_nil_subset_patternCell (fun _ => 0)) (imageSet_nil_saturatedAt (fun _ => 0))
      (fun s t _ ht => absurd ht (Nat.not_lt_zero t))
      (fun s t _ ht => absurd ht (Nat.not_lt_zero t))
      (fun A hA B hB => by
        have hB1 : B = 1 := hB
        rw [hB1]
        exact gradedUpgradeAt_one A 2 cDepB (fun _ => 0))
      (fun A hA B hB => by
        have hB1 : B = 1 := hB
        rw [hB1]
        exact polyKer_one_card A 2)
      GradedChain.nil
    exact h
  have h1 := GradedChain.cons (p := 3) (N := 4) (l := [blockC₂]) (X := 0) blockC₁ 4
    cFloA cFloB cDepA cDepB cQb cA₀ cB₀ (by norm_num)
    subset_rfl (patternCell_saturatedAt hM1C₁)
    (by rw [imageSet_singleton]; exact subset_rfl)
    (by rw [imageSet_singleton]; exact patternCell_saturatedAt hM1C₂)
    hM2C hqbC
    (fun A hA B hB => by
      rw [imageSet_singleton] at hB
      exact caseC_upgrade A hA B hB)
    (fun A hA B hB => by
      rw [imageSet_singleton] at hB
      exact caseC_ker_card A hA B hB)
    h2
  exact h1

/-- **`h_node1_general` DISCHARGED at gate cell C** (W4d2′ TODO 4, case C): the block-product
IMAGE obeys the em-square law `#(imageSet) · 3⁴ = 3^(8+5) = 3¹³` — case-C hypothesis gate closed
by `caseC_chain` + the coset-card certificates.  SCOPE: as in `h_node1_at_A`, `imageSet` is the
block-product image, not the classifier multi-block fiber; the identification is the named
obligation **W4d2-surj** (gate-verified d2-0, not yet formalized). -/
theorem h_node1_at_C :
    Nat.card (imageSet [blockC₁, blockC₂]) * 3 ^ 4 = 3 ^ 13 := by
  have h := HNode1.h_node1_general 3 4 caseC_chain
    (fun b => if b.deg = 4 then 8 else 5)
    (by
      intro b hb
      rcases List.mem_cons.mp hb with h1 | h1
      · subst h1
        exact caseC_card_SA.trans (by decide)
      · rcases List.mem_cons.mp h1 with h2 | h2
        · subst h2
          exact caseC_card_SB.trans (by decide)
        · simp at h2)
  exact h

/-- The block-product IMAGE count at cell C, through the chain: `19683` — matches
`caseC_image_card`.  (Not the classifier multi-block fiber; see `h_node1_at_C` scope note and
the named obligation W4d2-surj.) -/
theorem caseC_node_census : Nat.card (imageSet [blockC₁, blockC₂]) = 19683 := by
  have h := h_node1_at_C
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3 ^ 4)
    (h.trans (by norm_num : (3 : ℕ) ^ 13 = 19683 * 3 ^ 4))

end GateC

end LeanUrat.OM.GradedCertificates
