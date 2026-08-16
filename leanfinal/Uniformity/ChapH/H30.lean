/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H30 — the α-leg's geometric sum

**Chapter H, NODE H.30** (`blueprint/CHAP-H_general_induction.md` §6). *The α-leg's geometric
sum.* For `2 ≤ Q`, `1 ≤ c` and every `n`, in `ℝ`:

`Σ_{k<n} (Q−1) · Q^(−c·(k+1)) ≤ 1`.

This is the corpus's `Σ_{k≥1} (Q−1) Q^{−k·c(m)} ≤ 1 for c(m) ≥ 1`, stated as a partial sum. The
side condition is exactly `Q ≤ Q^c`, which is where `1 ≤ c` enters and nowhere else.

DEPENDS: none (pure real arithmetic; ENV-H1).

**SOURCE.** `EFF.GENIND.153` (`ANNEX-THEOREM GENIND.C′`'s α-leg, verbatim:
*"`Σ_{k≥1}(Q−1)Q^{−k·c(m)} ≤ 1` for `c(m) ≥ 1`"*), with the spec's audit
*"requires `(Q−1)·Q^{−c(m)}/(1−Q^{−c(m)}) ≤ 1` ⟺ `(Q−1) ≤ Q^{c(m)} − 1` ⟺ `Q ≤ Q^{c(m)}` ✓"*.

**TIGHTNESS.** The bound is attained in the limit at `c = 1` (`m = 2`, the chapter's ground
instance): `(Q−1)/Q + (Q−1)/Q² + … → 1`. So the non-strict partial-sum form is the correct
statement, and the hypothesis is at its true minimum `1 ≤ c` (not `2 ≤ c`).

**PROOF.** Write `r := (Q^c)⁻¹`, so the `k`-th term is `(Q−1)·r^(k+1)` (`pow_mul`, `inv_pow`).
The side condition `Q ≤ Q^c` gives `Q·r ≤ 1`, hence the one-step inequality
`(Q−1)·r ≤ 1 − r`. Induction on `n` then proves the *sharpened* statement
`Σ_{k<n} (Q−1)·r^(k+1) ≤ 1 − r^n` (the successor step multiplies the one-step inequality by
`r^m ≥ 0`), and `r^n ≥ 0` finishes. No `geom_sum` lemma is needed: the telescoping form
`1 − r^n` carries the induction by itself.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- *The α-leg's geometric sum.* For `2 ≤ Q` and `1 ≤ c`, every partial sum of
`Σ_k (Q−1)·Q^(−c·(k+1))` is at most `1`. Tight in the limit at `c = 1`. -/
theorem alpha_geom_partial_le_one (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ ≤ 1 := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < (Q:ℝ) := by linarith
  have hpc : (0:ℝ) < (Q:ℝ) ^ c := pow_pos hQ0 c
  set r : ℝ := ((Q:ℝ) ^ c)⁻¹ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  -- the side condition: `Q ≤ Q ^ c`, which is exactly where `1 ≤ c` is used
  have hle : (Q:ℝ) ≤ (Q:ℝ) ^ c := by
    have h : Q ≤ Q ^ c := Nat.le_self_pow (by omega) Q
    exact_mod_cast h
  have h1 : (Q:ℝ) * r ≤ 1 := by
    rw [hrdef, ← div_eq_mul_inv]
    exact (div_le_one hpc).mpr hle
  -- the one-step inequality `(Q−1)·r ≤ 1 − r`
  have hkey : ((Q:ℝ) - 1) * r ≤ 1 - r := by
    have hexp : ((Q:ℝ) - 1) * r = (Q:ℝ) * r - r := by ring
    rw [hexp]
    linarith
  -- the sharpened statement, which is what actually carries the induction
  have main : ∀ m : ℕ, ∑ k ∈ Finset.range m, ((Q:ℝ) - 1) * r ^ (k+1) ≤ 1 - r ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hrm : (0:ℝ) ≤ r ^ m := pow_nonneg hr0 m
      have hstep : ((Q:ℝ) - 1) * r ^ (m+1) ≤ r ^ m * (1 - r) := by
        have hre : ((Q:ℝ) - 1) * r ^ (m+1) = r ^ m * (((Q:ℝ) - 1) * r) := by ring
        rw [hre]
        exact mul_le_mul_of_nonneg_left hkey hrm
      have hpw : r ^ (m+1) = r ^ m * r := by ring
      rw [hpw]
      nlinarith [hstep]
  have hterm : ∀ k : ℕ, ((Q : ℝ) ^ (c * (k + 1)))⁻¹ = r ^ (k+1) := by
    intro k
    rw [hrdef, pow_mul, inv_pow]
  calc ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹
      = ∑ k ∈ Finset.range n, ((Q:ℝ) - 1) * r ^ (k+1) :=
        Finset.sum_congr rfl fun k _ => by rw [hterm k]
    _ ≤ 1 - r ^ n := main n
    _ ≤ 1 := by have := pow_nonneg hr0 n; linarith

/-! ## 2. NODE H.30b — the same sum, sharpened at `c ≥ 2`

**Chapter H, NODE H.30b** (AMENDMENT A-H.6 §6). H.30's `1` is TIGHT at `c = 1` (i.e. at
`m = 2`, where `clusterC 2 = 1`), so H.30 is NOT retired; but H.122's `m = 3` leg fires at
`clusterC 3 = 3 ≥ 2`, and there the induction only closes with the sharpened constant `1/3`:
with H.30's `Σ ≤ 1` the closing display `1 + (N−3) + N/3 ≤ N` is FALSE from `N = 4` on, while
with `Σ ≤ 1/3` the display `1 + (N−3)⁺/3 + N/3 ≤ N` holds.

The true value of the full sum is `(Q−1)/(Q^c − 1) ≤ 1/(Q+1)`; `1/3` is the `Q`-uniform
literal and is TIGHT at `(Q, c) = (2, 2)`, where `(Q−1)/(Q^c−1) = 1/3` exactly.

**PROOF.** H.30's skeleton verbatim, with the one-step inequality strengthened from
`(Q−1)·r ≤ 1 − r` to `(Q−1)·r ≤ (1/3)·(1 − r)`, i.e. to `3(Q−1) ≤ Q^c − 1`. That is where
`2 ≤ c` enters and nowhere else: `Q^c ≥ Q²` gives `Q^c − 1 − 3(Q−1) ≥ (Q−1)(Q−2) ≥ 0`.
The induction then carries the sharpened telescoped form `Σ_{k<n} ≤ (1/3)(1 − r^n)`.

TEETH: `verification/AH6_beta_envelope_check.py` check `E1` (`2 ≤ c ≤ 11`, `q ∈ {2,3}`, exact).
-/

/-- **H.30b [A-H.6 §6].** *H.30, sharpened where the slope has room.* For `2 ≤ Q` and
`2 ≤ c`, every partial sum of `Σ_k (Q−1)·Q^(−c·(k+1))` is at most `1/3`. Tight at
`(Q, c) = (2, 2)`. H.30 (`alpha_geom_partial_le_one`) stays live: its `1` is the true value
at `c = 1`, which is the `m = 2` leg's slope constant. -/
theorem alpha_geom_partial_le_third (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 2 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ ≤ 1 / 3 := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < (Q:ℝ) := by linarith
  have hpc : (0:ℝ) < (Q:ℝ) ^ c := pow_pos hQ0 c
  set r : ℝ := ((Q:ℝ) ^ c)⁻¹ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  -- the side condition, sharpened: `3(Q−1) ≤ Q^c − 1`, which is where `2 ≤ c` is used
  have hle : (Q:ℝ) ^ 2 ≤ (Q:ℝ) ^ c := by
    have h : Q ^ 2 ≤ Q ^ c := Nat.pow_le_pow_right (by omega) hc
    exact_mod_cast h
  have h1 : 3 * ((Q:ℝ) - 1) ≤ (Q:ℝ) ^ c - 1 := by
    have hsq : (Q:ℝ) ^ 2 = (Q:ℝ) * (Q:ℝ) := by ring
    nlinarith [hle, hsq]
  -- the one-step inequality `(Q−1)·r ≤ (1/3)·(1 − r)`
  have hrc : (Q:ℝ) ^ c * r = 1 := mul_inv_cancel₀ (ne_of_gt hpc)
  have hkey : ((Q:ℝ) - 1) * r ≤ (1/3) * (1 - r) := by
    have hmul : 3 * ((Q:ℝ) - 1) * r ≤ ((Q:ℝ) ^ c - 1) * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr0
    have hexp : ((Q:ℝ) ^ c - 1) * r = 1 - r := by rw [sub_mul, hrc, one_mul]
    linarith
  -- the sharpened telescoped statement, which carries the induction
  have main : ∀ j : ℕ, ∑ k ∈ Finset.range j, ((Q:ℝ) - 1) * r ^ (k+1) ≤ (1/3) * (1 - r ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have hrm : (0:ℝ) ≤ r ^ j := pow_nonneg hr0 j
      have hstep : ((Q:ℝ) - 1) * r ^ (j+1) ≤ r ^ j * ((1/3) * (1 - r)) := by
        have hre : ((Q:ℝ) - 1) * r ^ (j+1) = r ^ j * (((Q:ℝ) - 1) * r) := by ring
        rw [hre]
        exact mul_le_mul_of_nonneg_left hkey hrm
      have hpw : r ^ (j+1) = r ^ j * r := by ring
      rw [hpw]
      nlinarith [hstep]
  have hterm : ∀ k : ℕ, ((Q : ℝ) ^ (c * (k + 1)))⁻¹ = r ^ (k+1) := by
    intro k
    rw [hrdef, pow_mul, inv_pow]
  calc ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹
      = ∑ k ∈ Finset.range n, ((Q:ℝ) - 1) * r ^ (k+1) :=
        Finset.sum_congr rfl fun k _ => by rw [hterm k]
    _ ≤ (1/3) * (1 - r ^ n) := main n
    _ ≤ 1 / 3 := by have := pow_nonneg hr0 n; nlinarith

section AxCheck
#print axioms Uniformity.Density.Induction.alpha_geom_partial_le_one
#print axioms Uniformity.Density.Induction.alpha_geom_partial_le_third
end AxCheck

end Uniformity.Density.Induction
