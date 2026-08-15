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

section AxCheck
#print axioms Uniformity.Density.Induction.alpha_geom_partial_le_one
end AxCheck

end Uniformity.Density.Induction
