/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.MovesU.O12PoleFree

/-!
# Scaffold/O12/Core — q, E_e, κ₀/κ₁ shared arithmetic [BP_II units II-C1..C4]

Movement II core definitions (blueprint `lean/blueprints/BP_II.md` §1.1; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.2, §2.4).

This file carries **unit II-C1**: the transcribed definitions `qX`, `blockE`,
`kappa0`, `kappa1`. Units II-C2..C4 (the arithmetic lemmas `blockE_ge_three`,
`two_le_blockE_sub_one`, `kappa_add`, `gram_kappa0/1`) extend this module.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- The ambient field of symbolic rational functions in q (brief §2.2). -/
abbrev Qq := RatFunc ℚ

noncomputable def qX : Qq := algebraMap (Polynomial ℚ) Qq Polynomial.X

/-- `E_e = e(e+1)/2 = 1 + 2 + ⋯ + e` (brief §2.2). -/
def blockE (e : ℕ) : ℕ := e * (e + 1) / 2

theorem blockE_ge_three {e : ℕ} (he : 2 ≤ e) : 3 ≤ blockE e := by
  rw [blockE, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  calc 3 * 2 = 2 * 3 := by norm_num
    _ ≤ e * (e + 1) := Nat.mul_le_mul he (by omega)

theorem two_le_blockE_sub_one {e : ℕ} (he : 2 ≤ e) : 2 ≤ blockE e - 1 := by
  have h := blockE_ge_three he
  omega

/-- κ₀ = q^{−E} (the in-place loop mass, symbolic; brief §2.4). -/
noncomputable def kappa0 (e : ℕ) : Qq := (qX ^ blockE e)⁻¹

/-- κ₁ = (q−1)·q^{−E} (the recentering mass, symbolic). -/
noncomputable def kappa1 (e : ℕ) : Qq := (qX - 1) * (qX ^ blockE e)⁻¹

/-- κ₀ + κ₁ = q^{1−E} (Theorem 1(1)'s scalar). [BP_II unit II-C3] -/
theorem kappa_add (e : ℕ) : kappa0 e + kappa1 e = qX * (qX ^ blockE e)⁻¹ := by
  unfold kappa0 kappa1
  ring

/-! ## Unit II-C4: `q`-power helpers and the 𝒢-membership of κ₀/κ₁ -/

/-- `q ≠ 0` in `Qq` (II-C4 helper). -/
theorem qX_ne_zero : qX ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

/-- `q^n ≠ 0` in `Qq` (II-C4 helper). -/
theorem qX_pow_ne_zero (n : ℕ) : qX ^ n ≠ 0 :=
  pow_ne_zero n qX_ne_zero

/-- `q^n` is the image of the polynomial `X^n` (transport helper for the
`Gram.poly`/`Gram.invS` composites). -/
theorem qX_pow_eq_algebraMap (n : ℕ) :
    qX ^ n = algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ n) := by
  rw [qX, map_pow]

/-- κ₀ is 𝒢-generated: `q^{−E} = (algebraMap (X^E))⁻¹` is a `Gram.invS` atom via
`Xpow_mem_cycS` (brief §2.3 (g2)). [BP_II unit II-C4] -/
theorem gram_kappa0 (e : ℕ) : Gram (kappa0 e) := by
  rw [kappa0, qX_pow_eq_algebraMap]
  exact Gram.invS (LeanUrat.MovesU.Xpow_mem_cycS (blockE e))

/-- κ₁ is 𝒢-generated: `(q−1)·q^{−E}` is the `Gram.mul` of the `Gram.poly` atom
`X − 1` with κ₀ (brief §2.3 (g2)). [BP_II unit II-C4] -/
theorem gram_kappa1 (e : ℕ) : Gram (kappa1 e) := by
  have h1 : qX - 1 = algebraMap (Polynomial ℚ) Qq (Polynomial.X - 1) := by
    rw [map_sub, map_one, qX]
  rw [kappa1, h1, ← kappa0]
  exact Gram.mul (Gram.poly _) (gram_kappa0 e)

end LeanUrat.Scaffold
