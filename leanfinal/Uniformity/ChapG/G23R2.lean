/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G23R2 — the digit-read lemmas: `π ^ j · y` determines `ȳ`, and conversely

**Chapter G, NODE G.23R2** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The replacement route keys strata by the *digit*
`ȳ = y mod 𝔪` of a value written `π ^ j · y`. Two facts make that read well posed:

* **uniqueness** (`residue_eq_of_mk_pow_mul_eq`): as soon as `j < N`, the class of `π ^ j · y`
  in `Res O N` determines `ȳ`;
* **realization** (`mk_pow_mul_eq_of_residue_eq`): at the exact level `N ≤ j + 1` the digit
  determines the class, so the level-`(j+1)` read is a bijection onto its image.

Together they are the reason the route's TOP-level set `resTop` (G.23R4) has exactly `#𝒫`
elements (G.23R5) while its level-`N` preimage carries the free lower digits.

DEPENDS: landed `mem_maximalIdeal_pow_iff_dvd`, `mem_maximalIdeal_iff_dvd`
(`Drainage.lean:635,192`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **Digit uniqueness.** Below the level `N`, the class of `π ^ j · y` determines `y mod 𝔪`. -/
theorem residue_eq_of_mk_pow_mul_eq (hπ : Irreducible π) {j N : ℕ} (hj : j < N) {y y' : O}
    (h : (Ideal.Quotient.mk _ (π ^ j * y) : Res O N) = Ideal.Quotient.mk _ (π ^ j * y')) :
    IsLocalRing.residue O y = IsLocalRing.residue O y' := by
  have hdvd : π ^ N ∣ (π ^ j * y - π ^ j * y') :=
    (mem_maximalIdeal_pow_iff_dvd hπ N _).1 (Ideal.Quotient.eq.1 h)
  have hfac : π ^ N = π ^ j * π ^ (N - j) := by rw [← pow_add]; congr 1; omega
  rw [hfac, ← mul_sub] at hdvd
  have hcancel : π ^ (N - j) ∣ (y - y') :=
    (mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)).1 hdvd
  exact Ideal.Quotient.eq.2 ((mem_maximalIdeal_iff_dvd hπ _).2
    (dvd_trans (dvd_pow_self π (by omega : N - j ≠ 0)) hcancel))

/-- **Digit realization.** At the exact level `N ≤ j + 1`, equal digits give equal classes. -/
theorem mk_pow_mul_eq_of_residue_eq (hπ : Irreducible π) {j N : ℕ} (hN : N ≤ j + 1) {y y' : O}
    (h : IsLocalRing.residue O y = IsLocalRing.residue O y') :
    (Ideal.Quotient.mk _ (π ^ j * y) : Res O N) = Ideal.Quotient.mk _ (π ^ j * y') := by
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_iff_dvd hπ _).1 (Ideal.Quotient.eq.1 h)
  refine Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd hπ N _).2 ?_)
  rw [← mul_sub, hc]
  exact dvd_trans (pow_dvd_pow π hN) ⟨c, by rw [pow_succ]; ring⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.residue_eq_of_mk_pow_mul_eq
#print axioms Uniformity.Density.Menu.mk_pow_mul_eq_of_residue_eq

end AxCheck
