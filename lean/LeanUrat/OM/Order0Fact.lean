/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.OMType

/-!
# Order-0 factorization facts (blueprint HNODE0 §1, node γ4)

Structural facts about `M4.ResidualFactorization R` (the GAP-1 coprime factorization structure of
`LeanUrat/OM/ResidualPolynomial.lean`):

* `mem_factors_iff` — for `R ≠ 0`, membership in `F.factors` is EXACTLY "monic irreducible divisor
  of `R`" (so the factor `Finset` is canonical, independent of the choice of `F`).
* `mult_eq_one_of_squarefree` — a squarefree `R` forces every multiplicity to `1`.
* `factors_eq_normalizedFactors_toFinset` / `degrees_multiset` — for squarefree monic `R` the
  factor set is `(normalizedFactors R).toFinset` and the factor-degree multiset is the canonical
  `(normalizedFactors R).map natDegree`.
* `cells_childless_of_squarefree` — squarefree `T.Rr` makes every `M5.cells T` cell childless
  (the `2 ≤ mult ψ` descent guard never fires).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.Order0

open Polynomial

open scoped Classical

variable {kS : Type*} [Field kS] [Finite kS]

/-- **Any factor's prime power divides `R`** (the `M5.cells` divisibility chain, factored out):
for `ψ ∈ F.factors`, `ψ ^ F.mult ψ ∣ R` via `prod_eq`. -/
theorem pow_mult_dvd {R : kS[X]} (F : M4.ResidualFactorization R) {ψ : kS[X]}
    (hψ : ψ ∈ F.factors) : ψ ^ F.mult ψ ∣ R := by
  have hdvdprod : ψ ^ F.mult ψ ∣ ∏ φ ∈ F.factors, φ ^ F.mult φ :=
    Finset.dvd_prod_of_mem (fun φ => φ ^ F.mult φ) hψ
  exact (hdvdprod.mul_left _).trans (dvd_of_eq F.prod_eq.symm)

/-- **Any factor divides `R`**: `ψ ∣ ψ ^ mult ψ ∣ R` using `mult_pos`. -/
theorem factor_dvd {R : kS[X]} (F : M4.ResidualFactorization R) {ψ : kS[X]}
    (hψ : ψ ∈ F.factors) : ψ ∣ R :=
  dvd_trans (dvd_pow_self ψ (by have := F.mult_pos ψ hψ; omega)) (pow_mult_dvd F hψ)

/-- **Item 1: the factor `Finset` is canonical.** For `R ≠ 0`, `ψ ∈ F.factors` iff `ψ` is a monic
irreducible divisor of `R`. Forward: monic/irreducible are structure fields, divisibility is the
`dvd_pow_self`/`Finset.dvd_prod_of_mem` chain. Backward: `C R.leadingCoeff` is a unit (`R ≠ 0` over
a field), so a monic irreducible (hence prime, `Irreducible.prime` in the UFD `kS[X]`) divisor `ψ`
of `R` divides `∏ φ ^ mult φ`, hence some `φ ^ mult φ` (`Prime.exists_mem_finset_dvd`), hence some
`φ ∈ F.factors` (`Prime.dvd_of_dvd_pow`); two associated monic polynomials are equal
(`Irreducible.dvd_irreducible_iff_associated` + `Polynomial.eq_of_monic_of_associated`). -/
theorem mem_factors_iff (R : kS[X]) (hR : R ≠ 0) (F : M4.ResidualFactorization R)
    (ψ : kS[X]) : ψ ∈ F.factors ↔ (ψ.Monic ∧ Irreducible ψ ∧ ψ ∣ R) := by
  constructor
  · intro hψ
    exact ⟨F.factors_monic ψ hψ, F.factors_irreducible ψ hψ, factor_dvd F hψ⟩
  · rintro ⟨hmon, hirr, hdvd⟩
    have hprime : Prime ψ := hirr.prime
    -- `C R.leadingCoeff` is a unit
    have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR
    have hu : IsUnit (Polynomial.C R.leadingCoeff) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc)
    -- `ψ ∣ C lc * ∏ φ^mult φ`; by primality it divides one of the two, and not the unit
    have hdvd' : ψ ∣ Polynomial.C R.leadingCoeff * ∏ φ ∈ F.factors, φ ^ F.mult φ := by
      rw [← F.prod_eq]; exact hdvd
    have hprod : ψ ∣ ∏ φ ∈ F.factors, φ ^ F.mult φ := by
      rcases hprime.2.2 _ _ hdvd' with h | h
      · exact absurd (isUnit_of_dvd_unit h hu) hirr.not_isUnit
      · exact h
    -- pick the factor `φ` whose power `ψ` divides
    obtain ⟨φ, hφmem, hψφpow⟩ := hprime.exists_mem_finset_dvd hprod
    have hψφ : ψ ∣ φ := hprime.dvd_of_dvd_pow hψφpow
    have hφirr : Irreducible φ := F.factors_irreducible φ hφmem
    have hφmon : φ.Monic := F.factors_monic φ hφmem
    have hassoc : Associated ψ φ := (hirr.dvd_irreducible_iff_associated hφirr).mp hψφ
    have : ψ = φ := Polynomial.eq_of_monic_of_associated hmon hφmon hassoc
    rwa [this]

/-- **Item 2: squarefree `R` forces multiplicity 1.** If `2 ≤ mult ψ` then `ψ * ψ ∣ ψ ^ mult ψ ∣ R`
contradicts `Squarefree R` (`ψ` is not a unit, being irreducible); `mult_pos` then pins `mult ψ = 1`. -/
theorem mult_eq_one_of_squarefree (R : kS[X]) (hsq : Squarefree R)
    (F : M4.ResidualFactorization R) : ∀ ψ ∈ F.factors, F.mult ψ = 1 := by
  intro ψ hψ
  have hpos := F.mult_pos ψ hψ
  by_contra hne
  have h2 : 2 ≤ F.mult ψ := by omega
  have hψ2 : ψ * ψ ∣ R := by
    have := (pow_dvd_pow ψ h2).trans (pow_mult_dvd F hψ)
    rwa [pow_two] at this
  exact (F.factors_irreducible ψ hψ).not_isUnit (hsq ψ hψ2)

/-- **Item 3 (finset form): the factor set IS the normalized-factor set.** For `R ≠ 0`,
`F.factors = (normalizedFactors R).toFinset`: both sides are exactly the monic irreducible divisors
of `R` (`mem_factors_iff` vs `Polynomial.mem_normalizedFactors_iff`). -/
theorem factors_eq_normalizedFactors_toFinset (R : kS[X]) (hR : R ≠ 0)
    (F : M4.ResidualFactorization R) :
    F.factors = (UniqueFactorizationMonoid.normalizedFactors R).toFinset := by
  ext ψ
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hR,
    mem_factors_iff R hR F ψ]
  tauto

/-- **Item 3 (multiset form): the factor-degree multiset is the canonical one.** For squarefree
monic `R`, `normalizedFactors R` has no duplicates
(`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`), so
`F.factors.val = normalizedFactors R` on the nose (`Multiset.toFinset_val` + `Multiset.dedup_eq_self`),
and the degree multisets agree. -/
theorem degrees_multiset (R : kS[X]) (hR : R.Monic) (hsq : Squarefree R)
    (F : M4.ResidualFactorization R) :
    (F.factors.val.map Polynomial.natDegree) =
      (UniqueFactorizationMonoid.normalizedFactors R).map Polynomial.natDegree := by
  have hR0 : R ≠ 0 := hR.ne_zero
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors R).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hR0).mp hsq
  have hval : F.factors.val = UniqueFactorizationMonoid.normalizedFactors R := by
    rw [factors_eq_normalizedFactors_toFinset R hR0 F, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
  rw [hval]

/-- **Item 4 (bonus): squarefree residual ⇒ every cell is childless.** `M5.cells` emits a descent
child only under the guard `2 ≤ fact.mult ψ`, which `mult_eq_one_of_squarefree` kills. -/
theorem cells_childless_of_squarefree (T : M5.OMType) (hsq : Squarefree T.Rr)
    (_hR : T.Rr ≠ 0) : ∀ c ∈ M5.cells T, c.children = [] := by
  intro c hc
  simp only [M5.cells, List.mem_map] at hc
  obtain ⟨⟨ψ, hψ⟩, _hmem, rfl⟩ := hc
  have h1 : (Classical.choice (M4.factorize_any T.Rr)).mult ψ = 1 :=
    mult_eq_one_of_squarefree T.Rr hsq _ ψ hψ
  simp only [h1]
  rw [dif_neg (by omega)]

end LeanUrat.OM.Order0
