/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Shift

/-!
# UniformityCheck.N3CertRam — CASE R: `v(B₀) = 2` with `v(B₁) ≥ 2` is totally ramified

Unit `UNIFORMITY-CHECK-N3C`, layer 2 (`notes/N3_CHECK_2026-08-13.md` §13.2, CERT R). This is
HYP.07, the non-integral-slope totally-ramified certificate that `N3_CHECK` §12 recorded as
absent: a cubic all of whose coefficients lie in `𝔪`, with

    π² ∣ B₀ ,  π³ ∤ B₀ ,  π² ∣ B₁ ,  π ∣ B₂

has `typeOf = c3ram = {(3,1)}`. The Newton polygon reading is "one side of slope `−2/3`", but the
proof never mentions polygons:

1. **No root in `O`.** If `F(r) = 0` then `r³ ∈ 𝔪` so `π ∣ r`; then `π³` divides each of `r³`,
   `B₂r²` and `B₁r`, hence `π³ ∣ B₀` — contradiction.
2. **Irreducible.** A monic cubic over a domain that factors non-trivially has a monic degree-1
   factor (degrees add, and a degree-`0` factor of a monic polynomial is a unit), whose root is a
   root of the cubic.
3. **`f = 1`.** `N(θ) = −B₀` has valuation exactly `2`, and `deg F = 3` is always a
   norm-valuation (the norm of `π`); `gcd(2,3) = 1`, so `inertiaDegOf F = 1`
   (`inertiaDegOf_eq_one_of_coprime`) and `e = 3`.

⚠ The `π² ∣ B₁` hypothesis is NOT decoration: at `v(B₁) = 1` the polygon has two sides and the
type is `{(1,1),(2,1)}` instead (`N3CertLinRam.lean`). §13.1 records this as a correction to
`N3_CHECK` §9.4's table.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section CertRam

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A degree-`1` polynomial with unit leading coefficient has a root: monicize and read off
`r = −u⁻¹ · p₀`. -/
private theorem exists_root_of_natDegree_one {p : Polynomial O} (hd : p.natDegree = 1)
    (hu : IsUnit p.leadingCoeff) : ∃ r : O, p.eval r = 0 := by
  obtain ⟨u, hu'⟩ := hu
  have hp : p = C (p.coeff 1) * X + C (p.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one (by omega)
  have hlc : p.coeff 1 = (u : O) := by rw [hu', leadingCoeff, hd]
  have heval : ∀ r : O, p.eval r = p.coeff 1 * r + p.coeff 0 := by
    intro r
    conv_lhs => rw [hp]
    simp
  refine ⟨-((↑u⁻¹ : O) * p.coeff 0), ?_⟩
  rw [heval, hlc, mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]

/-- **A monic cubic with no root in `O` is irreducible.** Any nontrivial factorization of a
monic polynomial has both factors with unit leading coefficient and positive degree, so at
degree `3` one factor has degree `1`; monicizing it exhibits a root. -/
theorem irreducible_of_no_root_cubic {b : Fin 3 → O}
    (h : ∀ r : O, (monicPoly b).eval r ≠ 0) : Irreducible (monicPoly b) := by
  have hm : (monicPoly b).Monic := monicPoly_monic b
  have hd : (monicPoly b).natDegree = 3 := monicPoly_natDegree b
  constructor
  · intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  · intro g k hgk
    have hg0 : g ≠ 0 := by
      rintro rfl; exact hm.ne_zero (hgk.trans (zero_mul k))
    have hk0 : k ≠ 0 := by
      rintro rfl; exact hm.ne_zero (hgk.trans (mul_zero g))
    have hgu : IsUnit g.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic hm ⟨k, hgk⟩
    have hku : IsUnit k.leadingCoeff :=
      isUnit_leadingCoeff_of_dvd_monic hm ⟨g, by rw [hgk, mul_comm]⟩
    have hdeg : g.natDegree + k.natDegree = 3 := by
      rw [← natDegree_mul hg0 hk0, ← hgk]; exact hd
    rcases Nat.eq_zero_or_pos g.natDegree with hgz | hgpos
    · exact Or.inl (isUnit_of_natDegree_zero hgz hgu)
    rcases Nat.eq_zero_or_pos k.natDegree with hkz | hkpos
    · exact Or.inr (isUnit_of_natDegree_zero hkz hku)
    exfalso
    have key : ∀ p q : Polynomial O, monicPoly b = p * q → p.natDegree = 1 →
        IsUnit p.leadingCoeff → False := by
      intro p q hpq hp1 hpu
      obtain ⟨r, hr⟩ := exists_root_of_natDegree_one hp1 hpu
      exact h r (by rw [hpq, eval_mul, hr, zero_mul])
    have hone : g.natDegree = 1 ∨ k.natDegree = 1 := by omega
    rcases hone with h1 | h1
    · exact key g k hgk h1 hgu
    · exact key k g (by rw [hgk, mul_comm]) h1 hku

/-- **Step 1 of CERT R: no root in `O`.** -/
theorem no_root_of_val_two {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) (h0' : ¬ π ^ 3 ∣ b 0) (r : O) :
    (monicPoly b).eval r ≠ 0 := by
  intro hr
  rw [cubic_eval] at hr
  have h1' : π ∣ b 1 := (dvd_pow_self π two_ne_zero).trans h1
  have h0'' : π ∣ b 0 := (dvd_pow_self π two_ne_zero).trans h0
  -- `π ∣ r³` because `r³ = -(b₂r² + b₁r + b₀)` and `π` divides each summand
  have hcube : π ∣ r ^ 3 := by
    have hEq : r ^ 3 = -(b 2 * r ^ 2 + b 1 * r + b 0) := by linear_combination hr
    rw [hEq]
    exact dvd_neg.mpr
      (dvd_add (dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1' _)) h0'')
  have hπr : π ∣ r := hπ.prime.dvd_of_dvd_pow hcube
  obtain ⟨c, hc⟩ := h2
  obtain ⟨d, hd⟩ := h1
  obtain ⟨s, hs⟩ := hπr
  subst hs
  rw [hc, hd] at hr
  exact h0' ⟨-(s ^ 3 + c * s ^ 2 + d * s), by linear_combination hr⟩

/-- **CERT R (CASE R of §13.1).** `v(B₀) = 2` together with `v(B₁) ≥ 2`, `v(B₂) ≥ 1` forces the
totally ramified type `{(3,1)}` — over a general discrete valuation ring, no residue
characteristic hypothesis, no completeness. -/
theorem typeOf_ram3_of_val_two {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) (h0' : ¬ π ^ 3 ∣ b 0) :
    typeOf (monicPoly b) = c3ram := by
  have hirr : Irreducible (cub3 b) := by
    rw [← monicPoly_eq_cub3]
    exact irreducible_of_no_root_cubic (no_root_of_val_two hπ h2 h1 h0 h0')
  -- `b 0` has valuation exactly `2`
  obtain ⟨c, hc⟩ := h0
  have hcu : IsUnit c := by
    by_contra hcn
    refine h0' ?_
    have hπc : π ∣ c := by
      rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcn)
    obtain ⟨e, rfl⟩ := hπc
    exact ⟨e, by rw [hc]; ring⟩
  have hcv : IsDiscreteValuationRing.addVal O c = 0 := by
    rw [← hcu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hval : IsDiscreteValuationRing.addVal O (b 0) = ((2 : ℕ) : ℕ∞) := by
    rw [hc, AddValuation.map_mul, hπ.addVal_pow, hcv, add_zero]
  -- `θ ≠ 0` and `N(θ) = -b₀` has valuation `2`
  have hroot_elt : AdjoinRoot.root (cub3 b) = cubElt b ![0, 1, 0] := by
    rw [cubElt]; simp
  have hne : (AdjoinRoot.root (cub3 b)) ≠ 0 := by
    rw [hroot_elt]
    intro hz
    have hz1 := (cubElt_eq_zero_iff b ![0, 1, 0]).1 hz 1
    simp at hz1
  have hnegval : IsDiscreteValuationRing.addVal O (-(b 0))
      = IsDiscreteValuationRing.addVal O (b 0) := AddValuation.map_neg _ _
  have hmem2 : (2 : ℕ) ∈ normValues (cub3 b) := by
    refine ⟨two_pos, AdjoinRoot.root (cub3 b), hne, ?_⟩
    rw [norm_root_cub, hnegval, hval]
  have hmem3 : (3 : ℕ) ∈ normValues (cub3 b) := by
    have hmem := natDegree_mem_normValues (cub3_monic b) (by rw [cub3_natDegree]; omega) hπ
    rwa [cub3_natDegree] at hmem
  have hinf : inertiaDegOf (cub3 b) = 1 :=
    inertiaDegOf_eq_one_of_coprime hmem2 hmem3 (by norm_num)
  have hF : IsMonicFactorization (cub3 b) {cub3 b} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨cub3_monic b, hirr⟩, by simp⟩
  rw [monicPoly_eq_cub3]
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [c3ram, efPair, ramIndexOf, hinf, cub3_natDegree]

end CertRam

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.irreducible_of_no_root_cubic
#print axioms UniformityCheck.no_root_of_val_two
#print axioms UniformityCheck.typeOf_ram3_of_val_two

end AxCheck

end UniformityCheck
