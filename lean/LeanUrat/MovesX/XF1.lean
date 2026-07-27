/-
Unit XF.1 discCylinder  [PROVED]
moves_ref: the (3b) event is level-D cylinder data.
sketch: `polyOfCoeffs … = f.map (toZModPow D)` for monic deg-n (via `polyOfCoeffs`
naturality + `Monic.as_sum`); monic-case `discr_map` helper (Mathlib gap, re-proved here
through the resultant); `PadicInt.ker_toZModPow`. deps: Defs. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Polynomial

/-! ### Monic-case discriminant naturality (Mathlib has `Polynomial.discr` but no `discr_map`).
Derived through the resultant, which *is* natural under ring homs.  This mirrors
`LeanUrat.OM.M_F4.discr_map_monic`, re-proved here to keep this unit's dependency surface = Defs. -/

/-- For a monic polynomial of positive degree, `discr = ± resultant f f'`
(mathlib's `resultant_deriv` specialised to `leadingCoeff = 1`). -/
private theorem discr_monic_eq_resultant {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (hpos : 0 < f.natDegree) :
    f.discr =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        resultant f f.derivative f.natDegree (f.natDegree - 1) := by
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  have h := resultant_deriv hdeg
  rw [hf.leadingCoeff, mul_one] at h
  have hsq : ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc f.discr
      = 1 * f.discr := (one_mul _).symm
    _ = ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)) * f.discr := by rw [hsq]
    _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr) := by ring
    _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          resultant f f.derivative f.natDegree (f.natDegree - 1) := by rw [← h]

/-- Discriminant naturality for monic polynomials: `discr` commutes with any ring hom. -/
private theorem discr_map_monic {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : R[X]) (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with hz | hpos
  · have hf1 : f = 1 := eq_one_of_monic_natDegree_zero hf hz
    subst hf1
    have h1R : discr (1 : R[X]) = 1 := by rw [← C_1]; exact discr_C 1
    have h1S : discr (1 : S[X]) = 1 := by rw [← C_1]; exact discr_C 1
    rw [Polynomial.map_one, h1R, h1S, map_one]
  · by_cases hS : Nontrivial S
    · have hmap : (f.map φ).Monic := hf.map φ
      have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
      have hpos' : 0 < (f.map φ).natDegree := by rw [hdeg]; exact hpos
      rw [discr_monic_eq_resultant f hf hpos,
          discr_monic_eq_resultant (f.map φ) hmap hpos']
      have hder : (f.map φ).derivative = f.derivative.map φ := derivative_map f φ
      rw [hder, hdeg, resultant_map_map, map_mul, map_pow, map_neg, map_one]
    · rw [not_nontrivial_iff_subsingleton] at hS
      exact Subsingleton.elim _ _

/-- Naturality of `polyOfCoeffs` under a ring hom: mapping the coefficient tuple through
`φ` is the same as base-changing the whole polynomial through `φ`. -/
private lemma polyOfCoeffs_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (n : ℕ) (a : Fin n → R) :
    polyOfCoeffs S n (fun i => φ (a i)) = (polyOfCoeffs R n a).map φ := by
  simp only [polyOfCoeffs, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

/-- A monic degree-`n` polynomial is recovered from its own coefficient tuple by
`polyOfCoeffs`. -/
private lemma polyOfCoeffs_self {R : Type} [CommRing R] {n : ℕ} (f : Polynomial R)
    (hm : f.Monic) (hd : f.natDegree = n) :
    polyOfCoeffs R n (fun i => f.coeff i) = f := by
  simp only [polyOfCoeffs]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) n, ← hd]
  exact (hm.as_sum).symm

/-- The reduced-coefficient cylinder polynomial equals the base-change of `f` along
`toZModPow D`, for monic degree-`n` `f`. -/
private lemma polyOfCoeffs_eq_map {p n D : ℕ} [Fact p.Prime] (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n) :
    polyOfCoeffs (ZMod (p ^ D)) n (fun i => PadicInt.toZModPow D (f.coeff i))
      = f.map (PadicInt.toZModPow D) := by
  rw [polyOfCoeffs_map (PadicInt.toZModPow D) n (fun i => f.coeff i), polyOfCoeffs_self f hm hd]

theorem discCylinder (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n) :
    ((p : ℤ_[p]) ^ D ∣ f.discr ↔
      (polyOfCoeffs (ZMod (p ^ D)) n (fun i => PadicInt.toZModPow D (f.coeff i))).discr = 0) := by
  rw [polyOfCoeffs_eq_map f hm hd, discr_map_monic (PadicInt.toZModPow D) f hm,
    ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]

end LeanUrat.MovesX
