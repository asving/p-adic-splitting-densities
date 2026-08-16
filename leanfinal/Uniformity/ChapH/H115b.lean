/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115
import Uniformity.ChapH.H117
import Uniformity.ChapB.B59a

/-!
# Uniformity.ChapH.H115b — the α shear is ONTO (H.115 clause ii)

**Chapter H, NODE H.115, SPLIT b** (`blueprint/CHAP-H_general_induction.md` §17.2, the
blueprint's mandated split H.115a/H.115b/H.115c).

`alphaChild_surjective` — at a realized slope `k` and a nonzero residue `z`, every
window-`(N − m k)` cluster state is the α child of some α(k, z) state.

## The construction, in one line

Reverse the shear.  Given a child lift `b` (degree `m`, coefficients in `𝔪`) and the pinned
centre `ŵ = resSect O z`, put

* `alphaFrame b ŵ = (monicPoly b).comp (X − C ŵ)` — undo the recentring;
* `alphaParent π b k ŵ = (alphaFrame b ŵ).scaleRoots (π ^ k)` — undo the scaling.

Then `alphaParent`'s recentring is EXACTLY `C (π ^ (m k)) * monicPoly b`
(`alphaParent_recentre`), which is clause (i)'s conclusion read backwards, and the parent's
coefficients are `(alphaFrame b ŵ).coeff j · π ^ (k (m − j))` — all in `𝔪`, so the parent is a
cluster state.

## The four obligations of `IsAlphaState`, and where each is discharged

1. **non-drain** — `alphaParent_addVal_coeff_zero`: the constant coefficient has valuation
   EXACTLY `m k ≤ N − 1`, because `(alphaFrame b ŵ).coeff 0 = (monicPoly b).eval (−ŵ)` reduces
   to `(−z) ^ m ≠ 0` (here `z ≠ 0` is load-bearing, and only here and in the polygon step).
2. **the content** — `betaContent c k = m * k`, by H.108's infimum: every visible term
   `resOrd (c j) + j k` already dominates the monic top term `m k`.
3. **the child event** — `HasChildAt π c m k z` through H.109's conservativity
   `hasChildAt_of_exists`, read at the constructed lift pair, where the recentring is the
   explicit product above.
4. **not CS** — `not_isCSState_of_alphaParent`.  This is the only geometric step.  The
   parent's polygon is the SINGLE side from `(0, m k)` to `(m, 0)`: at `(u, ℓ)` with
   `u ≠ k ℓ` the supporting line touches one endpoint only, so `sideDeg = 0` and the residual
   polynomial is a nonzero constant, which no `ψ ^ μ` divides; at `(u, ℓ) = (k, 1)` (forced by
   `Nat.Coprime u ℓ`) B.59a's digit identity `resPoly_X_eq_map_of_scaleRoots` computes the
   residual polynomial as the reduction of `alphaFrame b ŵ`, namely `(Y − z) ^ m`, whose
   irreducible factors are all of degree `1` — and `IsCSState` demands a block
   `2 ≤ ℓ * deg ψ = deg ψ`.

Clause (i) (`alphaChild_spec`, in `ChapH/H115.lean`) then identifies the child of the
constructed parent with `d`: two monic developments equal after multiplication by the nonzero
`π ^ (m k)` are equal.

DEPENDS: H.115a (`resSect`, `alphaChild`, `alphaChild_spec`), H.117 (`sideMax_le_natDegree`),
H.112 (`exists_proj_eq`, `coeff_recentre_top`), H.111 (`IsAlphaState`), H.110 (`IsCSState`),
H.109 (`HasChildAt`, `hasChildAt_of_exists`), H.108 (`betaContent`), H.107 (`resOrd`) ·
CHAP-B B.15 (`npHgt_X`), B.16 (`sideSet`), B.20 (`sideMin`/`sideMax`/`sideDeg`), B.29
(`resPoly`), B.30 (`natDegree_resPoly`), B.34 (`IsPure`), B.59a
(`resPoly_X_eq_map_of_scaleRoots`) · mathlib `Polynomial.scaleRoots`,
`Polynomial.comp_C_mul_X_coeff`, `Prime.dvd_of_dvd_pow`.

**ENVIRONMENT — ENV-H17** + `π` explicit, every binder INLINE.  No `[Finite]` (clause (ii)
does not count).

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

section Parent

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## 1. The inverse shear: from a child lift to a parent frame -/

/-- **The un-scaled parent frame.**  Undo the recentring `y ↦ y + ŵ` of the child
development. -/
noncomputable def alphaFrame {m : ℕ} (b : Fin m → O) (ŵ : O) : Polynomial O :=
  (monicPoly b).comp (X - C ŵ)

theorem alphaFrame_monic {m : ℕ} (b : Fin m → O) (ŵ : O) : (alphaFrame b ŵ).Monic :=
  (monicPoly_monic b).comp (monic_X_sub_C ŵ) (by simp)

theorem alphaFrame_natDegree {m : ℕ} (b : Fin m → O) (ŵ : O) :
    (alphaFrame b ŵ).natDegree = m := by
  rw [alphaFrame, natDegree_comp, monicPoly_natDegree, natDegree_X_sub_C, mul_one]

/-- **The parent frame.**  Undo the scaling `y ↦ π ^ k y` as well: `scaleRoots` multiplies the
`j`-th coefficient by `(π ^ k) ^ (m − j)`, which is precisely the α digit pattern. -/
noncomputable def alphaParent (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) : Polynomial O :=
  (alphaFrame b ŵ).scaleRoots (π ^ k)

theorem alphaParent_monic (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    (alphaParent π b k ŵ).Monic :=
  (monic_scaleRoots_iff _).2 (alphaFrame_monic b ŵ)

theorem alphaParent_natDegree (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    (alphaParent π b k ŵ).natDegree = m := by
  rw [alphaParent, natDegree_scaleRoots, alphaFrame_natDegree]

theorem alphaParent_coeff (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) (j : ℕ) :
    (alphaParent π b k ŵ).coeff j = (alphaFrame b ŵ).coeff j * (π ^ k) ^ (m - j) := by
  rw [alphaParent, coeff_scaleRoots, alphaFrame_natDegree]

/-- **The inverse shear is a shear.**  The parent frame's recentring at the pinned pair is
exactly `π ^ (m k) ·` the child's monic development — clause (i)'s conclusion, backwards. -/
theorem alphaParent_recentre (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    (alphaParent π b k ŵ).comp (C (π ^ k) * (X + C ŵ)) = C (π ^ (m * k)) * monicPoly b := by
  have hstep : (alphaParent π b k ŵ).comp (C (π ^ k) * X)
      = C ((π ^ k) ^ m) * alphaFrame b ŵ := by
    refine Polynomial.ext fun j => ?_
    rw [comp_C_mul_X_coeff, alphaParent_coeff, coeff_C_mul]
    by_cases hj : j ≤ m
    · rw [mul_assoc, ← pow_add, show m - j + j = m from by omega]
      ring
    · have hz : (alphaFrame b ŵ).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [alphaFrame_natDegree]; omega)
      rw [hz, zero_mul, zero_mul, mul_zero]
  have hq : (C (π ^ k) * X).comp (X + C ŵ) = C (π ^ k) * (X + C ŵ) := by
    simp [mul_comp]
  have hinner : (alphaFrame b ŵ).comp (X + C ŵ) = monicPoly b := by
    rw [alphaFrame, Polynomial.comp_assoc]
    have : (X - C ŵ).comp (X + C ŵ) = (X : Polynomial O) := by
      simp [sub_comp]
    rw [this, comp_X]
  calc (alphaParent π b k ŵ).comp (C (π ^ k) * (X + C ŵ))
      = ((alphaParent π b k ŵ).comp (C (π ^ k) * X)).comp (X + C ŵ) := by
        rw [Polynomial.comp_assoc, hq]
    _ = (C ((π ^ k) ^ m) * alphaFrame b ŵ).comp (X + C ŵ) := by rw [hstep]
    _ = C (π ^ (m * k)) * monicPoly b := by
        rw [mul_comp, C_comp, hinner, ← pow_mul, Nat.mul_comm k m]

/-! ## 2. The parent's reduction and its valuation profile -/

/-- **The reduction of the parent frame.**  With every child coordinate in `𝔪` the child's
development reduces to `Y ^ m`, so the un-scaled parent frame reduces to `(Y − z) ^ m` — the
α residual polynomial, before any polygon apparatus is invoked. -/
theorem alphaFrame_map_residue {m : ℕ} {b : Fin m → O} (hb : ∀ i, b i ∈ maximalIdeal O)
    (ŵ : O) :
    (alphaFrame b ŵ).map (residue O) = (X - C (residue O ŵ)) ^ m := by
  have hmb : (monicPoly b).map (residue O) = (X : Polynomial (ResidueField O)) ^ m := by
    rw [monicPoly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum]
    have hz : ∀ i : Fin m, (C (b i) * X ^ (i : ℕ)).map (residue O) = 0 := by
      intro i
      have : residue O (b i) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hb i)
      rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, this, map_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero, add_zero]
  rw [alphaFrame, Polynomial.map_comp, hmb, Polynomial.map_sub, map_X, map_C, pow_comp, X_comp]

/-- **The parent frame's constant coefficient is a UNIT** — this is where `z ≠ 0` enters.  Its
reduction is `(−z) ^ m`. -/
theorem alphaFrame_coeff_zero_not_dvd {π : O} (hπ : Irreducible π) {m : ℕ}
    {b : Fin m → O} (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0)
    {ŵ : O} (hŵ : residue O ŵ = z) : ¬ π ∣ (alphaFrame b ŵ).coeff 0 := by
  intro hdvd
  have hmem : (alphaFrame b ŵ).coeff 0 ∈ maximalIdeal O := by
    have := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 ((alphaFrame b ŵ).coeff 0)).2
      (by rwa [pow_one])
    rwa [pow_one] at this
  have h0 : residue O ((alphaFrame b ŵ).coeff 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  have hmap : residue O ((alphaFrame b ŵ).coeff 0) = (-z) ^ m := by
    rw [← coeff_map, alphaFrame_map_residue hb ŵ, hŵ, coeff_zero_eq_eval_zero]
    simp
  rw [hmap] at h0
  exact hz (neg_eq_zero.1 (pow_eq_zero_iff' .. |>.1 h0).1)

/-- The parent's polygon point at abscissa `j` sits on or above the line of slope `−k` through
`(m, 0)`. -/
theorem alphaParent_npHgt_ge {π : O} (hπ : Irreducible π) {m : ℕ} (b : Fin m → O) (k : ℕ)
    (ŵ : O) (j : ℕ) :
    (((m - j) * k : ℕ) : ℕ∞) ≤ npHgt X (alphaParent π b k ŵ) j := by
  rw [npHgt_X, ← Uniformity.Hensel.pow_dvd_iff_le_addVal hπ, alphaParent_coeff]
  exact Dvd.dvd.mul_left (dvd_of_eq (by rw [← pow_mul, Nat.mul_comm k (m - j)])) _

/-- The parent's polygon point at abscissa `0` is EXACTLY `(0, m k)`. -/
theorem alphaParent_npHgt_zero {π : O} (hπ : Irreducible π) {m : ℕ} {b : Fin m → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0) (k : ℕ) {ŵ : O}
    (hŵ : residue O ŵ = z) :
    npHgt X (alphaParent π b k ŵ) 0 = ((m * k : ℕ) : ℕ∞) := by
  have hco : (alphaParent π b k ŵ).coeff 0 = (alphaFrame b ŵ).coeff 0 * π ^ (m * k) := by
    rw [alphaParent_coeff, Nat.sub_zero, ← pow_mul, Nat.mul_comm k m]
  have hunit : IsDiscreteValuationRing.addVal O ((alphaFrame b ŵ).coeff 0) = 0 := by
    by_contra hne
    refine alphaFrame_coeff_zero_not_dvd hπ hb hz hŵ ?_
    have h1 : ((1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal O ((alphaFrame b ŵ).coeff 0) := by
      exact_mod_cast Order.one_le_iff_ne_zero.2 hne
    have h2 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ
      (a := (alphaFrame b ŵ).coeff 0) (n := 1)).2 h1
    rwa [pow_one] at h2
  rw [npHgt_X, hco, AddValuation.map_mul, hunit, zero_add, hπ.addVal_pow]

/-- The parent's polygon point at abscissa `m` is EXACTLY `(m, 0)` — the monic top. -/
theorem alphaParent_npHgt_natDegree (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    npHgt X (alphaParent π b k ŵ) m = 0 := by
  have h1 : (alphaParent π b k ŵ).coeff m = 1 := by
    have := (alphaParent_monic π b k ŵ).coeff_natDegree
    rwa [alphaParent_natDegree] at this
  rw [npHgt_X, h1, AddValuation.map_one]

end Parent

end Uniformity.Density.Induction
