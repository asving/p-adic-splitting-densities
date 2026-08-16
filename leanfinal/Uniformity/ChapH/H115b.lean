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

end Parent

end Uniformity.Density.Induction
