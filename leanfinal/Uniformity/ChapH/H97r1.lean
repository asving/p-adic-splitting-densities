/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G60
import Uniformity.Density.TypeOfAlgebra
import Uniformity.Density.TypeOfInvariance
import Uniformity.Density.QuadCert
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H97r1 — the cubic peel toolkit, recentring, and the residue trichotomy

**Chapter H, node-support file `H97r1`** (unit OM-1, `docs/openmath-campaign/
OM-1_n3-rate_2026-08-16.md`, steps S1). First of the four support files that turn H.97's
`hrate` frontier into the unconditional `package_three` (H97b). Letter-suffix node precedent:
G.61a–e, G.23R1–12, H09w.

**PROVENANCE (quarry discipline, `leanfinal/notes/QUARRY_BACKPORT_2026-08-15.md`).** Backport
from this repo's own `leancheck` sidecar (same licence, same mathlib pin, statements about
`leanfinal`'s own objects), verified building green at leancheck commit `b00b0505`
(2026-08-16): `UniformityCheck/N3Base.lean` (§§2–4: `typeOf_X_sub_C`, `typeOf_linear_mul`,
`cubic_expand/_eval/_deriv_eval`, `peel`, `cubic_peel`, `exists_cubic_root`),
`UniformityCheck/N3Shift.lean` (`shiftVec` block), `UniformityCheck/N3Struct.lean`
(§§1–3: `cubeCoeff`, `cVal`/`cDer`, `cubeCoeff_injective`, `cubic_trichotomy`,
`cubic_structure`, `exists_root_congr`, `peel_congr`), plus `resVec`
(`UniformityCheck/N3Norm.lean`). **Dedup-audit — every declaration below is a verbatim move
except the following adaptations:**

1. namespace `UniformityCheck` → `Uniformity.Density`; `typeOf_mul`/`monicFactors_mul` are NOT
   ported (landed here as CN-03, `TypeOfAlgebra.lean`); `NoRootCubic` is NOT ported (landed at
   G.60, byte-identical definition).
2. `N3Shift`'s private `mem_maximalIdeal_pow_dvd` is dropped — the landed
   `mem_maximalIdeal_pow_iff_dvd` (`Drainage.lean`) is used instead (its
   `Finite (ResidueField O)` section hypothesis is carried by this file's sections).
3. `N3Struct.proj_of_dvd` is dropped — subsumed by the landed `proj_eq_iff_dvd`
   (`DensityAPI.lean`); the one use below is routed through it.
4. `cubic_trichotomy_disjoint` is not ported (no consumer on the rate chain; the leancheck
   copy remains the reference).
5. `N3Shift.typeOf_ram3_of_val_one` moves to `H97r2` (certificate layer).

## What this file provides

* the **peel toolkit**: `typeOf` of a monic linear factor, additivity over a peeled linear
  factor, the explicit shape of a monic cubic, the division-free peel
  `monicPoly a = (X − C r)·monicPoly (peel a r)` at a root `r`, and Hensel at a simple
  residue root;
* **recentring**: `shiftVec a γ` = the coefficient vector of `F_a(X + γ)`, with type
  invariance (P5's `typeOf_shift`), invertibility, congruence transport, and the
  triple-root-stratum criterion `shiftVec_mem_iff`;
* the **residue trichotomy** (`cubic_trichotomy`, characteristic-free) and its `O`-form
  `cubic_structure`: every monic cubic over a complete DVR has a unit-derivative root, or is
  residually rootless, or is residually a perfect cube;
* the **lossless peel congruences** `exists_root_congr` (the Hensel root moves no further
  than the coefficients) and `peel_congr`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. The peel toolkit (port: `N3Base` §§2–4) -/

section Mul

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The type of a monic linear factor. -/
theorem typeOf_X_sub_C (r : O) : typeOf (X - C r) = ⟨{(1, 1)}⟩ :=
  typeOf_of_natDegree_one (monic_X_sub_C r) (natDegree_X_sub_C r)

/-- **Peeling a linear factor off, at the level of types.** -/
theorem typeOf_linear_mul {g : Polynomial O} (hg : g.Monic) (r : O) :
    (typeOf ((X - C r) * g)).data = (1, 1) ::ₘ (typeOf g).data := by
  rw [typeOf_mul (monic_X_sub_C r) hg, typeOf_X_sub_C]
  rfl

end Mul

/-! ## 2. The shape of a monic cubic (port: `N3Base` §3) -/

section Shape

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cubic_expand (a : Fin 3 → O) :
    monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, mul_one]
  ring

theorem cubic_eval (a : Fin 3 → O) (x : O) :
    (monicPoly a).eval x = x ^ 3 + a 2 * x ^ 2 + a 1 * x + a 0 := by
  rw [cubic_expand]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]

theorem cubic_deriv_eval (a : Fin 3 → O) (x : O) :
    ((monicPoly a).derivative).eval x = 3 * x ^ 2 + 2 * a 2 * x + a 1 := by
  rw [cubic_expand]
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C, derivative_mul,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_zero, eval_one]
  ring

/-- The quadratic cofactor left after dividing the monic cubic `monicPoly a` by `X - r`.
(Junk unless `r` is a root; `cubic_peel` supplies the hypothesis.) -/
def peel (a : Fin 3 → O) (r : O) : Fin 2 → O := ![a 1 + a 2 * r + r ^ 2, a 2 + r]

@[simp] theorem peel_zero (a : Fin 3 → O) (r : O) : peel a r 0 = a 1 + a 2 * r + r ^ 2 := rfl
@[simp] theorem peel_one (a : Fin 3 → O) (r : O) : peel a r 1 = a 2 + r := rfl

/-- **Dividing out a root.** No division is used: this is a `ring` identity modulo `f(r) = 0`. -/
theorem cubic_peel (a : Fin 3 → O) (r : O) (hr : (monicPoly a).eval r = 0) :
    monicPoly a = (X - C r) * monicPoly (peel a r) := by
  have h : (C (a 0) : Polynomial O) = -(C (a 1) * C r + C (a 2) * C r ^ 2 + C r ^ 3) := by
    have hc : C (r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0) = (0 : Polynomial O) := by
      rw [← cubic_eval a r, hr, map_zero]
    simp only [map_add, map_mul, map_pow] at hc
    linear_combination hc
  rw [cubic_expand, monicPoly_two_expand, peel_zero, peel_one, h]
  simp only [map_add, map_mul, map_pow]
  ring

end Shape

/-! ## 3. Hensel at a simple residue root (port: `N3Base` §4) -/

section Hensel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **Hensel.** A simple root of the reduced cubic lifts to a root in `O`. This is the only place
completeness is used. -/
theorem exists_cubic_root (a : Fin 3 → O) (ρ : O)
    (h0 : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0 ∈ maximalIdeal O)
    (h1 : IsUnit (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1)) :
    ∃ r : O, (monicPoly a).eval r = 0 ∧ r - ρ ∈ maximalIdeal O := by
  obtain ⟨r, hr, hd⟩ :=
    HenselianLocalRing.is_henselian (monicPoly a) (monicPoly_monic a) ρ
      (by rw [cubic_eval]; exact h0) (by rw [cubic_deriv_eval]; exact h1)
  exact ⟨r, hr, hd⟩

end Hensel

/-! ## 4. The residue trichotomy (port: `N3Struct` §1) -/

section Trich

variable {K : Type*} [Field K]

/-- The coefficient vector of `(X − γ)³`, in the `monicPoly` convention
`X³ + c₂X² + c₁X + c₀`. -/
def cubeCoeff (γ : K) : Fin 3 → K := ![-(γ ^ 3), 3 * γ ^ 2, -(3 * γ)]

@[simp] theorem cubeCoeff_zero (γ : K) : cubeCoeff γ 0 = -(γ ^ 3) := rfl
@[simp] theorem cubeCoeff_one (γ : K) : cubeCoeff γ 1 = 3 * γ ^ 2 := rfl
@[simp] theorem cubeCoeff_two (γ : K) : cubeCoeff γ 2 = -(3 * γ) := rfl

/-- The value at `x` of the monic cubic with coefficient vector `c`. -/
def cVal (c : Fin 3 → K) (x : K) : K := x ^ 3 + c 2 * x ^ 2 + c 1 * x + c 0

/-- The derivative at `x` of the monic cubic with coefficient vector `c`. -/
def cDer (c : Fin 3 → K) (x : K) : K := 3 * x ^ 2 + 2 * c 2 * x + c 1

/-- `(X − γ)³ = (X − γ′)³` forces `γ = γ′`, in every characteristic (in characteristic `3` the
first two coefficients carry no information and the cube root is used instead). -/
theorem cubeCoeff_injective : Function.Injective (cubeCoeff (K := K)) := by
  intro γ γ' h
  have h0 : -(γ ^ 3) = -(γ' ^ 3) := congrFun h 0
  have h1 : 3 * γ ^ 2 = 3 * γ' ^ 2 := congrFun h 1
  have h2 : -(3 * γ) = -(3 * γ') := congrFun h 2
  have hcube : (γ - γ') ^ 3 = 0 := by
    linear_combination (-1 : K) * h0 - γ' * h1 - γ' ^ 2 * h2
  have hz := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hcube
  exact sub_eq_zero.1 hz

/-- **THE RESIDUE TRICHOTOMY.** Every monic cubic over a field has a simple root, or no root at
all, or is a perfect cube. Characteristic-free. -/
theorem cubic_trichotomy (c : Fin 3 → K) :
    (∃ ρ : K, cVal c ρ = 0 ∧ cDer c ρ ≠ 0) ∨ Menu.NoRootCubic c ∨ (∃ γ : K, c = cubeCoeff γ) := by
  by_cases hroot : ∃ ρ : K, cVal c ρ = 0
  swap
  · exact Or.inr (Or.inl (fun y hy => hroot ⟨y, hy⟩))
  obtain ⟨ρ, hρ⟩ := hroot
  by_cases hd : cDer c ρ = 0
  · -- `ρ` is a multiple root: `F = (X − ρ)²(X − s)` with `s = −c₂ − 2ρ`
    simp only [cVal] at hρ
    simp only [cDer] at hd
    by_cases hsρ : -(c 2) - 2 * ρ = ρ
    · -- the third root coincides: `F = (X − ρ)³`
      refine Or.inr (Or.inr ⟨ρ, ?_⟩)
      have h2 : c 2 = -(3 * ρ) := by linear_combination -hsρ
      have h1 : c 1 = 3 * ρ ^ 2 := by linear_combination hd - 2 * ρ * h2
      have h0 : c 0 = -(ρ ^ 3) := by linear_combination hρ - ρ * h1 - ρ ^ 2 * h2
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    · -- the third root is different, hence simple
      refine Or.inl ⟨-(c 2) - 2 * ρ, ?_, ?_⟩
      · simp only [cVal]
        linear_combination hρ + (-(c 2) - 3 * ρ) * hd
      · have hval : cDer c (-(c 2) - 2 * ρ) = (-(c 2) - 2 * ρ - ρ) ^ 2 := by
          simp only [cDer]; linear_combination hd
        rw [hval]
        exact pow_ne_zero 2 (sub_ne_zero.2 hsρ)
  · exact Or.inl ⟨ρ, hρ, hd⟩

end Trich

/-! ## 5. Recentring (port: `N3Shift`; `resVec` from `N3Norm`) -/

section Shift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The residue vector of a coefficient vector. -/
noncomputable def resVec (a : Fin 3 → O) : Fin 3 → ResidueField O := fun i => residue O (a i)

/-- **The recentred coefficient vector.** `shiftVec a γ` is the coefficient vector of
`F_a(X + γ)`: constant term `F_a(γ)`, linear term `F_a′(γ)`, quadratic term `a₂ + 3γ`. -/
def shiftVec (a : Fin 3 → O) (γ : O) : Fin 3 → O :=
  ![γ ^ 3 + a 2 * γ ^ 2 + a 1 * γ + a 0, 3 * γ ^ 2 + 2 * a 2 * γ + a 1, a 2 + 3 * γ]

@[simp] theorem shiftVec_zero (a : Fin 3 → O) (γ : O) :
    shiftVec a γ 0 = γ ^ 3 + a 2 * γ ^ 2 + a 1 * γ + a 0 := rfl

@[simp] theorem shiftVec_one (a : Fin 3 → O) (γ : O) :
    shiftVec a γ 1 = 3 * γ ^ 2 + 2 * a 2 * γ + a 1 := rfl

@[simp] theorem shiftVec_two (a : Fin 3 → O) (γ : O) : shiftVec a γ 2 = a 2 + 3 * γ := rfl

/-- **Recentring is the substitution `X ↦ X + γ`.** A coefficient identity: expand both sides
with `cubic_expand` and `ring`. -/
theorem monicPoly_shiftVec (a : Fin 3 → O) (γ : O) :
    monicPoly (shiftVec a γ) = (monicPoly a).comp (X + C γ) := by
  rw [cubic_expand (shiftVec a γ), cubic_expand a]
  simp only [shiftVec_zero, shiftVec_one, shiftVec_two, add_comp, mul_comp, pow_comp, X_comp,
    C_comp, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- **Recentring does not change the splitting type** (`typeOf_shift`, unit P5). -/
theorem typeOf_shiftVec (a : Fin 3 → O) (γ : O) :
    typeOf (monicPoly (shiftVec a γ)) = typeOf (monicPoly a) := by
  rw [monicPoly_shiftVec]
  exact typeOf_shift (monicPoly_monic a) γ

/-- **Recentring is invertible**: shifting back by `−γ` returns the original vector. Three
`ring` identities. -/
theorem shiftVec_shiftVec_neg (a : Fin 3 → O) (γ : O) : shiftVec (shiftVec a γ) (-γ) = a := by
  funext i
  fin_cases i
  · show (-γ) ^ 3 + (a 2 + 3 * γ) * (-γ) ^ 2 + (3 * γ ^ 2 + 2 * a 2 * γ + a 1) * (-γ)
        + (γ ^ 3 + a 2 * γ ^ 2 + a 1 * γ + a 0) = a 0
    ring
  · show 3 * (-γ) ^ 2 + 2 * (a 2 + 3 * γ) * (-γ) + (3 * γ ^ 2 + 2 * a 2 * γ + a 1) = a 1
    ring
  · show a 2 + 3 * γ + 3 * (-γ) = a 2
    ring

/-- **Recentring preserves level-`N` congruence** (each component is a polynomial in `a` and
`γ`). -/
theorem dvd_shiftVec_sub {π : O} {N : ℕ} {a a' : Fin 3 → O} (γ : O)
    (h : ∀ i, π ^ N ∣ (a' i - a i)) : ∀ i, π ^ N ∣ (shiftVec a' γ i - shiftVec a γ i) := by
  intro i
  obtain ⟨c0, hc0⟩ := h 0
  obtain ⟨c1, hc1⟩ := h 1
  obtain ⟨c2, hc2⟩ := h 2
  fin_cases i
  · show π ^ N ∣ ((γ ^ 3 + a' 2 * γ ^ 2 + a' 1 * γ + a' 0)
        - (γ ^ 3 + a 2 * γ ^ 2 + a 1 * γ + a 0))
    exact ⟨γ ^ 2 * c2 + γ * c1 + c0, by linear_combination γ ^ 2 * hc2 + γ * hc1 + hc0⟩
  · show π ^ N ∣ ((3 * γ ^ 2 + 2 * a' 2 * γ + a' 1) - (3 * γ ^ 2 + 2 * a 2 * γ + a 1))
    exact ⟨2 * γ * c2 + c1, by linear_combination 2 * γ * hc2 + hc1⟩
  · show π ^ N ∣ ((a' 2 + 3 * γ) - (a 2 + 3 * γ))
    exact ⟨c2, by linear_combination hc2⟩

/-- **The triple-root stratum in recentred coordinates.** All three recentred coefficients lie
in `𝔪` exactly when the residue cubic is `(X − γ̄)³` with `γ̄ = residue γ`.

The three component identities are `v₂ = −3g`, `v₁ = 3g²`, `v₀ = −g³` (`cubeCoeff`), each a
`ring` consequence of the previous ones; no characteristic hypothesis, so residue characteristic
`3` is covered. -/
theorem shiftVec_mem_iff (a : Fin 3 → O) (γ : O) :
    (∀ i, shiftVec a γ i ∈ maximalIdeal O) ↔ resVec a = cubeCoeff (residue O γ) := by
  constructor
  · intro h
    have e0 := (residue_eq_zero_iff (shiftVec a γ 0)).2 (h 0)
    have e1 := (residue_eq_zero_iff (shiftVec a γ 1)).2 (h 1)
    have e2 := (residue_eq_zero_iff (shiftVec a γ 2)).2 (h 2)
    simp only [shiftVec_zero, shiftVec_one, shiftVec_two, map_add, map_mul, map_pow,
      map_ofNat] at e0 e1 e2
    funext i
    fin_cases i
    · show residue O (a 0) = -(residue O γ ^ 3)
      linear_combination e0 - residue O γ * e1 + residue O γ ^ 2 * e2
    · show residue O (a 1) = 3 * residue O γ ^ 2
      linear_combination e1 - 2 * residue O γ * e2
    · show residue O (a 2) = -(3 * residue O γ)
      linear_combination e2
  · intro h
    have v0 : residue O (a 0) = -(residue O γ ^ 3) := congrFun h 0
    have v1 : residue O (a 1) = 3 * residue O γ ^ 2 := congrFun h 1
    have v2 : residue O (a 2) = -(3 * residue O γ) := congrFun h 2
    intro i
    fin_cases i
    · show γ ^ 3 + a 2 * γ ^ 2 + a 1 * γ + a 0 ∈ maximalIdeal O
      refine (residue_eq_zero_iff _).1 ?_
      simp only [map_add, map_mul, map_pow]
      linear_combination residue O γ ^ 2 * v2 + residue O γ * v1 + v0
    · show 3 * γ ^ 2 + 2 * a 2 * γ + a 1 ∈ maximalIdeal O
      refine (residue_eq_zero_iff _).1 ?_
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination 2 * residue O γ * v2 + v1
    · show a 2 + 3 * γ ∈ maximalIdeal O
      refine (residue_eq_zero_iff _).1 ?_
      simp only [map_add, map_mul, map_ofNat]
      linear_combination v2

end Shift

/-! ## 6. The trichotomy over `O`, with the simple residue root already Hensel-lifted
(port: `N3Struct` §2) -/

section OTrich

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **THE `n = 3` STRUCTURE THEOREM.** Every monic cubic over a complete DVR either has a root
in `O` at which the derivative is a UNIT (so it peels, losslessly — `exists_root_congr`), or
is residually rootless (so it is `{(1,3)}`-decided at level 1, G.61c), or is residually a
perfect cube (the triple-root stratum). -/
theorem cubic_structure (a : Fin 3 → O) :
    (∃ r : O, (monicPoly a).eval r = 0 ∧ IsUnit ((monicPoly a).derivative.eval r))
      ∨ Menu.NoRootCubic (resVec a)
      ∨ (∃ γ : O, resVec a = cubeCoeff (residue O γ)) := by
  rcases cubic_trichotomy (resVec a) with ⟨ρbar, hval, hder⟩ | hno | ⟨γbar, hγ⟩
  · obtain ⟨ρ, hρ⟩ := IsLocalRing.residue_surjective (R := O) ρbar
    have hv : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0 ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_add, map_mul, map_pow, hρ]
      simpa [cVal, resVec] using hval
    have hu : IsUnit (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1) := by
      refine notMem_maximalIdeal.1 (fun hmem => hder ?_)
      have h := (IsLocalRing.residue_eq_zero_iff _).2 hmem
      simp only [map_add, map_mul, map_pow, map_ofNat, hρ] at h
      simpa [cDer, resVec] using h
    obtain ⟨r, hr, hrρ⟩ := exists_cubic_root a ρ hv hu
    refine Or.inl ⟨r, hr, ?_⟩
    rw [cubic_deriv_eval]
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hbad : 3 * ρ ^ 2 + 2 * a 2 * ρ + a 1 ∈ maximalIdeal O := by
      have hid : 3 * ρ ^ 2 + 2 * a 2 * ρ + a 1
          = (3 * r ^ 2 + 2 * a 2 * r + a 1) - (r - ρ) * (3 * (r + ρ) + 2 * a 2) := by ring
      rw [hid]
      exact Ideal.sub_mem _ hmem (Ideal.mul_mem_right _ _ hrρ)
    exact absurd hbad (notMem_maximalIdeal.2 hu)
  · exact Or.inr (Or.inl hno)
  · obtain ⟨γ, hγ'⟩ := IsLocalRing.residue_surjective (R := O) γbar
    exact Or.inr (Or.inr ⟨γ, by rw [hγ, hγ']⟩)

end OTrich

/-! ## 7. The lossless peel congruences (port: `N3Struct` §3) -/

section PeelCong

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- Cancel a unit factor out of a divisibility. (Port of `N3Certs.dvd_of_isUnit_mul`,
same provenance as the file header.) -/
theorem dvd_of_isUnit_mul {c d e : O} (hu : IsUnit c) (h : d ∣ c * e) : d ∣ e := by
  obtain ⟨u, rfl⟩ := hu
  have he : e = ((↑u⁻¹ : O)) * ((u : O) * e) := by
    rw [← mul_assoc]
    simp
  rw [he]
  exact h.mul_left _

/-- **The Hensel root moves no further than the coefficients do.** If `r` is a root of `F_a` at
which the derivative is a unit and `a′ ≡ a (mod π^N)` (`N ≥ 1`), then `F_{a′}` has a root
`r′ ≡ r (mod π^N)`: the SAME `N`. The mechanism is the exact cubic expansion
`0 = F_{a′}(r) + δ·(unit)`, so `v(δ) = v(F_{a′}(r)) ≥ N`. -/
theorem exists_root_congr {π : O} (hπ : Irreducible π) {a a' : Fin 3 → O} {N : ℕ} (hN : 1 ≤ N)
    {r : O} (hr : (monicPoly a).eval r = 0) (hu : IsUnit ((monicPoly a).derivative.eval r))
    (hcong : ∀ i, π ^ N ∣ (a' i - a i)) :
    ∃ r' : O, (monicPoly a').eval r' = 0 ∧ π ^ N ∣ (r' - r) := by
  rw [cubic_deriv_eval] at hu
  rw [cubic_eval] at hr
  -- the perturbed value at the old root is deep
  have hE : π ^ N ∣ (r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0) := by
    have hid : r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0
        = (a' 2 - a 2) * r ^ 2 + (a' 1 - a 1) * r + (a' 0 - a 0)
          + (r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0) := by ring
    rw [hid, hr, add_zero]
    exact dvd_add (dvd_add ((hcong 2).mul_right _) ((hcong 1).mul_right _)) (hcong 0)
  -- the perturbed derivative at the old root is still a unit
  have hu' : IsUnit (3 * r ^ 2 + 2 * a' 2 * r + a' 1) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hshift : (2 : O) * (a' 2 - a 2) * r + (a' 1 - a 1) ∈ maximalIdeal O := by
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
      · have h2 : π ∣ (a' 2 - a 2) := dvd_trans (dvd_pow_self π (by omega : N ≠ 0)) (hcong 2)
        exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal_iff_dvd hπ _).2 h2)
      · exact (mem_maximalIdeal_iff_dvd hπ _).2
          (dvd_trans (dvd_pow_self π (by omega : N ≠ 0)) (hcong 1))
    have hbad : 3 * r ^ 2 + 2 * a 2 * r + a 1 ∈ maximalIdeal O := by
      have hid : 3 * r ^ 2 + 2 * a 2 * r + a 1
          = (3 * r ^ 2 + 2 * a' 2 * r + a' 1) - (2 * (a' 2 - a 2) * r + (a' 1 - a 1)) := by ring
      rw [hid]
      exact Ideal.sub_mem _ hmem hshift
    exact absurd hbad (notMem_maximalIdeal.2 hu)
  -- ordinary Hensel: a root `r′ ≡ r (mod 𝔪)`
  obtain ⟨r', hr', hδ⟩ := exists_cubic_root a' r
    ((mem_maximalIdeal_iff_dvd hπ _).2 (dvd_trans (dvd_pow_self π (by omega)) hE)) hu'
  refine ⟨r', hr', ?_⟩
  rw [cubic_eval] at hr'
  -- the exact expansion: `0 = E + δ·U` with `U` a unit
  set δ := r' - r with hδdef
  have hU : IsUnit ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hsmall : (3 * r + a' 2) * δ + δ ^ 2 ∈ maximalIdeal O := by
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hδ) ?_
      rw [pow_two]
      exact Ideal.mul_mem_left _ _ hδ
    have hbad : 3 * r ^ 2 + 2 * a' 2 * r + a' 1 ∈ maximalIdeal O := by
      have hid : 3 * r ^ 2 + 2 * a' 2 * r + a' 1
          = ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2)
            - ((3 * r + a' 2) * δ + δ ^ 2) := by ring
      rw [hid]
      exact Ideal.sub_mem _ hmem hsmall
    exact absurd hbad (notMem_maximalIdeal.2 hu')
  have hexp : δ * ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2)
      = -(r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0) := by
    rw [hδdef]
    linear_combination hr'
  have hdvd : π ^ N ∣ δ * ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2) := by
    rw [hexp]
    exact hE.neg_right
  exact dvd_of_isUnit_mul hU (by rwa [mul_comm] at hdvd)

/-- The quadratic cofactors of two congruent cubics, at their respective roots, are congruent —
with the same modulus. -/
theorem peel_congr {π : O} {a a' : Fin 3 → O} {N : ℕ} {r r' : O}
    (hcong : ∀ i, π ^ N ∣ (a' i - a i)) (hrr : π ^ N ∣ (r' - r)) :
    ∀ i, π ^ N ∣ (peel a' r' i - peel a r i) := by
  intro i
  fin_cases i
  · show π ^ N ∣ (peel a' r' 0 - peel a r 0)
    simp only [peel_zero]
    have hid : (a' 1 + a' 2 * r' + r' ^ 2) - (a 1 + a 2 * r + r ^ 2)
        = (a' 1 - a 1) + (a' 2 - a 2) * r' + a 2 * (r' - r) + (r' - r) * (r' + r) := by ring
    rw [hid]
    exact dvd_add (dvd_add (dvd_add (hcong 1) ((hcong 2).mul_right _)) (hrr.mul_left _))
      (hrr.mul_right _)
  · show π ^ N ∣ (peel a' r' 1 - peel a r 1)
    simp only [peel_one]
    have hid : (a' 2 + r') - (a 2 + r) = (a' 2 - a 2) + (r' - r) := by ring
    rw [hid]
    exact dvd_add (hcong 2) hrr

end PeelCong

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_linear_mul
#print axioms Uniformity.Density.cubic_peel
#print axioms Uniformity.Density.exists_cubic_root
#print axioms Uniformity.Density.cubeCoeff_injective
#print axioms Uniformity.Density.cubic_trichotomy
#print axioms Uniformity.Density.typeOf_shiftVec
#print axioms Uniformity.Density.dvd_shiftVec_sub
#print axioms Uniformity.Density.shiftVec_mem_iff
#print axioms Uniformity.Density.cubic_structure
#print axioms Uniformity.Density.exists_root_congr
#print axioms Uniformity.Density.peel_congr

end AxCheck
