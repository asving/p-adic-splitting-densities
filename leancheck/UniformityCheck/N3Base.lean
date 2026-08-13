/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity

/-!
# UniformityCheck.N3Base — the degree-3 scaffolding

Everything the `n = 3` certificates share, and nothing about densities yet:

* the five cubic splitting types `c3split`, `c3linInert`, `c3inert`, `c3linRam`, `c3ram`
  (`{(1,1)}³`, `{(1,1),(1,2)}`, `{(1,3)}`, `{(1,1),(2,1)}`, `{(3,1)}`), their degrees and their
  pairwise distinctness (needed to sum five densities);
* **`typeOf_mul`** — `typeOf` is additive on monic products, because `monicFactors` is. This is
  what reduces three of the five cubic types to a linear factor times a quadratic whose type
  `leanfinal` already certifies;
* the shape of a monic cubic (`cubic_expand`, `cubic_eval`, `cubic_deriv_eval`);
* **`cubic_peel`** — dividing out a root: if `f(r) = 0` then `monicPoly a = (X - C r) * monicPoly
  (peel a r)` with `peel a r = ![a₁ + a₂ r + r², a₂ + r]` (a `ring` identity, no division);
* **`exists_cubic_root`** — Hensel at a simple residue root, the only place completeness enters;
* `irreducible_of_map_irreducible` — a monic polynomial whose reduction is irreducible is
  irreducible.

Nothing here assumes anything about the residue characteristic.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

/-! ## 1. The five cubic splitting types -/

/-- Three linear factors: `σ = {(1,1),(1,1),(1,1)}`. -/
def c3split : FactorizationType := ⟨{(1, 1), (1, 1), (1, 1)}⟩

/-- A linear factor times an inert quadratic: `σ = {(1,1),(1,2)}`. -/
def c3linInert : FactorizationType := ⟨{(1, 1), (1, 2)}⟩

/-- Irreducible and unramified: `σ = {(1,3)}`. -/
def c3inert : FactorizationType := ⟨{(1, 3)}⟩

/-- A linear factor times a ramified quadratic: `σ = {(1,1),(2,1)}`. -/
def c3linRam : FactorizationType := ⟨{(1, 1), (2, 1)}⟩

/-- Totally ramified: `σ = {(3,1)}`. -/
def c3ram : FactorizationType := ⟨{(3, 1)}⟩

theorem c3split_degree : c3split.degree = 3 := by decide
theorem c3linInert_degree : c3linInert.degree = 3 := by decide
theorem c3inert_degree : c3inert.degree = 3 := by decide
theorem c3linRam_degree : c3linRam.degree = 3 := by decide
theorem c3ram_degree : c3ram.degree = 3 := by decide

theorem ne_of_data_ne {σ τ : FactorizationType} (h : σ.data ≠ τ.data) : σ ≠ τ := fun hst =>
  h (by rw [hst])

theorem c3split_ne_c3linInert : c3split ≠ c3linInert := ne_of_data_ne (by decide)
theorem c3split_ne_c3inert : c3split ≠ c3inert := ne_of_data_ne (by decide)
theorem c3split_ne_c3linRam : c3split ≠ c3linRam := ne_of_data_ne (by decide)
theorem c3split_ne_c3ram : c3split ≠ c3ram := ne_of_data_ne (by decide)
theorem c3linInert_ne_c3inert : c3linInert ≠ c3inert := ne_of_data_ne (by decide)
theorem c3linInert_ne_c3linRam : c3linInert ≠ c3linRam := ne_of_data_ne (by decide)
theorem c3linInert_ne_c3ram : c3linInert ≠ c3ram := ne_of_data_ne (by decide)
theorem c3inert_ne_c3linRam : c3inert ≠ c3linRam := ne_of_data_ne (by decide)
theorem c3inert_ne_c3ram : c3inert ≠ c3ram := ne_of_data_ne (by decide)
theorem c3linRam_ne_c3ram : c3linRam ≠ c3ram := ne_of_data_ne (by decide)

/-! ## 2. `typeOf` is additive on monic products -/

section Mul

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The monic factorization of a product is the sum of the factorizations. -/
theorem monicFactors_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
    monicFactors (f * g) = monicFactors f + monicFactors g := by
  refine monicFactors_eq ⟨fun h hh => ?_, ?_⟩
  · rcases Multiset.mem_add.1 hh with h1 | h1
    · exact (monicFactors_spec hf).1 h h1
    · exact (monicFactors_spec hg).1 h h1
  · rw [Multiset.prod_add, (monicFactors_spec hf).2, (monicFactors_spec hg).2]

/-- **`typeOf` is additive.** -/
theorem typeOf_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
    (typeOf (f * g)).data = (typeOf f).data + (typeOf g).data := by
  rw [typeOf_data, typeOf_data, typeOf_data, monicFactors_mul hf hg, Multiset.map_add]

/-- The type of a monic linear factor. -/
theorem typeOf_X_sub_C (r : O) : typeOf (X - C r) = ⟨{(1, 1)}⟩ :=
  typeOf_of_natDegree_one (monic_X_sub_C r) (natDegree_X_sub_C r)

/-- **Peeling a linear factor off, at the level of types.** -/
theorem typeOf_linear_mul {g : Polynomial O} (hg : g.Monic) (r : O) :
    (typeOf ((X - C r) * g)).data = (1, 1) ::ₘ (typeOf g).data := by
  rw [typeOf_mul (monic_X_sub_C r) hg, typeOf_X_sub_C]
  rfl

end Mul

/-! ## 3. The shape of a monic cubic -/

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

/-- The constant term of the cofactor: `a₀ = -r · g₀`. -/
theorem peel_const (a : Fin 3 → O) (r : O) (hr : (monicPoly a).eval r = 0) :
    a 0 = -(r * peel a r 0) := by
  rw [cubic_eval] at hr
  simp only [peel_zero]
  linear_combination hr

end Shape

/-! ## 4. Hensel at a simple residue root -/

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

/-! ## 5. Irreducibility descends from the residue field -/

section Irr

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A monic polynomial whose reduction mod `𝔪` is irreducible is itself irreducible. -/
theorem irreducible_of_map_irreducible {f : Polynomial O} (hf : f.Monic)
    (h : Irreducible (f.map (residue O))) : Irreducible f := by
  have hdeg : (f.map (residue O)).natDegree = f.natDegree := hf.natDegree_map _
  constructor
  · intro hu
    refine h.not_isUnit ?_
    exact hu.map (Polynomial.mapRingHom (residue O))
  · intro g k hgk
    have hgu : IsUnit g.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic hf ⟨k, hgk⟩
    have hku : IsUnit k.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic hf ⟨g, by rw [hgk]; ring⟩
    -- degrees survive reduction because the leading coefficients are units
    have hdegmap : ∀ p : Polynomial O, IsUnit p.leadingCoeff →
        (p.map (residue O)).natDegree = p.natDegree := fun p hp =>
      natDegree_map_eq_of_isUnit_leadingCoeff _ hp
    have hmapmul : f.map (residue O) = g.map (residue O) * k.map (residue O) := by
      rw [hgk, Polynomial.map_mul]
    rcases h.isUnit_or_isUnit hmapmul with hu | hu
    · left
      have h0 : g.natDegree = 0 := by
        rw [← hdegmap g hgu, natDegree_eq_zero_of_isUnit hu]
      rw [eq_C_of_natDegree_eq_zero h0]
      refine isUnit_C.2 ?_
      rwa [leadingCoeff, h0] at hgu
    · right
      have h0 : k.natDegree = 0 := by
        rw [← hdegmap k hku, natDegree_eq_zero_of_isUnit hu]
      rw [eq_C_of_natDegree_eq_zero h0]
      refine isUnit_C.2 ?_
      rwa [leadingCoeff, h0] at hku

end Irr

end UniformityCheck
