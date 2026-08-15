/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.P5Consume

/-!
# UniformityCheck.N3Shift — recentring a cubic at a residual triple root

Unit `UNIFORMITY-CHECK-N3C`, layer 1 (`notes/N3_CHECK_2026-08-13.md` §13.1). The triple-root
stratum `tripleSet` of `N3Drain.lean` is the set of classes whose residue cubic is `(X − γ̄)³`.
Every argument on that stratum runs on the RECENTRED coefficient vector

    shiftVec a γ = ![F_a(γ), F_a′(γ), a₂ + 3γ] ,      F_a = monicPoly a ,

for which `monicPoly (shiftVec a γ) = (monicPoly a).comp (X + C γ)`; the type is unchanged
(`typeOf_shift`, unit P5), recentring is invertible coefficientwise, it preserves congruence mod
`π ^ N`, and — the bridge to `tripleSet` — all three components lie in `𝔪` exactly when the
residue vector is `cubeCoeff γ̄`.

The last theorem is the `π`-divisibility phrasing of the landed Eisenstein certificate (case **E**
of §13.1's four-case split), so that all four cases can be tested with `π ∣ ·` predicates.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Shift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

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

/-- Local restatement of `Uniformity.Density.mem_maximalIdeal_pow_iff_dvd` (same one-line proof)
without that lemma's `Finite (ResidueField O)` section hypothesis, which this file does not carry:
`𝔪 ^ N = (π ^ N)` for a uniformizer `π`. -/
private theorem mem_maximalIdeal_pow_dvd {π : O} (hπ : Irreducible π) (N : ℕ) (x : O) :
    x ∈ (maximalIdeal O) ^ N ↔ π ^ N ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- **CASE E of §13.1**, in `π`-divisibility form: `v(B₀) = 1` (with `B₁, B₂ ∈ 𝔪`) forces
`{(3,1)}`. A restatement of `typeOf_ram3_of_eisenstein` through
`mem_maximalIdeal_pow_iff_dvd`. -/
theorem typeOf_ram3_of_val_one {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h0 : π ∣ b 0) (h0' : ¬ π ^ 2 ∣ b 0) (h1 : π ∣ b 1) (h2 : π ∣ b 2) :
    typeOf (monicPoly b) = c3ram := by
  have hmem : ∀ x : O, π ∣ x → x ∈ maximalIdeal O := fun x hx => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]; exact hx
  have h0m' : b 0 ∉ (maximalIdeal O) ^ 2 := fun hc =>
    h0' ((mem_maximalIdeal_pow_dvd hπ 2 (b 0)).1 hc)
  exact typeOf_ram3_of_eisenstein (hmem _ h0) h0m' (hmem _ h1) (hmem _ h2)

end Shift

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.monicPoly_shiftVec
#print axioms UniformityCheck.typeOf_shiftVec
#print axioms UniformityCheck.shiftVec_shiftVec_neg
#print axioms UniformityCheck.dvd_shiftVec_sub
#print axioms UniformityCheck.shiftVec_mem_iff
#print axioms UniformityCheck.typeOf_ram3_of_val_one

end AxCheck

end UniformityCheck
