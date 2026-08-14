/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.Density.Transport — `monicPoly` is onto the monic degree-`n` polynomials

**CN-01** (`spec/CERTAIN_NODES_2026-08-14.md`). `LocalData.lean` defines `monicPoly : (Fin n → O)
→ Polynomial O` and proves it is monic of degree `n` (`monicPoly_monic`, `monicPoly_natDegree`),
but never that every monic degree-`n` polynomial arises this way. This file supplies that
surjectivity, via the coefficient-reading witness `a i := f.coeff i`.

This is the transport lemma every polynomial-level theorem needs to be read off through the
census (`DecidedAt`/`PossibleAt`/`decidedSet`/`possibleSet`, which quantify over `Fin n → O`
through `monicPoly`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O]

/-- **The coefficients of `monicPoly a` below degree `n` are exactly `a`.** -/
theorem monicPoly_coeff_lt {n : ℕ} (a : Fin n → O) {i : ℕ} (h : i < n) :
    (monicPoly a).coeff i = a ⟨i, h⟩ := by
  unfold monicPoly
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt h), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨i, h⟩ : Fin n)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbi
    have hne : i ≠ (b : ℕ) := by
      intro heq
      exact hbi (Fin.ext heq.symm)
    rw [coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]
  · intro hni
    exact absurd (Finset.mem_univ _) hni

/-- **CN-01 — every monic degree-`n` polynomial is a `monicPoly`.** Witness:
`a i := f.coeff i`. The below-degree coefficients match by `monicPoly_coeff_lt`; the
degree-`n` coefficient matches because both sides are monic of degree `n`
(`Monic.coeff_natDegree`); above degree `n` both sides vanish
(`coeff_eq_zero_of_natDegree_lt`). -/
theorem exists_monicPoly_eq {n : ℕ} {f : Polynomial O} (hf : f.Monic) (hd : f.natDegree = n) :
    ∃ a : Fin n → O, monicPoly a = f := by
  refine ⟨fun i => f.coeff (i : ℕ), ?_⟩
  set a : Fin n → O := fun i => f.coeff (i : ℕ) with ha
  have hdeg : (monicPoly a).natDegree = n := monicPoly_natDegree a
  apply Polynomial.ext
  intro i
  rcases lt_trichotomy i n with hi | hi | hi
  · rw [monicPoly_coeff_lt a hi, ha]
  · subst hi
    have h1 : (monicPoly a).coeff i = 1 := by
      have := (monicPoly_monic a).coeff_natDegree
      rwa [hdeg] at this
    have h2 : f.coeff i = 1 := by
      have := hf.coeff_natDegree
      rwa [hd] at this
    rw [h1, h2]
  · have h1 : (monicPoly a).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hi)
    have h2 : f.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi)
    rw [h1, h2]

end Uniformity.Density
