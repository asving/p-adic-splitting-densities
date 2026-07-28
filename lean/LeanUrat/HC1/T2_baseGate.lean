/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.T1_baseStage

/-!
# HC1.T2_baseGate — concrete base inhabitant at p = 2, F = F₄, φ = X² + X + 1

moves_ref: MOVES 1992–1994. deps: T1. The honest replacement for MovesGr's held
`L4_base_nonvacuity_gate`, at the honest base pin; (e,h) = (1,1). difficulty: HARD
(the concrete Gauss-valuation fields are labor; escalation-risk). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- The base key `φ = X² + X + 1 ∈ ℤ_[2][X]` reduces mod 2 to `X² + X + 1 ∈ 𝔽₂[X]`. -/
private lemma baseKey_map :
    (X ^ 2 + X + 1 : Polynomial ℤ_[2]).map (PadicInt.toZMod (p := 2))
      = (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]

/-- The reduced base key is irreducible over `𝔽₂` (degree 2, no root in `𝔽₂`). -/
private lemma baseKey_irr :
    Irreducible ((X ^ 2 + X + 1 : Polynomial ℤ_[2]).map (PadicInt.toZMod (p := 2))) := by
  rw [baseKey_map]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    rw [h]; decide
  · intro x
    fin_cases x <;>
      simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one] <;> decide

/-- Over `𝔽₄ = GaloisField 2 2` the base key `X² + X + 1` has a root: any element
outside the prime subfield `{0, 1}` is one (Frobenius `z⁴ = z` factors as
`z(z-1)(z²+z+1)`). -/
private lemma exists_baseRoot : ∃ z : GaloisField 2 2, z ^ 2 + z + 1 = 0 := by
  classical
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using GaloisField.card 2 2 (by norm_num)
  -- some element lies outside the prime subfield {0, 1}
  have hne : ∃ z : GaloisField 2 2, z ≠ 0 ∧ z ≠ 1 := by
    by_contra h
    have h' : ∀ z : GaloisField 2 2, z ≠ 0 → z = 1 := by
      intro z hz0
      by_contra hz1
      exact h ⟨z, hz0, hz1⟩
    have hsub : (Finset.univ : Finset (GaloisField 2 2)) ⊆ {0, 1} := by
      intro z _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases eq_or_ne z 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h' z h0)
    have hcle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at hcle
    have hle : ({0, 1} : Finset (GaloisField 2 2)).card ≤ 2 := by
      apply le_trans (Finset.card_insert_le _ _); simp
    omega
  obtain ⟨z, hz0, hz1⟩ := hne
  refine ⟨z, ?_⟩
  have hpow : z ^ 4 = z := by
    have := FiniteField.pow_card z
    rwa [hcard] at this
  have hfact : z * (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hpow
  have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rcases mul_eq_zero.mp hfact with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hz0
    · exact absurd h' h1
  · exact h

/-- Unit T2: the tower base is non-vacuous — a concrete faithfully-based stage with
its round-5 core exists over the ambient F₄. -/
theorem T2_baseGate :
    ∃ σ : Stage 2 (GaloisField 2 2), IsBaseStage σ ∧ StageCoreL σ := by
  obtain ⟨z0, hz0root⟩ := exists_baseRoot
  -- assemble the §A base read pins at p = 2, φ = X²+X+1, (e,h) = (1,1)
  have bdata : BaseReadData 2 (GaloisField 2 2) 1 1 :=
    { φ := X ^ 2 + X + 1
      hmonic := by monicity!
      hdeg := by
        have h2 : (X ^ 2 + X + 1 : Polynomial ℤ_[2]).natDegree = 2 := by compute_degree!
        omega
      hirr := baseKey_irr
      res := algebraMap (ZMod 2) (GaloisField 2 2)
      z0 := z0
      hz0 := by
        rw [baseKey_map]
        simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one]
        exact hz0root
      he := le_refl 1
      hh := le_refl 1
      hcop := by decide }
  obtain ⟨σ, hbase, hcore, _, _⟩ := T1_baseStage (p := 2) (F := GaloisField 2 2) 1 1 bdata
  exact ⟨σ, hbase, hcore⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T2_baseGate
