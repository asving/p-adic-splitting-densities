/-
Unit E3.frameField_eq_pool  (MovesD campaign, E-phase)  [AUX]
informal: the frame field's image in F IS the pool (the unique subfield per order — what
lets classes of DIFFERENT members share one eligible-factor universe).
deps (blueprint): E1, E2.  [as-built, 2026-07-30 verify-2 fold-in: imports only Defs;
E1's `digit_in_pool` is not used, and E2's content is inlined (`pool_ncard_le` below),
so this unit rests only on Defs.]
sketch: range is a subfield of card p^w inside pool (E1); pool has ≤ p^w elements (E2);
equal cards force equality.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open Polynomial in
/-- The pool `{x : F | x ^ (p^w) = x}` has at most `p^w` elements: it is the root set of
the nonzero polynomial `X^(p^w) - X`, whose degree is `p^w`. (E2's content, inlined so
this unit rests only on `Defs`.) -/
private theorem pool_ncard_le {w : ℕ} (hp : 1 < p) (hw : w ≠ 0) :
    (pool p w F).ncard ≤ p ^ w := by
  classical
  have hq2 : 1 < p ^ w := Nat.one_lt_pow hw hp
  set P : Polynomial F := X ^ (p ^ w) - X with hP
  have hPne : P ≠ 0 := by
    intro h
    have h1 : (1 : ℕ) ≠ p ^ w := by omega
    have hc : P.coeff (p ^ w) = 1 := by
      simp [hP, coeff_X_pow, coeff_X, h1]
    rw [h] at hc
    simp at hc
  have hpeq : pool p w F = (↑(P.roots.toFinset) : Set F) := by
    ext x
    rw [pool, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots',
      and_iff_right hPne, IsRoot.def, hP]
    simp only [eval_sub, eval_pow, eval_X, sub_eq_zero]
  rw [hpeq, Set.ncard_coe_finset]
  calc P.roots.toFinset.card
      ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := P.card_roots'
    _ ≤ p ^ w := by
        rw [hP]
        calc (X ^ (p ^ w) - X : Polynomial F).natDegree
            ≤ max ((X ^ (p ^ w) : Polynomial F).natDegree)
                ((X : Polynomial F).natDegree) := natDegree_sub_le _ _
          _ = max (p ^ w) 1 := by rw [natDegree_X_pow, natDegree_X]
          _ = p ^ w := by omega

/-- The matched frame field's image in F IS the pool. -/
theorem frameField_eq_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    (Set.range (fun a : ↥ν.σ.K => (a : F))) = pool p R.w F := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcard, -⟩ := hM
  -- `hcard : Nat.card ↥ν.σ.K = p ^ R.w`
  set K := ν.σ.K with hKdef
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  have hw1 : R.w ≠ 0 := by have := R.hw; omega
  have hcardf : Fintype.card ↥K = p ^ R.w := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  -- Step 1: the image of the (finite, card p^w) subfield sits inside the pool.
  have hsub : Set.range (fun a : ↥K => (a : F)) ⊆ pool p R.w F := by
    rintro x ⟨a, rfl⟩
    rw [pool, Set.mem_setOf_eq]
    have hpow : a ^ (Fintype.card ↥K) = a := FiniteField.pow_card a
    rw [hcardf] at hpow
    calc ((a : F)) ^ (p ^ R.w) = ((a ^ (p ^ R.w) : ↥K) : F) := by push_cast; ring
      _ = (a : F) := by rw [hpow]
  -- Step 2: the image has exactly p^w elements (coercion is injective).
  have hinj : Function.Injective (fun a : ↥K => (a : F)) := fun a b hab => Subtype.ext hab
  have hSncard : (Set.range (fun a : ↥K => (a : F))).ncard = p ^ R.w := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    exact hcard
  -- Step 3: the pool has at most p^w elements, so the inclusion is an equality.
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [hSncard]
  exact pool_ncard_le hp2 hw1

end LeanUrat.MovesD
