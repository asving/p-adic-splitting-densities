/-
Unit E2.pool_card_le  (MovesD campaign, E-phase)  [AUX]
deps: Defs.
sketch: roots of the nonzero X^{p^w} − X; `Polynomial.card_roots`.
difficulty: medium.  hypothesis_fields: none.
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

/-- The pool has at most p^w elements (roots of the nonzero X^{p^w} − X). -/
theorem pool_card_le {w : ℕ} (hp : 2 ≤ p) (hw : 1 ≤ w) :
    Nat.card ↥(pool p w F) ≤ p ^ w := by
  classical
  -- The pool is the root set of `P = X^(p^w) - X`, a nonzero polynomial of degree `p^w`.
  set P : Polynomial F := Polynomial.X ^ (p ^ w) - Polynomial.X with hP
  have hpw : 2 ≤ p ^ w := Nat.one_lt_pow (by omega) (by omega)
  -- `P.coeff (p^w) = 1`, hence `P ≠ 0`.
  have hcoeff : P.coeff (p ^ w) = 1 := by
    rw [hP, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      if_pos rfl, if_neg (by omega : ¬ (1 = p ^ w))]
    ring
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  -- `P.natDegree ≤ p^w`.
  have hdeg : P.natDegree ≤ p ^ w := by
    rw [hP]
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    exact max_le (le_refl _) (by omega)
  -- The pool is contained in the (finite) set of roots of `P`.
  have hsub : pool p w F ⊆ (↑P.roots.toFinset : Set F) := by
    intro x hx
    have hxr : x ^ (p ^ w) = x := hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hP0, ?_⟩
    change Polynomial.eval x P = 0
    rw [hP]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hxr, sub_self]
  -- Count: pool ≤ roots.toFinset.card ≤ card roots ≤ natDegree ≤ p^w.
  calc Nat.card ↥(pool p w F)
      = (pool p w F).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑P.roots.toFinset : Set F).ncard :=
        Set.ncard_le_ncard hsub P.roots.toFinset.finite_toSet
    _ = P.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' _
    _ ≤ p ^ w := hdeg

end LeanUrat.MovesD
