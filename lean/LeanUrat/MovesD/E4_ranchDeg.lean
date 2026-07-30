/-
Unit E4.Ranch_deg  (MovesD campaign, E-phase)  [AUX]
informal: deg R_anch = ℓ_r — the note's "deg R_anch,r equals that side's NORMALIZED
horizontal length ℓ_r := w'_r/e_r" (L11), PROVED from the node Props.
deps: MovesC.
sketch: `hRanch` (the pattern sum) + `hpatTop` (top digit ≠ 0): natDegree of
Σ_{k≤len} C(pat k)·X^k with nonzero top.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC
open Polynomial

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The `n`-coefficient of `Σ_{k≤n} C(a k)·Xᵏ` is `a n` (all other terms vanish there). -/
private lemma coeff_C_pat_sum {K : Type*} [Semiring K] (n : ℕ) (a : ℕ → K) :
    (∑ k ∈ Finset.range (n + 1), C (a k) * X ^ k).coeff n = a n := by
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_self, if_true]

/-- The natDegree of `Σ_{k≤n} C(a k)·Xᵏ` is `n` when the top digit is nonzero. -/
private lemma natDegree_C_pat_sum {K : Type*} [Semiring K] (n : ℕ) (a : ℕ → K)
    (ha : a n ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), C (a k) * X ^ k).natDegree = n := by
  refine le_antisymm ?_ ?_
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    simp only [Finset.mem_range] at hi
    calc (C (a i) * X ^ i).natDegree ≤ i := natDegree_C_mul_X_pow_le (a i) i
      _ ≤ n := by omega
  · apply le_natDegree_of_ne_zero
    rwa [coeff_C_pat_sum]

/-- deg R_anch = ℓ_r = wSide/e, from the node Props alone. -/
theorem Ranch_deg (ν : Node p F) : ν.Ranch.natDegree = ν.wSide / ν.e := by
  rw [ν.hRanch]
  exact natDegree_C_pat_sum (ν.wSide / ν.e) ν.pat ν.hpatTop

end LeanUrat.MovesD
