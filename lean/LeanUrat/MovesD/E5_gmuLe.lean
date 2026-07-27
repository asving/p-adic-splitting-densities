/-
Unit E5.gmu_le_len  (MovesD campaign, E-phase)  [AUX]
informal: g·μ ≤ ℓ_r (each eligible factor contributes g·μ to deg R_anch — L11).
deps: E4.
sketch: `hOrd` gives ψ^μ ∣ Ranch, Ranch ≠ 0 (hpatTop); degrees: μ·g = deg ψ^μ ≤
deg Ranch = ℓ (hψdeg, E4).  difficulty: medium.  hypothesis_fields: none.
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

/-- g·μ ≤ ℓ_r: the descend factor's degree contribution fits the side length. -/
theorem gmu_le_len (ν : Node p F) : ν.g * ν.μ ≤ ν.wSide / ν.e := by
  -- `Ranch ≠ 0`: else `ψ^(μ+1) ∣ 0` would hold, contradicting `hOrd`.
  have hRne : ν.Ranch ≠ 0 := fun h => ν.hOrd.2 (h ▸ dvd_zero _)
  -- `ψ^μ ∣ Ranch` gives `deg (ψ^μ) ≤ deg Ranch`.
  have hdeg : (ν.ψ ^ ν.μ).natDegree ≤ ν.Ranch.natDegree :=
    Polynomial.natDegree_le_of_dvd ν.hOrd.1 hRne
  -- `deg (ψ^μ) = μ * g` (ψ over a field; `hψdeg`).
  have hpow : (ν.ψ ^ ν.μ).natDegree = ν.μ * ν.g := by
    rw [Polynomial.natDegree_pow, ν.hψdeg]
  -- `deg Ranch ≤ wSide/e` from the pattern sum `hRanch`.
  have hub : ν.Ranch.natDegree ≤ ν.wSide / ν.e := by
    rw [ν.hRanch]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    simp only [Finset.mem_range] at hk
    omega
  rw [Nat.mul_comm, ← hpow]
  exact le_trans hdeg hub

end LeanUrat.MovesD
