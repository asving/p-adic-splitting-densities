/-  MovesV unit V6-4a `gateB_numbers` (ROSTER ENUMERATED C28) — gate B's
    dyadic arithmetic, every number displayed. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Polynomial

/-- (a) ι = 2·2⁻³ = 1/4, T(2) = 1, g = 2⁻³, μ̂ = ι·T·g = 2⁻⁵ = 1/32. -/
theorem gateB_mass : gateB_iota = 2 * (1/2 : ℚ) ^ 3 ∧ gateB_T = 1 ∧
    gateB_g = (1/2 : ℚ) ^ 3 ∧
    gateB_muhat = gateB_iota * gateB_T * gateB_g ∧ gateB_muhat = (1/2 : ℚ) ^ 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [gateB_iota, gateB_T, gateB_g, gateB_muhat]

/-- (b) count shadow 2·1 = 2 + marked pairs 2^{3N−5}: N = 3 ↦ 16, N = 4 ↦ 128. -/
theorem gateB_shadow_check : Ient.eval 2 * gateB_T = 2 ∧
    (2 : ℚ) ^ (3 * 3 - 5 : ℕ) = 16 ∧ (2 : ℚ) ^ (3 * 4 - 5 : ℕ) = 128 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Ient, gateB_T]
    norm_num
  · norm_num
  · norm_num

/-- (c) A(ε) = 3, W_ent(ε) = 3, degree facts. -/
theorem gateB_ledger : gateB_A = 3 ∧ gateB_Went = 3 ∧
    Ient.natDegree ≤ gateB_Went := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [Ient, gateB_Went]
  compute_degree
  norm_num

/-- (d) I^ent = q(q−1) = q·|β₀| ≠ |β₀| — the displayed NOT-general instance. -/
theorem gateB_ient_ne (q : ℚ) (hq : 2 ≤ q) : Ient.eval q ≠ q - 1 := by
  simp only [Ient]
  intro h
  simp at h
  nlinarith [h]

end LeanUrat.MovesV
