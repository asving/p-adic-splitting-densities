/-
Unit XA.1 rowTotal  [E-phase: stated, body sorry]
moves_ref: "Every continuing node … exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h…)".
deps: Defs. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The row classification is total and exclusive: the five characterizations. -/
theorem rowTotal {n : ℕ} (ν : XNode n) :
    (rowOf ν = .T5 ↔ ν.sel = none) ∧
    (rowOf ν = .T1 ↔ ν.sel ≠ none ∧ 2 ≤ ν.ell) ∧
    (rowOf ν = .T2 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ 2 ≤ ν.h) ∧
    (rowOf ν = .T3 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1) ∧
    (rowOf ν = .T4 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ ν.e = 1) := by
  sorry

end LeanUrat.MovesX
