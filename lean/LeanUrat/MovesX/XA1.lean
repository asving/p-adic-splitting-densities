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
  have hell := ν.ellpos
  have he := ν.epos
  have hh := ν.hpos
  unfold rowOf
  split_ifs with h1 h2 h3 h4 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;> omega

end LeanUrat.MovesX
