/-
Unit XA.2 selForce  [PROVED, fleet 2026-07-28]
moves_ref: "μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side".
deps: XA.1. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem selForce {n : ℕ} (ν : XNode n) (g μ : ℕ) (hs : ν.sel = some (g, μ))
    (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell ∧ rowOf ν = .T1 := by
  obtain ⟨hg, hmu, hbound⟩ := ν.selBound g μ hs
  have hell : 2 ≤ ν.ell := by
    rcases h2 with h | h
    · calc (2 : ℕ) = 2 * 1 := by ring
        _ ≤ μ * g := Nat.mul_le_mul h hg
        _ ≤ ν.ell := hbound
    · calc (2 : ℕ) = 1 * 2 := by ring
        _ ≤ μ * g := Nat.mul_le_mul hmu h
        _ ≤ ν.ell := hbound
  refine ⟨hell, ?_⟩
  have hne : ν.sel ≠ none := by rw [hs]; exact Option.some_ne_none _
  simp only [rowOf, if_neg hne, if_pos hell]

end LeanUrat.MovesX
