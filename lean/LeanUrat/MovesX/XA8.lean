/-
Unit XA.8 t34Zero  [PROVED via XA.1 rowTotal + XA.6 lat1]
moves_ref: T3/T4 zero rulings. FINDING-1 SEMANTICS: the "0" records that the table
supplies NO POSITIVE PER-SIDE BOUND at T3/T4 — NEVER "actual ind_r = 0".
deps: XA.1, XA.6. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1
import LeanUrat.MovesX.XA6

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- T3/T4 zero rulings: empty region and `ind2 = 0` — "no positive per-side bound",
never "actual index zero" (finding-1 semantics). -/
theorem t34Zero {n : ℕ} (ν : XNode n) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) :
    ν.region.card = 0 ∧ ind2 ν = 0 := by
  obtain ⟨_, _, _, hT3, hT4⟩ := rowTotal ν
  -- XA.6: at ℓ = 1 the region count satisfies `2·card = (e-1)(h-1)`.
  have hcard := lat1 ν.s0 ν.u0 ν.e ν.h ν.epos ν.hpos ν.hcop
  refine ⟨?_, ?_⟩
  · -- region.card = 0: T3 forces h = 1, T4 forces e = 1, so one factor of (e-1)(h-1) is 0.
    rcases h34 with h3 | h4
    · obtain ⟨_, hell, _, hh⟩ := hT3.mp h3
      have hzero : (ν.e - 1) * (ν.h - 1) = 0 := by simp [hh]
      rw [hzero] at hcard
      unfold XNode.region
      rw [hell]
      omega
    · obtain ⟨_, hell, he⟩ := hT4.mp h4
      have hzero : (ν.e - 1) * (ν.h - 1) = 0 := by simp [he]
      rw [hzero] at hcard
      unfold XNode.region
      rw [hell]
      omega
  · -- ind2 = 0: the T3/T4 arms of the `ind2` match are both `0` (finding-1 semantics).
    rcases h34 with h | h <;> simp only [ind2, h]

end LeanUrat.MovesX
