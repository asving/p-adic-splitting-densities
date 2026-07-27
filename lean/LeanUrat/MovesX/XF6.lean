/-
Unit XF.6 ballCover  [E-phase: stated, body sorry]
moves_ref: "the a₀-translation, union bound + Fubini" (pairwise-congruence form;
`Event`/`fTail` = Defs).
sketch: f′ a₀-free; event point → root θᵢ with V.w(a₀ + c(θᵢ)) ≤ p^{−tailExp};
same-index points ultrametrically congruent; `.toNat` trivializes tailExp ≤ 0.
deps: XF.2, XF.4, XF.5 (INTERNAL unit, V explicit). difficulty: MEDIUM-HARD.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF2
import LeanUrat.MovesX.XF4
import LeanUrat.MovesX.XF5

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem ballCover (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (aTail : Fin (n - 1) → ℤ_[p])
    (V : ValExt p (fTail n p (by omega) aTail)) :
    ∃ idx : ℤ_[p] → Fin (n - 1), ∀ a0 b0,
      Event p n D (by omega) aTail a0 → Event p n D (by omega) aTail b0 →
      idx a0 = idx b0 → (p : ℤ_[p]) ^ (tailExp p n D).toNat ∣ (a0 - b0) := by
  sorry

end LeanUrat.MovesX
