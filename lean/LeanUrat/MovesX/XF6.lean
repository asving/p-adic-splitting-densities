/-
Unit XF.6 ballCover — pairwise-congruence covering (the a₀-translation)
[E-phase RESTORED 2026-07-27: the fleet's proof ("proved pending re-verification",
fleet record 328e926) FAILS independent re-verification — (kernel) deterministic
timeout at `ballCover`, reproduced twice in clean builds and once solo (>590s wall).
Proof text preserved VERBATIM at lean/notes/XF6_pending_reverify_2026-07-27.lean.txt
for the escalation prover; statement below unchanged (statement-fence). Body sorry.]
moves_ref: "the a₀-translation, union bound + Fubini" — f(θ) = a₀ + c(θ), c a₀-free.
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
