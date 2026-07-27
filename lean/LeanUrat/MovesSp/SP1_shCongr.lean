/-
Unit Sp.shCongr — moves_ref: "with u₀ := the left endpoint's height,
γ = e·u₀ + s₀′·h, so modulo e t·γ ≡ t·h·s₀′ ≡ (1 − e·s)·s₀′ ≡ s₀′".
sketch: substitute hγ; t·γ − s₀′ = e·(t·u0) + s₀′·(t·h − 1) = e·(t·u0 − s₀′·s);
`Int.ModEq` via dvd, `ring_nf`. difficulty: easy.
Hypothesis names mirror `Moves.Stage` fields (hbez ↔ `hbez`).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem sh_congr (e h s t γ u0 s0 : ℤ) (hbez : e * s + h * t = 1)
    (hγ : γ = e * u0 + s0 * h) : t * γ ≡ s0 [ZMOD e] := by
  have hdvd : s0 - t * γ = e * (s * s0 - t * u0) := by
    linear_combination (-t) * hγ + (-s0) * hbez
  rw [Int.modEq_iff_dvd]
  exact ⟨s * s0 - t * u0, hdvd⟩

end LeanUrat.MovesSp
