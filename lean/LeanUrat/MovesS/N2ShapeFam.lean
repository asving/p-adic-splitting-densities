/-
Unit `n2_shapefam` (easy; S5 construction batch) — ShapeFam (the n = 2 root
shapes, δOf ≡ 1); consumedDeltas = {1} at this instance (no split outcomes).
-/
import LeanUrat.MovesS.N2Shape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable def n2F : ShapeFam n2T := sorry

theorem n2_shapefam :
    (∀ Ŝ ∈ n2F.Sh, ∀ i, Ŝ.δOf i = 1) ∧
    n2F.Sh.Nonempty ∧
    consumedDeltas n2T n2F = {1} :=
  sorry

end LeanUrat.MovesS
