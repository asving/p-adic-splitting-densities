/-
Unit U-18b `interp_unique` (easy) — interpolant uniqueness on infinite OK sets.
sketch: U-27 on f − g.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem interp_unique (S : Set ℚ) (hS : S.Infinite) (f g : Qq)
    (hf : ∀ x ∈ S, f ∈ OKat x) (hg : ∀ x ∈ S, g ∈ OKat x)
    (h : ∀ x (hx : x ∈ S), evalAt x ⟨f, hf x hx⟩ = evalAt x ⟨g, hg x hx⟩) :
    f = g :=
  sorry

end LeanUrat.MovesS
