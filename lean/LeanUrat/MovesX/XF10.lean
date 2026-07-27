/-
Unit XF.10 discZeroNull — UNCONDITIONAL over the context (Ruling 2)
[E-phase: PROVED, body complete]
moves_ref: "corollary μ{disc f = 0} = 0".
sketch: discZero ⊆ {D ≤ vdisc ∨ discZero} for every D, so `C.vdisc_le_tail` + XF.8 +
`frac_nonneg` squeeze. deps: XF.8. difficulty: MEDIUM (EASY-MEDIUM band).
hyp_fields: XCtx's `vdisc_le_tail` (definitional cylinder fact, blueprint §4).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF8

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem discZeroNull (n p : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (C : XCtx n p) :
    C.frac (discZero n p) = 0 := by
  -- For every level `D`, `discZero ⊆ { f | D ≤ vdisc f ∨ f ∈ discZero }`, so `frac_mono`
  -- feeds the cylinder tail bound `vdisc_le_tail`; the tail → 0 (XF.8) squeezes `frac`.
  have hbound : ∀ D, C.frac (discZero n p) ≤ (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D) := by
    intro D
    have hsub : discZero n p ⊆ { f | D ≤ vdisc f ∨ f ∈ discZero n p } := fun f hf => Or.inr hf
    exact le_trans (C.frac_mono _ _ hsub) (C.vdisc_le_tail D)
  have hle : C.frac (discZero n p) ≤ 0 :=
    ge_of_tendsto' (tailZero p n h2) hbound
  exact le_antisymm hle (C.frac_nonneg _)

end LeanUrat.MovesX
