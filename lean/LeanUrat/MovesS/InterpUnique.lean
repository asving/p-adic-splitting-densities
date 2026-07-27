/-
Unit U-18b `interp_unique` (easy) — interpolant uniqueness on infinite OK sets.
sketch: U-27 on f − g.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem interp_unique (S : Set ℚ) (hS : S.Infinite) (f g : Qq)
    (hf : ∀ x ∈ S, f ∈ OKat x) (hg : ∀ x ∈ S, g ∈ OKat x)
    (h : ∀ x (hx : x ∈ S), evalAt x ⟨f, hf x hx⟩ = evalAt x ⟨g, hg x hx⟩) :
    f = g := by
  -- Apply U-27 (a rational function vanishing at infinitely many OK points is 0) to
  -- `f - g`: the denominator stays regular on `S` (OKat is a subring), and the value
  -- `(f - g)(x) = 0` follows because `evalAt x` is a ring hom and `f, g` agree there.
  apply sub_eq_zero.mp
  refine ratfunc_eval_infinite _ S hS ?_ ?_
  · -- denominator regular on `S`: `f - g ∈ OKat x`
    intro x hx
    have hmem : f - g ∈ OKat x := (OKat x).sub_mem (hf x hx) (hg x hx)
    exact mem_OKat_iff.mp hmem
  · -- the value `(f - g)(x) = 0`, via the ring hom `evalAt x`
    intro x hx
    have hmem : f - g ∈ OKat x := (OKat x).sub_mem (hf x hx) (hg x hx)
    have hsplit : (⟨f - g, hmem⟩ : OKat x) = ⟨f, hf x hx⟩ - ⟨g, hg x hx⟩ := by
      apply Subtype.ext
      simp
    have key : evalAt x ⟨f - g, hmem⟩ = 0 := by
      rw [hsplit, map_sub, h x hx, sub_self]
    exact key

end LeanUrat.MovesS
