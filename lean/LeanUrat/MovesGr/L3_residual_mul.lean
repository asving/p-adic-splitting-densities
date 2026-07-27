import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `L3_residual_mul` — the DefsL residual multiplicativity `σ.hRmul` recovered as a THEOREM
of the genuine graded model `M`, without citing `σ.hRmul` itself.

Chain: `Rg.if_mul` (genuine `[fg] = [f][g]` in `gr`) transported by the ring homs
`algebraMap` and `Θ` gives `σ.grRes (fg) = σ.grRes f · σ.grRes g` (via `M.discharge`).
Expanding `grRes f = C(R f)·T(w f)` and using `σ.hwmul` (`w(fg)=w f+w g`, a valuation, allowed)
cancels the degree-1 unit `T`, leaving `C(R(fg)) = C(R f · R g)`; `LaurentPolynomial.C` is
injective (coefficient at 0), giving the claim. -/
theorem L3_residual_mul (σ : Stage p F) (M : GenuineStageModel σ) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) : σ.R (f * g) = σ.R f * σ.R g := by
  letI := M.Rg.ring
  letI := M.alg
  letI := M.Loring
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hif : M.S.initialForm (f * g) = M.S.initialForm f * M.S.initialForm g :=
    M.Rg.if_mul f g hf hg
  -- transport the genuine multiplicativity along `algebraMap` and `Θ`
  have key : σ.grRes (f * g) = σ.grRes f * σ.grRes g := by
    have e1 := M.discharge (f * g) hfg
    have e2 := M.discharge f hf
    have e3 := M.discharge g hg
    rw [← e1, ← e2, ← e3, hif]
    simp only [map_mul]
  -- expand `grRes` and cancel the unit `T`
  have hw : σ.w (f * g) = σ.w f + σ.w g := σ.hwmul f g hf hg
  have lhs : σ.grRes (f * g)
      = LaurentPolynomial.C (σ.R (f * g)) * LaurentPolynomial.T (σ.w f + σ.w g) := by
    simp only [Stage.grRes, hw]
  have rhs : σ.grRes f * σ.grRes g
      = LaurentPolynomial.C (σ.R f * σ.R g) * LaurentPolynomial.T (σ.w f + σ.w g) := by
    simp only [Stage.grRes, map_mul, LaurentPolynomial.T_add]; ring
  rw [lhs, rhs] at key
  have hTne : (LaurentPolynomial.T (σ.w f + σ.w g) : LTwo ↥σ.K) ≠ 0 :=
    (LaurentPolynomial.isUnit_T (σ.w f + σ.w g)).ne_zero
  have hCeq : LaurentPolynomial.C (σ.R (f * g)) = LaurentPolynomial.C (σ.R f * σ.R g) :=
    mul_right_cancel₀ hTne key
  -- `C` injective: read coefficient at 0
  have hc := congrArg (fun x : LTwo ↥σ.K => x 0) hCeq
  simpa only [LaurentPolynomial.C_apply, if_true] using hc

#print axioms L3_residual_mul
