import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

set_option linter.style.longLine false
set_option linter.style.header false

theorem L3_rank1_residual (σ : Stage p F) (M : GenuineStageModel σ) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : letI := M.Rg.ring; letI := M.Loring; letI := M.alg; M.Θ (algebraMap M.S.Gr M.Lo (M.S.initialForm f)) * LaurentPolynomial.T (- σ.w f) = LaurentPolynomial.C (σ.R f) := by
  rw [M.discharge f hf]
  exact σ.grRes_mul_T_neg f
