/-
Unit U4.sq2_upper  (MovesU campaign)  [RETYPED 2026-07-30 per the ratification]
moves_ref: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
           "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 +
           the CL-5 mass identification"
deps: U3.
RETYPE (ratification CRITICAL 2): the solve identification is no longer an assumed
        field — `SolveSeam.solve_stack` DERIVES finiteness + identification +
        positivity from the real MovesS solve laws (`rsh_interp`/`r_bdd` through the
        `RegPin`-transported determinant gate). The unit's hypotheses are the typed
        seams + the roster pin + (REG-p) + primality.
hypothesis_fields: EXACTLY `TreeSeam` + `SolveSeam` + `RegPin`; explicit `RegP S D`,
        `p.Prime` (F9).
-/
import Mathlib
import LeanUrat.MovesU.U3_sq2_partial

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open scoped ENNReal

variable {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p} {F : FiberSeries n p X}
  {S : SolveData n} {D : RegData p}

/-- SQ.2, the fixpoint upper bound: decided_σ(N) ≤ R_σ(p)·p^{nN} — from the DERIVED
    solve stack (real MovesS solve laws) + the DERIVED partial-sum identity. -/
theorem sq2_upper (seam : TreeSeam n p X F) (ss : SolveSeam n p C F S)
    (P : RegPin C D) (hreg : RegP S D) (hp : p.Prime) (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- The DERIVED solve stack: finiteness, the literal identification, RS.3 positivity.
  obtain ⟨_hfin, heq, hpos⟩ := ss.solve_stack P hreg hp σ
  -- U3's domination corollary, in ℝ≥0∞, with the series sum rewritten to the literal value.
  have hle : (X.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * ENNReal.ofReal (evalℝ S σ p) := by
    rw [← heq]; exact sq2_partial_le seam σ N
  have ha : (X.decided σ N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hb : (p : ℝ≥0∞) ^ (n * N) * ENNReal.ofReal (evalℝ S σ p) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)) ENNReal.ofReal_ne_top
  -- Transfer ℝ≥0∞ → ℝ (both sides finite), then compute the toReals.
  have key := (ENNReal.toReal_le_toReal ha hb).mpr hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hpos,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast] at key
  rw [mul_comm (evalℝ S σ p)]
  exact key

end LeanUrat.MovesU
