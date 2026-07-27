/-
Unit U4.sq2_upper  (MovesU campaign)  [conditional]
moves_ref: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
           "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 +
           the CL-5 mass identification"
deps: U3.
sketch (F8's repair): `SS.solve_stack hreg σ` GIVES `0 ≤ evalℝ S σ p` as its third
        conjunct — no bogus case split. Transfer ℝ≥0∞ → ℝ from U3's corollary (fired
        on `FS`): `ENNReal.toReal_le_toReal` (LHS ≠ ⊤ since the RHS is finite),
        `ENNReal.toReal_mul`, `ENNReal.toReal_ofReal` (nonnegativity = the positivity
        conjunct).
hypothesis_fields: EXACTLY `FinStack` + `SolveStack` (the (U-n) upper side's displayed
        citation list, D12 — NO CL-2/CL-3/CL-4, NO RS.4, NO O3; VP-SOUND rides IN
        FinStack via `cl10_vpsound`, per the whole-CL-10 citation); explicit
        `RegP S D`, `p.Prime` (F9: never `1 < p`; ruling (D): `hreg` also gives
        `DefinedAt (S.R σ) p`, so `evalℝ` is the genuine literal value, never junk).
-/
import Mathlib
import LeanUrat.MovesU.U3_sq2_partial

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

variable {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X}
  {S : SolveData n} {D : RegData p} {M : MenuData} {K : KernelStatements}

/-- SQ.2, the fixpoint upper bound: decided_σ(N) ≤ R_σ(p)·p^{nN}. -/
theorem sq2_upper (FS : FinStack n p X F K) (SS : SolveStack n p X F S D M K)
    (hreg : RegP S D) (hp : p.Prime) (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N) :=
  sorry

end LeanUrat.MovesU
