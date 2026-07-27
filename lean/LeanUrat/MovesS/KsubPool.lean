/-
Unit U-10 `ksub_pool` (medium) — sub-stochastic active rows over Aℝ (D11/R22);
nonnegativity DERIVED and ROUTED (R2-12); `he` binder (Fable2-G3).
moves_ref: "K_e's rows are genuine sub-distributions … every summand ≥ 0 (the
ns-bound tail rides INSIDE the K_e term)".  hyp: LedgerIV + RatBurdens ONLY — for
non-split o, eval TG = rowVal = Σ μcell ≥ 0 (tg_interp + rep_indep + μcell-nonneg
from meas_card's card ratios + xhd_sum); split o likewise via j_interp.  NO
hypothesis about TG on split or J on non-split exists anywhere.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.KsubEval

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

theorem ksub_pool {T : TableShape n} {M : MeasuredSide T} {RB : RatBurdens T M}
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (L : LedgerIV T M)
    {hK : KmatHyp T e} {q₀ : ℚ} (P : PoolHyp T M RB e hK q₀) (τA : P.Act) :
    (∀ βA : P.Act, 0 ≤ Aℝ P τA βA) ∧ (∑ βA : P.Act, Aℝ P τA βA) ≤ 1 :=
  sorry

end LeanUrat.MovesS
