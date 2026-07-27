/-
Unit U-24a2 `interp_read_off` (easy) — the (ii-c) gate consumed (C1).
moves_ref: "the sealed check that the evaluated object's q₀-value … equals the
active-subsystem solve there must pass BEFORE it may be read off; a pole SURVIVING
cancellation at a wild pool is (ii-c)'s FAIL" + the (e3)-FENCE.  sketch: AVAgree
supplies hok + the active-solve value; rewrite with U-24a1.  Uncancelled wild
poles are EXCLUDED BY HYPOTHESIS — never claimed absent.
-/
import LeanUrat.MovesS.ActiveSolve
import LeanUrat.MovesS.BlockSolve

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

theorem interp_read_off {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (B : RS1Bundle T M RB hdc hK) (L : LedgerIV T M) (hdet : DetHyp T RB hK)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) {q₀ : ℚ}
    (P : PoolHyp T M RB e (hK e he) q₀)
    (σ' : Multiset T.VType) (h_ent : ℕ) (τA : P.Act)
    (hAV : AVAgree P (blockSolve T RB hdc hK hdet e he (↑τA) σ')
      (bhatMeas P (fun e' he' => B.βmeas e' he' h_ent) σ') τA) :
    ∃ hok : blockSolve T RB hdc hK hdet e he (↑τA) σ' ∈ OKat q₀,
      ((evalAt q₀ ⟨blockSolve T RB hdc hK hdet e he (↑τA) σ', hok⟩ : ℚ) : ℝ)
        = B.βmeas e he h_ent (↑τA) σ' q₀ :=
  sorry

end LeanUrat.MovesS
