/-
Unit U-9b `ksub` (medium) — the SYMBOLIC (K-SUB) `= 1` in Qq, via U-9a at every
ALL-ACTIVE pool (activity supplied by the locus) + U-27 infinitude on U-22b's
derived infinitude (R39).  deps: U-8, U-9a, U-22b, U-27.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.KsubEval

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem ksub {T : TableShape n} {M : MeasuredSide T} (RB : RatBurdens T M)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    ∑ o : T.Out e τ, routedMass RB e τ o = 1 :=
  sorry

end LeanUrat.MovesS
