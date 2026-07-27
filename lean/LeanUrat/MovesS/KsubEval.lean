/-
Unit U-9a `ksub_eval` (medium) — ACTIVITY-GUARDED evaluated (K-SUB) = 1 (R13).
hyp: LedgerIV.part1 + rep_indep (both guarded) + RB.tg_interp/j_interp — the
note's bracket "GIVEN the (iv) ledger + DEG-CONS + the (m, c) CLASSIFICATION with
its (SCS) clause", scoped "restricted per CTS-M(ii) to the ACTIVE block".
sketch: interp → rowVal; rep_indep → x-grouped cell sum; Finset.sum_fiberwise
over cellOut; part1 → 1.  The OKat membership of the routed sum is subring
closure over tg_ok/j_ok (existential-packaged here).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.KsubRegroup

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem ksub_eval {T : TableShape n} {M : MeasuredSide T} (RB : RatBurdens T M)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    ∃ hok : (∑ o : T.Out e τ, routedMass RB e τ o) ∈ OKat q₀,
      evalAt q₀ ⟨∑ o : T.Out e τ, routedMass RB e τ o, hok⟩ = 1 :=
  sorry

end LeanUrat.MovesS
