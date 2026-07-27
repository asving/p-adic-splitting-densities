/-
Unit U-17b `rexact_solve` (medium) — (R_e-exact) from `rexact` + `nsNull`,
POOL-GUARDED (R47/Fable#8-F1: the display matches the R40-quantified §2.D field;
βfull at q₀ ∉ Pools is unconstrained data).  moves_ref: "(R_e-exact) β_e^full =
β_e [GIVEN (ns-null) — CLOSED at [3t] §T.2]".  sketch: fire `rexact`.
-/
import LeanUrat.MovesS.Interfaces

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem rexact_solve {T : TableShape n} {M : MeasuredSide T} {RB : RatBurdens T M}
    {hdc : DegCons T} {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (B : RS1Bundle T M RB hdc hK) (hns : B.nsNull) :
    ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
      (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
      B.βfull e he h_ent τ σ' q₀ = B.βmeas e he h_ent τ σ' q₀ :=
  B.rexact hns

end LeanUrat.MovesS
