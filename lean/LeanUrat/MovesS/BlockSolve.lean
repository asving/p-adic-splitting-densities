/-
Unit U-16b `blockSolve` (medium) — the triangular bottom-up solve.
moves_ref: "blocks solve bottom-up, each b_e^split leg already solved"; body
`(1 - Kmat T RB e (hK e he))⁻¹ *ᵥ (bTerm T RB e σ' + bSplit T RB hdc e he βlt σ')`
by strong recursion on e ∈ Icc 1 n (σ′ UNRESTRICTED per R2-10).
Sorried def (E-phase); the defining equation is U-17a's statement.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

noncomputable def blockSolve (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK) :
    ∀ e, e ∈ Finset.Icc 1 n → T.State e → Multiset T.VType → Qq :=
  sorry

end LeanUrat.MovesS
