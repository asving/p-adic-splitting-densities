/-
Unit U-24a1 `active_solve_meas` (medium) — REDESIGNED (Fable C1; R14): the
measured value IS the active-subsystem solve, PER POOL, guards consumed.
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)"
+ "Every probabilistic claim in S.4/SQ.2 is about K_e restricted per CTS-M(ii) to
the ACTIVE block".  hyp: B.recursion_meas (W-3) + B.xrb + P (E0 inside) + L
(act_target + inactive_vanish give SUBSYSTEM CLOSURE).  sketch: β̂ := (βmeas ·)_Act
satisfies β̂ = Â β̂ + b̂ by recursion_meas restricted along the closure; (1 − Â)
invertible by U-21c on P.e0 (empty Act: trivial); uniqueness of the evaluated
solution.  NO induction, NO leg evaluation, NO hok claim — the legs enter b̂ as
measured values (D11: ℚ-matrix mapped ONCE through Aℝ, everything else ℝ).
CLOSES from the note's own display.
-/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.SolveIff
import LeanUrat.MovesS.SolveExistsUnique
import LeanUrat.MovesS.E0DetNeZero

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

/-- The D11 det transport (R19: `RingHom.map_det` + `Rat.cast_injective`). -/
theorem Aℝ_det_iff {T : TableShape n} {M : MeasuredSide T} {RB : RatBurdens T M}
    {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ} (P : PoolHyp T M RB e hK q₀) :
    (1 - Aℝ P).det ≠ 0 ↔ (1 - P.A).det ≠ 0 :=
  sorry

theorem active_solve_meas {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (B : RS1Bundle T M RB hdc hK) (L : LedgerIV T M)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) {q₀ : ℚ}
    (P : PoolHyp T M RB e (hK e he) q₀)
    (σ' : Multiset T.VType) (h_ent : ℕ) (τA : P.Act) :
    B.βmeas e he h_ent (↑τA) σ' q₀
      = ((1 - Aℝ P)⁻¹ *ᵥ bhatMeas P (fun e' he' => B.βmeas e' he' h_ent) σ') τA :=
  sorry

end LeanUrat.MovesS
