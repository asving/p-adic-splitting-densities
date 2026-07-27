/-
Unit U-17a `blockSolve_spec` (medium) — the (R_e-lump) defining equation, EVERY σ′
(R2-10: no SigSet).  moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} +
b_e^split [UNCONDITIONAL]".  `blockSolveLt` is the smaller-block restriction the
βlt slot consumes (dite-guarded on e' ∈ Icc 1 n — total in e' < e; under DegCons
every leg lands in the guard).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BlockSolve
import LeanUrat.MovesS.SolveIff

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

/-- The blockSolve-restriction fed to `bSplit`'s βlt slot. -/
noncomputable def blockSolveLt {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK)
    (e : ℕ) : ∀ e', e' < e → T.State e' → Multiset T.VType → Qq :=
  fun e' _ τ' σ'' =>
    if he' : e' ∈ Finset.Icc 1 n then blockSolve T RB hdc hK hdet e' he' τ' σ''
    else 0

theorem blockSolve_spec {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) (σ' : Multiset T.VType) (τ : T.State e) :
    blockSolve T RB hdc hK hdet e he τ σ' =
      (Kmat T RB e (hK e he) *ᵥ fun β => blockSolve T RB hdc hK hdet e he β σ') τ
      + bTerm T RB e σ' τ
      + bSplit T RB hdc e he (blockSolveLt RB hdc hK hdet e) σ' τ := by
  -- Raw one-step unfolding (past the private well-founded core): each state's entry
  -- is the corresponding component of `(1 - K_e)⁻¹ *ᵥ b`, with the SAME exit vector
  -- `b = b^{term,fin} + b^split` for every state (`blockSolveLt` is the βlt slot).
  have key : ∀ β, blockSolve T RB hdc hK hdet e he β σ' =
      ((1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
        (bTerm T RB e σ' + bSplit T RB hdc e he (blockSolveLt RB hdc hK hdet e) σ')) β := by
    intro β
    rw [blockSolve_eq]; rfl
  have hv : (fun β => blockSolve T RB hdc hK hdet e he β σ') =
      (1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
        (bTerm T RB e σ' + bSplit T RB hdc e he (blockSolveLt RB hdc hK hdet e) σ') := by
    funext β; exact key β
  -- `1 - K_e` is invertible at this block (the global determinant hypothesis).
  have hunit : IsUnit (1 - Kmat T RB e (hK e he)).det :=
    isUnit_iff_ne_zero.mpr (hdet e he)
  have hmul : (1 - Kmat T RB e (hK e he)) * (1 - Kmat T RB e (hK e he))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  -- The fixed-point identity: the solve `w = (1 - K)⁻¹ *ᵥ b` satisfies `w = K *ᵥ w + b`.
  have hsolve :
      (1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
        (bTerm T RB e σ' + bSplit T RB hdc e he (blockSolveLt RB hdc hK hdet e) σ') =
      Kmat T RB e (hK e he) *ᵥ
        ((1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
          (bTerm T RB e σ' + bSplit T RB hdc e he (blockSolveLt RB hdc hK hdet e) σ'))
        + (bTerm T RB e σ' + bSplit T RB hdc e he (blockSolveLt RB hdc hK hdet e) σ') := by
    rw [solve_iff, mulVec_mulVec, hmul, one_mulVec]
  rw [key τ, hv, congrFun hsolve τ]
  simp only [Pi.add_apply]
  ring

end LeanUrat.MovesS
