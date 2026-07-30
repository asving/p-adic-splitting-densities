/-
Unit U-16b `blockSolve` (medium) — the triangular bottom-up solve.
moves_ref: "blocks solve bottom-up, each b_e^split leg already solved"; body
`(1 - Kmat T RB e (hK e he))⁻¹ *ᵥ (bTerm T RB e σ' + bSplit T RB hdc e he βlt σ')`
by strong recursion on e ∈ Icc 1 n (σ′ UNRESTRICTED per R2-10).
Filled def (E-phase, WF recursion on `e`); the defining equation is U-17a's statement.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

/-- Strong-recursion core of `blockSolve`: the triangular fixed-point vector
`(1 - K_e)⁻¹ *ᵥ (b_e^{term,fin} + b_e^split)`, where the split legs feed back the
solves at strictly smaller block sizes (dite-guarded onto `Icc 1 n`; junk `0`
off it — every actual continuing leg has size in `Icc 1 n` by DegCons + (K-TRI),
so the guard is never hit on the support).  Well-founded on `e`. -/
private noncomputable def blockSolveCore (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (σ' : Multiset T.VType) : Qq :=
  ((1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
    (fun τ' => bTerm T RB e σ' τ' +
      bSplit T RB hdc e he
        (fun e' hlt τ'' σ'' =>
          if he' : e' ∈ Finset.Icc 1 n then
            blockSolveCore T RB hdc hK hdet e' he' τ'' σ''
          else 0)
        σ' τ')) τ
termination_by e
decreasing_by exact hlt

noncomputable def blockSolve (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK) :
    ∀ e, e ∈ Finset.Icc 1 n → T.State e → Multiset T.VType → Qq :=
  blockSolveCore T RB hdc hK hdet

/-- One-step unfolding of `blockSolve` past the `private` well-founded core: the
raw triangular-solve equation `blockSolve = (1 - K_e)⁻¹ *ᵥ (b^{term,fin} + b^split)`.
Public bridge consumed by U-17a `blockSolve_spec` (which cannot reach the private
`blockSolveCore` equation lemma across files). -/
theorem blockSolve_eq (T : TableShape n) {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (hdet : DetHyp T RB hK)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (σ' : Multiset T.VType) :
    blockSolve T RB hdc hK hdet e he τ σ' =
      ((1 - Kmat T RB e (hK e he))⁻¹ *ᵥ
        (bTerm T RB e σ' +
          bSplit T RB hdc e he
            (fun e' _ τ' σ'' =>
              if he' : e' ∈ Finset.Icc 1 n then
                blockSolve T RB hdc hK hdet e' he' τ' σ''
              else 0) σ')) τ := by
  conv_lhs => unfold blockSolve blockSolveCore
  rfl

end LeanUrat.MovesS
