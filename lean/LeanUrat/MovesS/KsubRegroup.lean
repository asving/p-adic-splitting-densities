/-
Unit U-8 `ksub_regroup` (medium) — the symbolic (K-SUB) regrouping over
verdictImage (R9, R2-10).  moves_ref: "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′}
b_e^{term,fin}(τ)(σ′) + (branching-cell one-step mass, per cell once) = 1"
— here the LEFT regrouping identity; the `= 1` evaluation is U-9a/U-9b.
verdictImage is exhaustive for the terminal columns BY CONSTRUCTION.
sketch: partition by routeOf; fiberwise regrouping by kTarget / by verdicts.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.Dispatch
import LeanUrat.MovesS.Scs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- The route-dispatched one-step mass: J on split, TG otherwise. -/
noncomputable def routedMass {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (e : ℕ) (τ : T.State e) (o : T.Out e τ) : Qq :=
  if routeOf (T.odata e τ o) = .split then RB.J e τ o else RB.TG e τ o

theorem ksub_regroup {T : TableShape n} {M : MeasuredSide T} (RB : RatBurdens T M)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (hK : KmatHyp T e) :
    (∑ β : T.State e, Kmat T RB e hK τ β)
      + (∑ σ' ∈ verdictImage T e τ, bTerm T RB e σ' τ)
      + (∑ o ∈ splitOuts T e τ, RB.J e τ o)
    = ∑ o : T.Out e τ, routedMass RB e τ o :=
  sorry

end LeanUrat.MovesS
