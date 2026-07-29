/-  MovesV unit V5-6 `comp_agg` — (COMP-AGG) GIVEN (COMP-Σ) + (iii) +
    (iv)-REP: summing over instantiations then templates — entrance heights
    EXACTLY ONCE; the common continuation factor pulled out by (iv)-REP;
    counts do NOT aggregate.  `aggMass` (NAME→HOME). -/
import LeanUrat.MovesV.V5_compsig
import LeanUrat.MovesV.V3_aggfullB
import LeanUrat.MovesV.V4_rep

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the ε̊-and-height double aggregate ((COMP-Σ)-shaped summands). -/
noncomputable def aggMass {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (cc : CompCarrier V TE)
    {X : XHDw n S} {D : XHDd n S TE} (Xs : XHDs n S X D)
    (β₀ : S.Cell) {α} (γ : Template n S α) (q₀ : ℚ) : ℝ :=
  ∑' εT : EntTemplate n, ∑' h : {h // (V.entDom εT).Mem h},
    iotaEps cc (writeHeights εT h.1) β₀ q₀ * stepProdVal V Xs γ q₀

theorem comp_agg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (Xs : XHDs n S X D) (XsEnt : XHDsEnt n S V) (DE : XHDdEnt n S V)
    (hTie : MarkFiberTie TE) (hHMC : HMC TE D) (hEU : EntU V)
    (hobs : ∀ s : Skeleton n, ObsCheck (C.bd s))
    (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    aggMass cc Xs β₀ γ q₀ = iotaValV V XsEnt β₀ q₀ * stepProdVal V Xs γ q₀ := by
  sorry

end LeanUrat.MovesV
