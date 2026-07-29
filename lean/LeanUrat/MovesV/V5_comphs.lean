/-  MovesV unit V5-4 `comp_hsum` — (COMP-hΣ) GIVEN XHD-d/s, NO HMC: the
    unfactored per-template series, via V0-3 over the listed components. -/
import LeanUrat.MovesV.V5_comphC
import LeanUrat.MovesV.V0_partition
import LeanUrat.MovesV.V1_xhds

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)
open Classical

/-- the template weight-sum value (dite-eval over the listed components). -/
noncomputable def gcVal {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    {X : XHDw n S} {D : XHDd n S TE} (Xs : XHDs n S X D) {α}
    (γ : Template n S α) (q₀ : ℚ) : ℝ :=
  ∑ j, if hok : Xs.Gc γ j ∈ OKat q₀
    then ((evalAt q₀ ⟨Xs.Gc γ j, hok⟩ : ℚ) : ℝ) else 0

theorem comp_hsum {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (Xs : XHDs n S X D) (hTie : MarkFiberTie TE) (ε : EntShapeV n)
    (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    HasSum (fun h : {h // (D.dom γ).Mem h} => μhatVal cc ε β₀ γ h.1 q₀)
      (iotaEps cc ε β₀ q₀ * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
        * gcVal Xs γ q₀) := by
  sorry

end LeanUrat.MovesV
