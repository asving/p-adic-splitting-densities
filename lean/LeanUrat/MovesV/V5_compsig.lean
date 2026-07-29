/-  MovesV unit V5-5 `comp_sigma` — (COMP-Σ) GIVEN additionally HMC (the tag
    rides — every consumer carries hHMC).  `stepProdVal` (NAME→HOME). -/
import LeanUrat.MovesV.V5_comphs
import LeanUrat.MovesV.V4_naming

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- ∏ᵢ Tᵢ.eval·ΣGᵢ over the template's step decomposition. -/
noncomputable def stepProdVal {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} {X : XHDw n S}
    {D : XHDd n S TE} (Xs : XHDs n S X D) :
    ∀ {α}, Template n S α → ℚ → ℝ
  | _, .last mv, q₀ =>
      (((tblOf V mv).eval q₀ : ℚ) : ℝ) * gcVal Xs (.last mv) q₀
  | _, .lastT mv, q₀ =>
      (((tblOfT V mv).eval q₀ : ℚ) : ℝ) * gcVal Xs (.lastT mv) q₀
  | _, .cons mv γ, q₀ =>
      (((tblOf V mv).eval q₀ : ℚ) : ℝ) * gcVal Xs (.last mv) q₀
        * stepProdVal V Xs γ q₀

theorem comp_sigma {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (Xs : XHDs n S X D) (hTie : MarkFiberTie TE) (hHMC : HMC TE D)
    (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) :
    iotaEps cc ε β₀ q₀ * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
        * gcVal Xs γ q₀
      = iotaEps cc ε β₀ q₀ * stepProdVal V Xs γ q₀ := by
  sorry

end LeanUrat.MovesV
