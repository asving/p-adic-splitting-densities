/-  MovesV unit V5-2c `comp_h` — (COMP-h) ASSEMBLED, ε concrete, h FIXED in
    H(γ) (counting-native, exact at stabilized levels).  μhatVal/iotaEps
    (NAME→HOME) = the stabilized values. -/
import LeanUrat.MovesV.V5_comphB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the stabilized marked-event value. -/
noncomputable def μhatVal {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (cc : CompCarrier V TE)
    (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α)
    (h : Hpt γ.D) (q₀ : ℚ) : ℝ :=
  cc.μhatN ε β₀ γ h q₀ (compLvl V TE ε γ)

/-- the stabilized entrance value. -/
noncomputable def iotaEps {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (cc : CompCarrier V TE)
    (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ) : ℝ :=
  cc.ιN ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)

theorem comp_h {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (hcp : CompProduct cc X)
    (hTie : MarkFiberTie TE) (ε : EntShapeV n) (β₀ : S.Cell)
    {α} (γ : Template n S α) (h : Hpt γ.D) (hmem : (D.dom γ).Mem h)
    {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    ∀ N ≥ compLvl V TE ε γ,
      cc.μhatN ε β₀ γ h q₀ N
        = cc.ιN ε β₀ q₀ N * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
            * gProd X γ h q₀ := by
  cases γ with
  | last mv => exact comp_h_one cc P X U hcp ε β₀ mv h hq
  | lastT mv =>
    -- the terminal-move leg, through the M3 NAMED OPEN ROW `CompProduct`
    -- (the old carrier-field route is deleted; see V5_comphA).
    exact fun N hN => hcp ε β₀ (.lastT mv) h hq N hN
  | cons mv γ => exact comp_h_step cc P X U hcp hTie ε β₀ mv γ h hmem hq

end LeanUrat.MovesV
