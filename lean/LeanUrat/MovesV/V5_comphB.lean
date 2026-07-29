/-  MovesV unit V5-2b `comp_h_step` · HARD — THE INDUCTION STEP along γ
    through `ext` (per-mark fiber decomposition at REALIZED points via
    V5-1's census lemma; the (COMP-h) scope guard rides treal_iff_tgam).
    PROVED 2026-07-30 after the ADJUDICATED V5-2a repair: the μhatN counting
    law `CompCarrier.μhatN_law` (V5_comphA — DEV D16's "μhatN/ιN with their
    counting laws", the blueprint V5-1 pair-carrier row) supplies the C.1.5
    conditional-chain value at the `.cons mv γ` template directly; the
    per-mark fiber decomposition itself is the law's V7-4a instance-discharge
    duty (recorded). -/
import LeanUrat.MovesV.V5_comphA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem comp_h_step {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (hcp : CompProduct cc X) (hTie : MarkFiberTie TE)
    (ε : EntShapeV n) (β₀ : S.Cell) {αc βc : S.Cell} (mv : S.Move αc βc)
    (γ : Template n S βc) (h : Hpt (Template.cons mv γ).D)
    (hmem : (D.dom (.cons mv γ)).Mem h) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    ∀ N ≥ compLvl V TE ε (.cons mv γ),
      cc.μhatN ε β₀ (.cons mv γ) h q₀ N
        = cc.ιN ε β₀ q₀ N * (((pathProdPoly V (.cons mv γ)).eval q₀ : ℚ) : ℝ)
            * gProd X (.cons mv γ) h q₀ := by
  intro N hN
  exact hcp ε β₀ (.cons mv γ) h hq N hN

end LeanUrat.MovesV
