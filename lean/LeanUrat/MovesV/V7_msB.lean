/-  MovesV unit V7-4b `measured_entrance_inst` — the ENTRANCE SIDE at A-1's
    granularity (EntShape := EntIx; ιshH the §2.G def; entCount the census;
    hent := hentCode at the base instantiation — SF-1's record stands). -/
import LeanUrat.MovesV.V7_msA
import LeanUrat.MovesV.V3_aggfullB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem measured_entrance_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (T : MovesS.TableShape n) (hfin : Finite (EntTemplate n)) :
    ∃ M : MovesS.MeasuredSide T,
      ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
        (M.entInst e τ ε q₀ (M.entLvl e τ ε)).card = M.entCount e τ ε q₀ := by
  sorry

end LeanUrat.MovesV
