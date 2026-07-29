/-  MovesV unit V7-3d `stage_law_burden` (NEW TYPE, Codex-20) — the general
    SCSData/KmatHyp supply as a TYPE.  [E-PHASE FORM: stated over an ABSTRACT
    TableShape + supplier data (the `*Of` functions ride as parameters until
    V7-3a/c's instance lands) — MANIFEST deviations.] -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the typed stage-law burden at a table shape T with supplier data
(the VERBATIM MovesS.SCSData laws at those data + KmatHyp/DegCons). -/
structure StageLawBurden (n : ℕ) (T : MovesS.TableShape n)
    (scs : MovesS.SCSData T) : Prop where
  kmat_all : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e
  degcons_all : MovesS.DegCons T

end LeanUrat.MovesV
