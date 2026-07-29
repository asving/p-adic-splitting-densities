/-  MovesV unit V3-8b `ent_agg_ival` — THE ιval IDENTIFICATION, GIVEN
    additionally (ENT-U) — the note's own INIT-RAT line's entry point.
    (`iotaValV`/`iotaShV` — the ledger-level ιval/ιsh defs, one definition,
    two homes recorded per the NAME→HOME table.) -/
import LeanUrat.MovesV.V3_aggfullA
import LeanUrat.MovesV.V3_entu

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

open Classical in
/-- ιsh per EntIx member: count × WEIGHT-ONLY sum (Codex-8's split). -/
noncomputable def iotaShV {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) {β₀ : S.Cell}
    (i : V.EntIx β₀) (q₀ : ℚ) : ℝ :=
  if hq : q₀ ∈ V.Pools then
    (V.entCount i q₀ : ℝ) * ((evalAt q₀ ⟨XsEnt.Gent β₀ i, XsEnt.Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ)
  else 0

open Classical in
/-- ιval: the finite EntIx aggregate (finiteness via V3-4 × list length). -/
noncomputable def iotaValV {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (β₀ : S.Cell)
    (q₀ : ℚ) : ℝ :=
  haveI : Finite (EntTemplate n) := template_finite n
  haveI : Finite (V.EntIx β₀) := by unfold CtsMeasured.EntIx; exact
    Subtype.finite
  haveI : Fintype (V.EntIx β₀) := Fintype.ofFinite _
  ∑ i : V.EntIx β₀, iotaShV V XsEnt i q₀

theorem ent_agg_ival {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (DE : XHDdEnt n S V)
    (hEU : EntU V) (β₀ : S.Cell) (q₀ : ℚ) (hq : q₀ ∈ V.Pools) :
    HasSum
      (fun p : Σ i : V.EntIx β₀,
          {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V p.1.1.1 p.2.1 β₀ q₀) (iotaValV V XsEnt β₀ q₀) := by
  sorry

end LeanUrat.MovesV
