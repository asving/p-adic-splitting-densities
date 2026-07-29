/-  MovesV unit V5-3 `comp_h_count` — THE COUNT SHADOW: Ĉ = I^ent·C_γ at the
    same concrete ε; degree ≤ W_ent(ε) + W(γ); fences typed as non-lemmas. -/
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V3_entcount

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the entrance count factor (ENT-COUNT's chosen polynomial). -/
noncomputable def entCountPolyC {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (hEC : EntCount V) (ε : EntShapeV n)
    (β₀ : S.Cell) (hR : Realizable V ε β₀) : Polynomial ℚ :=
  (hEC ε β₀ hR).choose

/-- the count shadow Ĉ_{ε,γ}(q) := I^ent·C_γ — the entrance factor never
omitted. -/
noncomputable def cshadowPoly {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (hEC : EntCount V) (ε : EntShapeV n)
    (β₀ : S.Cell) (hR : Realizable V ε β₀) {α} (γ : Template n S α) :
    Polynomial ℚ :=
  entCountPolyC hEC ε β₀ hR * pathProdPoly V γ

theorem count_shadow_deg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (hEC : EntCount V) (ε : EntShapeV n)
    (β₀ : S.Cell) (hR : Realizable V ε β₀) {α} (γ : Template n S α) :
    (cshadowPoly hEC ε β₀ hR γ).natDegree ≤ ε.Went + Wtmpl V γ := by
  sorry

end LeanUrat.MovesV
