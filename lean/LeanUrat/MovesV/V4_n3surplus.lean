/-  MovesV unit V4-8 `part2_n3_zero` (PREMISE DISPLAYED C18) — at n = 3 the
    surplus vanishes IDENTICALLY, GIVEN DegCons + the displayed ContTwo
    premise.  [Gate-roster decide leg deferred with the omem-roster deviation.] -/
import LeanUrat.MovesV.V2_degcons

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the note's own argument premise: a CONTINUING cluster has size ≥ 2. -/
def ContTwo {n : ℕ} (T : MovesS.TableShape n) : Prop :=
  ∀ e (τ : T.State e) (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem,
    μ.continuing → 2 ≤ μ.size

/-- at n = 3: at most one continuing member per outcome (2 + 2 > 3). -/
theorem surplus_zero (T : MovesS.TableShape 3) (hDC : MovesS.DegCons T)
    (h2 : ContTwo T) (e : ℕ) (he : e ∈ Finset.Icc 1 3) (τ : T.State e)
    (o : T.Out e τ) :
    ((T.odata e τ o).mem.filter (fun μ => μ.status.isRight)).length ≤ 1 := by
  sorry

end LeanUrat.MovesV
