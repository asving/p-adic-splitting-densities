/-  MovesV unit V0-4 `xhds_instance_A2` (RE-KEYED C3) — THE NON-DEGENERACY
    WITNESS for the XHD-s format, in the (t,u) CHART where `EA2` lives. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

/-- the cleared rational form X²/((X⁶−1)(X³−1)) — denominators in the
PolyGeom class. -/
noncomputable def GA2 : Qq :=
  algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ 2)
    / algebraMap (Polynomial ℚ) Qq
        ((Polynomial.X ^ 6 - 1) * (Polynomial.X ^ 3 - 1))

/-- the seal's base value: EA2.eval ![1,0] = 7 (E at (h₀,h₂) = (4,1)). -/
theorem EA2_seal : EA2.eval ![1, 0] = 7 := by decide

theorem xhds_instance_A2 (q₀ : ℚ) (hpp : IsPP q₀) (hq : 1 < q₀)
    (hok : GA2 ∈ OKat q₀) :
    HasSum (fun h : {h // A2dom.Mem h} =>
        (q₀ : ℝ) ^ (-(EA2.eval h.1 : ℤ)))
      ((evalAt q₀ ⟨GA2, hok⟩ : ℚ) : ℝ) := by
  sorry

end LeanUrat.MovesV
