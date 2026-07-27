/-
Unit `n2_sigmas` (easy; S5 chain batch) — THE FULL RS4Chain instance (R46,
Codex#7-2 = Fable#8-F2: no partial structures; every field listed at its owning
unit; the device shallow data enter via n2_wshp_device/n2_sh_events/n2_sh_laws).
This unit's display: sig_exact forces Sigmas = {(1,1)², (1,2), (2,1)}, the three
degree-2 multisets.
-/
import LeanUrat.MovesS.N2Beta
import LeanUrat.MovesS.N2ShapeFam

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

/-- The gate's RS4Chain (FULL instantiation; wave-4 re-keying replaces exactly the
device fields named at §W4-SYNC S-8/S-10). -/
noncomputable def n2Chain : RS4Chain n2T n2M n2RB n2hdc n2hK n2F := sorry

theorem n2_sigmas :
    n2Chain.Sigmas = {{n2v11, n2v11}, {n2v12}, {n2v21}} :=
  sorry

end LeanUrat.MovesS
