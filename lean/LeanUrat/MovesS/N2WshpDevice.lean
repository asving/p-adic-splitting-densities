/-
Unit `n2_wshp_device` (easy; S5 shallow-device batch, DEVICE-ONLY — R46/R52;
wave-4 re-keying REPLACES these fields, §W4-SYNC S-8/S-10) — WshP ≡ the
1-presentation (countT = countS = 1, geom = 1, qpow = 0) on the root shape
(Rsh σ = the blockSolve values — Fable-verified); WshVal := its evaluations;
wsh_ok/wsh_interp ride the trivial denominator.
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_wshp_device :
    (∀ Ŝ : Shape n2T, (n2Chain.WshP Ŝ).countT = 1 ∧ (n2Chain.WshP Ŝ).countS = 1 ∧
      (n2Chain.WshP Ŝ).geom = 1 ∧ (n2Chain.WshP Ŝ).qpow = 0) ∧
    (∀ Ŝ ∈ n2F.Sh, ∀ q₀ ∈ n2M.Pools, n2Chain.WshVal Ŝ q₀ = 1) :=
  sorry

end LeanUrat.MovesS
