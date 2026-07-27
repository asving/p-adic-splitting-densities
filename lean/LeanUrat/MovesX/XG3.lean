/-
Unit XG.3 x3Density — the density limit, DERIVED (finding 11: no detectInter, no
MassLink)  [E-phase: stated, body sorry]
moves_ref: "(X.3) … μ(Undec(N)) → 0 (N → ∞)" + CONDITIONALITY SUMMARY "X.3 = [routes] +
(ns-null, closed, tag displayed) + accepted perimeter".
sketch: ⋂Undec ⊆ InfTree ∪ ⋃ns (XG.2c); InfTree ⊆ discZero (XG.2d contrapositive);
frac(discZero) = 0 (XF.10); frac(⋃ns) = 0 (NS + nsCountable + frac_iUnion_null);
frac_mono/union_le ⟹ frac(⋂) = 0; frac_inter_tendsto + undec_antitone close the limit.
deps: XG.2c, XG.2d, XF.10, XD.1. difficulty: HARD (MEDIUM-HARD band).
hyp_fields: X3aRouteP, NsNullP (tag) — NOTHING else beyond XCtx's audited inputs.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XD1
import LeanUrat.MovesX.XF10
import LeanUrat.MovesX.XG2c
import LeanUrat.MovesX.XG2d

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x3Density {n : ℕ} (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (X.ctx p).frac ((X.ctx p).Undec N)) Filter.atTop (nhds 0) := by
  sorry

end LeanUrat.MovesX
